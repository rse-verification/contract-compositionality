open HolKernel boolLib Parse bossLib pred_setTheory combinTheory stringTheory string_numTheory listTheory nlistTheory folLangTheory folModelsTheory;

val _ = new_theory "folString";

Datatype:
 sterm = SV string | SFn string (sterm list)
End

Datatype:
 sform = SFalse
 | STrue
 | SPred string (sterm list)
 | SNot sform
 | SAnd sform sform
 | SOr sform sform
 | SImp sform sform
 | SIff sform sform
 | SForall string sform
 | SExists string sform
End

Datatype:
  smodel =
   <| SDom : 'a set ; SFun : string -> 'a list -> 'a ;
      SPred : string -> 'a list -> bool |>
End

val sterm_size_def = DB.fetch "-" "sterm_size_def";
val _ = export_rewrites ["sterm_size_def"];

val smodel_component_equality = DB.fetch "-" "smodel_component_equality";

Theorem sterm_size_lemma[simp]:
 !x l a. MEM a l ==> sterm_size a < 1 + (x + sterm1_size l)
Proof
  rpt gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >> simp [] >>
  res_tac >> simp []
QED

Theorem sterm_induct:
 !P. (!v. P (SV v)) /\ (!n ts. (!t. MEM t ts ==> P t) ==> P (SFn n ts)) ==> !t. P t
Proof
 rpt strip_tac >>
 qspecl_then [`P`, `\ts. !t. MEM t ts ==> P t`]
   (assume_tac o SIMP_RULE bool_ss [])
   (TypeBase.induction_of ``:sterm``) >> rfs[] >>
 fs[DISJ_IMP_THM, FORALL_AND_THM]
QED

val _ = TypeBase.update_induction sterm_induct;

Definition stermval[simp]:
 (stermval M v (SV x) = v x)
 /\
 (stermval M v (SFn f l) = M.SFun f (MAP (stermval M v) l))
Termination
  WF_REL_TAC `measure (sterm_size o SND o SND)` >> simp []
End

Definition sholds:
 (sholds M v SFalse = F)
 /\
 (sholds M v STrue = T)
 /\
 (sholds M v (SPred s l) = M.SPred s (MAP (stermval M v) l))
 /\
 (sholds M v (SNot sf) = (~ sholds M v sf))
 /\
 (sholds M v (SAnd sf1 sf2) = (sholds M v sf1 /\ sholds M v sf2))
 /\
 (sholds M v (SOr sf1 sf2) = (sholds M v sf1 \/ sholds M v sf2))
 /\
 (sholds M v (SImp sf1 sf2) = (sholds M v sf1 ==> sholds M v sf2))
 /\
 (sholds M v (SIff sf1 sf2) = (sholds M v sf1 <=> sholds M v sf2))
 /\
 (sholds M v (SForall s sf) = !a. a IN M.SDom ==> sholds M ((s =+ a)v) sf)
 /\
 (sholds M v (SExists s sf) = ?a. a IN M.SDom /\ sholds M ((s =+ a)v) sf)
End

(* ----------------------- *)
(* string-num translations *)
(* ----------------------- *)

Definition sterm2term:
 (sterm2term (SV s) = V (s2n s))
 /\
 (sterm2term (SFn s stl) = Fn (s2n s) (MAP sterm2term stl))
Termination
  WF_REL_TAC `measure sterm_size` >> simp []
End

Definition term2sterm:
 (term2sterm (V n) = SV (n2s n))
 /\
 (term2sterm (Fn n tl) = SFn (n2s n) (MAP term2sterm tl))
Termination
  WF_REL_TAC `measure term_size` >> simp []
End

Definition sform2form:
 (sform2form SFalse = False)
 /\
 (sform2form STrue = True)
 /\
 (sform2form (SPred s stl) = Pred (s2n s) (MAP sterm2term stl))
 /\
 (sform2form (SNot sf) = Not (sform2form sf))
 /\
 (sform2form (SAnd sf1 sf2) = And (sform2form sf1) (sform2form sf2))
 /\
 (sform2form (SOr sf1 sf2) = Or (sform2form sf1) (sform2form sf2))
 /\
 (sform2form (SImp sf1 sf2) = IMP (sform2form sf1) (sform2form sf2))
 /\
 (sform2form (SIff sf1 sf2) = Iff (sform2form sf1) (sform2form sf2))
 /\
 (sform2form (SForall s sf) = FALL (s2n s) (sform2form sf))
 /\
 (sform2form (SExists s sf) = Exists (s2n s) (sform2form sf))
End

Definition form2sform:
 (form2sform False = SFalse)
 /\
 (form2sform (Pred n tl) = SPred (n2s n) (MAP term2sterm tl))
 /\
 (form2sform (IMP f1 f2) = SImp (form2sform f1) (form2sform f2))
 /\
 (form2sform (FALL n f) = SForall (n2s n) (form2sform f))
End

Definition smodel2model:
 smodel2model M =
  <| Dom := M.SDom ; Fun := M.SFun o n2s ; Pred := M.SPred o n2s |>
End

Definition model2smodel:
 model2smodel M =
  <| SDom := M.Dom ; SFun := M.Fun o s2n ; SPred := M.Pred o s2n |>
End

(* --------------- *)
(* utility results *)
(* --------------- *)

Theorem MEM_MAP_all:
 !f g h l.
  (!a. MEM a l ==> f a = g (h a)) ==>
  MAP (\b. f b) l = MAP (\c. g c) (MAP (\d. h d) l)
Proof
 strip_tac >> strip_tac >> strip_tac >>
 Induct_on `l` >> rw [] 
QED

Theorem UPDATE_n2s_s2n_eq:
 !s a v. (((s =+ a)v) o n2s) = (((s2n s) =+ a)(v o n2s))
Proof
 rw [] >>
 match_mp_tac EQ_EXT >>
 rw [APPLY_UPDATE_THM] >-
 fs [s2n_n2s] >>
 fs [n2s_s2n]
QED

Theorem UPDATE_s2n_n2s_eq:
 !n a v. (((n =+ a)v) o s2n) = (((n2s n) =+ a)(v o s2n))
Proof
 rw [] >>
 match_mp_tac EQ_EXT >>
 rw [APPLY_UPDATE_THM] >-
 fs [n2s_s2n] >>
 fs [s2n_n2s]
QED

(* ----------------- *)
(* semantic mappings *)
(* ----------------- *)

Theorem sterm2term_term2sterm:
 !t. sterm2term (term2sterm t) = t
Proof
 ho_match_mp_tac term_induct >> rw [sterm2term,term2sterm] >>
 Induct_on `ts` >> fs [] >> rw []
QED

Theorem term2term_sterm2sterm:
 !st. term2sterm (sterm2term st) = st
Proof
 ho_match_mp_tac sterm_induct >> rw [sterm2term,term2sterm] >>
 Induct_on `ts` >> fs [] >> rw []
QED

Theorem sform2form_form2sform:
 !f. sform2form (form2sform f) = f
Proof
 Induct_on `f` >> rw [sform2form,form2sform] >>
 Induct_on `l` >> fs [] >> rw [sterm2term_term2sterm]
QED

Theorem smodel2model_model2smodel:
 !M. smodel2model (model2smodel M) = M
Proof
 rw [smodel2model,model2smodel,model_component_equality] >>
 match_mp_tac EQ_EXT >> rw []
QED

Theorem model2smodel_smodel2model:
 !M. model2smodel (smodel2model M) = M
Proof
 rw [smodel2model,model2smodel,smodel_component_equality] >>
 match_mp_tac EQ_EXT >> rw []
QED

Theorem holds_n2s_n2s:
 !M f v a s0.
  holds M (((s0 =+ a)v) o n2s) f <=> holds M (((s2n s0) =+ a)(v o n2s)) f
Proof
 rw [UPDATE_n2s_s2n_eq]
QED

Theorem sholds_s2n_s2n:
 !M sf v a n.
  sholds M (((n =+ a)v) o s2n) sf <=> sholds M (((n2s n) =+ a)(v o s2n)) sf
Proof
 rw [UPDATE_s2n_n2s_eq]
QED

Theorem stermval_termval:
 !M v st.
  stermval M v st = termval (smodel2model M) (v o n2s) (sterm2term st)
Proof
 strip_tac >> strip_tac >>
 ho_match_mp_tac sterm_induct >>
 rw [stermval,termval_def,smodel2model,sterm2term] >>
 METIS_TAC [MEM_MAP_all]
QED

(* FIXME: better proof using equalities likely possible *)
Theorem termval_stermval:
 !M v t.
  termval M v t = stermval (model2smodel M) (v o s2n) (term2sterm t)
Proof
 strip_tac >> strip_tac >>
 ho_match_mp_tac term_induct >>
 rw [stermval,termval_def,model2smodel,term2sterm] >>
 METIS_TAC [MEM_MAP_all]
QED

Theorem map_stermval_termval:
 !M v l.
  MAP (stermval M v) l = MAP (termval (smodel2model M) (v o n2s)) (MAP sterm2term l)
Proof
 strip_tac >> strip_tac >> Induct_on `l` >> rw [stermval_termval]
QED

Theorem map_termval_stermval:
 !M v l.
  MAP (termval M v) l = MAP (stermval (model2smodel M) (v o s2n)) (MAP term2sterm l)
Proof
 strip_tac >> strip_tac >> Induct_on `l` >> rw [termval_stermval]
QED

Theorem sholds_holds:
 !M v sf. sholds M v sf <=> holds (smodel2model M) (v o n2s) (sform2form sf)
Proof
 Induct_on `sf` >> rw [sholds,holds_def,sform2form] >| [
  rw [smodel2model,map_stermval_termval],
  EQ_TAC >> rw [smodel2model] >> METIS_TAC [holds_n2s_n2s],
  EQ_TAC >> rw [smodel2model] >> METIS_TAC [holds_n2s_n2s]
 ]
QED

Theorem holds_sholds:
 !M v f. holds M v f <=> sholds (model2smodel M) (v o s2n) (form2sform f)
Proof
 Induct_on `f` >> rw [sholds,holds_def,form2sform] >| [
  rw [model2smodel,map_termval_stermval],
  EQ_TAC >> rw [model2smodel] >> METIS_TAC [sholds_s2n_s2n]
 ]
QED

val _ = export_theory ();
