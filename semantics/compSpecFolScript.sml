open HolKernel boolLib Parse bossLib;
open pred_setTheory listTheory sumTheory combinTheory stringTheory;
open ottTheory folStringTheory compSpecTheory compSpecUtilityTheory compSpecMetaTheory;

val _ = new_theory "compSpecFol";

Definition spec_interp_func:
 spec_interp_func (omega : 'a set)
  (Mc : string -> 'a set)
  (MS : string -> ('a set) set) s l =
  if      s = "c_comp" then INL (OUTL (EL 0 l) INTER OUTL (EL 1 l))
  else if s = "S_conj" then INR (OUTR (EL 0 l) INTER OUTR (EL 1 l))
  else if s = "S_assume" then
   INR { B | B IN POW omega /\
    !B'. B' IN OUTR (EL 0 l) ==> B INTER B' IN OUTR (EL 1 l) }
  else if s = "S_par" then INR (double_intersection (OUTR (EL 0 l)) (OUTR (EL 1 l)))
  else if s = "S_compat" then INR { B | B IN POW omega  /\ B <> {} }
  else if s = "S_top" then INR { omega }
  else if TAKE 8 s = "c_const_" then INL (Mc (DROP 8 s))
  else if TAKE 8 s = "S_const_" then INR (MS (DROP 8 s))
  else @x.T
End

Definition spec_interp_pred:
 spec_interp_pred omega s l =
  if      s = "P_implements" then OUTL (EL 0 l) IN OUTR (EL 1 l)
  else if s = "P_refines" then OUTR (EL 0 l) SUBSET OUTR (EL 1 l)
  else if s = "P_asserts" then downward_closed (OUTR (EL 0 l))
  else if s = "P_eq_c" then OUTL (EL 0 l) = OUTL (EL 1 l)
  else if s = "P_eq_S" then OUTR (EL 0 l) = OUTR (EL 1 l)
  else if s = "P_is_c" then ISL (EL 0 l) /\ OUTL (EL 0 l) SUBSET omega
  else if s = "P_is_S" then ISR (EL 0 l) /\ OUTR (EL 0 l) SUBSET POW omega
  else @x.T
End

Definition spec_interp_smodel:
 spec_interp_smodel omega Mc MS =
  <| SDom := \x. (ISL x /\ OUTL x SUBSET omega) \/ (ISR x /\ OUTR x SUBSET POW omega);
     SFun := spec_interp_func omega Mc MS;
     SPred := spec_interp_pred omega |>
End

Definition c2sterm:
 (c2sterm (c_const s) = SFn (STRCAT "c_const_" s) [])
 /\
 (c2sterm (c_comp c1 c2) = SFn "c_comp" [c2sterm c1; c2sterm c2])
 /\
 (c2sterm (c_var s) = SV (STRCAT "c_var_" s))
End

Definition S2sterm:
 (S2sterm (S_const (Sc_const s)) = SFn (STRCAT "S_const_" s) [])
 /\
 (S2sterm (S_conj S1 S2) = SFn "S_conj" [S2sterm S1; S2sterm S2])
 /\
 (S2sterm (S_assume S1 S2) = SFn "S_assume" [S2sterm S1; S2sterm S2])
 /\
 (S2sterm (S_par S1 S2) = SFn "S_par" [S2sterm S1; S2sterm S2])
 /\
 (S2sterm (S_var s) = SV (STRCAT "S_var_" s))
 /\
 (S2sterm (S_const Sc_compat) = SFn "S_compat" [])
 /\
 (S2sterm (S_const Sc_top) = SFn "S_top" [])
End

Definition P2sform:
 (P2sform (P_implements c S) = SPred "P_implements" [c2sterm c; S2sterm S])
 /\
 (P2sform (P_refines S1 S2) = SPred "P_refines" [S2sterm S1; S2sterm S2])
 /\
 (P2sform (P_asserts S) = SPred "P_asserts" [S2sterm S])
 /\
 (P2sform (P_forall_c q P) = SForall (STRCAT "c_var_" q)
  (SImp (SPred "P_is_c" [SV (STRCAT "c_var_" q)]) (P2sform P)))
 /\
 (P2sform (P_exists_c q P) = SExists (STRCAT "c_var_" q)
  (SAnd (SPred "P_is_c" [SV (STRCAT "c_var_" q)]) (P2sform P)))
 /\
 (P2sform (P_forall_S Vx P) = SForall (STRCAT "S_var_" Vx)
  (SImp (SPred "P_is_S" [SV (STRCAT "S_var_" Vx)]) (P2sform P)))
 /\
 (P2sform (P_exists_S Vx P) = SExists (STRCAT "S_var_" Vx)
  (SAnd (SPred "P_is_S" [SV (STRCAT "S_var_" Vx)]) (P2sform P)))
 /\
 (P2sform (P_implies P1 P2) = SImp (P2sform P1) (P2sform P2))
 /\
 (P2sform (P_and P1 P2) = SAnd (P2sform P1) (P2sform P2))
 /\
 (P2sform (P_or P1 P2) = SOr (P2sform P1) (P2sform P2))
 /\
 (P2sform (P_not P) = SNot (P2sform P))
 /\
 (P2sform (P_c_eq c1 c2) = SPred "P_eq_c" [c2sterm c1; c2sterm c2])
 /\
 (P2sform (P_S_eq S1 S2) = SPred "P_eq_S" [S2sterm S1; S2sterm S2])
End

Definition cSval:
 cSval (Mq : string -> 'a set) (MV : string -> ('a set) set) s =
  if      TAKE 6 s = "c_var_" then INL (Mq (DROP 6 s))
  else if TAKE 6 s = "S_var_" then INR (MV (DROP 6 s))
  else @x.T
End

Theorem c_sem_stermval:
 !omega Mc MS Mq MV c.
  c_sem Mc Mq c = OUTL (stermval (spec_interp_smodel omega Mc MS) (cSval Mq MV) (c2sterm c))
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 Induct_on `c` >> rw [c_sem,stermval,spec_interp_smodel,c2sterm,spec_interp_func,cSval]
QED

Theorem S_sem_stermval:
 !omega Mc MS Mq MV S.
  S_sem omega MS MV S = OUTR (stermval (spec_interp_smodel omega Mc MS) (cSval Mq MV) (S2sterm S))
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Induct_on `S'` >> rw [S_sem,stermval,spec_interp_smodel,S2sterm,spec_interp_func,cSval] >>
 Cases_on `S'` >> rw [S_sem,stermval,spec_interp_smodel,S2sterm,spec_interp_func,cSval]
QED

Theorem ISL_OUTL_eq:
 !x y. OUTL x = OUTL y /\ ISL x /\ ISL y ==> x = y
Proof
 Cases_on `x` >- rw [ISL] >>
 Cases_on `y'` >> rw [ISL]
QED

Theorem cSval_UPDATE_Mq:
 !Mq MV s x. ((STRCAT "c_var_" s) =+ INL x) (cSval Mq MV) = cSval ((s =+ x) Mq) MV
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Q.ABBREV_TAC `cvars = STRCAT "c_var_" s` >>
 match_mp_tac EQ_EXT >> rw [cSval] >| [
  Cases_on `cvars = x'` >> rw [cSval] >> fs [Abbr `cvars`] >> rw [APPLY_UPDATE_THM] >-
  (`x' <> STRCAT "c_var_" (DROP 6 x')` suffices_by METIS_TAC [TAKE_DROP] >> fs []) >>
  rw [cSval],

  Cases_on `cvars = x'` >> rw [cSval,Abbr `cvars`,APPLY_UPDATE_THM] >> fs [],
  
  Cases_on `cvars = x'` >> rw [cSval,Abbr `cvars`,APPLY_UPDATE_THM] >> fs []
 ]
QED

Theorem cSval_UPDATE_MV:
 !Mq MV s x. ((STRCAT "S_var_" s) =+ INR x) (cSval Mq MV) = cSval Mq ((s =+ x) MV)
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Q.ABBREV_TAC `Svars = STRCAT "S_var_" s` >>
 match_mp_tac EQ_EXT >> rw [cSval] >| [
  Cases_on `Svars = x'` >> rw [cSval,Abbr `Svars`,APPLY_UPDATE_THM] >> fs [],

  Cases_on `Svars = x'` >> rw [cSval] >> fs [Abbr `Svars`] >> rw [APPLY_UPDATE_THM] >-
  (`x' <> STRCAT "S_var_" (DROP 6 x')` suffices_by METIS_TAC [TAKE_DROP] >> fs []) >>
  rw [cSval],
  
  Cases_on `Svars = x'` >> rw [cSval,Abbr `Svars`,APPLY_UPDATE_THM] >> fs []
 ]
QED

Theorem APPLY_UPDATE_SUBSET:
 !M omega s0 x.
  (!s. M s SUBSET omega) /\
  x SUBSET omega ==>
  !s. ((s0 =+ x) M) s SUBSET omega
Proof
 rw [APPLY_UPDATE_THM] >>
 Cases_on `s0 = s` >> rw []
QED

Theorem P_sem_sholds:
 !omega Mc MS Mq MV P.
  (!s. Mc s SUBSET omega) /\
  (!s. Mq s SUBSET omega) /\
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) ==>
  (P_sem omega Mc MS Mq MV P <=> sholds (spec_interp_smodel omega Mc MS) (cSval Mq MV) (P2sform P))
Proof
 Induct_on `P` >> rw [P_sem,sholds,P2sform,spec_interp_smodel,spec_interp_pred] >| [
  METIS_TAC [c_sem_stermval,S_sem_stermval,spec_interp_smodel],

  METIS_TAC [S_sem_stermval,spec_interp_smodel],

  METIS_TAC [S_sem_stermval,spec_interp_smodel],

  Q.ABBREV_TAC `cvars = STRING #"c" (STRING #"_" (STRING #"v" 
   (STRING #"a" (STRING #"r" (STRING #"_" s)))))` >>
  rw [APPLY_UPDATE_THM] >>
  EQ_TAC >> rw [] >| [
   Cases_on `a` >> fs [] >>
   `!s'. (s =+ x) Mq s' SUBSET omega` by METIS_TAC [APPLY_UPDATE_SUBSET] >>
   `sholds (spec_interp_smodel omega Mc MS) (cSval ((s =+ x) Mq) MV) (P2sform P)`    
    by METIS_TAC [spec_interp_smodel] >>
   METIS_TAC [spec_interp_smodel,cSval_UPDATE_Mq,Abbr `cvars`,STRCAT_def],

   METIS_TAC [NOT_ISL_ISR],

   `!s'. (s =+ qs) Mq s' SUBSET omega` by METIS_TAC [APPLY_UPDATE_SUBSET] >>
   `sholds (spec_interp_smodel omega Mc MS) ((cvars =+ INL qs) (cSval Mq MV)) (P2sform P)`    
    by fs [spec_interp_smodel,INL] >>
   METIS_TAC [spec_interp_smodel,cSval_UPDATE_Mq,Abbr `cvars`,STRCAT_def]
  ],

  Q.ABBREV_TAC `cvars = STRING #"c" (STRING #"_" (STRING #"v" 
   (STRING #"a" (STRING #"r" (STRING #"_" s)))))` >>
  rw [APPLY_UPDATE_THM] >>
  EQ_TAC >> rw [] >| [
   Q.EXISTS_TAC `INL qs` >> rw [] >>
   `!s'. (s =+ qs) Mq s' SUBSET omega` by METIS_TAC [APPLY_UPDATE_SUBSET] >>
   METIS_TAC [spec_interp_smodel,cSval_UPDATE_Mq,Abbr `cvars`,STRCAT_def],

   Cases_on `a` >> fs [] >>
   Q.EXISTS_TAC `x` >> rw [] >>
   `!s'. (s =+ x) Mq s' SUBSET omega` by METIS_TAC [APPLY_UPDATE_SUBSET] >>
   METIS_TAC [spec_interp_smodel,cSval_UPDATE_Mq,Abbr `cvars`,STRCAT_def],

   METIS_TAC [NOT_ISL_ISR]
  ],

  Q.ABBREV_TAC `Svars = STRING #"S" (STRING #"_" (STRING #"v" 
   (STRING #"a" (STRING #"r" (STRING #"_" s)))))` >>
  rw [APPLY_UPDATE_THM] >>
  EQ_TAC >> rw [] >| [
   METIS_TAC [NOT_ISL_ISR],

   Cases_on `a` >> fs [] >>
   `!s'. (s =+ y) MV s' SUBSET POW omega` by METIS_TAC [APPLY_UPDATE_SUBSET] >>
   `sholds (spec_interp_smodel omega Mc MS) (cSval Mq ((s =+ y) MV)) (P2sform P)`    
    by METIS_TAC [spec_interp_smodel] >>
   METIS_TAC [spec_interp_smodel,cSval_UPDATE_MV,Abbr `Svars`,STRCAT_def],

   `!s'. (s =+ Vs) MV s' SUBSET POW omega` by METIS_TAC [APPLY_UPDATE_SUBSET] >>
   `sholds (spec_interp_smodel omega Mc MS) ((Svars =+ INR Vs) (cSval Mq MV)) (P2sform P)`    
    by fs [spec_interp_smodel,INR] >>
   METIS_TAC [spec_interp_smodel,cSval_UPDATE_MV,Abbr `Svars`,STRCAT_def]
  ],

  Q.ABBREV_TAC `Svars = STRING #"S" (STRING #"_" (STRING #"v" 
   (STRING #"a" (STRING #"r" (STRING #"_" s)))))` >>
  rw [APPLY_UPDATE_THM] >>
  EQ_TAC >> rw [] >| [
   Q.EXISTS_TAC `INR Vs` >> rw [] >>
   `!s'. (s =+ Vs) MV s' SUBSET POW omega` by METIS_TAC [APPLY_UPDATE_SUBSET] >>
   METIS_TAC [spec_interp_smodel,cSval_UPDATE_MV,Abbr `Svars`,STRCAT_def],

   METIS_TAC [NOT_ISL_ISR],
   
   Cases_on `a` >> fs [] >>   
   Q.EXISTS_TAC `y` >> rw [] >>
   `!s'. (s =+ y) MV s' SUBSET POW omega` by METIS_TAC [APPLY_UPDATE_SUBSET] >>
   METIS_TAC [spec_interp_smodel,cSval_UPDATE_MV,Abbr `Svars`,STRCAT_def]
  ],

  METIS_TAC [c_sem_stermval,S_sem_stermval,spec_interp_smodel],

  METIS_TAC [S_sem_stermval,S_sem_stermval,spec_interp_smodel]
 ]
QED

Theorem P_sem_holds:
 !omega Mc MS Mq MV P.
  (!s. Mc s SUBSET omega) /\
  (!s. Mq s SUBSET omega) /\
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) ==>
  (P_sem omega Mc MS Mq MV P <=>
   holds (smodel2model (spec_interp_smodel omega Mc MS)) ((cSval Mq MV) o n2s) (sform2form (P2sform P)))
Proof
 once_rewrite_tac [GSYM sholds_holds] >>
 rw [P_sem_sholds]
QED

val _ = export_theory ();
