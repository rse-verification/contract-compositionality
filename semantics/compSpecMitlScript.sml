open HolKernel boolLib Parse bossLib pred_setTheory listTheory;
open combinTheory arithmeticTheory realTheory RealArith realSimps;
open ottTheory compSpecUtilityTheory compSpecTheory compSpecMetaTheory mitlTheory;

val _ = new_theory "compSpecMitl";

Definition St_sem:
 (St_sem state_holds omega MS MV (St_const (T_const sn)) = MS sn)
 /\
 (St_sem state_holds omega MS MV (St_conj S1 S2) =
   St_sem state_holds omega MS MV S1 INTER St_sem state_holds omega MS MV S2)
 /\
 (St_sem state_holds omega MS MV (St_assume S1 S2) =
  { B | B IN POW omega /\
    !B'. B' IN St_sem state_holds omega MS MV S1 ==> B INTER B' IN St_sem state_holds omega MS MV S2 })
 /\
 (St_sem state_holds omega MS MV (St_par S1 S2) =
  double_intersection (St_sem state_holds omega MS MV S1) (St_sem state_holds omega MS MV S2))
 /\
 (St_sem state_holds omega MS MV (St_var sn) = MV sn)
 /\
 (St_sem state_holds omega MS MV (St_const T_compat) = { B | B IN POW omega /\ B <> {} })
 /\
 (St_sem state_holds omega MS MV (St_const T_top) = { omega })
 /\
 (St_sem state_holds omega MS MV (St_const (T_hat f)) = POW (mitl_general_sem state_holds omega 0 f))
End

Definition Pt_sem:
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_implements c S) =
  (c_sem Mc Mq c IN St_sem state_holds omega MS MV S))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_refines S1 S2) =
  (St_sem state_holds omega MS MV S1 SUBSET St_sem state_holds omega MS MV S2))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_asserts S) =
  (downward_closed (St_sem state_holds omega MS MV S)))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_forall_c q P) =
  (!qs. Pt_sem state_holds omega Mc MS ((q =+ qs) Mq) MV P))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_exists_c q P) =
  (?qs. Pt_sem state_holds omega Mc MS ((q =+ qs) Mq) MV P))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_forall_St Vv P) =
  (!Vs. Pt_sem state_holds omega Mc MS Mq ((Vv =+ Vs) MV) P))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_exists_St Vv P) =
  (?Vs. Pt_sem state_holds omega Mc MS Mq ((Vv =+ Vs) MV) P))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_implies P1 P2) =
  (Pt_sem state_holds omega Mc MS Mq MV P1 ==> Pt_sem state_holds omega Mc MS Mq MV P2))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_and P1 P2) =
  (Pt_sem state_holds omega Mc MS Mq MV P1 /\ Pt_sem state_holds omega Mc MS Mq MV P2))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_not P) =
  ~(Pt_sem state_holds omega Mc MS Mq MV P))
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_c_eq c1 c2) =
  (c_sem Mc Mq c1 = c_sem Mc Mq c2)) 
 /\
 (Pt_sem state_holds omega Mc MS Mq MV (Pt_St_eq S1 S2) =
  (St_sem state_holds omega MS MV S1 = St_sem state_holds omega MS MV S2))
End

Theorem pow_mitl_sem_downward_closed:
 !state_holds omega fm. downward_closed (POW (mitl_general_sem state_holds omega 0 fm))
Proof
 strip_tac >> strip_tac >> Induct >> rw [downward_closed,mitl_general_sem] >>
 METIS_TAC [SUBSET_DEF,IN_POW]
QED

Theorem mitl_lift_assertional:
 !state_holds omega Mc MS Mq MV fm.
  Pt_sem state_holds omega Mc MS Mq MV (Pt_asserts (St_const (T_hat fm)))
Proof
 rw [Pt_sem,St_sem,pow_mitl_sem_downward_closed]
QED

Inductive spec_temporal_mitl_proof:
[spec_temporal_mitl:] (!(state_holds:'state -> 'a -> bool) omega (Gt:'a Gt) (fm fm':'a f).
 (!tau. tau IN omega /\ (!i. timed_word_suffix tau i IN omega) ==> mitl_general_holds state_holds tau 0 (mitl_implies fm fm'))
 ==>
 spec_temporal_mitl_holds state_holds omega Gt (Pt_refines (St_const (T_hat fm)) (St_const (T_hat fm'))))
End

Definition spec_temporal_mitl_system_sound:
  spec_temporal_mitl_system_sound R (state_holds : 'state -> 'a -> bool) omega =
  (!Mc MS Mq MV G Pt.
    (!s. Mc s SUBSET omega) /\
    (!s. Mq s SUBSET omega) /\
    (!s. MS s SUBSET POW omega) /\
    (!s. MV s SUBSET POW omega) /\
    (!P0. P0 IN G ==> Pt_sem state_holds omega Mc MS Mq MV P0) /\
    (!tau. tau IN omega ==> (!i. timed_word_suffix tau i IN omega)) /\
    R state_holds omega G Pt ==>
    Pt_sem state_holds omega Mc MS Mq MV Pt)
End

Theorem spec_temporal_mitl_holds_system_sound:
 !(state_holds : 'state -> 'a -> bool) omega.
  spec_temporal_mitl_system_sound spec_temporal_mitl_holds state_holds omega
Proof
 `!(state_holds : 'state -> 'a -> bool) omega G Pt.
  spec_temporal_mitl_holds state_holds omega G Pt ==>
  !Mc Mq MS MV.
  (!s. Mc s SUBSET omega) /\
  (!s. Mq s SUBSET omega) /\
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  (!P0. P0 IN G ==> Pt_sem state_holds omega Mc MS Mq MV P0) /\
  (!tau. tau IN omega ==> (!i. timed_word_suffix tau i IN omega)) ==>
  Pt_sem state_holds omega Mc MS Mq MV Pt`
  suffices_by METIS_TAC [spec_temporal_mitl_system_sound] >> 
 ho_match_mp_tac spec_temporal_mitl_proof_ind >> rw [] >| [
  rw [Pt_sem,St_sem] >>
  rw [SUBSET_DEF] >>
  `x SUBSET (mitl_general_sem state_holds omega 0 fm)` by METIS_TAC [IN_POW] >>
  `x SUBSET (mitl_general_sem state_holds omega 0 fm')` suffices_by METIS_TAC [IN_POW] >>
  fs [mitl_general_holds] >>
  `x SUBSET omega` by METIS_TAC [mitl_general_sem_omega,SUBSET_DEF] >>
  `!y. y IN mitl_general_sem state_holds omega 0 fm /\ y IN omega ==> y IN mitl_general_sem state_holds omega 0 fm'`
   suffices_by fs [SUBSET_DEF] >>
  rw [] >>
  `!i. timed_word_suffix y i IN omega` by METIS_TAC [] >>
  `mitl_general_holds state_holds y 0 fm` by METIS_TAC [mitl_general_holds_sem] >>
  `mitl_general_holds state_holds y 0 fm'` by METIS_TAC [] >>
  METIS_TAC [mitl_general_holds_sem]
 ]
QED

val _ = export_theory ();
