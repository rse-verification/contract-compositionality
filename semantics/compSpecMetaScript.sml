open HolKernel boolLib Parse bossLib;
open pred_setTheory listTheory combinTheory;
open stringTheory string_numTheory;
open ottTheory compSpecUtilityTheory compSpecTheory;

(* ====================================== *)
(* Compositional specification metatheory *)
(* ====================================== *)

val _ = new_theory "compSpecMeta";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

Definition S_par_list:
 S_par_list (S::Sl) = FOLDL (\S0. S_par S0) S Sl
End

(*
EVAL ``S_par_list (S_const Sc_top::S_const Sc_compat::S_const (Sc_const "test")::[])``
*)

(* -------------------- *)
(* Semantic definitions *)
(* -------------------- *)

Definition c_sem:
 (c_sem Mc Mq (c_const cn) = Mc cn)
 /\
 (c_sem Mc Mq (c_comp c1 c2) = c_sem Mc Mq c1 INTER c_sem Mc Mq c2)
 /\
 (c_sem Mc Mq (c_var q) = Mq q)
End

Definition S_sem:
 (S_sem omega MS MV (S_const (Sc_const sn)) = MS sn)
 /\
 (S_sem omega MS MV (S_conj S1 S2) = S_sem omega MS MV S1 INTER S_sem omega MS MV S2)
 /\
 (S_sem omega MS MV (S_assume S1 S2) =
  { B | B IN POW omega /\
    !B'. B' IN S_sem omega MS MV S1 ==> B INTER B' IN S_sem omega MS MV S2 })
 /\
 (S_sem omega MS MV (S_par S1 S2) =
  double_intersection (S_sem omega MS MV S1) (S_sem omega MS MV S2))
 /\
 (S_sem omega MS MV (S_var V) = MV V)
 /\
 (S_sem omega MS MV (S_const Sc_compat) = { B | B IN POW omega /\ B <> {} })
 /\
 (S_sem omega MS MV (S_const Sc_top) = { omega })
End

Definition P_sem:
 (P_sem omega Mc MS Mq MV (P_implements c S) =
  (c_sem Mc Mq c IN S_sem omega MS MV S))
 /\
 (P_sem omega Mc MS Mq MV (P_refines S1 S2) =
  (S_sem omega MS MV S1 SUBSET S_sem omega MS MV S2))
 /\
 (P_sem omega Mc MS Mq MV (P_asserts S) =
  (downward_closed (S_sem omega MS MV S)))
 /\
 (P_sem omega Mc MS Mq MV (P_forall_c q P) =
  (!qs. qs SUBSET omega ==> P_sem omega Mc MS ((q =+ qs) Mq) MV P))
 /\
 (P_sem omega Mc MS Mq MV (P_exists_c q P) =
  (?qs. qs SUBSET omega /\ P_sem omega Mc MS ((q =+ qs) Mq) MV P))
 /\
 (P_sem omega Mc MS Mq MV (P_forall_S V P) =
  (!Vs. Vs SUBSET POW omega ==> P_sem omega Mc MS Mq ((V =+ Vs) MV) P))
 /\
 (P_sem omega Mc MS Mq MV (P_exists_S V P) =
  (?Vs. Vs SUBSET POW omega /\ P_sem omega Mc MS Mq ((V =+ Vs) MV) P))
 /\
 (P_sem omega Mc MS Mq MV (P_implies P1 P2) =
  (P_sem omega Mc MS Mq MV P1 ==> P_sem omega Mc MS Mq MV P2))
 /\
 (P_sem omega Mc MS Mq MV (P_and P1 P2) =
  (P_sem omega Mc MS Mq MV P1 /\ P_sem omega Mc MS Mq MV P2))
 /\
 (P_sem omega Mc MS Mq MV (P_or P1 P2) =
  (P_sem omega Mc MS Mq MV P1 \/ P_sem omega Mc MS Mq MV P2))
 /\
 (P_sem omega Mc MS Mq MV (P_not P) =
  ~(P_sem omega Mc MS Mq MV P))
 /\
 (P_sem omega Mc MS Mq MV (P_c_eq c1 c2) =
  (c_sem Mc Mq c1 = c_sem Mc Mq c2))
 /\
 (P_sem omega Mc MS Mq MV (P_S_eq S1 S2) =
  (S_sem omega MS MV S1 = S_sem omega MS MV S2))
End

Definition spec_compositionality:
 spec_compositionality omega Mc MS Mq MV Sl S =
  (P_sem omega Mc MS Mq MV (P_refines (S_par_list Sl) S))
End

Definition spec_system_sound:
  spec_system_sound R omega =
  (!Mc MS Mq MV G P.
    (!s. Mc s SUBSET omega) /\
    (!s. Mq s SUBSET omega) /\
    (!s. MS s SUBSET POW omega) /\
    (!s. MV s SUBSET POW omega) /\
    (!P0. P0 IN G ==> P_sem omega Mc MS Mq MV P0) /\
    R G P ==>
    P_sem omega Mc MS Mq MV P)
End

(* --------------- *)
(* Utility results *)
(* --------------- *)

Theorem q_BIGUNION_IMAGE_fvP_c:
 !q (G:G).
  q IN BIGUNION (IMAGE fv_P_c G) <=> (?P. P IN G /\ q IN fv_P_c P)
Proof
 rw [BIGUNION] >>
 METIS_TAC []
QED

Theorem FINITE_IMAGE_s2n:
 !s. FINITE s ==> FINITE (IMAGE s2n s)
Proof
 rw [INJECTIVE_IMAGE_FINITE]
QED

Theorem SVARIANT_FINITE:
 !s. FINITE s ==> SVARIANT s NOTIN s
Proof
 rw [SVARIANT_def] >>
 `FINITE (IMAGE s2n s)` by METIS_TAC [FINITE_IMAGE_s2n] >>
 `!x. x IN (IMAGE s2n s) ==> x <= MAX_SET (IMAGE s2n s)`
  by METIS_TAC [in_max_set] >>
 strip_tac >>
 sg `MAX_SET (IMAGE s2n s) + 1 NOTIN (IMAGE s2n s)` >-
  (strip_tac >>
   `MAX_SET (IMAGE s2n s) + 1 <= MAX_SET (IMAGE s2n s)` by METIS_TAC [] >>
   DECIDE_TAC) >>
 `MAX_SET (IMAGE s2n s) + 1 IN (IMAGE s2n s)` suffices_by METIS_TAC [] >>
 `s2n (n2s (MAX_SET (IMAGE s2n s) + 1)) IN IMAGE s2n s` by METIS_TAC [IMAGE_IN] >>
 METIS_TAC [s2n_n2s] 
QED

Theorem fv_c_eq_c_sem:
 !Mc Mq Mq' c. (!q. q IN fv_c c ==> Mq q = Mq' q) ==>
  c_sem Mc Mq c = c_sem Mc Mq' c
Proof
 strip_tac >> strip_tac >> strip_tac >>
 Induct_on `c` >> rw [c_sem,fv_c]
QED

Theorem fv_S_eq_S_sem:
 !omega MS MV MV' S'. (!V. V IN fv_S S' ==> MV V = MV' V) ==>
  S_sem omega MS MV S' = S_sem omega MS MV' S'
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Induct_on `S'` >> rw [S_sem,fv_S] >>
 Cases_on `S'` >> rw [S_sem]
QED

Theorem fv_P_c_eq_P_sem:
 !omega Mc MS P Mq Mq' MV. 
  (!q. q IN fv_P_c P ==> Mq q = Mq' q) ==>
  P_sem omega Mc MS Mq MV P = P_sem omega Mc MS Mq' MV P
Proof
 strip_tac >> strip_tac >> strip_tac >>
 Induct_on `P` >> rw [P_sem,fv_P_c] >| [
  METIS_TAC [fv_c_eq_c_sem],

  EQ_TAC >> rw [] >>
  `!q. q IN fv_P_c P ==> ((s =+ qs) Mq) q = ((s =+ qs) Mq') q`
   by rw [APPLY_UPDATE_THM] >>
  sg `P_sem omega Mc MS ((s =+ qs) Mq) MV P <=> P_sem omega Mc MS ((s =+ qs) Mq') MV P` >-
   (Q.PAT_X_ASSUM `!M1 M2 M3. Q ==> R`
     (STRIP_ASSUME_TAC o (Q.SPECL [`(s =+ qs) Mq`,`(s =+ qs) Mq'`])) >>
    METIS_TAC []) >>
  METIS_TAC [],

  EQ_TAC >> rw [] >>
  `!q. q IN fv_P_c P ==> ((s =+ qs) Mq) q = ((s =+ qs) Mq') q`
   by rw [APPLY_UPDATE_THM] >>
  `P_sem omega Mc MS ((s =+ qs) Mq) MV P <=> P_sem omega Mc MS ((s =+ qs) Mq') MV P`
   by (Q.PAT_X_ASSUM `!M1 M2 M3. Q ==> R` (STRIP_ASSUME_TAC o
    (Q.SPECL [`(s =+ qs) Mq`,`(s =+ qs) Mq'`])) >>
    METIS_TAC []) >>
  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [fv_c_eq_c_sem]
 ]
QED

Theorem fv_P_S_eq_P_sem:
 !omega Mc MS P MV MV' Mq. 
  (!V. V IN fv_P_S P ==> MV V = MV' V) ==>
  P_sem omega Mc MS Mq MV P = P_sem omega Mc MS Mq MV' P
Proof
 strip_tac >> strip_tac >> strip_tac >>
 Induct_on `P` >> rw [P_sem,fv_P_S] >| [
  METIS_TAC [fv_S_eq_S_sem],

  METIS_TAC [fv_S_eq_S_sem],

  METIS_TAC [fv_S_eq_S_sem],

  METIS_TAC [],

  METIS_TAC [],

  EQ_TAC >> rw [] >>
  `!V. V IN fv_P_S P ==> ((s =+ Vs) MV) V = ((s =+ Vs) MV') V`
   by rw [APPLY_UPDATE_THM] >>
  `P_sem omega Mc MS Mq ((s =+ Vs) MV) P <=> P_sem omega Mc MS Mq ((s =+ Vs) MV') P`
   by (Q.PAT_X_ASSUM `!M1 M2 M3. Q ==> R` (STRIP_ASSUME_TAC o
    (Q.SPECL [`(s =+ Vs) MV`,`(s =+ Vs) MV'`])) >>
    METIS_TAC []) >>
  METIS_TAC [],

  EQ_TAC >> rw [] >>
  `!V. V IN fv_P_S P ==> ((s =+ Vs) MV) V = ((s =+ Vs) MV') V`
   by rw [APPLY_UPDATE_THM] >>
  `P_sem omega Mc MS Mq ((s =+ Vs) MV) P <=> P_sem omega Mc MS Mq ((s =+ Vs) MV') P`
   by (Q.PAT_X_ASSUM `!M1 M2 M3. Q ==> R` (STRIP_ASSUME_TAC o
    (Q.SPECL [`(s =+ Vs) MV`,`(s =+ Vs) MV'`])) >>
    METIS_TAC []) >>
  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [fv_S_eq_S_sem]
 ]
QED

Theorem fv_c_notin_c_sem:
 !Mc Mq c q qs. q NOTIN fv_c c ==>
  c_sem Mc Mq c = c_sem Mc ((q =+ qs) Mq) c
Proof
 rw [] >>
 match_mp_tac fv_c_eq_c_sem >>
 rw [] >>
 `q <> q'` by METIS_TAC [] >>
 rw [APPLY_UPDATE_THM]
QED

Theorem fv_c_empty_c_sem:
 !Mc Mq c q qs. fv_c c = {} ==>
  c_sem Mc Mq c = c_sem Mc ((q =+ qs) Mq) c
Proof
 rw [] >> 
 `q NOTIN fv_c c` by fs [] >>
 METIS_TAC [fv_c_notin_c_sem]
QED

Theorem fv_P_c_notin_P_sem:
 !omega Mc MS Mq MV P q qs. q NOTIN fv_P_c P ==>
  (P_sem omega Mc MS Mq MV P <=> P_sem omega Mc MS ((q =+ qs) Mq) MV P)
Proof
 rw [] >>
 match_mp_tac fv_P_c_eq_P_sem >>
 rw [] >>
 `q <> q'` by METIS_TAC [] >>
 rw [APPLY_UPDATE_THM]
QED

Theorem fv_S_notin_S_sem:
 !omega MS MV S V Vs. V NOTIN fv_S S ==>
  S_sem omega MS MV S = S_sem omega MS ((V =+ Vs) MV) S
Proof
 rw [] >>
 match_mp_tac fv_S_eq_S_sem >>
 rw [] >>
 `V <> V'` by METIS_TAC [] >>
 rw [APPLY_UPDATE_THM]
QED

Theorem fv_S_empty_S_sem:
 !omega MS MV S V Vs. fv_S S = {} ==>
  S_sem omega MS MV S = S_sem omega MS ((V =+ Vs) MV) S
Proof
 rw [] >> 
 `V NOTIN fv_S S'` by fs [] >>
 METIS_TAC [fv_S_notin_S_sem]
QED

Theorem c_sem_omega:
 !omega Mc Mq.
 (!s. Mc s SUBSET omega) /\
 (!s. Mq s SUBSET omega) ==>
 !c0. c_sem Mc Mq c0 SUBSET omega
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Induct_on `c0` >> rw [c_sem] >>
 fs [SUBSET_DEF,INTER_DEF]
QED

Theorem S_sem_omega:
 !omega MS MV.
 (!s. MS s SUBSET POW omega) /\
 (!s. MV s SUBSET POW omega) ==>
 !S0. S_sem omega MS MV S0 SUBSET POW omega
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Induct_on `S0` >> rw [S_sem] >| [
  Cases_on `S'` >> rw [S_sem] >-
  rw [SUBSET_DEF,IN_POW] >>
  rw [IN_POW],  
  fs [SUBSET_DEF,INTER_DEF],
  rw [SUBSET_DEF],
  rw [double_intersection,SUBSET_DEF] >>
  rw [INTER_DEF,IN_POW,SUBSET_DEF] >>
  METIS_TAC [IN_POW,SUBSET_DEF]
 ] 
QED

(* --------------------- *)
(* Metatheoretic results *)
(* --------------------- *)

Theorem c_sem_comp_IDEM:
 !Mc Mq c. c_sem Mc Mq (c_comp c c) = c_sem Mc Mq c
Proof
 rw [c_sem]
QED

Theorem c_sem_comp_ASSOC:
 !Mc Mq c1 c2 c3.
  c_sem Mc Mq (c_comp c1 (c_comp c2 c3)) = c_sem Mc Mq (c_comp (c_comp c1 c2) c3)
Proof
 rw [c_sem,INTER_ASSOC]
QED

Theorem c_sem_comp_COMM:
 !Mc Mq c1 c2.
  c_sem Mc Mq (c_comp c1 c2) = c_sem Mc Mq (c_comp c2 c1)
Proof
 rw [c_sem,INTER_COMM]
QED

Theorem S_sem_IN_assume_IN:
 !omega MS MV A1 G1 a.
  a IN S_sem omega MS MV (S_assume A1 G1) /\
  a IN S_sem omega MS MV A1 ==>
  a IN S_sem omega MS MV G1
Proof
 rw [S_sem] >> METIS_TAC [INTER_IDEMPOT]
QED

Theorem S_sem_IN_par_IN:
 !omega MS MV A1 G1 x.
  x IN S_sem omega MS MV (S_par A1 G1) <=>
  ?a b. x = a INTER b /\ a IN S_sem omega MS MV A1 /\ b IN S_sem omega MS MV G1
Proof
 rw [S_sem,double_intersection]
QED

Theorem S_sem_conj_IDEM:
 !omega MS MV S. S_sem omega MS MV (S_conj S S) = S_sem omega MS MV S
Proof
 rw [S_sem,INTER_IDEMPOT]
QED

Theorem S_sem_conj_ASSOC:
 !omega MS MV S1 S2 S3.
  S_sem omega MS MV (S_conj S1 (S_conj S2 S3)) = S_sem omega MS MV (S_conj (S_conj S1 S2) S3)
Proof
 rw [S_sem,INTER_ASSOC]
QED

Theorem S_sem_conj_COMM:
 !omega MS MV S1 S2.
  S_sem omega MS MV (S_conj S1 S2) = S_sem omega MS MV (S_conj S2 S1)
Proof
 rw [S_sem,INTER_COMM]
QED

Theorem S_sem_par_ASSOC:
 !omega MS MV S1 S2 S3.
  S_sem omega MS MV (S_par S1 (S_par S2 S3)) = S_sem omega MS MV (S_par (S_par S1 S2) S3)
Proof
 rw [S_sem,double_intersection_ASSOC]
QED

Theorem S_sem_par_COMM:
 !omega MS MV S1 S2.
  S_sem omega MS MV (S_par S1 S2) = S_sem omega MS MV (S_par S2 S1)
Proof
 rw [S_sem,double_intersection_COMM]
QED

Theorem proposition_2a:
 !omega Mc MS Mq MV c S1 S2.
  P_sem omega Mc MS Mq MV (P_implements c S1) /\
  P_sem omega Mc MS Mq MV (P_refines S1 S2) ==>
  P_sem omega Mc MS Mq MV (P_implements c S2)
Proof
 rw [P_sem] >> METIS_TAC [SUBSET_DEF]
QED

Theorem proposition_2b:
 !omega Mc MS Mq MV S1 S2 q.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  (P_sem omega Mc MS Mq MV
   (P_forall_c q
    (P_implies 
     (P_implements (c_var q) S1)
     (P_implements (c_var q) S2)))) ==>
  P_sem omega Mc MS Mq MV (P_refines S1 S2)
Proof
 rw [P_sem,c_sem] >>
 `S_sem omega MS MV S1 SUBSET POW omega`
  by METIS_TAC [S_sem_omega] >>
 METIS_TAC [SUBSET_DEF,APPLY_UPDATE_THM,IN_POW]
QED

Theorem proposition_2b_meta:
 !omega Mc MS Mq MV S1 S2.
  (!B. B IN S_sem omega MS MV S1 ==> B IN S_sem omega MS MV S2) ==>
  P_sem omega Mc MS Mq MV (P_refines S1 S2)
Proof
 rw [S_sem,P_sem,SUBSET_DEF]
QED

Theorem proposition_3a:
 !omega Mc MS Mq MV S q1 q2.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
   q1 <> q2 ==>
   (P_sem omega Mc MS Mq MV
    (P_forall_c q1 (P_forall_c q2
     (P_implies
      (P_implements (c_var q1) S)
      (P_implements (c_comp (c_var q1) (c_var q2)) S))))) ==>
   P_sem omega Mc MS Mq MV (P_asserts S)
Proof
 rw [P_sem,c_sem,downward_closed] >> 
 `e SUBSET omega` by METIS_TAC [IN_POW,SUBSET_DEF,S_sem_omega] >>
 `e' SUBSET omega` by fs [SUBSET_DEF] >>
 METIS_TAC [INTER_SUBSET_EQN,APPLY_UPDATE_THM]
QED

Theorem proposition_3a_meta:
 !omega Mc MS Mq MV S.
  (!B1 B2. B1 IN S_sem omega MS MV S ==> B1 INTER B2 IN S_sem omega MS MV S) ==>
  P_sem omega Mc MS Mq MV (P_asserts S)
Proof
 rw [S_sem,P_sem,downward_closed] >>
 METIS_TAC [INTER_SUBSET_EQN]
QED

Theorem proposition_3b:
 !omega Mc MS Mq MV S c1 c2.
  P_sem omega Mc MS Mq MV (P_asserts S) /\
  P_sem omega Mc MS Mq MV (P_implements c1 S) ==>
  P_sem omega Mc MS Mq MV (P_implements (c_comp c1 c2) S)
Proof
 rw [P_sem,downward_closed,c_sem] >>
 METIS_TAC [INTER_SUBSET]
QED

Theorem proposition_4a:
 !omega Mc MS Mq MV S1 S2 c.
  P_sem omega Mc MS Mq MV (P_implements c S1) /\
  P_sem omega Mc MS Mq MV (P_implements c S2) ==>
  P_sem omega Mc MS Mq MV (P_implements c (S_conj S1 S2))
Proof
 rw [P_sem,S_sem]
QED

Theorem proposition_4b:
 !omega Mc MS Mq MV S1 S2 c.
  P_sem omega Mc MS Mq MV (P_implements c (S_conj S1 S2)) ==>
  P_sem omega Mc MS Mq MV (P_implements c S1)
Proof
 rw [P_sem,S_sem]
QED

Theorem proposition_4b_alt:
 !omega Mc MS Mq MV S1 S2 c.
  P_sem omega Mc MS Mq MV (P_implements c (S_conj S1 S2)) ==>
  P_sem omega Mc MS Mq MV (P_implements c S2)
Proof
 rw [P_sem,S_sem]
QED

Theorem proposition_5a:
 !omega Mc MS Mq MV S1 S2 c q1 q2.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  q1 <> q2 /\
  q1 NOTIN fv_c c /\
  q2 NOTIN fv_c c ==>
  P_sem omega Mc MS Mq MV (P_implements c (S_par S1 S2)) ==>
  P_sem omega Mc MS Mq MV 
   (P_exists_c q1 (P_exists_c q2
     (P_and (P_implements (c_var q1) S1)
      (P_and (P_implements (c_var q2) S2)
       (P_c_eq c (c_comp (c_var q1) (c_var q2)))))))
Proof
 rw [P_sem,c_sem,S_sem,double_intersection,APPLY_UPDATE_THM] >>
 Q.EXISTS_TAC `a` >>
 rw [] >- METIS_TAC [IN_POW,SUBSET_DEF,S_sem_omega] >>
 Q.EXISTS_TAC `b` >>
 rw [] >- METIS_TAC [IN_POW,SUBSET_DEF,S_sem_omega] >>
 METIS_TAC [fv_c_notin_c_sem] 
QED

Theorem proposition_5a_meta:
 !omega Mc MS Mq MV S1 S2 c.
  P_sem omega Mc MS Mq MV (P_implements c (S_par S1 S2)) ==>
  ?B1 B2. B1 IN S_sem omega MS MV S1 /\
   B2 IN S_sem omega MS MV S2 /\
   B1 INTER B2 = c_sem Mc Mq c
Proof
 rw [P_sem,S_sem,double_intersection] >>
 Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `b` >>
 rw []
QED

Theorem proposition_5b:
 !omega Mc MS Mq MV S1 S2 c1 c2.
  P_sem omega Mc MS Mq MV (P_implements c1 S1) /\
  P_sem omega Mc MS Mq MV (P_implements c2 S2) ==>
  P_sem omega Mc MS Mq MV (P_implements (c_comp c1 c2) (S_par S1 S2))
Proof
 rw [P_sem,c_sem,S_sem,double_intersection] >> METIS_TAC []
QED

Theorem proposition_6a:
 !omega Mc MS Mq MV S1 S2.
  P_sem omega Mc MS Mq MV (P_refines (S_conj S1 S2) (S_par S1 S2))
Proof
 rw [P_sem,S_sem,double_intersection,SUBSET_DEF] >> METIS_TAC [INTER_IDEMPOT]
QED

Theorem proposition_6b:
 !omega Mc MS Mq MV S1 S2.
  P_sem omega Mc MS Mq MV (P_asserts S1) /\ P_sem omega Mc MS Mq MV (P_asserts S2) ==>
  P_sem omega Mc MS Mq MV (P_refines (S_par S1 S2) (S_conj S1 S2))
Proof
 rw [P_sem,S_sem,downward_closed,double_intersection,SUBSET_DEF] >>
 METIS_TAC [SUBSET_DEF,INTER_SUBSET]
QED

Theorem proposition_7a:
 !omega Mc MS Mq MV S1 S2.
  P_sem omega Mc MS Mq MV (P_refines (S_par S1 (S_assume S1 S2)) S2)
Proof
 rw [P_sem,S_sem,double_intersection,SUBSET_DEF] >> METIS_TAC [INTER_COMM]
QED

Theorem proposition_7a_alt:
 !omega Mc MS Mq MV S1 S2 c1 c2.
  P_sem omega Mc MS Mq MV (P_implements c1 S1) /\
  P_sem omega Mc MS Mq MV (P_implements c2 (S_assume S1 S2)) ==>
  P_sem omega Mc MS Mq MV (P_implements (c_comp c1 c2) S2)
Proof
 rw [P_sem,c_sem,S_sem] >> METIS_TAC [INTER_COMM]
QED

Theorem proposition_7b:
 !omega Mc MS Mq MV S1 S2 c2 q1.
  (!s. Mc s SUBSET omega) /\
  (!s. Mq s SUBSET omega) /\
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\  
   q1 NOTIN fv_c c2 ==>
   (P_sem omega Mc MS Mq MV
    (P_forall_c q1
     (P_implies (P_implements (c_var q1) S1)
      (P_implements (c_comp (c_var q1) c2) S2)))) ==>
   P_sem omega Mc MS Mq MV (P_implements c2 (S_assume S1 S2))
Proof
 rw [P_sem,c_sem,S_sem,APPLY_UPDATE_THM] >-
 METIS_TAC [IN_POW,c_sem_omega] >>
 `(B' INTER c_sem Mc Mq c2) IN S_sem omega MS MV S2` suffices_by METIS_TAC [INTER_COMM] >>
 `c_sem Mc Mq c2 = c_sem Mc ((q1 =+ B') Mq) c2`
  suffices_by METIS_TAC [IN_POW,SUBSET_DEF,S_sem_omega] >>
 match_mp_tac fv_c_eq_c_sem >>
 rw [APPLY_UPDATE_THM] >> fs []
QED

Theorem proposition_7b_meta:
 !omega Mc MS Mq MV S1 S2 c2.
  (!s. Mc s SUBSET omega) /\
  (!s. Mq s SUBSET omega) /\
  (!B. B IN S_sem omega MS MV S1 ==> B INTER c_sem Mc Mq c2 IN S_sem omega MS MV S2) ==>
  P_sem omega Mc MS Mq MV (P_implements c2 (S_assume S1 S2))
Proof
 rw [P_sem,S_sem,c_sem] >-
 METIS_TAC [IN_POW,c_sem_omega] >>
 METIS_TAC [INTER_COMM]
QED

Theorem proposition_7b_alt:
 !omega Mc MS Mq MV S1 S2 c2.
  (!s. Mc s SUBSET omega) /\
  (!s. Mq s SUBSET omega) /\
  P_sem omega Mc MS Mq MV (P_implements c2 S2) /\
  P_sem omega Mc MS Mq MV (P_asserts S2) ==>
  P_sem omega Mc MS Mq MV (P_implements c2 (S_assume S1 S2))
Proof
 rw [P_sem,S_sem,downward_closed] >-
 METIS_TAC [IN_POW,c_sem_omega] >>
 METIS_TAC [INTER_SUBSET]
QED

Theorem proposition_8_meta:
 !omega MS MV S.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) ==>
  S_sem omega MS MV S = S_sem omega MS MV (S_assume (S_const Sc_top) S)
Proof
 rw [S_sem,EXTENSION] >> EQ_TAC >> rw [] >| [
  METIS_TAC [SUBSET_DEF,S_sem_omega],

  `omega SUBSET B'` by METIS_TAC [SUBSET_DEF] >>
  `x INTER B' = x` suffices_by METIS_TAC [IN_POW] >>
  METIS_TAC [SUBSET_DEF,SUBSET_INTER_ABSORPTION,IN_POW,S_sem_omega],

  `x SUBSET omega` by METIS_TAC [IN_POW] >>
  `x INTER omega = x` by METIS_TAC [SUBSET_INTER_ABSORPTION] >>
  METIS_TAC []
 ]
QED

Theorem proposition_8:
 !omega Mc MS Mq MV S.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) ==>
  P_sem omega Mc MS Mq MV (P_S_eq S (S_assume (S_const Sc_top) S))
Proof
 rw [P_sem] >> METIS_TAC [proposition_8_meta]
QED

Theorem proposition_9:
 !omega Mc MS Mq MV S1 S2.
  P_sem omega Mc MS Mq MV (P_asserts S2) ==>
  P_sem omega Mc MS Mq MV (P_asserts (S_assume S1 S2))
Proof
 rw [P_sem,downward_closed,S_sem] >-
 METIS_TAC [IN_POW,SUBSET_DEF] >>
 `e INTER B' IN S_sem omega MS MV S2` by METIS_TAC [] >>
 `e' INTER B' SUBSET e INTER B'` suffices_by METIS_TAC [] >>
 fs [SUBSET_DEF]
QED

Theorem compat_comp:
 !omega Mc MS Mq MV c1 c2.
  (!s. Mc s SUBSET omega) /\
  (!s. Mq s SUBSET omega) ==>
  (P_sem omega Mc MS Mq MV (P_implements (c_comp c1 c2) (S_const Sc_compat)) <=>
  (c_sem Mc Mq c1) INTER (c_sem Mc Mq c2) <> {})
Proof
 rw [] >> EQ_TAC >> rw [P_sem,c_sem,S_sem] >> 
 METIS_TAC [IN_POW,SUBSET_DEF,IN_INTER,c_sem_omega]
QED

(* c substitution *)

Theorem csubst_c_triv:
 !c. csubst_c c_var c = c
Proof
 Induct >> rw [csubst_c]
QED

Theorem csubst_c_valuation:
 !c Mq1 Mq2. (!x. x IN fv_c c ==> (Mq1 x = Mq2 x)) ==> (csubst_c Mq1 c = csubst_c Mq2 c)
Proof
 Induct >> rw [csubst_c,fv_c]
QED

Theorem csubst_c_fv_c:
 !c Mq. fv_c (csubst_c Mq c) = { x | ?y. y IN fv_c c /\ x IN fv_c (Mq y) }
Proof
 Induct >> rw [csubst_c,fv_c] >>
 rw [UNION_DEF,EXTENSION] >> METIS_TAC []
QED

Theorem csubst_P_triv:
 !P. csubst_P c_var P = P
Proof
 Induct >> rw [csubst_P,fv_P_c] >>
 fs [combinTheory.APPLY_UPDATE_ID,fv_c] >>
 rw [csubst_c_triv]
QED

Theorem csubst_P_valuation:
 !P Mq1 Mq2. (!x. x IN fv_P_c P ==> (Mq1 x = Mq2 x)) ==>
  (csubst_P Mq1 P = csubst_P Mq2 P)
Proof
 Induct >> rw [fv_P_c,csubst_P] >>
 fs [combinTheory.UPDATE_APPLY,fv_P_c,fv_c] >>
 rw [csubst_c_valuation] >| [
  `csubst_P ((s =+ c_var s) Mq1) P = csubst_P ((s =+ c_var s) Mq2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [],

  `csubst_P ((s =+ c_var s) Mq1) P = csubst_P ((s =+ c_var s) Mq2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [combinTheory.APPLY_UPDATE_THM],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM],

  `csubst_P ((s =+ c_var s) Mq1) P = csubst_P ((s =+ c_var s) Mq2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [combinTheory.APPLY_UPDATE_THM],

  `csubst_P ((s =+ c_var s) Mq1) P = csubst_P ((s =+ c_var s) Mq2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [combinTheory.APPLY_UPDATE_THM],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  METIS_TAC [],

  `csubst_P ((s =+ c_var s) Mq1) P = csubst_P ((s =+ c_var s) Mq2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [combinTheory.APPLY_UPDATE_THM]
 ]
QED

(* S substitution *)

Theorem Ssubst_S_triv:
 !S. Ssubst_S S_var S = S
Proof
 Induct >> rw [Ssubst_S]
QED

Theorem Ssubst_S_valuation:
 !c MV1 MV2. (!x. x IN fv_S c ==> (MV1 x = MV2 x)) ==> (Ssubst_S MV1 c = Ssubst_S MV2 c)
Proof
 Induct >> rw [Ssubst_S,fv_S]
QED

Theorem Ssubst_S_fv_S:
 !S MV. fv_S (Ssubst_S MV S) = { x | ?y. y IN fv_S S /\ x IN fv_S (MV y) }
Proof
 Induct >> rw [Ssubst_S,fv_S] >>
 rw [UNION_DEF,EXTENSION] >> METIS_TAC []
QED

Theorem Ssubst_P_triv:
 !P. Ssubst_P S_var P = P
Proof
 Induct >> rw [Ssubst_P,fv_P_S] >>
 fs [combinTheory.APPLY_UPDATE_ID,fv_S] >>
 rw [Ssubst_S_triv]
QED

Theorem Ssubst_P_valuation:
 !P MV1 MV2. (!x. x IN fv_P_S P ==> (MV1 x = MV2 x)) ==>
  (Ssubst_P MV1 P = Ssubst_P MV2 P)
Proof
 Induct >> rw [fv_P_S,Ssubst_P] >>
 fs [combinTheory.UPDATE_APPLY,fv_P_S,fv_S] >>
 rw [Ssubst_S_valuation] >| [
  `Ssubst_P ((s =+ S_var s) MV1) P = Ssubst_P ((s =+ S_var s) MV2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [],

  `Ssubst_P ((s =+ S_var s) MV1) P = Ssubst_P ((s =+ S_var s) MV2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [combinTheory.APPLY_UPDATE_THM],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM],

  `Ssubst_P ((s =+ S_var s) MV1) P = Ssubst_P ((s =+ S_var s) MV2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [combinTheory.APPLY_UPDATE_THM],

  `Ssubst_P ((s =+ S_var s) MV1) P = Ssubst_P ((s =+ S_var s) MV2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [combinTheory.APPLY_UPDATE_THM],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  METIS_TAC [],

  fs[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  METIS_TAC [],

  `Ssubst_P ((s =+ S_var s) MV1) P = Ssubst_P ((s =+ S_var s) MV2) P`
   by fs[combinTheory.APPLY_UPDATE_THM] >>
  rw [combinTheory.APPLY_UPDATE_THM]
 ]
QED

(* free variables *)

Theorem FINITE_fv_c:
 !c. FINITE (fv_c c)
Proof
 Induct >> rw [fv_c]
QED

Theorem FINITE_fv_P_c:
 !P. FINITE (fv_P_c P)
Proof
 Induct >> rw [fv_P_c,FINITE_fv_c]
QED

Theorem FINITE_fv_S:
 !c. FINITE (fv_S c)
Proof
 Induct >> rw [fv_S]
QED

Theorem FINITE_fv_P_S:
 !P. FINITE (fv_P_S P)
Proof
 Induct >> rw [fv_P_S,FINITE_fv_S]
QED

Theorem SVARIANT_fv_P_c:
 !P. SVARIANT (fv_P_c P) NOTIN fv_P_c P
Proof
 METIS_TAC [SVARIANT_FINITE,FINITE_fv_P_c]
QED

Theorem SVARIANT_fv_P_S:
 !P. SVARIANT (fv_P_S P) NOTIN fv_P_S P
Proof
 METIS_TAC [SVARIANT_FINITE,FINITE_fv_P_S]
QED

Theorem c_sem_csubst:
 !c Mc Mq qc.
  c_sem Mc Mq (csubst_c qc c) = c_sem Mc (c_sem Mc Mq o qc) c
Proof
 Induct_on `c` >> rw [c_sem,csubst_c]
QED

Theorem c_sem_csubst1:
 !c Mc Mq c' q.
  c_sem Mc ((q =+ c_sem Mc Mq c') Mq) c =
  c_sem Mc Mq (csubst_c ((q =+ c') c_var) c)
Proof
 Induct >> rw [c_sem,csubst_c] >>
 fs[combinTheory.APPLY_UPDATE_THM] >>
 Cases_on `q = s` >> rw [c_sem]
QED

Theorem S_sem_Ssubst:
 !S omega MS MV VS.
  S_sem omega MS MV (Ssubst_S VS S) = S_sem omega MS (S_sem omega MS MV o VS) S
Proof
 ho_match_mp_tac S_induction >> rw [S_sem,Ssubst_S] >>
 Cases_on `S'` >> rw [S_sem]
QED

Theorem S_sem_Ssubst1:
 !S omega MS MV S' V.
  S_sem omega MS ((V =+ S_sem omega MS MV S') MV) S =
  S_sem omega MS MV (Ssubst_S ((V =+ S') S_var) S)
Proof
 Induct >> rw [S_sem,Ssubst_S] >>
 fs[combinTheory.APPLY_UPDATE_THM] >>
 Cases_on `V = s` >> rw [S_sem] >>
 Cases_on `S'` >> rw [S_sem]
QED

Theorem fv_P_c_IN_UNION:
 !P qc s. 
 {x | (∃y'. y' ∈ fv_P_c P ∧ x ∈ fv_c (if s = y' then c_var y' else qc y'))} =
 ({ x | s IN fv_P_c P /\ x IN fv_c (c_var s) } UNION
  { x | ?y. y IN fv_P_c P /\ y <> s /\ x IN fv_c (qc y) })
Proof
 rw [EXTENSION] >> EQ_TAC >> rw [] >> Cases_on `s = y'` >> rw [] >> fs [fv_c] >| [
   METIS_TAC [],
   
   rw [] >> Q.EXISTS_TAC `s` >> rw [fv_c],

   rw [] >> Q.EXISTS_TAC `s` >> rw [fv_c],

   Q.EXISTS_TAC `y` >> rw [],

   Q.EXISTS_TAC `y` >> rw []
 ]
QED

Theorem fv_P_S_IN_UNION:
 !P VS s. 
 {x | (∃y'. y' ∈ fv_P_S P ∧ x IN fv_S (if s = y' then S_var y' else VS y'))} =
 ({ x | s IN fv_P_S P /\ x IN fv_S (S_var s) } UNION
  { x | ?y. y IN fv_P_S P /\ y <> s /\ x IN fv_S (VS y) })
Proof
 rw [EXTENSION] >> EQ_TAC >> rw [] >> Cases_on `s = y'` >> rw [] >> fs [fv_S] >| [
   METIS_TAC [],
   
   rw [] >> Q.EXISTS_TAC `s` >> rw [fv_S],

   rw [] >> Q.EXISTS_TAC `s` >> rw [fv_S],

   Q.EXISTS_TAC `y` >> rw [],

   Q.EXISTS_TAC `y` >> rw []
 ]
QED

Theorem fv_P_c_BIGUNION:
 !P qc. 
 { x | ?y. y IN fv_P_c P /\ x IN fv_c (qc y) } =
  BIGUNION (IMAGE (\y. fv_c (qc y)) (fv_P_c P))
Proof
 rw [BIGUNION_IMAGE]
QED

Theorem fv_P_S_BIGUNION:
 !P VS. 
 { x | ?y. y IN fv_P_S P /\ x IN fv_S (VS y) } =
  BIGUNION (IMAGE (\y. fv_S (VS y)) (fv_P_S P))
Proof
 rw [BIGUNION_IMAGE]
QED

Theorem FINITE_fv_P_c_BIGUNION:
 !P qc. FINITE { x | ?y. y IN fv_P_c P /\ x IN fv_c (qc y) }
Proof
 rw [fv_P_c_BIGUNION] >-
 METIS_TAC [IMAGE_FINITE,FINITE_fv_P_c] >>
 METIS_TAC [FINITE_fv_c]
QED

Theorem FINITE_fv_P_S_BIGUNION:
 !P VS. FINITE { x | ?y. y IN fv_P_S P /\ x IN fv_S (VS y) }
Proof
 rw [fv_P_S_BIGUNION] >-
 METIS_TAC [IMAGE_FINITE,FINITE_fv_P_S] >>
 METIS_TAC [FINITE_fv_S]
QED

Theorem FINITE_fv_P_c_SUBSET:
 !P qc s. FINITE { x | ?y. y IN fv_P_c P /\ y <> s /\ x IN fv_c (qc y) }
Proof
 rw [] >>
 `{ x | ?y. y IN fv_P_c P /\ y <> s /\ x IN fv_c (qc y) } SUBSET
  { x | ?y. y IN fv_P_c P /\ x IN fv_c (qc y) }`
 suffices_by METIS_TAC [SUBSET_FINITE,FINITE_fv_P_c_BIGUNION] >>
 rw [SUBSET_DEF] >> METIS_TAC []
QED

Theorem FINITE_fv_P_S_SUBSET:
 !P VS s. FINITE { x | ?y. y IN fv_P_S P /\ y <> s /\ x IN fv_S (VS y) }
Proof
 rw [] >>
 `{ x | ?y. y IN fv_P_S P /\ y <> s /\ x IN fv_S (VS y) } SUBSET
  { x | ?y. y IN fv_P_S P /\ x IN fv_S (VS y) }`
 suffices_by METIS_TAC [SUBSET_FINITE,FINITE_fv_P_S_BIGUNION] >>
 rw [SUBSET_DEF] >> METIS_TAC []
QED

Theorem FINITE_s_fv_P_c:
 !P s. FINITE { x | s IN fv_P_c P /\ x IN fv_c (c_var s) }
Proof
 rw [] >>
 `{x | s ∈ fv_P_c P ∧ x ∈ fv_c (c_var s)} SUBSET
  fv_c (c_var s)`
  suffices_by METIS_TAC [SUBSET_FINITE,FINITE_fv_c] >>
 rw [SUBSET_DEF]
QED

Theorem FINITE_s_fv_P_S:
 !P s. FINITE { x | s IN fv_P_S P /\ x IN fv_S (S_var s) }
Proof
 rw [] >>
 `{x | s IN fv_P_S P ∧ x IN fv_S (S_var s)} SUBSET
  fv_S (S_var s)`
  suffices_by METIS_TAC [SUBSET_FINITE,FINITE_fv_S] >>
 rw [SUBSET_DEF]
QED

Theorem FINITE_fv_P_c_fv_c:
 !P qc s.
  FINITE {x | (∃y'. y' ∈ fv_P_c P ∧ x ∈ fv_c (if s = y' then c_var y' else qc y'))}
Proof
 rw [fv_P_c_IN_UNION] >-
 rw [FINITE_s_fv_P_c] >-
 rw [FINITE_fv_P_c_SUBSET]
QED

Theorem FINITE_fv_P_S_fv_S:
 !P VS s.
  FINITE {x | (?y'. y' IN fv_P_S P /\ x IN fv_S (if s = y' then S_var y' else VS y'))}
Proof
 rw [fv_P_S_IN_UNION] >-
 rw [FINITE_s_fv_P_S] >-
 rw [FINITE_fv_P_S_SUBSET]
QED

Theorem csubst_P_fv_P_c:
 !P qc. fv_P_c (csubst_P qc P) = { x | ?y. y IN fv_P_c P /\ x IN fv_c (qc y) }
Proof
 Induct >> rw [fv_P_c,csubst_P,fv_c] >| [
  rw [csubst_c_fv_c],

  fs [combinTheory.APPLY_UPDATE_THM,fv_c,fv_P_c] >>
  Cases_on `s = y` >> fs [fv_c] >>
  fs [EXTENSION] >> rw [] >> EQ_TAC >> rw [] >| [
    Cases_on `s = y'` >> fs [fv_c] >> Q.EXISTS_TAC `y'` >> rw [],

    Q.EXISTS_TAC `y'` >> rw [],
    
    strip_tac >>
    sg `x IN {x | (∃y'. y' ∈ fv_P_c P ∧ x ∈ fv_c (if s = y' then c_var y' else qc y'))}` >-
     (rw [] >> Q.EXISTS_TAC `y'` >> rw []) >>
    METIS_TAC [SVARIANT_FINITE,FINITE_fv_P_c_fv_c]
  ],

  fs [combinTheory.APPLY_UPDATE_THM,fv_c,fv_P_c] >>
  rw [EXTENSION] >>
  EQ_TAC >> rw [] >| [
   Cases_on `s = y` >> fs [fv_c] >>
   Q.EXISTS_TAC `y` >> rw [],

   Q.EXISTS_TAC `y` >> rw [],
   
   Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`y`])) >> rw [] >>
   Cases_on `s = y` >> fs [] >>
   METIS_TAC []
  ],

  fs [combinTheory.APPLY_UPDATE_THM,fv_c,fv_P_c] >>
  Cases_on `s = y` >> fs [fv_c] >>
  fs [EXTENSION] >> rw [] >> EQ_TAC >> rw [] >| [
    Cases_on `s = y'` >> fs [fv_c] >> Q.EXISTS_TAC `y'` >> rw [],

    Q.EXISTS_TAC `y'` >> rw [],
    
    strip_tac >>
    sg `x IN {x | (∃y'. y' ∈ fv_P_c P ∧ x ∈ fv_c (if s = y' then c_var y' else qc y'))}` >-
     (rw [] >> Q.EXISTS_TAC `y'` >> rw []) >>
    METIS_TAC [SVARIANT_FINITE,FINITE_fv_P_c_fv_c]
  ],

  fs [combinTheory.APPLY_UPDATE_THM,fv_c,fv_P_c] >>
  rw [EXTENSION] >>
  EQ_TAC >> rw [] >| [
   Cases_on `s = y` >> fs [fv_c] >>
   Q.EXISTS_TAC `y` >> rw [],

   Q.EXISTS_TAC `y` >> rw [],
   
   Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`y`])) >> rw [] >>
   Cases_on `s = y` >> fs [] >>
   METIS_TAC []
  ],

  rw [UNION_DEF,EXTENSION] >> EQ_TAC >> METIS_TAC [],

  rw [UNION_DEF,EXTENSION] >> EQ_TAC >> METIS_TAC [],

  rw [UNION_DEF,EXTENSION] >> EQ_TAC >> METIS_TAC [],

  rw [csubst_c_fv_c,UNION_DEF,EXTENSION] >> EQ_TAC >> METIS_TAC []
 ]
QED

Theorem Ssubst_P_fv_P_S:
 !P VS. fv_P_S (Ssubst_P VS P) = { x | ?y. y IN fv_P_S P /\ x IN fv_S (VS y) }
Proof
 Induct >> rw [fv_P_S,Ssubst_P,fv_S] >| [
  rw [Ssubst_S_fv_S],

  rw [Ssubst_S_fv_S,UNION_DEF,EXTENSION] >> METIS_TAC [],

  rw [Ssubst_S_fv_S,UNION_DEF,EXTENSION] >> METIS_TAC [],

  fs [combinTheory.APPLY_UPDATE_THM,fv_S,fv_P_S] >>
  Cases_on `s = y` >> fs [fv_S] >>
  fs [EXTENSION] >> rw [] >> EQ_TAC >> rw [] >| [
    Cases_on `s = y'` >> fs [fv_c] >> Q.EXISTS_TAC `y'` >> rw [] >> fs [fv_S],

    Q.EXISTS_TAC `y'` >> rw [],
    
    strip_tac >>
    sg `x IN {x | (?y'. y' IN fv_P_S P /\ x IN fv_S (if s = y' then S_var y' else VS y'))}` >-
     (rw [] >> Q.EXISTS_TAC `y'` >> rw []) >>
    METIS_TAC [SVARIANT_FINITE,FINITE_fv_P_S_fv_S]
  ],

  fs [combinTheory.APPLY_UPDATE_THM,fv_S,fv_P_S] >>
  rw [EXTENSION] >>
  EQ_TAC >> rw [] >| [
   Cases_on `s = y` >> fs [fv_S] >>
   Q.EXISTS_TAC `y` >> rw [],

   Q.EXISTS_TAC `y` >> rw [],

   Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`y`])) >> rw [] >>
   Cases_on `s = y` >> fs [] >>
   METIS_TAC []
  ],

  fs [combinTheory.APPLY_UPDATE_THM,fv_S,fv_P_S] >>
  Cases_on `s = y` >> fs [fv_S] >>
  fs [EXTENSION] >> rw [] >> EQ_TAC >> rw [] >| [
    Cases_on `s = y'` >> fs [fv_S] >> Q.EXISTS_TAC `y'` >> rw [],

    Q.EXISTS_TAC `y'` >> rw [],
    
    strip_tac >>
    sg `x IN {x | (?y'. y' IN fv_P_S P /\ x IN fv_S (if s = y' then S_var y' else VS y'))}` >-
     (rw [] >> Q.EXISTS_TAC `y'` >> rw []) >>
    METIS_TAC [SVARIANT_FINITE,FINITE_fv_P_S_fv_S]
  ],

  fs [combinTheory.APPLY_UPDATE_THM,fv_S,fv_P_S] >>
  rw [EXTENSION] >>
  EQ_TAC >> rw [] >| [
   Cases_on `s = y` >> fs [fv_S] >>
   Q.EXISTS_TAC `y` >> rw [],

   Q.EXISTS_TAC `y` >> rw [],

   Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`y`])) >> rw [] >>
   Cases_on `s = y` >> fs [] >>
   METIS_TAC []
  ],

  rw [UNION_DEF,EXTENSION] >> EQ_TAC >> METIS_TAC [],

  rw [UNION_DEF,EXTENSION] >> EQ_TAC >> METIS_TAC [],

  rw [UNION_DEF,EXTENSION] >> EQ_TAC >> METIS_TAC [],

  rw [Ssubst_S_fv_S,UNION_DEF,EXTENSION] >> EQ_TAC >> METIS_TAC []
 ]
QED

Theorem P_sem_csubst:
 !P omega Mc MS Mq MV qc.
  P_sem omega Mc MS Mq MV (csubst_P qc P) <=>
  P_sem omega Mc MS (c_sem Mc Mq o qc) MV P
Proof
 Induct_on `P` >> rw [P_sem,csubst_P,fv_P_c,fv_c] >| [
  rw [c_sem_csubst],

  fs [combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  EQ_TAC >> rw [] >-
   (`!q. q IN fv_P_c P ==> 
    (c_sem Mc Mq⦇SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) ↦ qs⦈ ∘
      qc⦇s ↦ c_var (SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)))⦈) q =
    ((c_sem Mc Mq ∘ qc)⦇s ↦ qs⦈) q`
     suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
    rw [combinTheory.APPLY_UPDATE_THM,c_sem] >>
    `SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) NOTIN fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)`
     by METIS_TAC [SVARIANT_fv_P_c] >>
    irule fv_c_eq_c_sem >>
    rw [] >>
    fs [combinTheory.APPLY_UPDATE_THM] >> rw [] >>
    `SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) IN
     fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)` suffices_by METIS_TAC [] >>
    `fv_c (qc q) SUBSET fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)`
     suffices_by METIS_TAC [SUBSET_DEF] >>
    rw [SUBSET_DEF] >>
    rw [csubst_P_fv_P_c] >>
    Q.EXISTS_TAC `q` >>
    rw [combinTheory.APPLY_UPDATE_THM]) >>
  `!q. q IN fv_P_c P ==> 
  (c_sem Mc Mq⦇SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) ↦ qs⦈ ∘
     qc⦇s ↦ c_var (SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)))⦈) q =
  ((c_sem Mc Mq ∘ qc)⦇s ↦ qs⦈) q`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
  rw [combinTheory.APPLY_UPDATE_THM,c_sem] >>
  `SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) NOTIN fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)`
    by METIS_TAC [SVARIANT_fv_P_c] >>
  irule fv_c_eq_c_sem >>
  rw [] >>
  fs [combinTheory.APPLY_UPDATE_THM] >> rw [] >>
  `SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) IN
   fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)` suffices_by METIS_TAC [] >>
  `fv_c (qc q) SUBSET fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)`
    suffices_by METIS_TAC [SUBSET_DEF] >>
  rw [SUBSET_DEF] >>
  rw [csubst_P_fv_P_c] >>
  Q.EXISTS_TAC `q` >>
  rw [combinTheory.APPLY_UPDATE_THM],

  fs [combinTheory.APPLY_UPDATE_THM] >>
  EQ_TAC >> rw [] >-
   (`!q. q IN fv_P_c P ==> (c_sem Mc Mq⦇s ↦ qs⦈ ∘ qc⦇s ↦ c_var s⦈) q = ((c_sem Mc Mq ∘ qc)⦇s ↦ qs⦈) q`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
    rw [] >>
    Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`q`])) >-
     (rw [combinTheory.APPLY_UPDATE_THM,c_sem]) >>
    Cases_on `s = q` >> fs [combinTheory.APPLY_UPDATE_THM,fv_c] >>
    METIS_TAC [fv_c_notin_c_sem]) >>
  `!q. q IN fv_P_c P ==> (c_sem Mc Mq⦇s ↦ qs⦈ ∘ qc⦇s ↦ c_var s⦈) q = ((c_sem Mc Mq ∘ qc)⦇s ↦ qs⦈) q`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
  rw [] >>
  Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`q`])) >-
   (rw [combinTheory.APPLY_UPDATE_THM,c_sem]) >>
  Cases_on `s = q` >> fs [combinTheory.APPLY_UPDATE_THM,fv_c] >>
  METIS_TAC [fv_c_notin_c_sem],

  fs [combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_c] >>
  EQ_TAC >> rw [] >-
   (`!q. q IN fv_P_c P ==> 
    (c_sem Mc Mq⦇SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) ↦ qs⦈ ∘
      qc⦇s ↦ c_var (SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)))⦈) q =
    ((c_sem Mc Mq ∘ qc)⦇s ↦ qs⦈) q`
     suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
    rw [combinTheory.APPLY_UPDATE_THM,c_sem] >>
    `SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) NOTIN fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)`
     by METIS_TAC [SVARIANT_fv_P_c] >>
    irule fv_c_eq_c_sem >>
    rw [] >>
    fs [combinTheory.APPLY_UPDATE_THM] >> rw [] >>
    `SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) IN
     fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)` suffices_by METIS_TAC [] >>
    `fv_c (qc q) SUBSET fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)`
     suffices_by METIS_TAC [SUBSET_DEF] >>
    rw [SUBSET_DEF] >>
    rw [csubst_P_fv_P_c] >>
    Q.EXISTS_TAC `q` >>
    rw [combinTheory.APPLY_UPDATE_THM]) >>
  `!q. q IN fv_P_c P ==> 
  (c_sem Mc Mq⦇SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) ↦ qs⦈ ∘
     qc⦇s ↦ c_var (SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)))⦈) q =
  ((c_sem Mc Mq ∘ qc)⦇s ↦ qs⦈) q`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
  rw [combinTheory.APPLY_UPDATE_THM,c_sem] >>
  `SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) NOTIN fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)`
    by METIS_TAC [SVARIANT_fv_P_c] >>
  irule fv_c_eq_c_sem >>
  rw [] >>
  fs [combinTheory.APPLY_UPDATE_THM] >> rw [] >>
  `SVARIANT (fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)) IN
   fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)` suffices_by METIS_TAC [] >>
  `fv_c (qc q) SUBSET fv_P_c (csubst_P qc⦇s ↦ c_var s⦈ P)`
    suffices_by METIS_TAC [SUBSET_DEF] >>
  rw [SUBSET_DEF] >>
  rw [csubst_P_fv_P_c] >>
  Q.EXISTS_TAC `q` >>
  rw [combinTheory.APPLY_UPDATE_THM],

  fs [combinTheory.APPLY_UPDATE_THM] >>
  EQ_TAC >> rw [] >-
   (Q.EXISTS_TAC `qs` >> rw [] >>
    `!q. q IN fv_P_c P ==> (c_sem Mc Mq⦇s ↦ qs⦈ ∘ qc⦇s ↦ c_var s⦈) q = ((c_sem Mc Mq ∘ qc)⦇s ↦ qs⦈) q`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
    rw [] >>
    Q.PAT_X_ASSUM `!y. Q` (STRIP_ASSUME_TAC o (Q.SPECL [`q`])) >-
     (rw [combinTheory.APPLY_UPDATE_THM,c_sem]) >>
    Cases_on `s = q` >> fs [combinTheory.APPLY_UPDATE_THM,fv_c] >>
    METIS_TAC [fv_c_notin_c_sem]) >>
  Q.EXISTS_TAC `qs` >> rw [] >>
  `!q. q IN fv_P_c P ==> (c_sem Mc Mq⦇s ↦ qs⦈ ∘ qc⦇s ↦ c_var s⦈) q = ((c_sem Mc Mq ∘ qc)⦇s ↦ qs⦈) q`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
  rw [] >>
  Q.PAT_X_ASSUM `!y. Q` (STRIP_ASSUME_TAC o (Q.SPECL [`q`])) >-
   (rw [combinTheory.APPLY_UPDATE_THM,c_sem]) >>
  Cases_on `s = q` >> fs [combinTheory.APPLY_UPDATE_THM,fv_c] >>
  METIS_TAC [fv_c_notin_c_sem],

  rw [c_sem_csubst]
 ]
QED

Theorem P_sem_Ssubst:
 !P omega Mc MS Mq MV VS.
  P_sem omega Mc MS Mq MV (Ssubst_P VS P) <=>
  P_sem omega Mc MS Mq (S_sem omega MS MV o VS) P
Proof
 Induct_on `P` >> rw [P_sem,Ssubst_P,fv_P_S,fv_S] >| [
  rw [S_sem_Ssubst],

  rw [S_sem_Ssubst],

  rw [S_sem_Ssubst],

  fs [combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  EQ_TAC >> rw [] >-
   (`!V. V IN fv_P_S P ==> 
    (S_sem omega MS MV⦇SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) ↦ Vs⦈ o
      VS⦇s ↦ S_var (SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)))⦈) V =
    ((S_sem omega MS MV o VS)⦇s ↦ Vs⦈) V`
     suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>

    rw [combinTheory.APPLY_UPDATE_THM,S_sem] >>
    `SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) NOTIN fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)`
     by METIS_TAC [SVARIANT_fv_P_S] >>
    irule fv_S_eq_S_sem >>
    rw [] >>
    fs [combinTheory.APPLY_UPDATE_THM] >> rw [] >>
    `SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) IN
     fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)` suffices_by METIS_TAC [] >>
    `fv_S (VS V) SUBSET fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)`
     suffices_by METIS_TAC [SUBSET_DEF] >>
    rw [SUBSET_DEF] >>
    rw [Ssubst_P_fv_P_S] >>
    Q.EXISTS_TAC `V` >>
    rw [combinTheory.APPLY_UPDATE_THM]) >>
  `!V. V IN fv_P_S P ==> 
   (S_sem omega MS MV⦇SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) ↦ Vs⦈ o
     VS⦇s ↦ S_var (SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)))⦈) V =
  ((S_sem omega MS MV o VS)⦇s ↦ Vs⦈) V`
    suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
  rw [combinTheory.APPLY_UPDATE_THM,S_sem] >>
  `SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) NOTIN fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)`
    by METIS_TAC [SVARIANT_fv_P_S] >>
  irule fv_S_eq_S_sem >>
  rw [] >>
  fs [combinTheory.APPLY_UPDATE_THM] >> rw [] >>
  `SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) IN
   fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)` suffices_by METIS_TAC [] >>
  `fv_S (VS V) SUBSET fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)`
    suffices_by METIS_TAC [SUBSET_DEF] >>
  rw [SUBSET_DEF] >>
  rw [Ssubst_P_fv_P_S] >>
  Q.EXISTS_TAC `V` >>
  rw [combinTheory.APPLY_UPDATE_THM],

  fs [combinTheory.APPLY_UPDATE_THM] >>
  EQ_TAC >> rw [] >-
   (`!V. V IN fv_P_S P ==>
     (S_sem omega MS MV⦇s ↦ Vs⦈ o VS⦇s ↦ S_var s⦈) V =
     ((S_sem omega MS MV o VS)⦇s ↦ Vs⦈) V`
    suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
    rw [] >>
    Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`V`])) >-
     (rw [combinTheory.APPLY_UPDATE_THM,S_sem]) >>
    Cases_on `s = V` >> fs [combinTheory.APPLY_UPDATE_THM,fv_S] >>
    METIS_TAC [fv_S_notin_S_sem]) >>
  `!V. V IN fv_P_S P ==>
    (S_sem omega MS MV⦇s ↦ Vs⦈ ∘ VS⦇s ↦ S_var s⦈) V = ((S_sem omega MS MV o VS)⦇s ↦ Vs⦈) V`
    suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
  rw [] >>
  Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`V`])) >-
   (rw [combinTheory.APPLY_UPDATE_THM,S_sem]) >>
  Cases_on `s = V` >> fs [combinTheory.APPLY_UPDATE_THM,fv_S] >>
  METIS_TAC [fv_S_notin_S_sem],

  fs [combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `s = y` >> fs [fv_S] >>
  EQ_TAC >> rw [] >-
   (`!V. V IN fv_P_S P ==> 
    (S_sem omega MS MV⦇SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) ↦ Vs⦈ o
      VS⦇s ↦ S_var (SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)))⦈) V =
    ((S_sem omega MS MV o VS)⦇s ↦ Vs⦈) V`
     suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>

    rw [combinTheory.APPLY_UPDATE_THM,S_sem] >>
    `SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) NOTIN fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)`
     by METIS_TAC [SVARIANT_fv_P_S] >>
    irule fv_S_eq_S_sem >>
    rw [] >>
    fs [combinTheory.APPLY_UPDATE_THM] >> rw [] >>
    `SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) IN
     fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)` suffices_by METIS_TAC [] >>
    `fv_S (VS V) SUBSET fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)`
     suffices_by METIS_TAC [SUBSET_DEF] >>
    rw [SUBSET_DEF] >>
    rw [Ssubst_P_fv_P_S] >>
    Q.EXISTS_TAC `V` >>
    rw [combinTheory.APPLY_UPDATE_THM]) >>
  `!V. V IN fv_P_S P ==> 
   (S_sem omega MS MV⦇SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) ↦ Vs⦈ o
     VS⦇s ↦ S_var (SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)))⦈) V =
  ((S_sem omega MS MV o VS)⦇s ↦ Vs⦈) V`
    suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
  rw [combinTheory.APPLY_UPDATE_THM,S_sem] >>
  `SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) NOTIN fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)`
    by METIS_TAC [SVARIANT_fv_P_S] >>
  irule fv_S_eq_S_sem >>
  rw [] >>
  fs [combinTheory.APPLY_UPDATE_THM] >> rw [] >>
  `SVARIANT (fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)) IN
   fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)` suffices_by METIS_TAC [] >>
  `fv_S (VS V) SUBSET fv_P_S (Ssubst_P VS⦇s ↦ S_var s⦈ P)`
    suffices_by METIS_TAC [SUBSET_DEF] >>
  rw [SUBSET_DEF] >>
  rw [Ssubst_P_fv_P_S] >>
  Q.EXISTS_TAC `V` >>
  rw [combinTheory.APPLY_UPDATE_THM],

  fs [combinTheory.APPLY_UPDATE_THM] >>
  EQ_TAC >> rw [] >-
   (`!V. V IN fv_P_S P ==>
     (S_sem omega MS MV⦇s ↦ Vs⦈ o VS⦇s ↦ S_var s⦈) V =
     ((S_sem omega MS MV o VS)⦇s ↦ Vs⦈) V`
    suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
    rw [] >>
    Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`V`])) >-
     (rw [combinTheory.APPLY_UPDATE_THM,S_sem]) >>
    Cases_on `s = V` >> fs [combinTheory.APPLY_UPDATE_THM,fv_S] >>
    METIS_TAC [fv_S_notin_S_sem]) >>
  `!V. V IN fv_P_S P ==>
    (S_sem omega MS MV⦇s ↦ Vs⦈ ∘ VS⦇s ↦ S_var s⦈) V = ((S_sem omega MS MV o VS)⦇s ↦ Vs⦈) V`
    suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
  rw [] >>
  Q.PAT_X_ASSUM `!y. Q \/ R` (STRIP_ASSUME_TAC o (Q.SPECL [`V`])) >-
   (rw [combinTheory.APPLY_UPDATE_THM,S_sem]) >>
  Cases_on `s = V` >> fs [combinTheory.APPLY_UPDATE_THM,fv_S] >>
  METIS_TAC [fv_S_notin_S_sem],

  rw [S_sem_Ssubst]
 ]
QED

Theorem P_sem_csubst1:
 !P omega Mc MS Mq MV c q.
  P_sem omega Mc MS Mq MV (csubst_P ((q =+ c) c_var) P) <=>
  P_sem omega Mc MS ((q =+ c_sem Mc Mq c) Mq) MV P
Proof
 simp[P_sem_csubst] >> 
 rw [] >>
 irule fv_P_c_eq_P_sem >>
 rw[combinTheory.APPLY_UPDATE_THM,c_sem]
QED

Theorem P_sem_Ssubst1:
 !P omega Mc MS Mq MV S V.
  P_sem omega Mc MS Mq MV (Ssubst_P ((V =+ S) S_var) P) <=>
  P_sem omega Mc MS Mq ((V =+ S_sem omega MS MV S) MV) P
Proof
 simp[P_sem_Ssubst] >> 
 rw [] >>
 irule fv_P_S_eq_P_sem >>
 rw[combinTheory.APPLY_UPDATE_THM,S_sem]
QED

Theorem P_sem_rename_c:
 !P omega Mc MS Mq MV x y.
  P_sem omega Mc MS Mq MV (csubst_P ((x =+ c_var y) c_var) P) <=>
  P_sem omega Mc MS ((x =+ Mq y) Mq) MV P
Proof
 rw [P_sem_csubst1,c_sem]
QED

Theorem P_sem_rename_S:
 !P omega Mc MS Mq MV x y.
  P_sem omega Mc MS Mq MV (Ssubst_P ((x =+ S_var y) S_var) P) <=>
  P_sem omega Mc MS Mq ((x =+ MV y) MV) P
Proof
 rw [P_sem_Ssubst1,S_sem]
QED

Theorem P_sem_alpha_forall_c:
 !P omega Mc MS Mq MV x y. y NOTIN fv_P_c (P_forall_c x P) ==>
 (P_sem omega Mc MS Mq MV (P_forall_c y (csubst_P ((x =+ c_var y) c_var) P)) <=>
  P_sem omega Mc MS Mq MV (P_forall_c x P))
Proof
 rw [P_sem,P_sem_csubst1,c_sem,fv_P_c] >> 
 EQ_TAC >> rw [] >-
  (`P_sem omega Mc MS ((x =+ qs) ((y =+ qs) Mq)) MV P`
    by METIS_TAC [] >>
   `(!q. q IN fv_P_c P ==> ((x =+ qs) ((y =+ qs) Mq)) q = ((x =+ qs) Mq) q)`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
   rw [] >>
   `q <> y` by METIS_TAC [] >>
   rw [combinTheory.APPLY_UPDATE_THM]) >>
 `P_sem omega Mc MS ((x =+ qs) Mq) MV P`
  by METIS_TAC [] >>
 `(!q. q IN fv_P_c P ==> ((x =+ qs) ((y =+ qs) Mq)) q = ((x =+ qs) Mq) q)`
  suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
 rw [] >>
 `q <> y` by METIS_TAC [] >>
 rw [combinTheory.APPLY_UPDATE_THM]
QED

Theorem P_sem_alpha_forall_S:
 !P omega Mc MS Mq MV x y. y NOTIN fv_P_S (P_forall_S x P) ==>
 (P_sem omega Mc MS Mq MV (P_forall_S y (Ssubst_P ((x =+ S_var y) S_var) P)) <=>
  P_sem omega Mc MS Mq MV (P_forall_S x P))
Proof
 rw [P_sem,P_sem_Ssubst1,S_sem,fv_P_S] >> 
 EQ_TAC >> rw [] >-
  (`P_sem omega Mc MS Mq ((x =+ Vs) ((y =+ Vs) MV)) P`
    by METIS_TAC [] >>
   `(!V. V IN fv_P_S P ==> ((x =+ Vs) ((y =+ Vs) MV)) V = ((x =+ Vs) MV) V)`
    suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
   rw [] >>
   `V <> y` by METIS_TAC [] >>
   rw [combinTheory.APPLY_UPDATE_THM]) >>
 `P_sem omega Mc MS Mq ((x =+ Vs) MV) P`
  by METIS_TAC [] >>
 `(!V. V IN fv_P_S P ==> ((x =+ Vs) ((y =+ Vs) MV)) V = ((x =+ Vs) MV) V)`
  suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
 rw [] >>
 `V <> y` by METIS_TAC [] >>
 rw [combinTheory.APPLY_UPDATE_THM]
QED

(* proof system soundness *)

Theorem spec_holds_system_sound:
 !omega. spec_system_sound spec_holds omega
Proof
 strip_tac >>
 `!G P. spec_holds G P ==>
  !Mc Mq MS MV.
  (!s. Mc s SUBSET omega) /\
  (!s. Mq s SUBSET omega) /\
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
   (!P0. P0 IN G ==> P_sem omega Mc MS Mq MV P0) ==> P_sem omega Mc MS Mq MV P`
  suffices_by METIS_TAC [spec_system_sound] >>
 ho_match_mp_tac spec_proof_ind >> rw [] >| [
  (* ri *)
  fs [P_sem] >> fs [c_sem] >>
  rw [SUBSET_DEF] >>
  fs [APPLY_UPDATE_THM] >>
  `S_sem omega MS MV S1 SUBSET POW omega`
   by METIS_TAC [S_sem_omega] >>
  qsuff_tac `x SUBSET omega` >- METIS_TAC [] >>
  fs [POW_DEF,SUBSET_DEF] >> METIS_TAC [],

  (* re *)
  METIS_TAC [proposition_2a],

  (* am1 *)
  METIS_TAC [proposition_3a],

  (* am2 *)
  METIS_TAC [proposition_3b],

  (* conji *)
  METIS_TAC [proposition_4a],

  (* conje1 *)
  METIS_TAC [proposition_4b],

  (* conje2 *)
  METIS_TAC [proposition_4b_alt],

  (* pi *)
  rw [P_sem] >> rw [c_sem] >> rw [S_sem] >>
  rw [double_intersection] >>
  Q.EXISTS_TAC `c_sem Mc Mq c1` >>
  Q.EXISTS_TAC `c_sem Mc Mq c2` >>
  fs [P_sem],

  (* pe *)
  METIS_TAC [proposition_5a],

  (* ci *)
  METIS_TAC [proposition_7b],

  (* ce *)
  METIS_TAC [proposition_7a_alt],

  (* cre *)
  `P_sem omega Mc MS Mq MV (P_implements c (S_conj S1 S2))` by METIS_TAC [] >>
  METIS_TAC [proposition_4b_alt,proposition_2a,proposition_4a],

  (* cr *)
  `P_sem omega Mc MS Mq MV (P_implements c (S_conj S1 S3))` by METIS_TAC [] >>
  `P_sem omega Mc MS Mq MV (P_refines S1 S2)` by METIS_TAC [] >>
  fs [P_sem,S_sem] >>
  METIS_TAC [SUBSET_DEF],

  (* andi *)
  rw [P_sem],

  (* ande1 *)
  `P_sem omega Mc MS Mq MV (P_and P P2)` by METIS_TAC [] >>
  METIS_TAC [P_sem],

  (* ande2 *)
  `P_sem omega Mc MS Mq MV (P_and P1 P)` by METIS_TAC [] >>
  METIS_TAC [P_sem],

  (* impi *)
  rw [P_sem] >>
  `!P0. P0 = P1 \/ P0 IN G ==> P_sem omega Mc MS Mq MV P0`
   by METIS_TAC [] >>
  METIS_TAC [],

  (* impe *)
  `P_sem omega Mc MS Mq MV (P_implies P' P)` by METIS_TAC [] >>
  `P_sem omega Mc MS Mq MV P'` by METIS_TAC [] >>
  METIS_TAC [P_sem],

  (* ori1 *)
  `P_sem omega Mc MS Mq MV P`
   by METIS_TAC [] >>
  METIS_TAC [P_sem],

  (* ori2 *)
  `P_sem omega Mc MS Mq MV P`
   by METIS_TAC [] >>
  METIS_TAC [P_sem],

  (* orel *)
  `P_sem omega Mc MS Mq MV (P_or P1 P2)` by METIS_TAC [] >>
  fs [P_sem] >-
   (`!P0. P0 = P1 \/ P0 IN G ==> P_sem omega Mc MS Mq MV P0`
     by METIS_TAC [] >>
    METIS_TAC []) >>
  `!P0. P0 = P2 \/ P0 IN G ==> P_sem omega Mc MS Mq MV P0`
   by METIS_TAC [] >>
  METIS_TAC [],

  (* notin *)
  rw [P_sem] >> strip_tac >>
  `!P0. P0 = P1 \/ P0 IN G ==> P_sem omega Mc MS Mq MV P0`
   by METIS_TAC [] >>
  `P_sem omega Mc MS Mq MV P` by METIS_TAC [] >>
  `P_sem omega Mc MS Mq MV (P_not P)` by METIS_TAC [] >>
  METIS_TAC [P_sem],

  (* notel *)
  `P_sem omega Mc MS Mq MV (P_not (P_not P))`
   by METIS_TAC [] >>
  METIS_TAC [P_sem],

  (* allel *)
  `P_sem omega Mc MS Mq MV (P_forall_c q P)` by METIS_TAC [] >>
  fs [P_sem] >>
  `c_sem Mc Mq c SUBSET omega` by METIS_TAC [c_sem_omega] >>
  `P_sem omega Mc MS ((q =+ c_sem Mc Mq c) Mq) MV P` by METIS_TAC [] >>
  METIS_TAC [P_sem_csubst1],

  (* allin *)
  rw [P_sem] >>
  `!s. ((q' =+ qs) Mq) s SUBSET omega`
   by rw [APPLY_UPDATE_THM] >>
  sg `!P0. P0 IN G ==> P_sem omega Mc MS ((q' =+ qs) Mq) MV P0` >-
   (rw [] >>
    `q' NOTIN fv_P_c P0` by METIS_TAC [] >>
    `P_sem omega Mc MS Mq MV P0` by METIS_TAC [] >>
    `!q0. q0 IN fv_P_c P0 ==> ((q' =+ qs) Mq) q0 = Mq q0`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
    rw [APPLY_UPDATE_THM] >> METIS_TAC []) >>
  `P_sem omega Mc MS ((q' =+ qs) Mq) MV (csubst_P c_var⦇q ↦ c_var q'⦈ P)`
   by METIS_TAC [] >>
  `P_sem omega Mc MS ((q =+ (Mq⦇q' ↦ qs⦈) q') (Mq⦇q' ↦ qs⦈)) MV P`
   by METIS_TAC [P_sem_rename_c] >>
  fs [APPLY_UPDATE_THM] >>
  `!q0. q0 IN fv_P_c P ==> (Mq⦇q ↦ qs; q' ↦ qs⦈) q0 = (Mq⦇q ↦ qs⦈) q0`
   suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
  rw [APPLY_UPDATE_THM] >> METIS_TAC [],

  (* eq_el_c *)
  `P_sem omega Mc MS Mq MV (P_c_eq c c')` by METIS_TAC [] >>
  `P_sem omega Mc MS Mq MV (csubst_P c_var⦇q ↦ c⦈ P)` by METIS_TAC [] >>  
  fs [P_sem_csubst1,P_sem] >>
  METIS_TAC [],

  (* all_el_S *)
  `P_sem omega Mc MS Mq MV (P_forall_S V P)` by METIS_TAC [] >>
  fs [P_sem] >>
  `S_sem omega MS MV S' SUBSET POW omega` by METIS_TAC [S_sem_omega] >>
  `P_sem omega Mc MS Mq ((V =+ S_sem omega MS MV S') MV) P` by METIS_TAC [] >>
  METIS_TAC [P_sem_Ssubst1],

  (* all_in_S *)
  rw [P_sem] >>
  `!s. ((V' =+ Vs) MV) s SUBSET POW omega`
   by rw [APPLY_UPDATE_THM] >>
  sg `!P0. P0 IN G ==> P_sem omega Mc MS Mq ((V' =+ Vs) MV) P0` >-
   (rw [] >>
    `V' NOTIN fv_P_S P0` by METIS_TAC [] >>
    `P_sem omega Mc MS Mq MV P0` by METIS_TAC [] >>
    `!V0. V0 IN fv_P_S P0 ==> ((V' =+ Vs) MV) V0 = MV V0`
    suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
    rw [APPLY_UPDATE_THM] >> METIS_TAC []) >>
  `P_sem omega Mc MS Mq ((V' =+ Vs) MV) (Ssubst_P S_var⦇V ↦ S_var V'⦈ P)`
   by METIS_TAC [] >>
  `P_sem omega Mc MS Mq ((V =+ (MV⦇V' ↦ Vs⦈) V') (MV⦇V' ↦ Vs⦈)) P`
   by METIS_TAC [P_sem_rename_S] >>
  fs [APPLY_UPDATE_THM] >>
  `!V0. V0 IN fv_P_S P ==> (MV⦇V ↦ Vs; V' ↦ Vs⦈) V0 = (MV⦇V ↦ Vs⦈) V0`
   suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
  rw [APPLY_UPDATE_THM] >> METIS_TAC [],

  (* eq_el_S *)
  `P_sem omega Mc MS Mq MV (P_S_eq S'' S')` by METIS_TAC [] >>
  `P_sem omega Mc MS Mq MV (Ssubst_P S_var⦇V ↦ S''⦈ P)` by METIS_TAC [] >>  
  fs [P_sem_Ssubst1,P_sem] >>
  METIS_TAC [],

  (* ex_in_c *)
  `P_sem omega Mc MS Mq MV (csubst_P ((q =+ c) c_var) P)`
   by METIS_TAC [] >>
  rw [P_sem] >>
  Q.EXISTS_TAC `c_sem Mc Mq c` >>
  rw [] >- METIS_TAC [c_sem_omega] >>
  METIS_TAC [P_sem_csubst1],

  (* ex_el_c *)
  fs [P_sem] >>
  sg `!qs P0. P0 IN G ==> P_sem omega Mc MS ((q' =+ qs) Mq) MV P0` >-
   (rw [] >>
    `q' NOTIN fv_P_c P0` by METIS_TAC [] >>
    `P_sem omega Mc MS Mq MV P0` by METIS_TAC [] >>
    `!q0. q0 IN fv_P_c P0 ==> ((q' =+ qs) Mq) q0 = Mq q0`
    suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
    rw [APPLY_UPDATE_THM] >> METIS_TAC []) >>
  `?qs. qs SUBSET omega /\ P_sem omega Mc MS ((q =+ qs) Mq) MV P'` by METIS_TAC [] >>
  sg `P_sem omega Mc MS ((q =+ (Mq⦇q' ↦ qs⦈) q') (Mq⦇q' ↦ qs⦈)) MV P'` >-
   (rw [P_sem_csubst1] >>
    `!q0. q0 IN fv_P_c P' ==> (Mq⦇q ↦ qs; q' ↦ qs⦈) q0 = (Mq⦇q ↦ qs⦈) q0`
     suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
    rw [APPLY_UPDATE_THM] >> METIS_TAC []) >>      
  `P_sem omega Mc MS (Mq⦇q' ↦ qs⦈) MV (csubst_P c_var⦇q ↦ c_var q'⦈ P')`
   by METIS_TAC [P_sem_rename_c] >>
  sg `!P0. P0 IN G' ==> P_sem omega Mc MS Mq⦇q' ↦ qs⦈ MV P0` >-
   (rw [] >>
    `P_sem omega Mc MS Mq MV P0` by METIS_TAC [] >>
    `!q0. q0 IN fv_P_c P0 ==> (Mq⦇q' ↦ qs⦈) q0 = Mq q0`
     suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
    rw [APPLY_UPDATE_THM] >> METIS_TAC []) >>
  `!s. (Mq⦇q' ↦ qs⦈) s SUBSET omega` by rw [APPLY_UPDATE_THM] >>
  `P_sem omega Mc MS Mq⦇q' ↦ qs⦈ MV P` by METIS_TAC [] >>
  `!q0. q0 IN fv_P_c P ==> (Mq⦇q' ↦ qs⦈) q0 = Mq q0`
   suffices_by METIS_TAC [fv_P_c_eq_P_sem] >>
  rw [APPLY_UPDATE_THM] >> METIS_TAC [],

  (* ex_in_S *)
  `P_sem omega Mc MS Mq MV (Ssubst_P ((V =+ S') S_var) P)`
   by METIS_TAC [] >>
  rw [P_sem] >>
  Q.EXISTS_TAC `S_sem omega MS MV S'` >>
  rw [] >- METIS_TAC [S_sem_omega] >>
  METIS_TAC [P_sem_Ssubst1],

  (* ex_el_S *)
  fs [P_sem] >>
  sg `!VS P0. P0 IN G ==> P_sem omega Mc MS Mq ((V' =+ VS) MV) P0` >-
   (rw [] >>
    `V' NOTIN fv_P_S P0` by METIS_TAC [] >>
    `P_sem omega Mc MS Mq MV P0` by METIS_TAC [] >>
    `!V0. V0 IN fv_P_S P0 ==> ((V' =+ VS) MV) V0 = MV V0`
     suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
    rw [APPLY_UPDATE_THM] >> METIS_TAC []) >>
  `?VS. VS SUBSET POW omega /\ P_sem omega Mc MS Mq ((V =+ VS) MV) P'` by METIS_TAC [] >>
  sg `P_sem omega Mc MS Mq ((V =+ (MV⦇V' ↦ VS⦈) V') (MV⦇V' ↦ VS⦈)) P'` >-
   (rw [P_sem_Ssubst1] >>
    `!V0. V0 IN fv_P_S P' ==> (MV⦇V ↦ VS; V' ↦ VS⦈) V0 = (MV⦇V ↦ VS⦈) V0`
     suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
    rw [APPLY_UPDATE_THM] >> METIS_TAC []) >>
  `P_sem omega Mc MS Mq (MV⦇V' ↦ VS⦈) (Ssubst_P S_var⦇V ↦ S_var V'⦈ P')`
   by METIS_TAC [P_sem_rename_S] >>
  sg `!P0. P0 IN G' ==> P_sem omega Mc MS Mq MV⦇V' ↦ VS⦈ P0` >-
   (rw [] >>
    `P_sem omega Mc MS Mq MV P0` by METIS_TAC [] >>
    `!V0. V0 IN fv_P_S P0 ==> (MV⦇V' ↦ VS⦈) V0 = MV V0`
     suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
    rw [APPLY_UPDATE_THM] >> METIS_TAC []) >>

  `!s. (MV⦇V' ↦ VS⦈) s SUBSET POW omega` by rw [APPLY_UPDATE_THM] >>
  `P_sem omega Mc MS Mq MV⦇V' ↦ VS⦈ P` by METIS_TAC [] >>
  `!V0. V0 IN fv_P_S P ==> (MV⦇V' ↦ VS⦈) V0 = MV V0`
   suffices_by METIS_TAC [fv_P_S_eq_P_sem] >>
  rw [APPLY_UPDATE_THM] >> METIS_TAC []
 ]
QED

(* proving compositionality *)

Theorem implements_comp_refines_two:
 !omega Mc MS Mq MV S0 S1 S2 q1 q2.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  q1 <> q2 /\
  (P_sem omega Mc MS Mq MV
  (P_forall_c q1 (P_forall_c q2
   (P_implies
     (P_and (P_implements (c_var q1) S1) (P_implements (c_var q2) S2))
     (P_implements (c_comp (c_var q1) (c_var q2)) S0))))) ==>
  P_sem omega Mc MS Mq MV (P_refines (S_par S1 S2) S0)
Proof
 rw [P_sem,c_sem,S_sem,APPLY_UPDATE_THM] >>
 Cases_on `q2 = q1` >> fs [] >>
 rw [double_intersection,SUBSET_DEF] >>
 METIS_TAC [IN_POW,SUBSET_DEF,S_sem_omega]
QED

Theorem contract_compositionality_sem_two:
 !omega Mc MS Mq MV A G A1 A2 G1 G2 q1 q2.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  q1 <> q2 /\
  (P_sem omega Mc MS Mq MV
  (P_forall_c q1 (P_forall_c q2
   (P_implies
     (P_and (P_implements (c_var q1) (S_assume A1 G1)) (P_implements (c_var q2) (S_assume A2 G2)))
     (P_implements (c_comp (c_var q1) (c_var q2)) (S_assume A G)))))) ==>
  P_sem omega Mc MS Mq MV (P_refines (S_par (S_assume A1 G1) (S_assume A2 G2)) (S_assume A G))
Proof
 METIS_TAC [implements_comp_refines_two]
QED

Theorem contract_compositionality_system_two:
 !R omega Mc MS Mq MV.
 spec_system_sound R omega /\
 (!s. Mc s SUBSET omega) /\
 (!s. Mq s SUBSET omega) /\
 (!s. MS s SUBSET POW omega) /\
 (!s. MV s SUBSET POW omega) ==>
 !Gamma. (!P0. P0 IN Gamma ==> P_sem omega Mc MS Mq MV P0) ==>
 !A G A1 A2 G1 G2 q1 q2.
  q1 <> q2 /\
  R Gamma (P_forall_c q1 (P_forall_c q2 (P_implies
   (P_and (P_implements (c_var q1) (S_assume A1 G1)) (P_implements (c_var q2) (S_assume A2 G2)))
   (P_implements (c_comp (c_var q1) (c_var q2)) (S_assume A G))))) ==>
 P_sem omega Mc MS Mq MV (P_refines (S_par (S_assume A1 G1) (S_assume A2 G2)) (S_assume A G))
Proof
 rw [spec_system_sound] >>
 match_mp_tac contract_compositionality_sem_two >>
 Q.EXISTS_TAC `q1` >> Q.EXISTS_TAC `q2` >>
 rw [] >> METIS_TAC []
QED

Theorem implements_comp_refines_three:
 !omega Mc MS Mq MV S0 S1 S2 S3 q1 q2 q3.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  q1 <> q2 /\ q1 <> q3 /\ q2 <> q3 /\
  (P_sem omega Mc MS Mq MV
   (P_forall_c q1 (P_forall_c q2 (P_forall_c q3
    (P_implies
     (P_and (P_implements (c_var q1) S1) (P_and (P_implements (c_var q2) S2) (P_implements (c_var q3) S3)))
     (P_implements (c_comp (c_var q1) (c_comp (c_var q2) (c_var q3))) S0)))))) ==>
  P_sem omega Mc MS Mq MV (P_refines (S_par S1 (S_par S2 S3)) S0)
Proof
 rw [P_sem,c_sem,S_sem,APPLY_UPDATE_THM] >>
 Cases_on `q2 = q1` >> fs [] >>
 Cases_on `q3 = q1` >> fs [] >>
 Cases_on `q3 = q2` >> fs [] >> 
 rw [double_intersection,SUBSET_DEF] >>
 METIS_TAC [IN_POW,SUBSET_DEF,S_sem_omega]
QED

Theorem contract_compositionality_sem_three:
 !omega Mc MS Mq MV A G A1 G1 A2 G2 A3 G3 q1 q2 q3.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  q1 <> q2 /\ q1 <> q3 /\ q2 <> q3 /\
  (P_sem omega Mc MS Mq MV
   (P_forall_c q1 (P_forall_c q2 (P_forall_c q3
    (P_implies
     (P_and (P_implements (c_var q1) (S_assume A1 G1))
      (P_and (P_implements (c_var q2) (S_assume A2 G2)) (P_implements (c_var q3) (S_assume A3 G3))))
     (P_implements (c_comp (c_var q1) (c_comp (c_var q2) (c_var q3))) (S_assume A G))))))) ==>
  P_sem omega Mc MS Mq MV (P_refines (S_par (S_assume A1 G1) (S_par (S_assume A2 G2) (S_assume A3 G3))) (S_assume A G))
Proof
 METIS_TAC [implements_comp_refines_three]
QED

Theorem contract_compositionality_system_three:
 !R omega Mc MS Mq MV.
 spec_system_sound R omega /\
 (!s. Mc s SUBSET omega) /\
 (!s. Mq s SUBSET omega) /\
 (!s. MS s SUBSET POW omega) /\
 (!s. MV s SUBSET POW omega) ==>
 !Gamma. (!P0. P0 IN Gamma ==> P_sem omega Mc MS Mq MV P0) ==>
 !A G A1 G1 A2 G2 A3 G3 q1 q2 q3.
  q1 <> q2 /\ q1 <> q3 /\ q2 <> q3 /\
  R Gamma
   (P_forall_c q1 (P_forall_c q2 (P_forall_c q3
    (P_implies
     (P_and (P_implements (c_var q1) (S_assume A1 G1))
      (P_and (P_implements (c_var q2) (S_assume A2 G2)) (P_implements (c_var q3) (S_assume A3 G3))))
     (P_implements (c_comp (c_var q1) (c_comp (c_var q2) (c_var q3))) (S_assume A G)))))) ==>   
  P_sem omega Mc MS Mq MV (P_refines (S_par (S_assume A1 G1) (S_par (S_assume A2 G2) (S_assume A3 G3))) (S_assume A G))
Proof
 rw [spec_system_sound] >>
 match_mp_tac contract_compositionality_sem_three >>
 Q.EXISTS_TAC `q1` >> Q.EXISTS_TAC `q2` >> Q.EXISTS_TAC `q3` >>
 rw [] >> METIS_TAC []
QED

Theorem implements_comp_three_refines:
 !omega Mc MS Mq MV S0 S1 S2 S3 q1 q2 q3.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  q1 <> q2 /\ q1 <> q3 /\ q2 <> q3 /\
  P_sem omega Mc MS Mq MV (P_refines (S_par S1 (S_par S2 S3)) S0) ==>
  (P_sem omega Mc MS Mq MV
   (P_forall_c q1 (P_forall_c q2 (P_forall_c q3
    (P_implies
     (P_and (P_implements (c_var q1) S1) (P_and (P_implements (c_var q2) S2) (P_implements (c_var q3) S3)))
     (P_implements (c_comp (c_var q1) (c_comp (c_var q2) (c_var q3))) S0))))))
Proof
 rw [P_sem,c_sem,S_sem,APPLY_UPDATE_THM] >>
 fs [double_intersection,SUBSET_DEF] >>
 METIS_TAC []
QED

Theorem implements_comp_three_refines_term:
 !omega Mc MS Mq MV S0 S1 S2 S3 c1 c2 c3.
  (!s. MS s SUBSET POW omega) /\
  (!s. MV s SUBSET POW omega) /\
  P_sem omega Mc MS Mq MV (P_refines (S_par S1 (S_par S2 S3)) S0) /\
  P_sem omega Mc MS Mq MV (P_implements c1 S1) /\
  P_sem omega Mc MS Mq MV (P_implements c2 S2) /\
  P_sem omega Mc MS Mq MV (P_implements c3 S3) ==>
  P_sem omega Mc MS Mq MV (P_implements (c_comp c1 (c_comp c2 c3)) S0)
Proof
 rw [P_sem,c_sem,S_sem] >>
 fs [double_intersection,SUBSET_DEF] >>
 METIS_TAC []
QED

Theorem compositionality_contracts_three:
 !R omega Mc MS Mq MV.
 spec_system_sound R omega /\
 (!s. Mc s SUBSET omega) /\
 (!s. Mq s SUBSET omega) /\
 (!s. MS s SUBSET POW omega) /\
 (!s. MV s SUBSET POW omega) ==>
 !Gamma. (!P0. P0 IN Gamma ==> P_sem omega Mc MS Mq MV P0) ==>
 !S0 S1 S2 S3 c1 c2 c3.
 P_sem omega Mc MS Mq MV (P_refines (S_par S1 (S_par S2 S3)) S0) /\
 R Gamma (P_implements c1 S1) /\
 R Gamma (P_implements c2 S2) /\
 R Gamma (P_implements c3 S3) ==>
 P_sem omega Mc MS Mq MV (P_implements (c_comp c1 (c_comp c2 c3)) S0)
Proof
 rw [spec_system_sound] >>
 match_mp_tac implements_comp_three_refines_term >>
 METIS_TAC []
QED

Theorem double_par_intersection1:
 !omega MS MV S1 S2 S3 x. 
  x IN S_sem omega MS MV (S_par S1 (S_par S2 S3)) ==>
  x IN { a INTER b INTER c | a IN S_sem omega MS MV S1 /\
     b IN S_sem omega MS MV S2 /\ c IN S_sem omega MS MV S3 }
Proof
 rw [S_sem,double_intersection] >>
 Q.EXISTS_TAC `a` >>
 Q.EXISTS_TAC `a'` >>
 Q.EXISTS_TAC `b'` >>
 rw [] >> 
 METIS_TAC [INTER_ASSOC]
QED

Theorem double_par_intersection2:
 !omega MS MV S1 S2 S3 x. 
  x IN { a INTER b INTER c | a IN S_sem omega MS MV S1 /\
     b IN S_sem omega MS MV S2 /\ c IN S_sem omega MS MV S3 } ==>
  x IN S_sem omega MS MV (S_par S1 (S_par S2 S3))
Proof
 rw [S_sem,double_intersection] >>
 Q.EXISTS_TAC `a` >>
 Q.EXISTS_TAC `b INTER c` >>
 rw [] >- METIS_TAC [INTER_ASSOC] >>
 Q.EXISTS_TAC `b` >>
 Q.EXISTS_TAC `c` >>
 rw []
QED

Theorem double_par_intersection:
 !omega MS MV S1 S2 S3. 
  S_sem omega MS MV (S_par S1 (S_par S2 S3)) =
   { a INTER b INTER c | a IN S_sem omega MS MV S1 /\
     b IN S_sem omega MS MV S2 /\ c IN S_sem omega MS MV S3 }
Proof
 rw [] >>
 once_rewrite_tac [EXTENSION] >>
 METIS_TAC [double_par_intersection1,double_par_intersection2]
QED

val _ = export_theory ();
