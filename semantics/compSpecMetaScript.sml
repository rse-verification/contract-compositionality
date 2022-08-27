open HolKernel boolLib Parse bossLib pred_setTheory listTheory combinTheory ottTheory compSpecUtilityTheory compSpecTheory;

(* ====================================== *)
(* Compositional specification metatheory *)
(* ====================================== *)

val _ = new_theory "compSpecMeta";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

Definition list_S_par:
 (list_S_par S [] = S)
 /\
 (list_S_par S (S'::Sl) = S_par S (list_S_par S' Sl))
End

Definition list_S_par_alt:
 list_S_par_alt (S:S) Sl = FOLDL (\S'. S_par S') S Sl
End

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
 (S_sem MS MV (S_const sn) = MS sn)
 /\
 (S_sem MS MV (S_conj S1 S2) = S_sem MS MV S1 INTER S_sem MS MV S2)
 /\
 (S_sem MS MV (S_assume S1 S2) =
  { b | !b'. b' IN S_sem MS MV S1 ==> b INTER b' IN S_sem MS MV S2 })
 /\
 (S_sem MS MV (S_par S1 S2) =
  double_intersection (S_sem MS MV S1) (S_sem MS MV S2))
 /\
 (S_sem MS MV (S_var V) = MV V)
 /\
 (S_sem MS MV S_compat = { B | B <> {} })
 /\
 (S_sem MS MV S_top = { UNIV })
End

Definition P_sem:
 (P_sem Mc MS Mq MV (P_implements c S) =
  (c_sem Mc Mq c IN S_sem MS MV S))
 /\
 (P_sem Mc MS Mq MV (P_refines S1 S2) =
  (S_sem MS MV S1 SUBSET S_sem MS MV S2))
 /\
 (P_sem Mc MS Mq MV (P_asserts S) =
  (downward_closed (S_sem MS MV S)))
 /\
 (P_sem Mc MS Mq MV (P_forall_c q P) =
  (!qs. P_sem Mc MS ((q =+ qs) Mq) MV P))
 /\
 (P_sem Mc MS Mq MV (P_exists_c q P) =
  (?qs. P_sem Mc MS ((q =+ qs) Mq) MV P))
 /\
 (P_sem Mc MS Mq MV (P_forall_S V P) =
  (!Vs. P_sem Mc MS Mq ((V =+ Vs) MV) P))
 /\
 (P_sem Mc MS Mq MV (P_exists_S V P) =
  (?Vs. P_sem Mc MS Mq ((V =+ Vs) MV) P))
 /\
 (P_sem Mc MS Mq MV (P_implies P1 P2) =
  (P_sem Mc MS Mq MV P1 ==> P_sem Mc MS Mq MV P2))
 /\
 (P_sem Mc MS Mq MV (P_and P1 P2) =
  (P_sem Mc MS Mq MV P1 /\ P_sem Mc MS Mq MV P2))
 /\
 (P_sem Mc MS Mq MV (P_c_eq c1 c2) =
  (c_sem Mc Mq c1 = c_sem Mc Mq c2))
 /\
 (P_sem Mc MS Mq MV (P_S_eq S1 S2) =
  (S_sem MS MV S1 = S_sem MS MV S2))
End

Definition spec_compositionality:
 spec_compositionality Mc MS Mq MV S0 Sl S =
  (P_sem Mc MS Mq MV (P_refines (list_S_par S0 Sl) S))
End

(* FIXME: valuations not needed *)
Definition spec_system_sound:
 spec_system_sound R Mc MS Mq MV =
  !G P. (!P0. P0 IN G ==> P_sem Mc MS Mq MV P0) /\
    R G P ==>
    P_sem Mc MS Mq MV P
End

(* --------------- *)
(* Utility results *)
(* --------------- *)

Theorem fv_c_eq_c_sem:
 !Mc Mq Mq' c. (!q. q IN fv_c c ==> Mq q = Mq' q) ==>
  c_sem Mc Mq c = c_sem Mc Mq' c
Proof
 strip_tac >> strip_tac >> strip_tac >>
 Induct_on `c` >> rw [c_sem,fv_c]
QED

Theorem fv_S_eq_S_sem:
 !MS MV MV' S'. (!V. V IN fv_S S' ==> MV V = MV' V) ==>
  S_sem MS MV S' = S_sem MS MV' S'
Proof
 strip_tac >> strip_tac >> strip_tac >>
 Induct_on `S'` >> rw [S_sem,fv_S]
QED

Theorem fv_P_c_eq_P_sem:
 !Mc MS P Mq Mq' MV. 
  (!q. q IN fv_P_c P ==> Mq q = Mq' q) ==>
  P_sem Mc MS Mq MV P = P_sem Mc MS Mq' MV P
Proof
 strip_tac >> strip_tac >>
 Induct_on `P` >> rw [P_sem,fv_P_c] >| [
  METIS_TAC [fv_c_eq_c_sem],

  EQ_TAC >> rw [] >>
  `!q. q IN fv_P_c P ==> ((s =+ qs) Mq) q = ((s =+ qs) Mq') q`
   by rw [APPLY_UPDATE_THM] >>
  `P_sem Mc MS ((s =+ qs) Mq) MV P <=> P_sem Mc MS ((s =+ qs) Mq') MV P`
   by (Q.PAT_X_ASSUM `!M1 M2 M3. Q ==> R` (STRIP_ASSUME_TAC o
    (Q.SPECL [`(s =+ qs) Mq`,`(s =+ qs) Mq'`])) >>
    METIS_TAC []) >>
  METIS_TAC [],

  EQ_TAC >> rw [] >>
  `!q. q IN fv_P_c P ==> ((s =+ qs) Mq) q = ((s =+ qs) Mq') q`
   by rw [APPLY_UPDATE_THM] >>
  `P_sem Mc MS ((s =+ qs) Mq) MV P <=> P_sem Mc MS ((s =+ qs) Mq') MV P`
   by (Q.PAT_X_ASSUM `!M1 M2 M3. Q ==> R` (STRIP_ASSUME_TAC o
    (Q.SPECL [`(s =+ qs) Mq`,`(s =+ qs) Mq'`])) >>
    METIS_TAC []) >>
  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [fv_c_eq_c_sem]
 ]
QED

Theorem fv_P_S_eq_P_sem:
 !Mc MS P MV MV' Mq. 
  (!V. V IN fv_P_S P ==> MV V = MV' V) ==>
  P_sem Mc MS Mq MV P = P_sem Mc MS Mq MV' P
Proof
 strip_tac >> strip_tac >>
 Induct_on `P` >> rw [P_sem,fv_P_S] >| [
  METIS_TAC [fv_S_eq_S_sem],

  METIS_TAC [fv_S_eq_S_sem],

  METIS_TAC [fv_S_eq_S_sem],

  METIS_TAC [],

  METIS_TAC [],

  EQ_TAC >> rw [] >>
  `!V. V IN fv_P_S P ==> ((s =+ Vs) MV) V = ((s =+ Vs) MV') V`
   by rw [APPLY_UPDATE_THM] >>
  `P_sem Mc MS Mq ((s =+ Vs) MV) P <=> P_sem Mc MS Mq ((s =+ Vs) MV') P`
   by (Q.PAT_X_ASSUM `!M1 M2 M3. Q ==> R` (STRIP_ASSUME_TAC o
    (Q.SPECL [`(s =+ Vs) MV`,`(s =+ Vs) MV'`])) >>
    METIS_TAC []) >>
  METIS_TAC [],

  EQ_TAC >> rw [] >>
  `!V. V IN fv_P_S P ==> ((s =+ Vs) MV) V = ((s =+ Vs) MV') V`
   by rw [APPLY_UPDATE_THM] >>
  `P_sem Mc MS Mq ((s =+ Vs) MV) P <=> P_sem Mc MS Mq ((s =+ Vs) MV') P`
   by (Q.PAT_X_ASSUM `!M1 M2 M3. Q ==> R` (STRIP_ASSUME_TAC o
    (Q.SPECL [`(s =+ Vs) MV`,`(s =+ Vs) MV'`])) >>
    METIS_TAC []) >>
  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [],

  METIS_TAC [fv_S_eq_S_sem]
 ]
QED

Theorem fv_c_empty_c_sem:
 !Mc Mq c q qs. fv_c c = {} ==>
  c_sem Mc Mq c = c_sem Mc ((q =+ qs) Mq) c
Proof
 rw [] >> 
 match_mp_tac fv_c_eq_c_sem >>
 rw []
QED

Theorem fv_S_empty_S_sem:
 !MS MV S V Vs. fv_S S = {} ==>
  S_sem MS MV S = S_sem MS ((V =+ Vs) MV) S
Proof
 rw [] >>
 match_mp_tac fv_S_eq_S_sem >>
 rw []
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
 !MS MV A1 G1 a.
  a IN S_sem MS MV (S_assume A1 G1) /\
  a IN S_sem MS MV A1 ==>
  a IN S_sem MS MV G1
Proof
 rw [S_sem] >> METIS_TAC [INTER_IDEMPOT]
QED

Theorem S_sem_IN_assume_IN:
 !MS MV A1 G1 a.
  a IN S_sem MS MV (S_assume A1 G1) /\
  a IN S_sem MS MV A1 ==>
  a IN S_sem MS MV G1
Proof
 rw [S_sem] >> METIS_TAC [INTER_IDEMPOT]
QED

Theorem S_sem_IN_par_IN:
 !MS MV A1 G1 x.
  x IN S_sem MS MV (S_par A1 G1) <=>
  ?a b. x = a INTER b /\ a IN S_sem MS MV A1 /\ b IN S_sem MS MV G1
Proof
 rw [S_sem,double_intersection]
QED

Theorem S_sem_conj_IDEM:
 !MS MV S. S_sem MS MV (S_conj S S) = S_sem MS MV S
Proof
 rw [S_sem,INTER_IDEMPOT]
QED

Theorem S_sem_conj_ASSOC:
 !MS MV S1 S2 S3.
  S_sem MS MV (S_conj S1 (S_conj S2 S3)) = S_sem MS MV (S_conj (S_conj S1 S2) S3)
Proof
 rw [S_sem,INTER_ASSOC]
QED

Theorem S_sem_conj_COMM:
 !MS MV S1 S2.
  S_sem MS MV (S_conj S1 S2) = S_sem MS MV (S_conj S2 S1)
Proof
 rw [S_sem,INTER_COMM]
QED

Theorem S_sem_par_ASSOC:
 !MS MV S1 S2 S3.
  S_sem MS MV (S_par S1 (S_par S2 S3)) = S_sem MS MV (S_par (S_par S1 S2) S3)
Proof
 rw [S_sem,double_intersection_ASSOC]
QED

Theorem S_sem_par_COMM:
 !MS MV S1 S2. S_sem MS MV (S_par S1 S2) = S_sem MS MV (S_par S2 S1)
Proof
 rw [S_sem,double_intersection_COMM]
QED

Theorem proposition_2a:
 !Mc MS Mq MV c S1 S2.
  P_sem Mc MS Mq MV (P_implements c S1) /\
  P_sem Mc MS Mq MV (P_refines S1 S2) ==>
  P_sem Mc MS Mq MV (P_implements c S2)
Proof
 rw [P_sem] >> METIS_TAC [SUBSET_DEF]
QED

Theorem proposition_2b:
 !Mc MS Mq MV S1 S2 q.
  (P_sem Mc MS Mq MV
   (P_forall_c q
    (P_implies 
     (P_implements (c_var q) S1)
     (P_implements (c_var q) S2)))) ==>
  P_sem Mc MS Mq MV (P_refines S1 S2)
Proof
 rw [P_sem,c_sem] >> METIS_TAC [SUBSET_DEF,APPLY_UPDATE_THM]
QED

Theorem proposition_3a:
 !Mc MS Mq MV S q1 q2.
   q1 <> q2 ==>
   (P_sem Mc MS Mq MV
    (P_forall_c q1 (P_forall_c q2
     (P_implies
      (P_implements (c_var q1) S)
      (P_implements (c_comp (c_var q1) (c_var q2)) S))))) ==>
   P_sem Mc MS Mq MV (P_asserts S)
Proof
 rw [P_sem,c_sem,downward_closed] >>
 METIS_TAC [INTER_SUBSET_EQN,APPLY_UPDATE_THM]
QED

Theorem proposition3_b:
 !Mc MS Mq MV S c1 c2.
  P_sem Mc MS Mq MV (P_asserts S) /\
  P_sem Mc MS Mq MV (P_implements c1 S) ==>
  P_sem Mc MS Mq MV (P_implements (c_comp c1 c2) S)
Proof
 rw [P_sem,downward_closed,c_sem] >>
 METIS_TAC [INTER_SUBSET]
QED

Theorem proposition_4a:
 !Mc MS Mq MV S1 S2 c.
  P_sem Mc MS Mq MV (P_implements c S1) /\
  P_sem Mc MS Mq MV (P_implements c S2) ==>
  P_sem Mc MS Mq MV (P_implements c (S_conj S1 S2))
Proof
 rw [P_sem,S_sem]
QED

Theorem proposition_4b:
 !Mc MS Mq MV S1 S2 c.
  P_sem Mc MS Mq MV (P_implements c (S_conj S1 S2)) ==>
  P_sem Mc MS Mq MV (P_implements c S1)
Proof
 rw [P_sem,S_sem]
QED

Theorem proposition_4b_alt:
 !Mc MS Mq MV S1 S2 c.
  P_sem Mc MS Mq MV (P_implements c (S_conj S1 S2)) ==>
  P_sem Mc MS Mq MV (P_implements c S2)
Proof
 rw [P_sem,S_sem]
QED

Theorem proposition_5a:
 !Mc MS Mq MV S1 S2 c q1 q2.
  q1 <> q2 ==>
  fv_c c = {} ==>
  P_sem Mc MS Mq MV (P_implements c (S_par S1 S2)) ==>
  P_sem Mc MS Mq MV 
   (P_exists_c q1 (P_exists_c q2
     (P_and (P_implements (c_var q1) S1)
      (P_and (P_implements (c_var q2) S2)
       (P_c_eq c (c_comp (c_var q1) (c_var q2)))))))
Proof
 rw [P_sem,c_sem,S_sem,double_intersection,APPLY_UPDATE_THM] >>
 Q.EXISTS_TAC `a` >>
 Q.EXISTS_TAC `b` >>
 rw [] >>
 METIS_TAC [fv_c_empty_c_sem]
QED

Theorem proposition_5b:
 !Mc MS Mq MV S1 S2 c1 c2.
  P_sem Mc MS Mq MV (P_implements c1 S1) /\
  P_sem Mc MS Mq MV (P_implements c2 S2) ==>
  P_sem Mc MS Mq MV (P_implements (c_comp c1 c2) (S_par S1 S2))
Proof
 rw [P_sem,c_sem,S_sem,double_intersection] >> METIS_TAC []
QED

Theorem proposition_6a:
 !Mc MS Mq MV S1 S2. P_sem Mc MS Mq MV (P_refines (S_conj S1 S2) (S_par S1 S2))
Proof
 rw [P_sem,S_sem,double_intersection,SUBSET_DEF] >> METIS_TAC [INTER_IDEMPOT]
QED

Theorem proposition_6b:
 !Mc MS Mq MV S1 S2.
  P_sem Mc MS Mq MV (P_asserts S1) /\ P_sem Mc MS Mq MV (P_asserts S2) ==>
  P_sem Mc MS Mq MV (P_refines (S_par S1 S2) (S_conj S1 S2))
Proof
 rw [P_sem,S_sem,downward_closed,double_intersection,SUBSET_DEF] >>
 METIS_TAC [SUBSET_DEF,INTER_SUBSET]
QED

Theorem proposition_7a:
 !Mc MS Mq MV S1 S2. P_sem Mc MS Mq MV (P_refines (S_par S1 (S_assume S1 S2)) S2)
Proof
 rw [P_sem,S_sem,double_intersection,SUBSET_DEF] >> METIS_TAC [INTER_COMM]
QED

Theorem proposition_7a_alt:
 !Mc MS Mq MV S1 S2 c1 c2.
  P_sem Mc MS Mq MV (P_implements c1 S1) /\
  P_sem Mc MS Mq MV (P_implements c2 (S_assume S1 S2)) ==>
  P_sem Mc MS Mq MV (P_implements (c_comp c1 c2) S2)
Proof
 rw [P_sem,c_sem,S_sem] >> METIS_TAC [INTER_COMM]
QED

Theorem proposition_7b:
 !Mc MS Mq MV S1 S2 c2 q1.
   q1 NOTIN fv_c c2 ==>
   (P_sem Mc MS Mq MV
    (P_forall_c q1
     (P_implies (P_implements (c_var q1) S1)
      (P_implements (c_comp (c_var q1) c2) S2)))) ==>
   P_sem Mc MS Mq MV (P_implements c2 (S_assume S1 S2))
Proof
 rw [P_sem,c_sem,S_sem,APPLY_UPDATE_THM] >>
 `(b' INTER c_sem Mc Mq c2) IN S_sem MS MV S2` suffices_by METIS_TAC [INTER_COMM] >>
 `c_sem Mc Mq c2 = c_sem Mc ((q1 =+ b') Mq) c2`
  suffices_by METIS_TAC [] >>
 match_mp_tac fv_c_eq_c_sem >>
 rw [APPLY_UPDATE_THM] >> fs []
QED

Theorem proposition_7b_alt:
 !Mc MS Mq MV S1 S2 c2. 
  P_sem Mc MS Mq MV (P_implements c2 S2) ==>
  P_sem Mc MS Mq MV (P_asserts S2) ==>
  P_sem Mc MS Mq MV (P_implements c2 (S_assume S1 S2))
Proof
 rw [P_sem,S_sem,downward_closed] >>
 METIS_TAC [INTER_SUBSET]
QED

Theorem proposition_8:
 !MS MV S. S_sem MS MV S = S_sem MS MV (S_assume S_top S)
Proof
 rw [S_sem]
QED

Theorem proposition_9:
 !Mc MS Mq MV S1 S2.
  P_sem Mc MS Mq MV (P_asserts S2) ==>
  P_sem Mc MS Mq MV (P_asserts (S_assume S1 S2))
Proof
 rw [P_sem,downward_closed,S_sem] >>
 `e INTER b' IN S_sem MS MV S2` by METIS_TAC [] >>
 `e' INTER b' SUBSET e INTER b'` suffices_by METIS_TAC [] >>
 fs [SUBSET_DEF]
QED

Theorem compat_comp:
 !Mc MS Mq MV c1 c2.
  P_sem Mc MS Mq MV (P_implements (c_comp c1 c2) S_compat) <=>
  (c_sem Mc Mq c1) INTER (c_sem Mc Mq c2) <> {}
Proof
 rw [] >> EQ_TAC >> rw [P_sem,c_sem,S_sem]
QED

Theorem spec_holds_system_sound:
 !Mc MS Mq MV. spec_system_sound spec_holds Mc MS Mq MV
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 `!G P. spec_holds G P ==> 
   (!P0. P0 IN G ==> P_sem Mc MS Mq MV P0) ==> P_sem Mc MS Mq MV P`
  suffices_by METIS_TAC [spec_system_sound] >>
 ho_match_mp_tac spec_holds_ind >> rw [] >| [
  (* re *)
  METIS_TAC [proposition_2a],

  (* am *)
  METIS_TAC [proposition3_b],

  (* conji *)
  METIS_TAC [proposition_4a],

  (* conje1 *)
  METIS_TAC [proposition_4b],

  (* conje2 *)
  METIS_TAC [proposition_4b_alt],

  (* ce *)
  METIS_TAC [proposition_7a_alt],

  (* ci *)
  METIS_TAC [proposition_7b],

  (* cre *)
  METIS_TAC [proposition_4b_alt,proposition_2a,proposition_4a]
 ]
QED

Theorem contract_compositionality_sem_two:
 !Mc MS Mq MV S1 S2 A1 A2 G1 G2 q1 q2.
  q1 <> q2 /\
  (P_sem Mc MS Mq MV
  (P_forall_c q1 (P_forall_c q2
   (P_implies
     (P_and (P_implements (c_var q1) (S_assume A1 G1)) (P_implements (c_var q2) (S_assume A2 G2)))
     (P_implements (c_comp (c_var q1) (c_var q2)) (S_assume S1 S2)))))) ==>
  P_sem Mc MS Mq MV (P_refines (S_par (S_assume A1 G1) (S_assume A2 G2)) (S_assume S1 S2))
Proof
 rw [P_sem,c_sem,APPLY_UPDATE_THM] >>
 rw [SUBSET_DEF] >>
 `?a b. x = a INTER b /\ a IN S_sem MS MV (S_assume A1 G1) /\ b IN S_sem MS MV (S_assume A2 G2)`
  by METIS_TAC [S_sem_IN_par_IN] >>
 rw [] >> Cases_on `q1 = q2` >> fs []
QED

Theorem contract_compositionality_system_two:
 !R Mc MS Mq MV.
 spec_system_sound R Mc MS Mq MV ==>
 !G. (!P0. P0 IN G ==> P_sem Mc MS Mq MV P0) ==>
 !S1 S2 A1 A2 G1 G2 q1 q2.
  q1 <> q2 ==>
  R G (P_forall_c q1 (P_forall_c q2 (P_implies
   (P_and (P_implements (c_var q1) (S_assume A1 G1)) (P_implements (c_var q2) (S_assume A2 G2)))
   (P_implements (c_comp (c_var q1) (c_var q2)) (S_assume S1 S2))))) ==>
 P_sem Mc MS Mq MV (P_refines (S_par (S_assume A1 G1) (S_assume A2 G2)) (S_assume S1 S2))
Proof
 rw [spec_system_sound] >>
 match_mp_tac contract_compositionality_sem_two >>
 Q.EXISTS_TAC `q1` >> Q.EXISTS_TAC `q2` >>
 rw [] >> METIS_TAC []
QED

val _ = export_theory ();
