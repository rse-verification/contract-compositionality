open HolKernel boolLib Parse bossLib;
open pred_setTheory listTheory combinTheory;
open ottTheory compSpecUtilityTheory compSpecTheory compSpecMetaTheory;

val _ = new_theory "compSpecExample";

Definition example_implements:
 example_implements c1 c2 A G =
  P_implements (c_comp c1 c2) (S_assume A G)
End

(* EVAL ``P_sem omega Mc MS Mq MV (example_implements c1 c2 A G)`` *)

Definition example_4_MS:
 (example_4_MS s =
  if s = "S1"
  then {{(0, 0, 0); (0, 0, 1)}; {(0, 1, 0); (0, 1, 1)}}
  else if s = "S2"
  then {{(0, 1, 0); (0, 1, 1)}; {(0, 1, 0); (1, 1, 0)}}
  else {})
End

Definition example_5_Mc:
 (example_5_Mc s =
  if s = "c3"
  then {(0, 0, 0); (0, 0, 1)}
  else if s = "c4"
  then {(0, 1, 0); (0, 1, 1)}
  else if s = "c5"
  then {(0, 1, 0); (1, 1, 0)}
  else {})
End

Theorem example_5_c3_S1:
 !Mq MV. P_sem UNIV example_5_Mc example_4_MS Mq MV (P_implements (c_const "c3") (S_const (Sc_const "S1")))
Proof
 rw [P_sem,c_sem,S_sem,example_5_Mc,example_4_MS]
QED

Theorem example_5_c4_S1:
 !Mq MV. P_sem UNIV example_5_Mc example_4_MS Mq MV (P_implements (c_const "c4") (S_const (Sc_const "S1")))
Proof
 rw [P_sem,c_sem,S_sem,example_5_Mc,example_4_MS]
QED

Theorem example_5_c3_c4_S1:
 !Mq MV. ~ (P_sem UNIV example_5_Mc example_4_MS Mq MV
    (P_implements (c_comp (c_const "c3") (c_const "c4")) (S_const (Sc_const "S1"))))
Proof
 rw [P_sem,c_sem,S_sem,example_5_Mc,example_4_MS,INTER_DEF] >-
  (rw [EXTENSION] >> Q.EXISTS_TAC `(0,0,0)` >> fs []) >>
 rw [EXTENSION] >>
 Q.EXISTS_TAC `(0,1,0)` >>
 fs []
QED

Theorem example_5_c4_S2:
 !Mq MV. P_sem UNIV example_5_Mc example_4_MS Mq MV (P_implements (c_const "c4") (S_const (Sc_const "S2")))
Proof
 rw [P_sem,c_sem,S_sem,example_5_Mc,example_4_MS]
QED

Theorem example_5_c5_S2:
 !Mq MV. P_sem UNIV example_5_Mc example_4_MS Mq MV (P_implements (c_const "c5") (S_const (Sc_const "S2")))
Proof
 rw [P_sem,c_sem,S_sem,example_5_Mc,example_4_MS]
QED

Theorem example_5_c4_c5_S2:
 !Mq MV. ~ (P_sem UNIV example_5_Mc example_4_MS Mq MV
    (P_implements (c_comp (c_const "c4") (c_const "c5")) (S_const (Sc_const "S2"))))
Proof
 rw [P_sem,c_sem,S_sem,example_5_Mc,example_4_MS,INTER_DEF] >-
  (rw [EXTENSION] >> Q.EXISTS_TAC `(0,1,1)` >> fs []) >>
 rw [EXTENSION] >>
 Q.EXISTS_TAC `(1,1,0)` >>
 fs []
QED

Definition P_c_eq_forall_c_assoc:
 P_c_eq_forall_c_assoc =
  (P_forall_c "q" (P_forall_c "q'" (P_forall_c "q''"
     (P_c_eq (c_comp (c_comp (c_var "q") (c_var "q'")) (c_var "q''"))
             (c_comp (c_var "q") (c_comp (c_var "q'") (c_var "q''")))))))
End

Theorem P_sem_forall_c_assoc:
 !omega Mc MS Mq MV.
   P_sem omega Mc MS Mq MV P_c_eq_forall_c_assoc
Proof
 rw [P_c_eq_forall_c_assoc,P_sem,c_sem_comp_ASSOC]
QED

Definition P_S_eq_forall_S_conj_comm:
 P_S_eq_forall_S_conj_comm S1 S2 =
  (P_S_eq (S_conj S1 S2) (S_conj S2 S1))
End

Theorem P_sem_S_eq_forall_S_conj_comm:
 !S1 S2 omega Mc MS Mq MV. P_sem omega Mc MS Mq MV (P_S_eq_forall_S_conj_comm S1 S2)
Proof
 rw [P_S_eq_forall_S_conj_comm,P_sem,S_sem_conj_COMM]
QED

Definition P_S_eq_conj_comm_assoc_compat:
 P_S_eq_conj_comm_assoc_compat S1 S2 =
  (P_S_eq
   (S_conj S2 (S_conj S1 (S_const Sc_compat)))
   (S_conj (S_conj S1 S2) (S_const Sc_compat)))
End

Theorem P_sem_S_eq_conj_comm_assoc_compat:
 !S1 S2 omega Mc MS Mq MV. P_sem omega Mc MS Mq MV (P_S_eq_conj_comm_assoc_compat S1 S2)
Proof
 rw [P_S_eq_conj_comm_assoc_compat,P_sem,GSYM S_sem_conj_ASSOC] >>
 rw [S_sem_conj_ASSOC] >>
 rw [S_sem] >>
 METIS_TAC [INTER_COMM] 
QED

Definition example_Gamma:
 example_Gamma A A1 A2 G G1 G2 =
  { P_asserts A; P_refines A A1; P_refines (S_conj A G1) A2; P_refines G2 G }
End

Definition example_Gamma_ext:
 example_Gamma_ext A A1 A2 A3 G G1 G2 G3 =
  { P_asserts A;
    P_refines A A1;
    P_refines (S_conj A G1) A2;
    P_refines (S_conj A1 G2) A3;
    P_refines G3 G }
End

Definition example_Ps:
 example_Ps A A1 A2 G G1 G2 =
  P_S_eq_conj_comm_assoc_compat G1 A INSERT
  P_S_eq_forall_S_conj_comm A G1 INSERT
  P_c_eq_forall_c_assoc INSERT
  example_Gamma A A1 A2 G G1 G2
End

Definition example_goal:
 example_goal A A1 A2 G G1 G2 =
  P_forall_c "q" (P_implies
   (P_implements (c_var "q") (S_assume (S_conj A1 (S_const Sc_compat)) (S_conj G1 (S_const Sc_compat))))
   (P_forall_c "q'" (P_implies
     (P_implements (c_var "q'") (S_assume (S_conj A2 (S_const Sc_compat)) (S_conj G2 (S_const Sc_compat))))
     (P_implements (c_comp (c_var "q") (c_var "q'"))
        (S_assume (S_conj A (S_const Sc_compat)) (S_conj G (S_const Sc_compat)))))))
End

Definition example_goal_ext:
 example_goal_ext A A1 A2 A3 G G1 G2 G3 =
  P_forall_c "q" (P_implies
   (P_implements (c_var "q") (S_assume (S_conj A1 (S_const Sc_compat)) (S_conj G1 (S_const Sc_compat))))
   (P_forall_c "q'" (P_implies
     (P_implements (c_var "q'") (S_assume (S_conj A2 (S_const Sc_compat)) (S_conj G2 (S_const Sc_compat))))
     (P_forall_c "q''" (P_implies
       (P_implements (c_var "q''") (S_assume (S_conj A3 (S_const Sc_compat)) (S_conj G3 (S_const Sc_compat))))
        (P_implements (c_comp (c_var "q") (c_comp (c_var "q'") (c_var "q''")))
         (S_assume (S_conj A (S_const Sc_compat)) (S_conj G (S_const Sc_compat)))))))))
End

Theorem SUBSET_INTER_POW[local]:
 !s1 s2 s. s1 SUBSET s /\ s2 SUBSET s ==>
  s1 INTER s2 IN POW s
Proof
 rw [INTER_DEF,SUBSET_DEF,POW_DEF]
QED

Theorem example_refine_sem:
 !omega Mc MS Mq MV. 
 (!s. Mc s SUBSET omega) /\
 (!s. Mq s SUBSET omega) /\
 (!s. MS s SUBSET POW omega) /\
 (!s. MV s SUBSET POW omega) ==>
 !A A1 A2 G G1 G2.
 (!P0. P0 IN example_Ps A A1 A2 G G1 G2 ==> P_sem omega Mc MS Mq MV P0) ==>
 P_sem omega Mc MS Mq MV (example_goal A A1 A2 G G1 G2)
Proof
 rw [example_Ps,example_goal,example_Gamma] >>

 `P_sem omega Mc MS Mq MV (P_asserts A)` by METIS_TAC [] >>
 `P_sem omega Mc MS Mq MV (P_refines A A1)` by METIS_TAC [] >>
 `P_sem omega Mc MS Mq MV (P_refines (S_conj A G1) A2)` by METIS_TAC [] >>
 `P_sem omega Mc MS Mq MV (P_refines G2 G)` by METIS_TAC [] >>

 Q.PAT_X_ASSUM `!P0. P` (fn thm => ALL_TAC) >> 
 fs [P_sem,S_sem,c_sem,downward_closed] >> rw [APPLY_UPDATE_THM] >-
 METIS_TAC [SUBSET_INTER_POW] >>

 `B' IN S_sem omega MS MV A1` by METIS_TAC [SUBSET_DEF] >>
 `B' IN POW omega` by METIS_TAC [POW_DEF,SUBSET_DEF] >>
 
 `qs INTER B' IN S_sem omega MS MV G1` by METIS_TAC [] >>
 `qs INTER B' <> {}` by METIS_TAC [] >>
 `qs INTER B' IN POW omega` by METIS_TAC [] >>
 `qs INTER B' IN S_sem omega MS MV A2` by
   (`qs INTER B' IN S_sem omega MS MV A INTER S_sem omega MS MV G1`
      suffices_by METIS_TAC [SUBSET_DEF] >>
    `!e'. e' SUBSET B' ==> e' IN S_sem omega MS MV A` by METIS_TAC [] >>
    `qs INTER B' SUBSET B'` by rw [INTER_DEF,SUBSET_DEF] >>
    `qs INTER B' IN S_sem omega MS MV A` by METIS_TAC [] >>
    METIS_TAC [IN_INTER]) >| [

    `qs' INTER (qs INTER B') IN S_sem omega MS MV G`
     by METIS_TAC [SUBSET_DEF] >>
    METIS_TAC [INTER_COMM,INTER_ASSOC],

    
    `qs' INTER (qs INTER B') IN POW omega`
     by METIS_TAC [SUBSET_DEF] >>
    METIS_TAC [INTER_COMM,INTER_ASSOC],

    `qs' INTER (qs INTER B') <> {}`
      by METIS_TAC [SUBSET_DEF] >>
    METIS_TAC [INTER_COMM,INTER_ASSOC]
 ]
QED

Theorem example_refine_sem_ext[local]:
 !omega Mc MS Mq MV. 
 (!s. Mc s SUBSET omega) /\
 (!s. Mq s SUBSET omega) /\
 (!s. MS s SUBSET POW omega) /\
 (!s. MV s SUBSET POW omega) ==>
 !A A1 A2 A3 G G1 G2 G3.
 (!P0. P0 IN example_Gamma_ext A A1 A2 A3 G G1 G2 G3 ==> P_sem omega Mc MS Mq MV P0) ==>
 P_sem omega Mc MS Mq MV (example_goal_ext A A1 A2 A3 G G1 G2 G3)
Proof
 rw [example_Gamma_ext,example_goal_ext] >> 

 `P_sem omega Mc MS Mq MV (P_asserts A)` by METIS_TAC [] >>
 `P_sem omega Mc MS Mq MV (P_refines A A1)` by METIS_TAC [] >>
 `P_sem omega Mc MS Mq MV (P_refines (S_conj A G1) A2)` by METIS_TAC [] >>
 `P_sem omega Mc MS Mq MV (P_refines (S_conj A1 G2) A3)` by METIS_TAC [] >>
 `P_sem omega Mc MS Mq MV (P_refines G3 G)` by METIS_TAC [] >>

 Q.PAT_X_ASSUM `!P0. P` (fn thm => ALL_TAC) >> 

 fs [P_sem,S_sem,c_sem,downward_closed] >> rw [APPLY_UPDATE_THM] >-
 cheat >| [

  `B' IN S_sem omega MS MV A1` by METIS_TAC [SUBSET_DEF] >>
  `B' IN POW omega` by METIS_TAC [POW_DEF,SUBSET_DEF] >>
 
  `qs INTER B' IN S_sem omega MS MV G1` by METIS_TAC [] >>
  `qs INTER B' <> {}` by METIS_TAC [] >>

  `!e'. e' SUBSET B' ==> e' IN S_sem omega MS MV A` by METIS_TAC [] >>
  `qs INTER B' SUBSET B'` by rw [INTER_DEF,SUBSET_DEF] >>
  `qs INTER B' IN S_sem omega MS MV A` by METIS_TAC [] >>
  
  cheat,

  cheat,

  cheat
]
QED

Theorem ax_IN:
 !P G. P IN G ==> spec_holds G P
Proof
 rw [] >> 
 sg `?G'. G = P INSERT G'` >-
  (Q.EXISTS_TAC `G DELETE P` >>
   rw [INSERT_DELETE]) >>
 rw [] >> MATCH_MP_TAC ax >> rw [clause_name_def]
QED

Theorem SVARIANT_INSERT:
 !s x. FINITE s ==> SVARIANT (x INSERT s) <> x
Proof
 rw [] >>
 strip_tac >>
 `FINITE (x INSERT s)` by rw [FINITE_INSERT] >>
 `SVARIANT (x INSERT s) NOTIN (x INSERT s)` by
  METIS_TAC [SVARIANT_FINITE] >>
 fs []
QED

Theorem FINITE_example_Ps:
 !A A1 A2 G G1 G2.
  FINITE (example_Ps A A1 A2 G G1 G2)
Proof
 rw [example_Ps,example_Gamma]
QED

Theorem fv_P_c_P_c_eq_forall_c_assoc_EMPTY:
 fv_P_c P_c_eq_forall_c_assoc = {}
Proof
 rw [fv_P_c,P_c_eq_forall_c_assoc,fv_c,UNION_DEF,DELETE_DEF,DIFF_DEF,EXTENSION] >>
 METIS_TAC []
QED

Theorem fv_P_c_P_S_eq_forall_S_conj_comm_EMPTY:
 !S1 S2. fv_P_c (P_S_eq_forall_S_conj_comm S1 S2) = {}
Proof
 rw [fv_P_c,P_S_eq_forall_S_conj_comm]
QED

Theorem fv_P_c_P_S_eq_conj_comm_assoc_compat_EMPTY:
 !S1 S2. fv_P_c (P_S_eq_conj_comm_assoc_compat S1 S2) = {}
Proof
 rw [fv_P_c,P_S_eq_conj_comm_assoc_compat]
QED

Theorem fv_P_S_P_S_eq_forall_S_conj_comm_EMPTY:
 !S1 S2. fv_P_S (P_S_eq_forall_S_conj_comm S1 S2) = fv_S S1 UNION fv_S S2
Proof
 rw [fv_P_S,P_S_eq_forall_S_conj_comm,fv_S,UNION_DEF,EXTENSION] >>
 METIS_TAC []
QED

Theorem fv_P_S_P_S_eq_conj_comm_assoc_compat_UNION:
 !S1 S2. fv_P_S (P_S_eq_conj_comm_assoc_compat S1 S2) = fv_S S1 UNION fv_S S2
Proof
 rw [fv_P_S,P_S_eq_conj_comm_assoc_compat,fv_S,UNION_DEF,EXTENSION] >>
 METIS_TAC []
QED

Theorem BIGUNION_IMAGE_f_NOTIN:
 !x f G.
  (x NOTIN BIGUNION (IMAGE f G))
  <=>
  (!P. P IN G ==> x NOTIN (f P))
Proof
 rw [] >> METIS_TAC []
QED

Theorem example_Gamma_fv_P_c_NOTIN:
 !A A1 A2 G G1 G2 P.
  P IN example_Gamma A A1 A2 G G1 G2 ==>
  fv_P_c P = {}
Proof
 rw [example_Gamma] >> rw [fv_P_c]
QED

Theorem example_Gamma_fv_P_S:
 !A A1 A2 G G1 G2 P.
  BIGUNION (IMAGE fv_P_S (example_Gamma A A1 A2 G G1 G2)) =
  (fv_S A UNION fv_S A1 UNION fv_S A2 UNION fv_S G UNION fv_S G1 UNION fv_S G2)
Proof
 rw [example_Gamma] >> rw [fv_P_S,fv_S] >> rw [UNION_DEF,EXTENSION] >> METIS_TAC []
QED

Theorem example_Gamma_fv_P_c_empty:
 !A A1 A2 G G1 G2 x.
  IMAGE fv_P_c (example_Gamma A A1 A2 G G1 G2) = {{}}
Proof
 rw [example_Gamma,fv_P_c]
QED

Theorem example_Ps_fv_P_c_NOTIN:
 !A A1 A2 G G1 G2 x. x NOTIN BIGUNION (IMAGE fv_P_c (example_Ps A A1 A2 G G1 G2))
Proof
 rw [BIGUNION_IMAGE_f_NOTIN,example_Ps] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_S_eq_conj_comm_assoc_compat_EMPTY] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_S_eq_forall_S_conj_comm_EMPTY] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_c_eq_forall_c_assoc_EMPTY] >> 
 METIS_TAC [example_Gamma_fv_P_c_NOTIN,NOT_IN_EMPTY]
QED

Theorem example_Ps_INSERT_fv_P_c_NOTIN:
 !A A1 A2 G G1 G2 q q'.
  q <> q' ==>
  q' NOTIN BIGUNION (IMAGE fv_P_c
   (P_implements (c_var q)
   (S_assume (S_conj A1 (S_const Sc_compat))
             (S_conj G1 (S_const Sc_compat))) INSERT
   example_Ps A A1 A2 G G1 G2))
Proof
 rw [BIGUNION_IMAGE_f_NOTIN,example_Ps] >-
 rw [fv_P_c,fv_c] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_S_eq_conj_comm_assoc_compat_EMPTY] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_S_eq_forall_S_conj_comm_EMPTY] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_c_eq_forall_c_assoc_EMPTY] >> 
 METIS_TAC [example_Gamma_fv_P_c_NOTIN,NOT_IN_EMPTY]
QED

Theorem example_Ps_INSERT_INSERT_fv_P_c_NOTIN:
 !A A1 A2 G G1 G2 q q' q0.
  q <> q0 /\ q' <> q0 ==> 
  q0 NOTIN BIGUNION (IMAGE fv_P_c
   ((P_implements (c_var q')
   (S_assume (S_conj A2 (S_const Sc_compat))
             (S_conj G2 (S_const Sc_compat)))) INSERT
   (P_implements (c_var q)
   (S_assume (S_conj A1 (S_const Sc_compat))
             (S_conj G1 (S_const Sc_compat)))) INSERT
   example_Ps A A1 A2 G G1 G2))
Proof
 rw [BIGUNION_IMAGE_f_NOTIN,example_Ps] >>
 rw [fv_P_c,fv_c] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_S_eq_conj_comm_assoc_compat_EMPTY] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_S_eq_forall_S_conj_comm_EMPTY] >-
 METIS_TAC [NOT_IN_EMPTY,fv_P_c_P_c_eq_forall_c_assoc_EMPTY] >> 
 METIS_TAC [example_Gamma_fv_P_c_NOTIN,NOT_IN_EMPTY]
QED

Theorem Ssubst_SVARIANT_fv_S:
 !S S' VS. 
  FINITE VS /\ fv_S S SUBSET VS ==>
  Ssubst_S ((SVARIANT VS =+ S') S_var) S = S
Proof
 Induct >>  rw [Ssubst_S,fv_S] >>
 rw [APPLY_UPDATE_THM] >>
 METIS_TAC [SVARIANT_FINITE]
QED

Theorem example_refine_spec_holds:
 !A A1 A2 G G1 G2.
 spec_holds
  (example_Ps A A1 A2 G G1 G2)
  (example_goal A A1 A2 G G1 G2)
Proof
 rw [example_goal] >>

 MATCH_MP_TAC all_in_c >>
 Q.EXISTS_TAC `"q1"` >>
 rw [clause_name_def,example_Ps_fv_P_c_NOTIN] >-
 rw [fv_P_c,fv_c] >>
 rw [csubst_P] >-
 (fs [fv_P_c,fv_c] >> rw [] >> fs [APPLY_UPDATE_THM,fv_c]) >>
 PAT_X_ASSUM ``~ ?y. P`` (fn thm => ALL_TAC) >>
 rw [csubst_c,APPLY_UPDATE_THM] >>

 MATCH_MP_TAC imp_in >>
 rw [clause_name_def] >>

 MATCH_MP_TAC all_in_c >>
 Q.EXISTS_TAC `"q2"` >>

 rw [clause_name_def,example_Ps_INSERT_fv_P_c_NOTIN] >-
 rw [fv_P_c,fv_c] >>
 rw [csubst_P,csubst_c,APPLY_UPDATE_THM] >>

 MATCH_MP_TAC imp_in >>
 rw [clause_name_def] >>

 MATCH_MP_TAC cont_in >>

 Q.EXISTS_TAC `"q"` >>
 rw [clause_name_def,fv_c] >>

 MATCH_MP_TAC all_in_c >>
 Q.EXISTS_TAC `"q0"` >>

 rw [clause_name_def,example_Ps_INSERT_INSERT_fv_P_c_NOTIN] >-
 rw [fv_P_c,fv_c] >>
 rw [csubst_P,csubst_c,APPLY_UPDATE_THM] >>

 MATCH_MP_TAC imp_in >>
 rw [clause_name_def] >>

 MATCH_MP_TAC cr >>
 Q.EXISTS_TAC `G2` >>

 rw [clause_name_def] >-
  (Q.ABBREV_TAC `Gamma = P_implements (c_var "q0") (S_conj A (S_const Sc_compat)) INSERT
      P_implements (c_var "q2")
        (S_assume (S_conj A2 (S_const Sc_compat))
           (S_conj G2 (S_const Sc_compat))) INSERT
      P_implements (c_var "q1")
        (S_assume (S_conj A1 (S_const Sc_compat))
           (S_conj G1 (S_const Sc_compat))) INSERT example_Ps A A1 A2 G G1 G2` >>
  `spec_holds Gamma (csubst_P
    (("q" =+ (c_comp (c_var "q0") (c_comp (c_var "q1") (c_var "q2")))) c_var)
     (P_implements (c_var "q") (S_conj G2 (S_const Sc_compat))))`
   suffices_by rw [csubst_P,csubst_c] >>
  
  MATCH_MP_TAC eq_el_c >>
  
  Q.EXISTS_TAC `c_comp (c_comp (c_var "q0") (c_var "q1")) (c_var "q2")` >>
  rw [clause_name_def] >-
   (`spec_holds Gamma
      (csubst_P (("q''" =+ (c_var "q2")) c_var)
        (P_c_eq (c_comp (c_comp (c_var "q0") (c_var "q1")) (c_var "q''"))
                (c_comp (c_var "q0") (c_comp (c_var "q1") (c_var "q''")))))`
      suffices_by rw [csubst_P,csubst_c,APPLY_UPDATE_THM] >>

    MATCH_MP_TAC all_el_c >>
    rw [clause_name_def] >>
    
    `spec_holds Gamma
      (csubst_P (("q'" =+ (c_var "q1")) c_var)
        (P_forall_c "q''" 
           (P_c_eq
                (c_comp (c_comp (c_var "q0") (c_var "q'")) (c_var "q''"))
                (c_comp (c_var "q0") (c_comp (c_var "q'") (c_var "q''"))))))`
      suffices_by rw [csubst_P,csubst_c,APPLY_UPDATE_THM,fv_P_c,fv_c] >>

    MATCH_MP_TAC all_el_c >>
    rw [clause_name_def] >>

    `spec_holds Gamma
      (csubst_P (("q" =+ (c_var "q0")) c_var)
       (P_forall_c "q'"
         (P_forall_c "q''"
           (P_c_eq
            (c_comp (c_comp (c_var "q") (c_var "q'")) (c_var "q''"))
            (c_comp (c_var "q") (c_comp (c_var "q'") (c_var "q''")))))))`
      suffices_by rw [csubst_P,csubst_c,APPLY_UPDATE_THM,fv_P_c,fv_c] >>

    MATCH_MP_TAC all_el_c >>
    rw [clause_name_def] >>
    
    match_mp_tac ax_IN >>
    rw [Abbr `Gamma`, example_Ps,example_Gamma,P_c_eq_forall_c_assoc]) >>
  
  rw [csubst_P,csubst_c] >>

  MATCH_MP_TAC cont_el >>
  Q.EXISTS_TAC `S_conj A2 (S_const Sc_compat)` >>
  rw [clause_name_def] >-
   (MATCH_MP_TAC cr >>
    Q.EXISTS_TAC `S_conj G1 A` >>
    rw [clause_name_def] >-
     (`spec_holds Gamma
       (Ssubst_P (("V" =+ S_conj (S_conj G1 A) (S_const Sc_compat)) S_var)
         (P_implements (c_comp (c_var "q0") (c_var "q1")) (S_var "V")))`
       suffices_by rw [Ssubst_P,Ssubst_S] >>
      
      MATCH_MP_TAC eq_el_S >>
      rw [clause_name_def] >>

      Q.EXISTS_TAC `S_conj A (S_conj G1 (S_const Sc_compat))` >>
      rw [Ssubst_P,Ssubst_S,APPLY_UPDATE_THM] >-
       (match_mp_tac ax_IN >>
        rw [Abbr `Gamma`, example_Ps,example_Gamma,P_S_eq_conj_comm_assoc_compat]) >>

      MATCH_MP_TAC conj_in >>
      rw [clause_name_def] >-
       (MATCH_MP_TAC assn_el >>
        rw [clause_name_def] >-
         (match_mp_tac ax_IN >>
          rw [Abbr `Gamma`, example_Ps,example_Gamma]) >>
        MATCH_MP_TAC conj_el1 >>
        Q.EXISTS_TAC `S_const (Sc_compat)` >>
        rw [clause_name_def] >>
        match_mp_tac ax_IN >>
        rw [Abbr `Gamma`, example_Ps,example_Gamma]) >>
      MATCH_MP_TAC cont_el >>
      Q.EXISTS_TAC `S_conj A1 (S_const Sc_compat)` >>
      rw [clause_name_def] >-
       (MATCH_MP_TAC cr >>
        Q.EXISTS_TAC `A` >>
        rw [clause_name_def] >>
        match_mp_tac ax_IN >>
        rw [Abbr `Gamma`, example_Ps,example_Gamma]) >>
      match_mp_tac ax_IN >>
      rw [Abbr `Gamma`, example_Ps,example_Gamma]) >>

    `!S. Ssubst_S S_var⦇SVARIANT (fv_S A2) ↦ S⦈ A2 = A2`
     by (MATCH_MP_TAC Ssubst_SVARIANT_fv_S >> fs [FINITE_fv_S]) >>

    `spec_holds Gamma (Ssubst_P
      ((SVARIANT (fv_S A2) =+ S_conj G1 A) S_var) (P_refines (S_var (SVARIANT (fv_S A2))) A2))`
     suffices_by (rw [Ssubst_P,Ssubst_S,APPLY_UPDATE_THM]) >>

    MATCH_MP_TAC eq_el_S >>
    Q.EXISTS_TAC `S_conj A G1` >>

    rw [clause_name_def] >-
     (match_mp_tac ax_IN >> rw [Abbr `Gamma`,example_Ps,example_Gamma,P_S_eq_forall_S_conj_comm]) >>
    rw [Ssubst_P,Ssubst_S] >>
    match_mp_tac ax_IN >>
    rw [Abbr `Gamma`,example_Ps,example_Gamma]) >>
   match_mp_tac ax_IN >>
   rw [Abbr `Gamma`,example_Ps,example_Gamma]) >>
 match_mp_tac ax_IN >>
 rw [example_Ps,example_Gamma]
QED

Theorem example_refine_sem_spec_holds:
 !omega Mc MS Mq MV. 
 (!s. Mc s SUBSET omega) /\
 (!s. Mq s SUBSET omega) /\
 (!s. MS s SUBSET POW omega) /\
 (!s. MV s SUBSET POW omega) ==>
 !A A1 A2 G G1 G2.
 (!P0. P0 IN example_Ps A A1 A2 G G1 G2 ==> P_sem omega Mc MS Mq MV P0) ==>
 P_sem omega Mc MS Mq MV (example_goal A A1 A2 G G1 G2)
Proof
 rw [] >>
 `spec_system_sound spec_holds omega`
  by rw [spec_holds_system_sound] >>
 `spec_holds (example_Ps A A1 A2 G G1 G2) (example_goal A A1 A2 G G1 G2)`
  by METIS_TAC [example_refine_spec_holds] >>
 fs [spec_system_sound] >>
 METIS_TAC []
QED

(* FIXME: express example_goal in FOL *)

val _ = export_theory ();
