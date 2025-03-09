open HolKernel boolLib Parse bossLib;
open pred_setTheory listTheory sumTheory combinTheory stringTheory;
open arithmeticTheory realTheory RealArith realSimps;
open compSpecTheory;

val _ = new_theory "mitl";

Definition interval_sem:
 (interval_sem (interval_closed a b) =
  { r | &a <= r /\ r <= &b })
 /\
 (interval_sem (interval_left_half_open a b) =
  { r | &a < r /\ r <= &b })
 /\
 (interval_sem (interval_right_half_open_num a b) =
  { r | &a <= r /\ r < &b })
 /\
 (interval_sem (interval_right_half_open_inf a) =
  { r | &a <= r })
/\
 (interval_sem (interval_open_num a b) =
  { r | &a < r /\ r < &b })
 /\
 (interval_sem (interval_open_inf a) =
  { r | &a < r })
End

Definition interval_pos_shift:
 (interval_pos_shift (t:real) (interval_closed a b) =
  { r | r >= 0 /\ t + &a <= r /\ r <= t + &b })
 /\
 (interval_pos_shift t (interval_left_half_open a b) =
  { r | r >= 0 /\ t + &a < r /\ r <= t + &b })
 /\
 (interval_pos_shift t (interval_right_half_open_num a b) =
  { r | r >= 0 /\ t + &a <= r /\ r < t + &b })
 /\
 (interval_pos_shift t (interval_right_half_open_inf a) =
  { r | r >= 0 /\ t + &a <= r })
 /\
 (interval_pos_shift t (interval_open_num a b) =
  { r | r >= 0 /\ t + &a < r /\ r < t + &b })
 /\
 (interval_pos_shift t (interval_open_inf a) =
  { r | r >= 0 /\ t + &a < r })
End

Definition interval_neg_shift:
 (interval_neg_shift (t:real) (interval_closed a b) =
  { r | r >= 0 /\ t - &b <= r /\ r <= t - &a })
 /\
 (interval_neg_shift t (interval_left_half_open a b) =
  { r | r >= 0 /\ t - &b <= r /\ r < t - &a })
 /\
 (interval_neg_shift t (interval_right_half_open_num a b) =
  { r | r >= 0 /\ t - &b < r /\ r <= t - &a })
 /\
 (interval_neg_shift t (interval_right_half_open_inf a) =
  { r | r >= 0 /\ r <= t - &a })
 /\
 (interval_neg_shift t (interval_open_num a b) =
  { r | r >= 0 /\ t - &b < r /\ r < t - &a })
 /\
 (interval_neg_shift t (interval_open_inf a) =
  { r | r >= 0 /\ r < t - &a })
End

Type timed_word = ``:(num -> ('state # real))``

Definition timed_word_suffix:
 timed_word_suffix (tau: 'state timed_word) (i:num) : 'state timed_word =
   \x. tau (i + x)
End

Definition mitl_general_holds:
  (mitl_general_holds 
    (state_holds : 'state -> 'a -> bool)
    (tau : 'state timed_word)
    (i : num) (mitl_const p : 'a f) : bool = 
   state_holds (FST (tau i)) p)
  /\
  (mitl_general_holds state_holds tau i (mitl_not f) =
   ~ mitl_general_holds state_holds tau i f)
  /\
  (mitl_general_holds state_holds tau i (mitl_and f f') =
    (mitl_general_holds state_holds tau i f /\ mitl_general_holds state_holds tau i f'))
  /\
  (mitl_general_holds state_holds tau i (mitl_implies f f') =
    (mitl_general_holds state_holds tau i f ==> mitl_general_holds state_holds tau i f'))
  /\
  (mitl_general_holds state_holds tau i (mitl_until f iv f') =
   (?j. (SND (tau j)) IN interval_pos_shift (SND (tau i)) iv /\
     mitl_general_holds state_holds tau j f' /\
     !k. (SND (tau k)) IN { r | (SND (tau i)) <= r /\ r <= (SND (tau j)) } ==>
      mitl_general_holds state_holds tau k f))
  /\
  (mitl_general_holds state_holds tau i (mitl_box iv f) = 
   (!j. (SND (tau j)) IN interval_pos_shift (SND (tau i)) iv ==>
     mitl_general_holds state_holds tau j f))
  /\
  (mitl_general_holds state_holds tau i (mitl_diamond iv f) =
   (?j. (SND (tau j)) IN interval_pos_shift (SND (tau i)) iv /\
     mitl_general_holds state_holds tau j f))
  /\
  (mitl_general_holds state_holds tau i (mitl_since f iv f') =
   (?j. (SND (tau j)) IN interval_neg_shift (SND (tau i)) iv /\
     mitl_general_holds state_holds tau j f' /\
     !k. (SND (tau k)) IN { r | (SND (tau j)) <= r /\ r <= (SND (tau i)) } ==> 
      mitl_general_holds state_holds tau k f))
  /\
  (mitl_general_holds state_holds tau i (mitl_box_dash iv f) = 
   (!j. (SND (tau j)) IN interval_neg_shift (SND (tau i)) iv ==>
     mitl_general_holds state_holds tau j f))
  /\
  (mitl_general_holds state_holds tau i (mitl_diamond_dash iv f) = 
   (?j. (SND (tau j)) IN interval_neg_shift (SND (tau i)) iv /\
     mitl_general_holds state_holds tau j f))
End

Definition mitl_general_sem:
 (mitl_general_sem
  (state_holds : 'state -> 'a -> bool)
  (omega : ('state timed_word) set)
  (i : num) (mitl_const p : 'a f) : ('state timed_word) set =
  { tau | tau IN omega /\ state_holds (FST (tau i)) p })
 /\
 (mitl_general_sem state_holds omega i (mitl_not dm) =
  omega DIFF (mitl_general_sem state_holds omega i dm))
 /\
 (mitl_general_sem state_holds omega i (mitl_and dm1 dm2) =
  (mitl_general_sem state_holds omega i dm1) INTER
   (mitl_general_sem state_holds omega i dm2))
 /\
 (mitl_general_sem state_holds omega i (mitl_implies dm1 dm2) =
  mitl_general_sem state_holds omega i dm2 UNION
   (omega DIFF mitl_general_sem state_holds omega i dm1))                   
 /\
 (mitl_general_sem state_holds omega i (mitl_until dm1 iv dm2) =
  { tau | tau IN omega /\
    ?j. (SND (tau j)) IN interval_pos_shift (SND (tau i)) iv /\
     tau IN mitl_general_sem state_holds omega j dm2 /\ 
      !k. (SND (tau k)) IN { r | (SND (tau i)) <= r /\ r <= (SND (tau j)) } ==>
       tau IN mitl_general_sem state_holds omega k dm1 })
 /\
 (mitl_general_sem state_holds omega i (mitl_since dm1 iv dm2) =
  { tau | tau IN omega /\
   ?j. (SND (tau j)) IN interval_neg_shift (SND (tau i)) iv /\
    tau IN mitl_general_sem state_holds omega j dm2 /\ 
     !k. (SND (tau k)) IN { r | (SND (tau j)) <= r /\ r <= (SND (tau i)) } ==>
      tau IN mitl_general_sem state_holds omega k dm1 })
 /\
 (mitl_general_sem state_holds omega i (mitl_box iv dm) = 
  { tau | tau IN omega /\
    !j. (SND (tau j)) IN interval_pos_shift (SND (tau i)) iv ==>
     tau IN mitl_general_sem state_holds omega j dm })
 /\
 (mitl_general_sem state_holds omega i (mitl_diamond iv dm) =
  { tau | tau IN omega /\
     ?j. (SND (tau j)) IN interval_pos_shift (SND (tau i)) iv /\
      tau IN mitl_general_sem state_holds omega j dm })
 /\
 (mitl_general_sem state_holds omega i (mitl_box_dash iv dm) = 
  { tau | tau IN omega /\
    !j. (SND (tau j)) IN interval_neg_shift (SND (tau i)) iv ==>
     tau IN mitl_general_sem state_holds omega j dm })
 /\
 (mitl_general_sem state_holds omega i (mitl_diamond_dash iv dm) = 
  { tau | tau IN omega /\
     ?j. (SND (tau j)) IN interval_neg_shift (SND (tau i)) iv /\
      tau IN mitl_general_sem state_holds omega j dm })
End

Theorem interval_sem_geq_zero:
 !iv r. r IN interval_sem iv ==> r >= 0
Proof
 Cases_on `iv` >| [
  rw [interval_sem] >>
  `0 <= &n` by rw [REAL_POS] >>
  `0 <= r` suffices_by REAL_ARITH_TAC >>
  METIS_TAC [REAL_LE_TRANS],

  rw [interval_sem] >>
  `0 <= &n` by rw [REAL_POS] >>
  `0 < r` suffices_by REAL_ARITH_TAC >>
  METIS_TAC [REAL_LET_TRANS],

  rw [interval_sem] >>
  `0 <= &n` by rw [REAL_POS] >>
  `0 <= r` suffices_by REAL_ARITH_TAC >>
  METIS_TAC [REAL_LE_TRANS],

  rw [interval_sem] >>
  `0 <= &n` by rw [REAL_POS] >>
  `0 <= r` suffices_by REAL_ARITH_TAC >>
  METIS_TAC [REAL_LE_TRANS],

  rw [interval_sem] >>
  `0 <= &n` by rw [REAL_POS] >>
  `0 < r` suffices_by REAL_ARITH_TAC >>
  METIS_TAC [REAL_LET_TRANS],

  rw [interval_sem] >>
  `0 <= &n` by rw [REAL_POS] >>
  `0 < r` suffices_by REAL_ARITH_TAC >>
  METIS_TAC [REAL_LET_TRANS]
 ]
QED

Theorem timed_word_suffix_eq:
 !tau. timed_word_suffix tau 0 = tau
Proof
 rw [timed_word_suffix,EQ_EXT]
QED

Theorem timed_word_suffix_suffix:
 !tau i j.
  timed_word_suffix (timed_word_suffix tau i) j =
  timed_word_suffix tau (i + j)
Proof
 rw [timed_word_suffix]
QED

Theorem timed_word_suffix_all_omega:
 (!i. timed_word_suffix tau i IN omega) ==>
 tau IN omega
Proof
 rw [] >>
 METIS_TAC [timed_word_suffix_eq]
QED

Theorem mitl_general_holds_sem:
 !dm state_holds omega tau k. 
  (!i. timed_word_suffix tau i IN omega) ==>
  (mitl_general_holds state_holds tau k dm <=>
   tau IN mitl_general_sem state_holds omega k dm)
Proof
 Induct >> rw [mitl_general_holds,mitl_general_sem] >| [
  METIS_TAC [timed_word_suffix_eq],

  METIS_TAC [timed_word_suffix_eq],

  METIS_TAC [],
  
  EQ_TAC >> rw [] >| [
   Cases_on `mitl_general_holds state_holds tau k dm'` >-
   METIS_TAC [] >>
   `tau IN omega` by rw [timed_word_suffix_all_omega] >>
   Cases_on `mitl_general_holds state_holds tau k dm` >>
   METIS_TAC [],

   METIS_TAC [],

   METIS_TAC []
  ],

  EQ_TAC >> rw [] >| [
   METIS_TAC [timed_word_suffix_eq],
   
   Q.EXISTS_TAC `j` >>
   METIS_TAC [],

   Q.EXISTS_TAC `j` >>
   METIS_TAC []   
  ],

  EQ_TAC >> rw [] >| [
   METIS_TAC [timed_word_suffix_eq],
   
   Q.EXISTS_TAC `j` >>
   METIS_TAC [],

   Q.EXISTS_TAC `j` >>
   METIS_TAC []   
  ],

  EQ_TAC >> rw [] >| [
   METIS_TAC [timed_word_suffix_eq],

   METIS_TAC [],

   METIS_TAC []
  ],

  EQ_TAC >> rw [] >| [
   METIS_TAC [timed_word_suffix_eq],
   
   Q.EXISTS_TAC `j` >>
   METIS_TAC [],

   Q.EXISTS_TAC `j` >>
   METIS_TAC []   
  ],

  EQ_TAC >> rw [] >| [
   METIS_TAC [timed_word_suffix_eq],

   METIS_TAC [],

   METIS_TAC []
  ],

  EQ_TAC >> rw [] >| [
   METIS_TAC [timed_word_suffix_eq],
   
   Q.EXISTS_TAC `j` >>
   METIS_TAC [],

   Q.EXISTS_TAC `j` >>
   METIS_TAC []   
  ]
 ]
QED

Theorem mitl_general_sem_omega:
 !dm state_holds omega tau k.
 mitl_general_sem state_holds omega k dm SUBSET omega
Proof
 Induct >> rw [mitl_general_sem] >| [
  rw [SUBSET_DEF],

  `mitl_general_sem state_holds omega k dm' SUBSET omega`
   by METIS_TAC [] >>
  `(mitl_general_sem state_holds omega k dm INTER
    mitl_general_sem state_holds omega k dm') SUBSET
   mitl_general_sem state_holds omega k dm'`
   by METIS_TAC [INTER_SUBSET] >>
  METIS_TAC [SUBSET_TRANS],

  rw [SUBSET_DEF],

  rw [SUBSET_DEF],

  rw [SUBSET_DEF],

  rw [SUBSET_DEF],

  rw [SUBSET_DEF],

  rw [SUBSET_DEF]
 ]
QED

(* G_[0,inf) (G_[0,3] b -> F_[3,5] d) *)
Definition mitl_example:
 mitl_example (b:string) =
  (mitl_box (interval_right_half_open_inf 0) (mitl_const b))
End

val _ = export_theory ();
