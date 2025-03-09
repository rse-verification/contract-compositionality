open HolKernel boolLib Parse bossLib;
open pred_setTheory;

(* ========================================== *)
(* Compositional specification utility theory *)
(* ========================================== *)

val _ = new_theory "compSpecUtility";

(* ----------- *)
(* Definitions *)
(* ----------- *)

Definition double_intersection:
 double_intersection s1 s2 = { a INTER b | a IN s1 /\ b IN s2 }
End

Definition downward_closed:
 downward_closed s = (!e. e IN s ==> (!e'. e' SUBSET e ==> e' IN s))
End

Definition ifst:
 ifst : 'a -> ('a + 'b + 'c + 'd) = INL
End

Definition isnd:
 isnd : 'b -> ('a + 'b + 'c + 'd) = INR o INL
End

Definition itrd:
 itrd : 'c -> ('a + 'b + 'c + 'd) = INR o INR o INL
End

Definition ifth:
 ifth : 'd -> ('a + 'b + 'c + 'd) = INR o INR o INR
End

Definition ofst:
 ofst : ('a + 'b + 'c + 'd) -> 'a = OUTL
End

Definition osnd:
 osnd : ('a + 'b + 'c + 'd) -> 'b = OUTL o OUTR
End

Definition otrd:
 otrd : ('a + 'b + 'c + 'd) -> 'c = OUTL o OUTR o OUTR
End

Definition ofth:
 ofth : ('a + 'b + 'c + 'd) -> 'd = OUTR o OUTR o OUTR
End

(* ------- *)
(* Results *)
(* ------- *)

Theorem double_intersection_IN:
 !x s1 s2. x IN double_intersection s1 s2 <=>
  (?a b. x = a INTER b /\ a IN s1 /\ b IN s2)
Proof
 rw [double_intersection]
QED

Theorem double_intersection_ASSOC:
 !s1 s2 s3.
  double_intersection s1 (double_intersection s2 s3) =
  double_intersection (double_intersection s1 s2) s3
Proof
 once_rewrite_tac [double_intersection] >>
 strip_tac >> strip_tac >> strip_tac >> once_rewrite_tac [EXTENSION] >>
 strip_tac >> EQ_TAC >> strip_tac >-
  (fs [] >> rw [] >>
   `?c d. b = c INTER d /\ c IN s2 /\ d IN s3` by METIS_TAC [double_intersection_IN] >>
   rw [] >>
   `a INTER (c INTER d) = (a INTER c) INTER d` by METIS_TAC [INTER_ASSOC,INTER_COMM] >>
   rw [] >>
   Q.EXISTS_TAC `a INTER c` >> Q.EXISTS_TAC `d` >>
   METIS_TAC [double_intersection_IN]) >>
 fs [] >> rw [] >>
 `?c d. a = c INTER d /\ c IN s1 /\ d IN s2` by METIS_TAC [double_intersection_IN] >>
 rw [] >>
 `c INTER d INTER b = c INTER (d INTER b)` by METIS_TAC [INTER_ASSOC] >>
 rw [] >>
 Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `d INTER b` >>
 METIS_TAC [double_intersection_IN]
QED

Theorem double_intersection_COMM:
 !s1 s2. double_intersection s1 s2 = double_intersection s2 s1
Proof
 once_rewrite_tac [double_intersection] >>
 strip_tac >> strip_tac >> once_rewrite_tac [EXTENSION] >>
 strip_tac >> EQ_TAC >> strip_tac >-
  (fs [] >> rw [] >> Q.EXISTS_TAC `b` >> Q.EXISTS_TAC `a` >>
   rw [INTER_COMM]) >>
 fs [] >> rw [] >> Q.EXISTS_TAC `b` >> Q.EXISTS_TAC `a` >>
 rw [INTER_COMM]
QED

Theorem not_all_IN_INTER:
 ~ (!s1 (a : num set) b. a IN s1 /\ b IN s1 ==> a INTER b IN s1)
Proof
 rw [] >>
 Q.EXISTS_TAC `{{0};{1}}` >>
 Q.EXISTS_TAC `{0}` >>
 Q.EXISTS_TAC `{1}` >>
 rw [INTER_DEF]
QED

Theorem not_double_intersection_IDEM:
 ~ (!(s1 : (num set) set). double_intersection s1 s1 = s1)
Proof
 rw [double_intersection] >>
 MP_TAC not_all_IN_INTER >>
 rw [] >>
 Q.EXISTS_TAC `s1` >> strip_tac >>
 `a INTER b NOTIN {a INTER b | a IN s1 /\ b IN s1}`
  by METIS_TAC [] >>
 fs [] >> METIS_TAC []
QED

val _ = export_theory ();
