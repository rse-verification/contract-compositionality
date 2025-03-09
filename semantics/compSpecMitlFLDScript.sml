open HolKernel boolLib Parse bossLib pred_setTheory listTheory;
open combinTheory arithmeticTheory realTheory RealArith realSimps;
open ottTheory compSpecUtilityTheory compSpecTheory compSpecMetaTheory;
open mitlTheory compSpecMitlTheory;

val _ = new_theory "compSpecMitlFLD";

Datatype:
 var_FLD = Var_Avout | Var_Avin | Var_Al | Var_Dl
End

Datatype:
 val_FLD = Val_num num | Val_real real
End

Type state_FLD = ``:var_FLD -> val_FLD``

Datatype:
 exp_FLD = exp_EQ var_FLD val_FLD | exp_LT var_FLD val_FLD | exp_GT var_FLD val_FLD
  | exp_AND exp_FLD exp_FLD | exp_OR exp_FLD exp_FLD | exp_NOT exp_FLD
End

Definition state_holds_FLD:
 (state_holds_FLD (s:state_FLD) (exp_EQ var val) : bool =
  (s var = val))
 /\
 (state_holds_FLD (s:state_FLD) (exp_LT Var_Avout (Val_real r)) : bool =
  (case s Var_Avout of Val_real r' => r < r' | _ => F))
 /\
 (state_holds_FLD (s:state_FLD) (exp_LT Var_Avin (Val_real r)) : bool =
  (case s Var_Avin of Val_real r' => r < r' | _ => F))
 /\
 (state_holds_FLD (s:state_FLD) (exp_LT Var_Al (Val_num n)) : bool =
  (case s Var_Al of Val_num n' => n < n' | _ => F))
 /\
 (state_holds_FLD (s:state_FLD) (exp_LT Var_Dl (Val_num n)) : bool =
  (case s Var_Dl of Val_num n' => n < n' | _ => F))
 /\
 (state_holds_FLD (s:state_FLD) (exp_GT Var_Avout (Val_real r)) : bool =
  (case s Var_Avout of Val_real r' => r > r' | _ => F))
 /\
 (state_holds_FLD (s:state_FLD) (exp_GT Var_Avin (Val_real r)) : bool =
  (case s Var_Avin of Val_real r' => r > r' | _ => F))
 /\
 (state_holds_FLD (s:state_FLD) (exp_GT Var_Al (Val_num n)) : bool =
  (case s Var_Al of Val_num n' => n > n' | _ => F))
 /\
 (state_holds_FLD (s:state_FLD) (exp_GT Var_Dl (Val_num n)) : bool =
  (case s Var_Dl of Val_num n' => n > n' | _ => F))
 /\
 (state_holds_FLD (s:state_FLD) (exp_AND e1 e2) : bool =
  (state_holds_FLD s e1 /\ state_holds_FLD s e2))
 /\
 (state_holds_FLD (s:state_FLD) (exp_OR e1 e2) : bool =
  (state_holds_FLD s e1 \/ state_holds_FLD s e2))
 /\
 (state_holds_FLD (s:state_FLD) (exp_NOT e) : bool =
  (~ state_holds_FLD s e))
End

Type timed_word_FLD = ``:(num -> (state_FLD # real))``

Definition omega_FLD:
 omega_FLD : timed_word_FLD set =
  { tau |     
    (!i j. i < j ==> (SND (tau i)) < (SND (tau j)))
    /\
    (!i. ?r. (FST (tau i)) Var_Avout = Val_real r)
    /\
    (!i. ?r. (FST (tau i)) Var_Avin = Val_real r)
    /\
    (!i. ?n. (FST (tau i)) Var_Al = Val_num n)
    /\
    (!i. ?n. (FST (tau i)) Var_Dl = Val_num n)
  }
End

Theorem omega_FLD_suffix:
 !tau. tau IN omega_FLD ==>
 !i. timed_word_suffix tau i IN omega_FLD
Proof
 rw [omega_FLD,timed_word_suffix]
QED

Definition spec_temporal_holds_FLD_def:
 spec_temporal_holds_FLD : (exp_FLD Pt -> bool) -> exp_FLD Pt -> bool = 
  spec_temporal_holds
End

val _ = export_theory ();
