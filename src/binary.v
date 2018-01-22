Require Import Bool List Arith Nat Coq.Arith.Div2.
Import ListNotations.


Fixpoint bit_n (l : list bool) : nat :=
  match l with
    | [] => 0
    | a :: tl => 2 * bit_n tl + Nat.b2n a
  end.



Fixpoint n_bit (n : nat) (k : nat) : option (list bool) :=
    match n with
      | 0 => match k with
             | 0 => Some []
             | S _ => None
             end
      | S n' => match n_bit n' (Nat.div2 k) with
                  | None => None
                  | Some l => Some (Nat.odd k :: l)
                end
    end.


(* ------------------------------- Auxiliary Lemma------------  Used later *)
Lemma size_n_bit : forall (n k: nat) (l : list bool),
    n_bit n k = Some l -> length l = n.
Proof.
  induction n; intros k l.
  (* case 0 *)
  -assert (I : n_bit 0 k = Some l -> length l = 0).
   { destruct k; simpl; intro H.
     -inversion H. reflexivity.
     -discriminate.
   } assumption.
  -(* case S n) *)
    assert(II : n_bit (S n) k = Some l -> length l = S n).
    { simpl. destruct (n_bit n (Nat.div2 k)) eqn:H1; intros; try (discriminate).
      inversion H. simpl. apply Nat.succ_inj_wd. eapply IHn. exact H1.
    } assumption.
Qed.






(* ---------------------- Theorem that state that fonctions are inverse --------------------*)
Theorem n_bit_n : forall (l : list bool) (n k : nat),
    n_bit n k = Some l -> bit_n l = k.
Proof.
  induction l; intros n k.
  -assert (I : n_bit n k = Some [] -> bit_n [] = k).
   {
     destruct n; simpl.
     -destruct k. reflexivity. discriminate.
     -destruct (n_bit n (Nat.div2 k)); discriminate.
   } assumption.
  -assert (II : n_bit n k = Some (a :: l) -> bit_n (a :: l) = k).
   {
     intros H. rewrite (Nat.div2_odd k). simpl.     
      destruct n; simpl in H.
      - destruct k; discriminate.
      - destruct (n_bit n (Nat.div2 k)) eqn:Hl; try discriminate.
        inversion H; subst.
        erewrite IHl; eauto.
   } assumption.
Qed.
  

(* second proof *)
Theorem bit_n_bit : forall (l : list bool) (n : nat),
                      n = length l -> (n_bit n (bit_n l)) = Some l.
Proof.
  assert (I : forall (l : list bool) (n : nat), n = length l -> n_bit n (bit_n l) = Some l).
  {
    induction l.
    assert (I_1 : forall n : nat, n = length ([] : list bool) -> n_bit n (bit_n []) = Some []).
    {
      simpl.
      intros n H.
      rewrite H.
      reflexivity.
    }
    exact I_1.
    assert (I_2 : forall n : nat, n = length (a :: l) -> n_bit n (bit_n (a :: l)) = Some (a :: l)).
    {
      intros n.
      simpl.
      destruct a.
      assert (I_2_1 : n = length (true :: l) -> n_bit n (bit_n (true :: l)) = Some (true :: l)).
      {
        simpl.
        Search (_ + 0).
        rewrite <- plus_n_O.
        intros H.
        rewrite H.
        simpl.
        assert (I_2_1_1 : forall l' : (list bool), bit_n l' + bit_n l' = 2 * bit_n l').
        {
          induction l'.
          -reflexivity.
          -simpl.
           rewrite <- plus_n_O.
           rewrite <- plus_n_O.
           reflexivity.
        }        
        rewrite I_2_1_1.
        Search (_ + 1 = S _).
        Search (Nat.div2 _).
        rewrite Nat.add_1_r.
        Check even_div2.
        rewrite <- even_div2.
        -Search (Nat.div2 (2 * _)).
         rewrite div2_double.
         rewrite IHl.
         +assert (I_2_1_2 : forall (n' : nat), Nat.odd (S (2 * n')) = true).
          {
            intros n'.
            induction n'.
            -reflexivity.
            -simpl.
             rewrite <- plus_n_Sm.
             simpl in IHn'.
             rewrite <- IHn'.
             Search (Nat.odd (S (S _))).
             rewrite Nat.odd_succ_succ. reflexivity.
          }
          rewrite I_2_1_2.
          reflexivity.
         +reflexivity.
        -assert (I_2_1_3 : Even.even (2 * bit_n l)).
         {
           (* this is supposed to be trivial -_-_-_-_-_-_-_-_-_-_-_-_- *)
           Check Nat.even_add_mul_2.
           Search (0 + _).
           rewrite <- Nat.add_0_l.
           SearchAbout (even (_ + _)).
           specialize (Nat.even_add_mul_2 0 (bit_n l)).
           intros.
           Check Even.even_equiv.
           apply Even.even_equiv.
           (* even spec *)
           Check Nat.even_spec.
           simpl in H0.
           Search (_ + _ = 2 * _).
           Check I_2_1_1.
           rewrite <- I_2_1_1.
           assert (0 + (bit_n l + bit_n l) = bit_n l + (bit_n l + 0)).
           { simpl. Search (_ + 0). rewrite <- plus_n_O. reflexivity. }
           rewrite H1. 
           rewrite Nat.even_spec in H0.
           exact H0.
         }
         exact I_2_1_3.
      }
      exact I_2_1.
      assert (I_2_2 : n = S (length l) -> n_bit n (bit_n l + (bit_n l + 0) + Nat.b2n false) = Some (false :: l)).
      {
        simpl.
        Search (_ + 0).
        rewrite <- plus_n_O.
        rewrite <- plus_n_O.
        intros H.
        rewrite H.
        simpl.
        Search (2 * _ = _).
        assert (I_2_2_0 : forall (n' : nat), 2 * n' = n' + n').
        {
          intros n'. simpl. rewrite <- plus_n_O. reflexivity.
        }
        rewrite <- I_2_2_0.
        rewrite div2_double.
        rewrite IHl.
        -assert (I_2_2_1 : forall (n' : nat), Nat.odd (2 * n') = false).
         {
           induction n'.
           -simpl. Search (Nat.odd 0).
            rewrite Nat.odd_0. reflexivity.
           -simpl.
            Search (_ + 0).
            rewrite <- plus_n_O.
            Search (_ + _ = _ + _).
            rewrite <- plus_Snm_nSm.
            Search (S _ + _).
            rewrite plus_Sn_m.
            Search (Nat.odd (S (S _))).
            rewrite Nat.odd_succ_succ.
            simpl in IHn'.
            rewrite <- plus_n_O in IHn'.
            rewrite IHn'.
            reflexivity.            
         }
         rewrite I_2_2_1.
         reflexivity.
        -reflexivity.
      }
      exact I_2_2.
    }
    exact I_2.
  }
  exact I.
Qed.