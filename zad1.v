Require Import Classical.

(*1.Zadatak*)

(*a*)

Goal forall X Y : Prop, (X /\ ~Y) \/ (~X /\ ~Y) \/ (~X /\ Y) <-> ~Y \/ ~X.
Proof.
 intros X Y. split; intros H.
 -destruct H as [H1 | [H2|H3]].
  +destruct H1 as [_ ny]. left. exact ny.
  +destruct H2 as [nx _]. right. exact nx.
  +destruct H3 as [nx _]. right. exact nx.
 -destruct (classic Y) as [y | ny].
   +right. right. split.
     *intros x. destruct H as [ny | nx].
       **apply ny. exact y.
       **apply nx. exact x.
     *exact y.
   +destruct (classic X) as [x | nx].
    *left. split.
      **exact x.
      **exact ny.
    *right. left. split.
      **exact nx.
      **exact ny.
Qed.

(*b*) 

Goal forall X Y Z : Prop, (~(~X /\ Y /\ Z) /\ ~(X /\ Y /\ ~Z) /\ (X /\ ~Y /\ Z)) <-> (X /\ ~Y /\ Z).
 intros X Y Z. split; intros H.
 destruct H as [H1 [H2 [x [ny z]]]].
 -split.
  +exact x.
  +split.
    *exact ny.
    *exact z.
 -destruct H as [x[ny z]]. split.
   +intros [nx[y _]]. contradiction.
   +split.
    *intros [_ [y nz]]. contradiction.
    *split.
      **exact x.
      **split.
         ***exact ny.
        ***exact z.
Qed.
  
 
 












