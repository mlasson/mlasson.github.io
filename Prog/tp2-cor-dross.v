(********* Types de donnees inductifs ********)      

(* En coq, on peut définir des nouveaux types de données
   (habitant dans Set) via des définitions inductives. 
  On a vu dans TP1 le type des entiers naturels.
*)

Print nat.

(* De facon informelle, quand on definit un type inductif 
  on donne toutes les manières de construire un élément de ce type.
  Un entier naturel est soit zero (construit par le constructeur "O"),
  soit le successeur d'un autre entier naturel 
  (construit par le constructeur "S").


                      n : nat 
   ----------      --------------
    0 : nat          S n : nat             

*)

(* Un autre exemple c'est le type des booleens. *)

Print bool.

(*
                        
    -----------          ------------
    true : bool          false : bool             
*)


(* Exercice 1. Définir le type "listN" de liste des entiers naturels
  avec deux constructeurs : "videN" qui permet de construire la liste
  vide et "consN" qui permet de construire une nouvele liste à partir 
  d'un entier et une liste.


                            l : listN      n : nat 
    -------------         --------------------------
    videN : listN             consN n l : listN             

*)

(* Chaque fois qu'on définit un type inductif, Coq génère un principe
   d'induction pour ce type. *)

Inductive listN : Set :=
videN : listN
|consN : nat ->  listN -> listN.


Check listN_ind.
Check nat_ind.
Check bool_ind.

(* Ce principe va être automatiquement invoqué quand on utilise la 
  tactique [induction].
  Morale : on peut utiliser [induction] pour faire de preuves sur 
  tous les types inductifs.
*)


(* Exercice 2 : 
a. Définir la fonction "longN" qui prend en argument une "listN" 
  et retourne un "nat" représentant la longeur de la liste.
b. Définir la fonction "concatN" qui prend en argument deux listes
  et retourne la concatenation de ces deux listes.
c. Montrer les propriétés suivantes : *)

Fixpoint longN (liste : listN) := match liste with
|videN => 0
|consN p l_r => S (longN l_r)
end.

Check longN.

Fixpoint concatN (l1 : listN)( l2 : listN) := match l1 with
|videN => l2
|consN p l_r => consN p (concatN l_r l2)
end.

Lemma videN_concat : forall l, concatN videN l = l.
intros.
trivial.

Qed.

Lemma concat_videN : forall l, concatN l videN = l.
intros.
induction l.
trivial.
simpl.
rewrite IHl.
trivial.

Qed.

Lemma long_concat: forall (l1 l2 : listN), longN (concatN l1 l2) = (longN l1) + (longN l2).
intros.
induction l1.
simpl. reflexivity.
simpl.
rewrite IHl1.
trivial.

Qed.



(************* Predicats inductifs ****************)

(* En plus des types de données inductifs, Coq permet de
  définir des propriétés inductives. 
  Par exemple, la propriété que un nat est pair peut être
  défini de la facon suivante : *)

Inductive even : nat -> Prop := 
    even_zero : even 0 
  | even_succ : forall n, even n -> even (S (S n)).


(*                   even n 
   --------       -------------- 
    even 0        even (S (S n))                *)


(* Il génère également un principe d'induction : *)
Check even_ind.

(* Exercice 3. Définissez vous-même le prédicat "odd" 
  pour designer les impaires. Essayez de trouver une 
  définition avec un seul constructeur. *) 

Inductive odd : nat -> Prop :=
     odd_succ : forall n, even n -> odd (S n).

Lemma odd_even : forall n, odd n -> even (S n).
intros.
destruct H.
apply even_succ.
apply H.

Qed.

Lemma even_twice : forall n, even (n * 2).
intros.
induction n.
simpl.
apply even_zero.
simpl.
apply even_succ.
assumption.

Qed.

Lemma odd_or_even : forall n, even n \/ odd n.
intros.
induction n.
left.
apply even_zero.
destruct IHn.
right.
apply odd_succ.
assumption.
left.
apply odd_even.
assumption.

Qed.

(* [inversion H] est une tactique compliquée qui élimine les 
   cas impossibles dans les types inductifs. Servez-vous en 
   pour prouver : *)
Lemma not_even: ~ odd 0.
intros H.
inversion H.

Qed. (* La tactique [inversion] est compliquée à comprendre. 
Si elle vous fait peur, rassurez-vous: les TD-(wo)men feront de 
leur mieux pour minimiser son utilisation. *) 

(* Exercice 4. Définissez la relation <= sur les nats. 
  On va le faire de 2 manieres différents, à l'aide de deux
  prédicats inductifs [le] et [le'] qui correspondent aux 
  règles ci-dessous. 

                le n m
   ------    --------------
   le 0 n    le (S n) (S m) 

               le' n m
   -------   --------------
   le' n n    le' n (S m)              *)

 
Inductive le : nat -> nat -> Prop := 
    le_0 : forall n, le 0 n
    |le_S : forall n m, (le n m) -> le (S n) (S m).
Inductive le' : nat -> nat -> Prop :=
    le'_id : forall n, le' n n
    |le'_S : forall n m, (le' n m) -> le' n (S m).

Check le_ind. (* Méditez ce principe d'induction. *)

Lemma le'0: forall n, le' 0 n.
intros.
induction n.
apply le'_id.
apply le'_S.
assumption.
  
Qed.

Lemma le'SS: forall n m, le' n m -> le' (S n) (S m).
intros.
induction H.
apply le'_id.
apply le'_S.
assumption.
  
Qed.
  
Theorem le_le' : forall n m, le n m -> le' n m.
intros.
induction H.
apply le'0.
apply le'SS.
assumption.
  
Qed. 

Lemma le_refl: forall n, le n n.
induction n.
apply le_0.
apply le_S.
assumption.
  
Qed.

Lemma leS: forall n m, le n m -> le n (S m).
intros.
induction H.
apply le_0.
apply le_S.
assumption.
  
Qed.

Theorem le'_le : forall n m, le' n m -> le n m.
intros.
induction H.
apply le_refl.
apply leS.
assumption.
 
  
Qed.

Lemma plus_zero : forall n, n + 0 = n.
intros.
induction n.
simpl. trivial.
simpl. rewrite IHn. trivial.
Qed.

(* On montre que la définition de <= de la semaine dernière 
   est équivalente à le et le'. *)
Lemma le_exists : forall n m, le n m <-> exists k, n+k = m.
intros.
split.
intros.
induction H.
exists n.
simpl. trivial.
simpl.
destruct IHle.
exists x.
rewrite H0.
reflexivity.

intros.
induction H.
induction H.
induction n. 
apply le_0.
simpl.
apply le_S.
assumption.
Qed.

Lemma le'_exists : forall n m, le' n m <-> exists k, n+k = m.
intros.
split.
intros.
apply ->le_exists.
apply le'_le.
assumption.

intros.
apply le_le'.
apply <-le_exists.
assumption.
Qed.


(**************** Relations *************)

(* Le type [A -> A -> Prop] des formules paramétrées par deux
    éléments de A sert à représenter les relations sur A. *)
Definition relation A := A -> A -> Prop.

(* Par exemple la relation [le] est une [relation nat] *)

(* Mais on peut aussi définir des relations de relations
   comme par example l'inclusion entre les relations. *)
Definition incl A : relation (relation A) := fun R1 R2 => 
    forall x y, R1 x y -> R2 x y.




(* Definissez la relation maximale,
    la relation minimale (i.e. la relation vide)
    ainsi que la relation identité. *)
Definition rel_full A : relation A := fun x y => True.
Definition rel_empty A : relation A := fun x y => False.
Definition rel_id A : relation A := fun x y => x = y.


(* Étant donnée une relation, définissez la relation réciproque. *)
Definition converse A (R : relation A) :=
    fun x y => R y x.

(* On peut aussi définir des propriétés sur les relations 
   comme par exemple la transitivité : *)
Definition transitive A (R : relation A) : Prop  := 
  forall x y z, R x y -> R y z -> R x z.

(* Définissez la réflexivité et la symmétrie: *)
Definition reflexive A (R : relation A) : Prop := 
  forall x, R x x.
Definition symmetric A (R : relation A) : Prop := 
  forall x y, R x y <-> R y x.

(* Pour vous chauffer, prouvez le lemme suivant.
    Indice: Utilisez la tactique [unfold D] pour déplier la définition D.
    La tactique [compute in H] permet de normaliser le type de H *)
Lemma incl_conv : forall A R,
  incl A R (converse A R) -> symmetric A R.

intros.
unfold symmetric.
intros.
split.
intros.
compute in H.
apply H.
assumption.

intros.
compute in H.
apply H.
assumption.
Qed.

(* Dans cette section nous allons fabriquer la cloture reflexive
    transitive d'une relation. *)
Section Star. 
(* On suppose qu'on dispose d'un type A et d'une relation sur A. *)
Variable A : Type. 
Variable R : A -> A -> Prop. 

(* On définit le prédicat inductif suivant : *)
Inductive star : A -> A -> Prop :=
  | star_refl : forall a, star a a
  | star_R : forall a b c, R a b -> star b c -> star a c.

(* Prouvez que R est incluse dans sa cloture. *)
Lemma R_star : incl A R star .
unfold incl.
intros.
assert (star y y -> star x y).
apply star_R.
assumption.

apply H0.
apply star_refl.

Qed.

(* Prouvez que la cloture est transitive. *)
(* Indice : Dans [apply h with t], le mot-clef 'with' permet de 
    donner à apply les arguments qu'il n'arrive pas à inférer.  *)
Lemma star_trans : transitive _ star.
unfold transitive.
intros.
induction H.
assumption.
apply star_R with b.
assumption.
apply IHstar.
assumption.

Qed.

(* En passant, vous pouvez démontrer ça aussi. *)
Lemma star_symm : symmetric _ R -> symmetric _ star.
intros.
unfold symmetric.
intros.
split.
intros.
induction H0.
apply star_refl.
destruct H with a b.
apply star_trans with b.
assumption.
apply R_star.
apply H2.
assumption.


intros.
induction H0.
apply star_refl.
destruct H with a b.
apply star_trans with b.
assumption.
apply R_star.
apply H2.
assumption.

Qed.

Check star_trans.  (* Hummm.... *)
End Star.
Check star_trans. (* Vous comprenez les sections maintenant ? *)



(* Et enfin pour les plus courageux d'entre vous : *)
(* On définit la rélation "n divise m" par le prédicat [div] *)

Inductive div : nat -> nat -> Prop :=
  | div1 : forall n, div n 0
  | div2 : forall n m, div n m -> div n (n + m).

Require Import Arith.

Lemma div_refl : forall n, div n n.
intros.
assert (div n (n+0)).
apply div2.
apply div1.
rewrite plus_0_r in H.
assumption.
 
Qed. 

Lemma div_plus : forall a b, div a b -> forall c, div a c -> div a (b + c).
intros.
induction H.
simpl. assumption.
rewrite <-plus_assoc.
apply div2.
apply IHdiv.
assumption.
 
Qed.

Lemma div_trans : forall a b c, div a b -> div b c -> div a c.
intros.
induction H0.
apply div1.
assert (div a m).
apply IHdiv.
apply H.
rewrite plus_comm.
apply div_plus.
assumption.
assumption.

Qed.


Lemma evenS_odd : forall n, even (S n) -> odd n.
intros.
inversion H.
apply odd_succ.
assumption.


Qed.

Lemma oddS_even : forall n, odd (S n) -> even n.
intros.
inversion H.
assumption.

Qed.

(* Conseil: utiliser inversion. *)
Lemma odd_and_even : forall n, ~ (even n /\ odd n).
intros.
intros H.
destruct H.
induction n.
inversion H0.
destruct IHn.
apply oddS_even.
assumption.
apply evenS_odd.
assumption.

Qed.

Lemma div_mult : forall a k, div k (a * k).
intros.
induction a.
simpl.
apply div1.
rewrite mult_succ_l.
rewrite plus_comm.
apply div2.
assumption.

Qed.

Lemma twice_even : forall n, even n -> exists k, n = 2 * k.
intros.
induction H.
exists 0.
rewrite mult_0_r.
trivial.
destruct IHeven.
exists (S x).
rewrite H0.
rewrite mult_succ_r.
rewrite plus_comm.
trivial.

Qed.

Lemma div_div : (* pareil que le précédent. *)
   forall a b, div a b -> exists k, b = a * k.
intros.
induction H.
exists 0.
trivial.
destruct IHdiv.
rewrite H0.
exists (S x).
rewrite mult_succ_r.
rewrite plus_comm.
trivial.

Qed.