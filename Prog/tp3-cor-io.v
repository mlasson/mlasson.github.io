(* TP n°3 *)
Definition relation A := A -> A -> Prop.

(* Par exemple la relation [div] est une [relation nat] *)
Inductive div : relation nat := 
 | div_zero: forall n, div n 0
 | div_plus : forall n m, div n m -> div n (n+m).

(* Mais on peut aussi définir des relations de relations
   comme par example l'inclusion entre les relations. *)
Definition incl A : relation (relation A) := fun R1 R2 => 
    forall x y, R1 x y -> R2 x y.

(* Definissez la relation maximale, la relation minimale (i.e. vide)
    ainsi que la relation "identite". *)
Definition rel_full A : relation A := fun x y => True.
Definition rel_empty A : relation A := fun x y => False.
Definition rel_id A : relation A := fun x y => x = y.

(* Étant donnée une relation, définissez la relation réciproque. *)
Definition converse A (R : relation A) := fun x y => R y x.


(* On peut aussi définition des propriétés sur les relations 
   comme par exemple la transitivité : *)
Definition transitive A (R : relation A) : Prop  := 
  forall x y z, R x y -> R y z -> R x z.

(* Définissez la réflexivité et la symmétrie: *)
Definition reflexive A (R : relation A) : Prop := 
  forall x, R x x.

Definition symmetric A (R : relation A) : Prop := 
  forall x y, R x y -> R y x.


Variable B : Type.
Variable P : B -> B -> Prop.
Check (converse B P).
Check (incl _ P (converse _ P)).
Eval compute in (incl _ P (converse _ P)).


(* Pour vous chauffer, prouvez le lemme suivant.
    Indice: Utilisez la tactique [unfold D] pour déplier la définition D. *)
Lemma incl_conv : forall A R,
  incl A R (converse A R) -> symmetric A R.
Proof.
  intros A R Hincl.  
  intros x y HRxy.
  apply Hincl.
  apply HRxy.
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
Proof.
unfold incl. 
intros x y HR.
apply star_R with y.
  apply HR.
apply star_refl.
Qed.

(* Prouvez que la cloture est transitive. *)
Lemma star_trans : transitive _ star.
Proof.
  unfold transitive.
  intros x y z Hxy Hyz. 
  induction Hxy.
    apply Hyz.
    apply star_R with b.
      assumption.
    apply IHHxy. 
    apply Hyz.
Qed.

Goal transitive _ star.
Proof.
  unfold transitive.
  intros x y z Hxy Hyz.
  induction Hxy.
    apply Hyz.
  apply star_R with b.
    assumption.
  apply IHHxy.
  assumption.
Qed.

(* En passant, vous pouvez démontrer ça aussi. *)
Lemma star_symm : symmetric _ R -> symmetric _ star.
  intro Hsym.
  intros x y Hstar.
  induction Hstar.
    apply star_refl.
    apply star_trans with b.
      assumption.
      apply star_R with a.
         apply Hsym. assumption.
         apply star_refl.
Qed.

Check star_trans.  (* Hummm.... *)
End Star.
Check star_trans. (* Vous comprenez les sections maintenant ? *)


(* Durant le reste du TP, on va chercher à étudier la sémantique 
   à petits pas et à grands pas pour le language minimaliste suivant:  *)

Inductive expr : Set :=
  | N : nat -> expr
  | Plus : expr -> expr -> expr
  | Mult : expr -> expr -> expr
  | Minus : expr -> expr -> expr.

Infix "[+]" := Plus (at level 50, left associativity).
Infix "[*]" := Mult (at level 40, left associativity).
Infix "[-]" := Minus(at level 50, left associativity).

Definition example := (N 1) [+] (N 5) [*] (N 4) [-] (N 2).

Reserved Notation "x '-->' y" (at level 60).

(* Implémentez une sémantique à petit pas pour l'évalution 
    de ces expressions à l'aide d'un prédicat inductif. *)
Inductive ss : expr -> expr -> Prop := 
  | ss_plus : forall n m, ((N n) [+] (N m)) --> (N (n + m))
  | ss_mult : forall n m, ((N n) [*] (N m)) --> (N (n * m))
  | ss_minus : forall n m, ((N n) [-] (N m)) --> (N (n - m))
  | ss_left_plus : forall a a' b, a --> a' -> (a [+] b) --> (a' [+] b)
  | ss_left_mult : forall a a' b, a --> a' -> (a [*] b) --> (a' [*] b)
  | ss_left_minus : forall a a' b, a --> a' -> (a [-] b) -->  (a' [-] b)
  | ss_right_plus : forall a b b', b --> b' -> (a [+] b) --> (a [+] b')
  | ss_right_mult : forall a b b', b --> b' -> (a [*] b) --> (a [*] b')
  | ss_right_minus : forall a b b', b --> b' -> (a [-] b) --> (a [-] b')
where "a --> b" := (ss a b).


Definition sse := star expr ss. 

Infix "-->>" := sse (at level 60).

(* Indice :  [replace t₁ with t₂] remplace toute 
    occurrence de t₁ par t₂ et génère le but (t₂=t₁) *)
Lemma ten : example -->> (N 19).
  unfold example.
  apply star_R with (N 1[+]N 20[-]N 2).
    apply ss_left_minus.
    apply ss_right_plus.
    apply ss_mult.
  apply star_R with (N 21 [-] N 2).
    apply ss_left_minus.
    apply ss_plus.
  apply star_R with (N 19).
  apply ss_minus.
  apply star_refl.
Qed.


(* Est-ce que votre solution est déterministe ? 
    Est-ce que vous pourriez trouver une version ss' déterministe ? 
    (Exercice à la maison: prouver que ss et ss' définissent la même 
     clôture reflexive-transitive et que ss' est bien déterministe (pas 
     facile)). *)

(* Donnez maintenant une sémantique à grand pas. *)
Inductive bs : expr -> nat -> Prop := 
  | bs_nat : forall n, bs (N n) n
  | bs_plus : forall e1 e2 n1 n2, bs e1 n1 -> bs e2 n2 -> bs (e1 [+] e2) (n1 + n2)
  | bs_mult : forall e1 e2 n1 n2, bs e1 n1 -> bs e2 n2 -> bs (e1 [*] e2) (n1 * n2)
  | bs_minus : forall e1 e2 n1 n2, bs e1 n1 -> bs e2 n2 -> bs (e1 [-] e2) (n1 - n2)
.

(* Vous pouvez utiliser la tactique [rewrite t₁ with t₂]. *)
Lemma dix : bs example 19.
  unfold example.
  replace 19 with (1+5*4-2).
  repeat constructor.
  reflexivity.
Qed.

(* On peut aussi utiliser les points fixe de coq pour 
   évaluer ce language (c'est pas toujours possible, mais là 
   le language est vraiment très simple : *)
Fixpoint eval e := match e with 
  | N n => n 
  | e1 [+] e2 => (eval e1) + (eval e2)
  | e1 [*] e2 => (eval e1) * (eval e2)
  | e1 [-] e2 => (eval e1) - (eval e2) end.

(* Prouver que la sémantique à grand pas est correcte vis-à-vis d'éval. *)
Lemma bs_correct : forall e, bs e (eval e).
  intros e. 
  induction e; simpl.
  constructor.
  apply bs_plus; assumption.
  apply bs_mult; assumption.
  apply bs_minus; assumption.
Qed.

(* En déduire que la sémantique à grands pas est totale. *)
Lemma bs_tot : forall e, exists n, bs e n.
  intros e; exists (eval e).
  apply bs_correct.
Qed.

(* On va commencer par prouver que "grand pas" implique "petit pas". *)
 
(* Tout d'abord deux petits lemmes pour vous aider. *)
Lemma star_ss_plus : forall  a b c, a -->> c ->  (a [+] b) -->> (c [+] b). 
   intros a b c H.
   induction H.
   apply star_refl.
   apply star_R with (b0 [+] b).
   apply ss_left_plus.
   assumption.
   assumption.
Qed. 

Lemma star_ss_plus' : forall a b c,  b -->> c -> (a [+] b) -->> (a [+] c). 
   intros a b c H.
   induction H.
   apply star_refl.
   apply star_R with (a [+] b).
   apply ss_right_plus.
   assumption.
   assumption.
Qed. 


Lemma star_ss_mult : forall  a b c, a -->> c ->  (a [*] b) -->> (c [*] b). 
   intros a b c H.
   induction H.
   apply star_refl.
   apply star_R with (b0 [*] b).
   apply ss_left_mult.
   assumption.
   assumption.
Qed. 

Lemma star_ss_mult' : forall a b c,  b -->> c -> (a [*] b) -->> (a [*] c). 
   intros a b c H.
   induction H.
   apply star_refl.
   apply star_R with (a [*] b).
   apply ss_right_mult.
   assumption.
   assumption.
Qed. 


Lemma star_ss_minus : forall  a b c, a -->> c ->  (a [-] b) -->> (c [-] b). 
   intros a b c H.
   induction H.
   apply star_refl.
   apply star_R with (b0 [-] b).
   apply ss_left_minus.
   assumption.
   assumption.
Qed. 

Lemma star_ss_minus' : forall a b c,  b -->> c -> (a [-] b) -->> (a [-] c). 
   intros a b c H.
   induction H.
   apply star_refl.
   apply star_R with (a [-] b).
   apply ss_right_minus.
   assumption.
   assumption.
Qed. 


Lemma bs_sse : forall a n, bs a n -> sse a (N n).
 intros n a H.
 induction H.
 apply star_refl.
 apply star_trans with (N n1 [+] e2).
 apply star_ss_plus.
 assumption.
 apply star_trans with (N n1 [+] N n2).
 apply star_ss_plus'.
 assumption.
 apply star_R with (N (n1 + n2)).
 apply ss_plus. 
 apply star_refl.
 apply star_trans with (N n1 [*] e2).
 apply star_ss_mult.
 assumption.
 apply star_trans with (N n1 [*] N n2).
 apply star_ss_mult'.
 assumption.
 apply star_R with (N (n1 * n2)).
 apply ss_mult. 
 apply star_refl.
 apply star_trans with (N n1 [-] e2).
 apply star_ss_minus.
 assumption.
 apply star_trans with (N n1 [-] N n2).
 apply star_ss_minus'.
 assumption.
 apply star_R with (N (n1 - n2)).
 apply ss_minus. 
 apply star_refl.
Qed.


(* En déduire que la sémantique à petits pas est totale. *)
Lemma sse_tot : forall e, exists n, sse e (N n).
  intros e. 
  exists (eval e).
  apply bs_sse.
  apply bs_correct.
Qed.

(* Et maintenant on va prouver la réciproque: 
       "Petit pas" implique "grand pas". *)

(* Mais avant tout d'autres lemmes. *)
(* Rappel : [inversion H]  élimine des cas impossibles
    si le type de H est inductif.
    Il peut être pratique de simplifier les hypothèses
    obtenues en utilisant [subst]. *)
Lemma ss_bs_bs: forall a b, ss a b -> forall n, bs b n -> bs a n.
  intros a b H1.
  induction H1; intros k H2;inversion H2; subst; 
  try repeat constructor; auto.    
Qed. 

Lemma  sse_bs_aux : forall a b n, sse a b -> b = N n -> bs a n.
  intros a b n H.
  induction H; intros; subst.
  constructor.
  apply ss_bs_bs with b.
  assumption.
  apply IHstar.
  reflexivity.
Qed. 

Lemma sse_bs : forall a n, sse a (N n) -> bs a n.
  intros a n H.
  apply sse_bs_aux with (N n). 
  assumption.
  reflexivity.
Qed. 

Lemma bs_conflu : forall a n, bs a n -> forall m, bs a m -> n = m.
  intros a n H1.
  induction H1.
(* constante *)
  intros m H2.
  inversion H2.
  reflexivity.
(* addition *)
  intros m H2.
  inversion H2.
  subst.
  rewrite IHbs1 with n0.
  rewrite IHbs2 with n3.
  reflexivity.
  assumption.
  assumption.
(* multiplication *)
  intros m H2.
  inversion H2.
  subst.
  rewrite IHbs1 with n0.
  rewrite IHbs2 with n3.
  reflexivity.
  assumption.
  assumption.
(* soustraction *)
  intros m H2.
  inversion H2.
  subst.
  rewrite IHbs1 with n0.
  rewrite IHbs2 with n3.
  reflexivity.
  assumption.
  assumption.
Qed.

(* En déduire la confluence de petits pas. *)
(* Indice : [cut P] permet d'utiliser P comme étape intermédiaire *)

Lemma ss_bs_bs2: forall a b, ss a b -> forall n, bs a n -> bs b n.
  intros a b H1.
  induction H1.
 (* addition de constantes *)
  intros k H2.
  inversion H2.
  subst.
  inversion H1.
  inversion H4.
  apply bs_nat.
 (* multiplication de constantes *)
  intros k H2.
  inversion H2.
  subst.
  inversion H1.
  inversion H4.
  apply bs_nat.
 (* soustraction de constantes *)
  intros k H2.
  inversion H2.
  subst.
  inversion H1.
  inversion H4.
  apply bs_nat.
 (* addition regle gauche *)
  intros k H2.
  inversion H2.
  subst.
  apply bs_plus.
  apply IHss.
  assumption.
  assumption.
(* multiplication regle gauche *)
  intros k H2.
  inversion H2.
  subst.
  apply bs_mult.
  apply IHss.
  assumption.
  assumption.
(* soustraction regle gauche *)
  intros k H2.
  inversion H2.
  subst.
  apply bs_minus.
  apply IHss.
  assumption.
  assumption.
(* addition regle droite *)
  intros k H2.
  inversion H2.
  subst.
  apply bs_plus.
  assumption.
  apply IHss.  
  assumption.
(* multiplication regle droite *)
  intros k H2.
  inversion H2.
  subst.
  apply bs_mult.
  assumption.
  apply IHss.  
  assumption.
(* soustraction regle droite *)
  intros k H2.
  inversion H2.
  subst.
  apply bs_minus.
  assumption.
  apply IHss.  
  assumption.
Qed. 

Lemma sse_bs_bs2: forall a b, sse a b -> forall n, bs a n -> bs b n.
  intros a b H1.
  induction H1.
  trivial.
  intros.
  apply IHstar.
  apply ss_bs_bs2 with a.
  assumption.
  assumption.
Qed.


Lemma ss_conflu : forall a b b', 
   sse a b -> sse a b' -> exists c, sse b c /\ sse b' c.
   intros a b b' H1 H2. 
   exists (N (eval a)); split.
   apply bs_sse.
   apply sse_bs_bs2 with a .
   assumption.
   apply bs_correct.
   apply bs_sse.
   apply sse_bs_bs2 with a.
   assumption.
   apply bs_correct.
Qed.





(* Dans cette dernière partie, on va compiler notre language de 
    départ en notation polonaise inversée et on va prouver 
    que la compilation préserve la sémantique. *)

(* On charge le module [List] de la bibliothèque standard. *)
Require Import List. 

Check (1::2::nil). (** Ça marche comme en caml (sauf que [] est noté nil). *)
Print list. (* Vous pouvez regarder la définition. *)
 
(* On compile vers une liste de cexpr *)
Inductive cexpr : Set :=
  | cN : nat -> cexpr
  | cPlus : cexpr
  | cMult : cexpr
  | cMinus : cexpr.

(* (1 + 2) * (5 - 2) est compilé en la liste [1;2;+;5;2;-;*]. *)

(* Implémentez la fonction de compilation [compile e l] qui 
   compile l'expression [e] et concatène la liste obtenue à [l]. 
   Conseil: il faut voir [l] comme étant "la suite des calculs". *)
Fixpoint compile e l := match e with 
  | N n => (cN n)::l
  | e₁ [+] e₂ => compile e₁ (compile e₂ (cPlus::l))
  | e₁ [*] e₂ => compile e₁ (compile e₂ (cMult::l))
  | e₁ [-] e₂ => compile e₁ (compile e₂ (cMinus::l))
 end.

(* Ce prédicat décrit l'exécution d'une petit machine à pile. 
    Essayez de comprendre comment elle calcule. *)
Inductive exec : list cexpr * list nat -> list cexpr * list nat -> Prop :=
  | exec_nat   : forall n l e, exec ((cN n) ::l,e) (l,n::e)
  | exec_plus  : forall l a b e, exec (cPlus :: l, a :: b :: e) (l,(b+a) :: e)
  | exec_mult  : forall l a b e, exec (cMult :: l, a :: b :: e) (l,(b*a) :: e) 
  | exec_minus : forall l a b e, exec (cMinus :: l, a :: b :: e) (l,(b-a) :: e).

Infix "=>>" := exec (at level 40). 

(* On prend sa cloture-reflexive transitive. *)
Notation "a =>>* b" := (star _ exec a b) (at level 40).

(* Montrez qu'elle est correcte vis-à-vis de big step: *)
Lemma compilation_correct_aux :
  forall a n, bs a n -> forall l l', (compile a l,l') =>>* (l,n :: l').
  intros a n H.
  induction H. 
  (* constante *)
  simpl; intros l l'.
  apply star_R with (l, n :: l').
  apply exec_nat. 
  apply star_refl.
  (* addition *)
  intros l l'.
  simpl.
  apply star_trans with ((compile e2 (cPlus :: l)) , n1 :: l').
  apply IHbs1.
  apply star_trans with ((cPlus :: l),  n2 :: n1 :: l').
  apply IHbs2.
  apply star_R with (l, n1 + n2 :: l').
  apply exec_plus.
  apply star_refl.
  (* multiplication *)
  intros l l'.
  simpl.
  apply star_trans with ((compile e2 (cMult :: l)) , n1 :: l').
  apply IHbs1.
  apply star_trans with ((cMult :: l),  n2 :: n1 :: l').
  apply IHbs2.
  apply star_R with (l, n1 * n2 :: l').
  apply exec_mult.
  apply star_refl.
  (* soustraction *)
  intros l l'.
  simpl.
  apply star_trans with ((compile e2 (cMinus :: l)) , n1 :: l').
  apply IHbs1.
  apply star_trans with ((cMinus :: l),  n2 :: n1 :: l').
  apply IHbs2.
  apply star_R with (l, n1 - n2 :: l').
  apply exec_minus.
  apply star_refl.
Qed.

(* Voilà ! *)
Lemma compilation_correct : 
  forall a n, bs a n -> (compile a nil,nil) =>>* (nil,n :: nil).
  intros. 
  apply compilation_correct_aux.
  assumption.
Qed.

