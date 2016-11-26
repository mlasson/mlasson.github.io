(* TP n°5 : Équivalence petit pas-grand pas pour 
            un langage de termes arithmétiques *)

Section Star.
(* On suppose qu'on dispose d'un type A et d'une relation sur A. *)
Variable A : Type. 
Variable R : A -> A -> Prop. 

(* On définit le prédicat inductif suivant : *)
Inductive star : A -> A -> Prop :=
  | star_refl : forall a, star a a
  | star_R : forall a b c, R a b -> star b c -> star a c.

(* Prouvez que R est incluse dans sa cloture. *)
Lemma R_star : forall x y, R x y -> star x y.
Proof.

Qed.

(* Prouvez que la cloture est transitive. *)
Lemma star_trans : forall x y z, star x y -> star y z -> star x z.
Proof.

Qed.
Check star_trans.
End Star.

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

(* Implémentez une sémantique à petit pas pour l'évalution 
    de ces expressions à l'aide d'un prédicat inductif. *)
Inductive ss : expr -> expr -> Prop := 
 ...

Definition sse := star expr ss. 
Infix "-->'" := se (at level 60).
Infix "-->>" := sse (at level 60).

Lemma ten : example -->> (N 19).

Qed.


(* Est-ce que votre solution est déterministe ? 
    Est-ce que vous pourriez trouver une version ss' déterministe ? 
    (Exercice à la maison: prouver que ss et ss' définissent la même 
     clôture reflexive-transitive et que ss' est bien déterministe (pas 
     facile)). *)

(* Donnez maintenant une sémantique à grand pas. *)
Inductive bs : expr -> nat -> Prop := 
...

(* Vous pouvez utiliser la tactique [rewrite t₁ with t₂]. *)
Lemma dix : bs example 19.
  
Qed.

(* On peut aussi utiliser les points fixe de coq pour 
   évaluer ce language (c'est pas toujours possible, mais là 
   le language est vraiment très simple : *)
Fixpoint eval e := ...

(* Prouver que la sémantique à grand pas est correcte vis-à-vis d'éval. *)
Lemma bs_correct : forall e, bs e (eval e).

Qed.

(* En déduire que la sémantique à grands pas est totale. *)
Lemma bs_tot : forall e, exists n, bs e n.

Qed.

(* On va commencer par prouver que "grand pas" implique "petit pas". *)
 
(* Tout d'abord six petits lemmes pour vous aider. *)
Lemma star_ss_plus : forall  a b c, a -->> c ->  (a [+] b) -->> (c [+] b). 

Qed. 

Lemma star_ss_plus' : forall a b c,  b -->> c -> (a [+] b) -->> (a [+] c). 

Qed. 

Lemma star_ss_mult : forall  a b c, a -->> c ->  (a [*] b) -->> (c [*] b). 

Qed. 

Lemma star_ss_mult' : forall a b c,  b -->> c -> (a [*] b) -->> (a [*] c). 

Qed. 

Lemma star_ss_minus : forall  a b c, a -->> c ->  (a [-] b) -->> (c [-] b). 

Qed. 

Lemma star_ss_minus' : forall a b c,  b -->> c -> (a [-] b) -->> (a [-] c). 

Qed. 

Lemma bs_sse : forall a n, bs a n -> a -->> (N n).

Qed.

(* En déduire que la sémantique à petits pas est totale. *)
Lemma sse_tot : forall e, exists n, e -->> (N n).

Qed.

(* Et maintenant on va prouver la réciproque: 
       "Petit pas" implique "grand pas". *)

(* Mais avant tout d'autres lemmes. *)
(* Rappel : [inversion H]  élimine des cas impossibles
    si le type de H est inductif.
    Il peut être pratique de simplifier les hypothèses
    obtenues en utilisant [subst]. *)
Lemma ss_bs_bs: forall a b, ss a b -> forall n, bs b n -> bs a n.

Qed. 

Lemma  sse_bs_aux : forall a b n, a -->> b -> b = N n -> bs a n.

Qed. 

Lemma sse_bs : forall a n, a -->> (N n) -> bs a n.

Qed. 

Lemma bs_conflu : forall a n, bs a n -> forall m, bs a m -> n = m.

Qed.

(* En déduire la confluence de petits pas (vous avez le droit
   de rajouter des lemmes ici). *)

Lemma ss_conflu : forall a b b', 
   sse a b -> sse a b' -> exists c, sse b c /\ sse b' c.
   
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
Fixpoint compile e l := ...

(* On peut tester la fonction sur l'exemple: *)
Eval compute in (compile example nil).

(* Ce prédicat décrit l'exécution d'une petit machine à pile. 
    Essayez de comprendre comment elle calcule. *)
Inductive exec : list cexpr * list nat -> list cexpr * list nat -> Prop :=
  | exec_nat   : forall n l e, exec ((cN n) ::l,e) (l,n::e)
  | exec_plus  : forall l a b e, exec (cPlus :: l, a :: b :: e) (l,(b+a) :: e)
  | exec_mult  : forall l a b e, exec (cMult :: l, a :: b :: e) (l,(b*a) :: e) 
  | exec_minus : forall l a b e, exec (cMinus :: l, a :: b :: e) (l,(b-a) :: e).

Infix "=>" := exec (at level 40). 

(* On prend sa cloture-reflexive transitive. *)
Notation "a =>> b" := (star _ exec a b) (at level 40).

(* Montrez qu'elle est correcte vis-à-vis de big step: *)
Lemma compilation_correct_aux :
  forall a n, bs a n -> forall l l', (compile a l,l') =>> (l,n :: l').

Qed.
 
(* Voilà ! *)
Lemma compilation_correct : 
  forall a n, bs a n -> (compile a nil,nil) =>> (nil,n :: nil).

Qed.
