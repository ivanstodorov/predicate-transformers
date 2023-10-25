namespace PredicateTransformers

namespace Free
  inductive Free (C : Type) (R : C → Type) (a : Type u) : Type u where
    | pure : a → Free C R a
    | step : (c : C) → (R c → Free C R a) → Free C R a

  def map : (a → b) → Free C R a → Free C R b
    | f, Free.pure x   => Free.pure (f x)
    | f, Free.step c k => Free.step c (λ r => map f (k r))

  def bind : Free C R a → (a → Free C R b) → Free C R b
    | Free.pure x,   f => f x
    | Free.step c x, f => Free.step c (λ r => bind (x r) f)

  instance : Monad (Free C R) where
    pure := Free.pure
    bind := bind

  def hAndThen : Free C R a → (Unit → Free C R b) → Free C R b :=
    λ c1 c2 => c1 >>= λ _ => c2 ()

  instance : HAndThen (Free C R a) (Free C R b) (Free C R b) where
    hAndThen := hAndThen

  def wp {a : Type u} {b : a → Type v} : ((x : a) → b x) → ((x : a) → b x → Prop) → (a → Prop) :=
    λ f P x => P x (f x)

  def subset {a : Type} (P Q : a → Prop) : Prop :=
    ∀ x, P x → Q x

  notation "_⊆_" => subset
  infix:50 "⊆" => subset

  def sqsubset {a : Type} {b : a → Type} (pt1 pt2 : ((x : a) → b x → Prop) → (a → Prop)) : Prop :=
    ∀ P, pt1 P ⊆ pt2 P

  notation "_⊑_" => sqsubset
  infix:50 "⊑" => sqsubset

  theorem sqsubsetTrans {a : Type} {b : a → Type} {P Q R : ((x : a) → b x → Prop) → (a → Prop)} : P ⊑ Q → Q ⊑ R → P ⊑ R := by
    intro h₁ h₂ _ _ h
    apply h₂
    apply h₁
    exact h

  notation "⊑-trans" => sqsubsetTrans

  theorem sqsubsetRefl {a : Type} {b : a → Type} {P : ((x : a) → b x → Prop) → (a → Prop)} : P ⊑ P := by
    intro _ _ h
    exact h

  notation "⊑-refl" => sqsubsetRefl

  theorem sqsubsetEq {a b : Type} : (f g : a → b) → wp f ⊑ wp g → (x : a) → f x = g x := by
    intro _ _ R _
    apply R
    rw [wp]

  notation "⊑-eq" => sqsubsetEq

  theorem eqSqsubset {a b : Type} : (f g : a → b) → ((x : a) → f x = g x) → wp f ⊑ wp g := by
    intro _ _ eq _ _ h
    rw [wp] at *
    rw [←eq]
    exact h

  notation "eq-⊑" => eqSqsubset
end Free

namespace Maybe
  open Free

  inductive C : Type where
    | abort : C

  def R : C → Type :=
    λ _ => Empty

  def Partial : Type → Type :=
    Free C R

  instance : Monad Partial where
    pure := Free.pure
    bind := Free.bind

  instance : HAndThen (Partial a) (Partial b) (Partial b) where
    hAndThen := Free.hAndThen

  def abort : Partial a :=
    Free.step C.abort Empty.rec

  inductive Expr : Type where
    | val : Nat → Expr
    | div : Expr → Expr → Expr

  inductive Semantics : Expr → Nat → Prop where
    | base : Semantics (Expr.val x) x
    | step : Semantics l v1 → Semantics r (Nat.succ v2) → Semantics (Expr.div l r) (v1 / (Nat.succ v2))

  notation "_⇓_" => Semantics
  infix:50 "⇓" => Semantics

  def div : Nat → Nat → Partial Nat
    | _, Nat.zero   => abort
    | n, Nat.succ k => pure (n / (Nat.succ k))

  notation "_÷_" => div
  infix:50 "÷" => div

  def eval : Expr → Partial Nat
    | Expr.val x     => pure x
    | Expr.div e1 e2 =>
      eval e1 >>= λ v1 =>
      eval e2 >>= λ v2 =>
      v1 ÷ v2

  notation "⟦_⟧" => eval
  notation "⟦" e "⟧" => eval e

  def mustPT {a : Type} {b : a → Type} : ((x : a) → b x → Prop) → (x : a) → Partial (b x) → Prop
    | P, _, Free.pure x         => P _ x
    | _, _, Free.step C.abort _ => False

  def wpPartial {a : Type} {b : a → Type} : ((x : a) → Partial (b x)) → ((x : a) → b x → Prop) → (a → Prop) :=
    λ f P => wp f (mustPT P)

  def safeDiv : Expr → Prop
    | Expr.val _     => True
    | Expr.div e1 e2 => (e2 ⇓ Nat.zero → False) ∧ safeDiv e1 ∧ safeDiv e2

  theorem correct : safeDiv ⊆ wpPartial ⟦_⟧ _⇓_
    | Expr.val _,     _                                => Semantics.base
    | Expr.div e₁ e₂, (And.intro hn (And.intro h₁ h₂)) => by
      have ih₁ := correct e₁ h₁
      have ih₂ := correct e₂ h₂
      simp [wpPartial, mustPT, wp, eval] at *
      match heq₁ : ⟦e₁⟧, heq₂ : ⟦e₂⟧ with
      | Free.pure _,         Free.pure Nat.zero     =>
        simp [heq₂] at ih₂
        simp [ih₂] at hn
      | Free.pure _,         Free.pure (Nat.succ _) =>
        simp [Bind.bind, Free.bind, div]
        exact Semantics.step (by simp [heq₁] at ih₁; exact ih₁) (by simp [heq₂] at ih₂; exact ih₂)
      | Free.pure _,         Free.step C.abort _    => simp [heq₂] at ih₂
      | Free.step C.abort _, _                      => simp [heq₁] at ih₁

  def dom {a : Type} {b : a → Type} : ((x : a) → Partial (b x)) → (a → Prop) :=
    λ f => wpPartial f (λ _ _ => True)

  theorem sound : dom ⟦_⟧ ⊆ wpPartial ⟦_⟧ _⇓_
    | Expr.val _,     _ => Semantics.base
    | Expr.div e₁ e₂, h => by
      have ih₁ := sound e₁
      have ih₂ := sound e₂
      simp [dom, wpPartial, mustPT, wp, eval] at *
      match heq₁ : ⟦e₁⟧, heq₂ : ⟦e₂⟧ with
      | Free.pure _,         Free.pure Nat.zero     => simp [heq₁, heq₂, Bind.bind, Free.bind, div, abort] at h
      | Free.pure _,         Free.pure (Nat.succ _) =>
        simp [Bind.bind, Free.bind, div]
        exact Semantics.step (by simp [heq₁] at ih₁; exact ih₁) (by simp [heq₂] at ih₂; exact ih₂)
      | Free.pure _,         Free.step C.abort _    => simp [heq₁, heq₂, Bind.bind, Free.bind] at h
      | Free.step C.abort _, _                      => simp [heq₁, Bind.bind, Free.bind] at h

  theorem inDom : (e : Expr) → ⟦e⟧ = Free.pure v → dom ⟦_⟧ e
    | Expr.val _, _     => by simp [dom, wpPartial, mustPT, wp, eval, pure]
    | Expr.div e₁ e₂, h => by
      simp [dom, wpPartial, mustPT, wp, eval] at *
      match heq₁ : ⟦e₁⟧, heq₂ : ⟦e₂⟧ with
      | Free.pure _,         Free.pure Nat.zero     => simp [heq₁, heq₂, Bind.bind, Free.bind, div, abort] at h
      | Free.pure _,         Free.pure (Nat.succ _) => simp [Bind.bind, Free.bind, div]
      | Free.pure _,         Free.step C.abort _    => simp [heq₁, heq₂, Bind.bind, Free.bind] at h
      | Free.step C.abort _, _                      => simp [heq₁, Bind.bind, Free.bind] at h

  theorem aux : ⟦e⟧ = Free.pure v → e ⇓ v := by
    intro eq
    have h := sound e (inDom e eq)
    simp [wpPartial, mustPT, wp, eq] at h
    exact h

  theorem wpPartial₁ : wpPartial ⟦_⟧ _⇓_ (Expr.div e₁ e₂) → wpPartial ⟦_⟧ _⇓_ e₁ := by
    simp [wpPartial, mustPT, wp, eval]
    intro h
    match heq₁ : ⟦e₁⟧, heq₂ : ⟦e₂⟧ with
    | Free.pure _,         Free.pure Nat.zero     => simp [heq₁, heq₂, Bind.bind, Free.bind, div, abort] at h
    | Free.pure _,         Free.pure (Nat.succ _) =>
      simp
      exact aux heq₁
    | Free.pure _,         Free.step C.abort _    => simp [heq₁, heq₂, Bind.bind, Free.bind] at h
    | Free.step C.abort _, _                      => simp [heq₁, Bind.bind, Free.bind] at h

  theorem wpPartial₂ : wpPartial ⟦_⟧ _⇓_ (Expr.div e₁ e₂) → wpPartial ⟦_⟧ _⇓_ e₂ := by
    simp [wpPartial, mustPT, wp, eval]
    intro h
    match heq₁ : ⟦e₁⟧, heq₂ : ⟦e₂⟧ with
    | Free.pure _,         Free.pure _         =>
      simp
      exact aux heq₂
    | Free.pure _,         Free.step C.abort _ => simp [heq₁, heq₂, Bind.bind, Free.bind] at h
    | Free.step C.abort _, _                   => simp [heq₁, Bind.bind, Free.bind] at h

  theorem complete : wpPartial ⟦_⟧ _⇓_ ⊆ dom ⟦_⟧
    | Expr.val _,     _ => by simp [dom, wpPartial, mustPT, wp, eval, pure]
    | Expr.div e₁ e₂, h => by
      simp [dom, wpPartial, mustPT, wp, eval] at *
      match heq₁ : ⟦e₁⟧, heq₂ : ⟦e₂⟧ with
      | Free.pure _,         Free.pure Nat.zero     => simp [heq₁, heq₂, Bind.bind, Free.bind, div, abort] at h
      | Free.pure _,         Free.pure (Nat.succ _) => simp [Bind.bind, Free.bind, div]
      | Free.pure _,         Free.step C.abort _    => simp [heq₁, heq₂, Bind.bind, Free.bind] at h
      | Free.step C.abort _, _                      => simp [heq₁, Bind.bind, Free.bind] at h

  structure Spec (a : Type) (b : a → Type) : Type where
    pre  : a → Prop
    post : (x : a) → b x → Prop

  notation "⟨" pre ", " post "⟩" => { pre := pre, post := post : Spec _ _ }

  notation "K" x => λ _ => x

  def SpecK : Type → Type → Type :=
    λ a b => Spec a (K b)

  inductive Add : List Nat → List Nat → Prop where
    | addStep : Add (x₁ :: x₂ :: xs) ((x₁ + x₂) :: xs)

  def addSpec : SpecK (List Nat) (List Nat) :=
    ⟨λ xs => List.length xs > 1, Add⟩

  def wpSpec {a : Type} {b : a → Type} : Spec a b → ((x : a) → b x → Prop) → (a → Prop) :=
    λ spec P x => spec.pre x ∧ spec.post x ⊆ P x

  def pop : List a → Partial (a × List a)
    | x :: xs => pure (x, xs)
    | _       => abort

  def add : List Nat → Partial (List Nat) :=
    λ xs =>
      pop xs >>= λ (x₁, xs) =>
      pop xs >>= λ (x₂, xs) =>
      pure ((x₁ + x₂) :: xs)

  theorem correctnessAdd : wpSpec addSpec ⊑ wpPartial add
    | _, [],           h              => by simp [wpSpec, addSpec] at h
    | _, _ :: [],      h              => by simp [wpSpec, addSpec] at h
    | _, _ :: _ :: _, (And.intro _ h) => h _ Add.addStep

  def product : List Nat → Nat :=
    List.foldr (·*·) 1

  def fastProduct : List Nat → Partial Nat
    | []            => pure 1
    | Nat.zero :: _ => abort
    | k :: xs       => map (·* k) (fastProduct xs)

  def defaultHandler : a → Partial a → a
    | _, Free.pure x         => x
    | d, Free.step C.abort _ => d

  def defaultPT (P : a → b → Prop) (d : b) : a → Partial b → Prop
    | x, Free.pure y         => P x y
    | x, Free.step C.abort _ => P x d

  def wpDefault : b → (a → Partial b) → (a → b → Prop) → (a → Prop) :=
    λ d f P => wp f (defaultPT P d)

  theorem soundness (P : a → b → Prop) (d : b) (f : a → Partial b) : ∀ x, wpDefault d f P x → P x (defaultHandler d (f x)) := by
    intro _ h
    simp [wpDefault, defaultPT, wp] at h
    split at h
    all_goals
      rename_i heq
      simp [heq, defaultHandler, h]

  theorem correctnessProductPure : ∀ xs v, fastProduct xs = Free.pure v → product xs = v := by
    intro xs _ h
    match xs with
    | []               =>
      simp [fastProduct, pure] at h
      cases h
      simp [product]
    | Nat.zero :: _    =>
      simp [fastProduct] at h
      cases h
    | Nat.succ _ :: xs =>
      simp [fastProduct] at h
      have ih := correctnessProductPure xs
      cases heq : fastProduct xs
      case pure v =>
        simp [heq, map] at h
        cases h
        have h := ih v heq
        simp [product] at h
        simp [product, List.foldr, h, Nat.mul_comm]
      case step c _ =>
        cases c
        simp [heq, map] at h

  theorem correctnessProductStep : ∀ xs, (∃ k, fastProduct xs = Free.step C.abort k) → product xs = 0 := by
    intro xs h
    match xs with
    | []               =>
      cases h
      rename_i h
      simp [fastProduct] at h
    | Nat.zero :: _    => simp [product, List.foldr]
    | Nat.succ _ :: xs =>
      simp [fastProduct] at h
      have ih := correctnessProductStep xs
      cases heq : fastProduct xs
      case pure =>
        cases h
        rename_i h
        simp [heq, map] at h
      case step c k =>
        cases c
        simp [heq, product] at ih
        simp [product, List.foldr, ih (Exists.intro k rfl)]

  theorem correctnessProduct : wp product ⊑ wpDefault 0 fastProduct := by
    intro _ _ h
    simp [wp] at h
    simp [wpDefault, defaultPT, wp]
    split
    case h_1 heq =>
      simp [correctnessProductPure _ _ heq] at h
      exact h
    case h_2 heq =>
      simp [correctnessProductStep _ (Exists.intro _ heq)] at h
      exact h
end Maybe

namespace State
  open Free

  inductive C (s : Type) : Type where
    | get : C s
    | put : s → C s

  def R {s : Type} : C s → Type
    | C.get   => s
    | C.put _ => Unit

  def State (s : Type) : Type u → Type u :=
    Free (C s) R

  instance : Monad (State s) where
    pure := Free.pure
    bind := Free.bind

  instance : HAndThen (State s a) (State s b) (State s b) where
    hAndThen := Free.hAndThen

  def get : State s s :=
    Free.step C.get pure

  def put : s → State s Unit :=
    λ s => Free.step (C.put s) (λ _ => pure ())

  def run : State s a → s → a × s
    | Free.pure x,           s  => (x, s)
    | Free.step C.get k,     s  => run (k s) s
    | Free.step (C.put s) k, _  => run (k ()) s

  def statePT : (b × s → Prop) → State s b → (s → Prop)
    | P, Free.pure x           => λ s  => P (x, s)
    | P, Free.step C.get k     => λ s  => statePT P (k s) s
    | P, Free.step (C.put s) k => λ _  => statePT P (k ()) s

  def statePT' : (s → b × s → Prop) → State s b → (s → Prop) :=
    λ P c i => statePT (P i) c i

  def wpState : (a → State s b) → (a × s → b × s → Prop) → (a × s → Prop) :=
    λ f P (x, i) => wp f (λ _ c => statePT' (λ j => P (x, j)) c i) x

  theorem soundness' (P : a × s → b × s → Prop) : (st : s) → (statec : State s b) → (statePT (P (x, i)) statec st) → P (x, i) (run statec st)
    | _, Free.pure _,           h => h
    | i, Free.step C.get k,     h => soundness' P i (k i) h
    | _, Free.step (C.put s) k, h => soundness' P s (k ()) h

  theorem soundness (P : a × s → b × s → Prop) (f : a → State s b) : ∀ i x, wpState f P (x, i) → P (x, i) (run (f x) i) :=
    λ i x h => soundness' P i (f x) h
end State

section Relabel
  open Free Maybe State

  inductive Tree (a : Type) : Type where
    | leaf : a → Tree a
    | node : Tree a → Tree a → Tree a

  def flatten : Tree a → List a
    | Tree.leaf x   => [x]
    | Tree.node l r => flatten l ++ flatten r

  def size : Tree a → Nat
    | Tree.leaf _   => 1
    | Tree.node l r => size l + size r

  def seq : Nat → Nat → List Nat
    | _, Nat.zero   => []
    | i, Nat.succ n => List.cons i (seq (Nat.succ i) n)

  def relabelPost : Tree a × Nat → Tree Nat × Nat → Prop :=
    λ (t, s) (t', s') => (flatten t' = (seq s (size t))) ∧ (s + size t = s')

  def relabelSpec : SpecK (Tree a × Nat) (Tree Nat × Nat) :=
    ⟨K True, relabelPost⟩

  def fresh : State Nat Nat :=
    State.get >>= λ n =>
    State.put (Nat.succ n) >>
    Eq.mp (@congrFun _ _ (Free (State.C Nat) State.R) (State Nat) rfl _) (Free.pure n)

  def relabel : Tree a → State Nat (Tree Nat)
    | Tree.leaf _    => map Tree.leaf fresh
    | Tree.node l r  =>
      relabel l >>= λ l' =>
      relabel r >>= λ r' =>
      pure (Tree.node l' r')

  theorem compositionality : (c : State Nat a) → (f : a → State Nat b) → ∀ i P, statePT P (c >>= f) i = statePT (wpState f (λ _ => P)) c i
    | Free.pure _,           _, _, _ => rfl
    | Free.step C.get k,     f, i, P => compositionality (k i) f i P
    | Free.step (C.put x) k, f, _, P => compositionality (k ()) f x P

  theorem proveBind (mx : State Nat a) (f : a → State Nat b) : statePT (wpState f λ _ => P) mx i → statePT P (mx >>= f) i :=
    Eq.mp (Eq.symm (compositionality mx f i P))

  theorem proveBindSpec (mx : State Nat a) (f : a → State Nat b) (spec) : ∀ P i, (∀ Q, Spec.pre spec i ∧ (Spec.post spec i ⊆ Q) → statePT Q mx i) → Spec.pre spec i ∧ (Spec.post spec i ⊆ wpState f (λ _ => P)) → statePT P (mx >>= f) i :=
    λ P _ hmx hf => proveBind mx f (hmx (wpState f (λ _ => P)) hf)

  def applySpec : SpecK (a × s) (b × s) → a → SpecK s (b × s) :=
    λ spec x =>  ⟨λ s => spec.pre (x, s), λ s => spec.post (x, s)⟩

  theorem appendSeq : ∀ a b c, seq a b ++ seq (a + b) c = seq a (b + c)
    | a, Nat.zero, c => by
      simp_arith
      simp [seq]
    | a, Nat.succ b, c => by
      simp [Nat.add_succ, Nat.succ_add, seq]
      simp [←Nat.succ_add]
      apply appendSeq

  theorem postcondition : (fl = seq s sl) ∧ (s + sl = s') → (fr = seq s' sr) ∧ (s' + sr = s'') → (fl ++ fr = seq s (sl + sr)) ∧ (s + (sl + sr) = s'') :=
    λ (And.intro l₁ l₂) (And.intro r₁ r₂) => And.intro (by simp [l₁, r₁, ←l₂, appendSeq]) (by simp [←r₂, ←l₂, Nat.add_assoc])

  theorem step2' : ∀ P (t : Tree a) s, wpSpec relabelSpec P (t, s) → statePT (P (t, s)) (relabel t) s
    | _, Tree.leaf _,   s, (And.intro _ snd)   => snd (Tree.leaf s, Nat.succ s) (And.intro (by simp [flatten, size, seq]) (by simp [size]))
    | _, Tree.node l r, _, (And.intro fst snd) => by
      apply proveBindSpec (relabel l) _ (applySpec relabelSpec l)
      . intro Q h
        apply step2' (λ _ => Q) l
        apply And.intro
        . exact fst
        . intro _ _
          apply h.right
          unfold relabelSpec applySpec
          assumption
      . apply And.intro
        . unfold relabelSpec applySpec
          simp
        . intro _ postL
          apply proveBindSpec (relabel r) _ (applySpec relabelSpec r)
          . intro Q h
            apply step2' (λ _ => Q) r
            apply And.intro
            . unfold relabelSpec
              simp
            . intro _ _
              apply h.right
              . unfold relabelSpec applySpec
                assumption
          . apply And.intro
            . unfold relabelSpec applySpec
              simp
            . intro _ postR
              apply snd
              simp [relabelSpec, relabelPost]
              apply postcondition
              . unfold relabelSpec applySpec at postL
                simp [relabelPost] at postL
                exact postL
              . unfold relabelSpec applySpec at postR
                simp [relabelPost] at postR
                exact postR

  theorem step2 : wpSpec (@relabelSpec a) ⊑ wpState relabel :=
    λ P (t, s) h => step2' P t s h

  theorem correctnessRelabel : wpSpec (@relabelSpec x) ⊑ wpState relabel :=
    step2
end Relabel

namespace Compositionality
  open Free
  open Maybe (C R wpSpec)

  def pt (ptalgebra : (c : C) → (R c → Prop) → Prop) : Free C R a → (a → Prop) → Prop
    | Free.pure x,   P => P x
    | Free.step c x, P => ptalgebra c (λ r => pt ptalgebra (x r) P)

  def wpCR (ptalgebra : (c : C) → (R c → Prop) → Prop) {a : Type} {b : a → Type} : ((x : a) → Free C R (b x)) → ((x : a) → b x → Prop) → (a → Prop) :=
    λ f P x => pt ptalgebra (f x) (P x)

  theorem compositionality (ptalgebra : (c : C) → (R c → Prop) → Prop) : (c : Free C R a) → (f : a → Free C R b) → ∀ P, pt ptalgebra (c >>= f) P = pt ptalgebra c (wpCR ptalgebra f (λ _ => P))
    | Free.pure x,   f, P => rfl
    | Free.step c x, f, P => by
      simp [wpCR, pt]
      have h := congrArg (λ h => ptalgebra c h) (funext (λ r => compositionality ptalgebra (x r) f P))
      simp [Bind.bind, wpCR, pt] at h
      exact h

  theorem compositionalityLeft (ptalgebra : (c : C) → (R c → Prop) → Prop) (f₁ f₂ : a → Free C R b) (g : b → Free C R c) : wpCR ptalgebra f₁ ⊑ wpCR ptalgebra f₂ → wpCR ptalgebra (f₁ >=> g) ⊑ wpCR ptalgebra (f₂ >=> g) := by
    intro h _ _ _
    simp [wpCR, Bind.kleisliRight] at *
    apply Eq.mpr (compositionality _ _ _ _)
    apply h
    apply Eq.mp (compositionality _ _ _ _)
    assumption

  theorem monotonicity {P Q : a → Prop} (ptalgebra : (c : C) → (R c → Prop) → Prop) : P ⊆ Q → (c : Free C R a) → pt ptalgebra c P → pt ptalgebra c Q := by
    intro h x
    induction x
    case pure =>
      simp [pt]
      apply h
    case step c k ih =>
      cases c
      simp [pt]
      match λ r => pt ptalgebra (k r) P, λ r => pt ptalgebra (k r) Q with
      | fp, fq =>
        have heq : fp = fq := by
          apply funext
          intro x
          cases x
        simp [←heq]
        apply id

  theorem compositionalityRight (ptalgebra : (c : C) → (R c → Prop) → Prop) (f : a → Free C R b) (g₁ g₂ : b → Free C R c) : wpCR ptalgebra g₁ ⊑ wpCR ptalgebra g₂ → wpCR ptalgebra (f >=> g₁) ⊑ wpCR ptalgebra (f >=> g₂) := by
    intro h _ _ _
    simp [wpCR, Bind.kleisliRight] at *
    apply Eq.mpr (compositionality _ _ _ _)
    apply monotonicity ptalgebra (h _)
    apply Eq.mp (compositionality _ _ _ _)
    assumption

  theorem weakenPre {a : Type} {b : a → Type} {P P' : a → Prop} {Q : (x : a) → b x → Prop} : (P ⊆ P') → (wpSpec ⟨P, Q⟩ ⊑ wpSpec ⟨P', Q⟩) :=
    λ h₁ _ h₂ (And.intro pre post) => And.intro (h₁ h₂ pre) post

  theorem strengthenPost {a : Type} {b : a → Type} {P : a → Prop} {Q Q' : (x : a) → b x → Prop} : ((x : a) → Q' x ⊆ Q x) → (wpSpec ⟨P, Q⟩ ⊑ wpSpec ⟨P, Q'⟩) :=
    λ h _ _ (And.intro pre post) => And.intro pre (λ x y => post x (h _ x y))
end Compositionality

namespace Laws
  open State

  def wpState' : State s b → (P : s → b × s → Prop) → (s → Prop) :=
    λ t P s => wpState (λ _ => t) (λ ((), s') y => P s' y) ((), s)

  def equiv : State s b → State s b → Prop :=
    λ t₁ t₂ => (wpState' t₁ ⊑ wpState' t₂) ∧ (wpState' t₂ ⊑ wpState' t₁)

  notation "_≃_" => equiv
  infix:50 "≃" => equiv
end Laws

namespace Nondeterminism
  open Free
  open Maybe (SpecK wpSpec)

  inductive C : Type where
    | fail : C
    | choice : C

  def R : C → Type
    | C.fail   => Empty
    | C.choice => Bool

  def ND : Type → Type :=
    Free C R

  def fail : ND a :=
    Free.step C.fail Empty.rec

  def choice : ND a → ND a → ND a :=
    λ c1 c2 => Free.step C.choice (λ (b : Bool) => if b then c1 else c2)

  def allPT {a : Type} {b : a → Type} : ((x : a) → b x → Prop) → (x : a) → ND (b x) → Prop := by
    intro P _ x
    induction x
    case pure x => exact P _ x
    case step c k ih =>
      cases c
      case fail => exact True
      case choice => exact ih true ∧ ih false

  def wpAll {a : Type} {b : a → Type} : ((x : a) → ND (b x)) → ((x : a) → b x → Prop) → (a → Prop) :=
    λ f P => wp f (allPT P)

  def anyPT {a : Type} {b : a → Type} : ((x : a) → b x → Prop) → (x : a) → ND (b x) → Prop := by
    intro P _ x
    induction x
    case pure x => exact P _ x
    case step c k ih =>
      cases c
      case fail => exact False
      case choice => exact ih true ∨ ih false

  def wpAny {a : Type} {b : a → Type} : ((x : a) → ND (b x)) → (P : (x : a) → b x → Prop) → (a → Prop) :=
    λ f P => wp f (anyPT P)

  def run : ND a → List a
    | Free.pure x          => [x]
    | Free.step C.fail _   => []
    | Free.step C.choice k => run (k true) ++ run (k false)

  def all : (a → Prop) → List a → Prop
    | _, []        => True
    | P, (x :: xs) => P x ∧ all P xs

  def all' : (P : a → Prop) → (xs ys : List a) → all P xs → all P ys → all P (xs ++ ys)
    | _, [], _, _, h => h
    | P, (_ :: xs), ys, (And.intro Px h₁), h₂ => And.intro Px (all' P xs ys h₁ h₂)

  theorem allSoundness {a : Type} {b : a → Type} (P : (x : a) → b x → Prop) (x : a) : (nd : ND (b x)) → allPT P x nd → all (P x) (run nd)
    | Free.pure y,          h                 => by
      simp [allPT] at h
      simp [all, h]
    | Free.step C.fail _,   _                 => by simp [all]
    | Free.step C.choice _, (And.intro h₁ h₂) => by
      apply all'
      . apply allSoundness
        exact h₁
      . apply allSoundness
        exact h₂

  theorem wpAllSoundness {a : Type} {b : a → Type} (f : (x : a) → ND (b x)) : ∀ P x, wpAll f P x → all (P x) (run (f x)) :=
    λ P x h => allSoundness P x (f x) h

  inductive Elem {a : Type} (x : a) : ND a → Prop where
    | here  : Elem x (Free.pure x)
    | left  : Elem x (k true) → Elem x (Free.step C.choice k)
    | right : Elem x (k false) → Elem x (Free.step C.choice k)

  def subset' (nd₁ nd₂ : ND a) : Prop :=
    ∀ x, Elem x nd₁ → Elem x nd₂

  notation "_⊆'_" => subset'
  infix:50 "⊆'" => subset'

  theorem allP : ∀ (P : a → b → Prop) (S : ND b), allPT P x S ↔ (∀ y, Elem y S → P x y) := by
    intro P S
    apply Iff.intro
    . induction S
      case pure =>
        intro h _ x
        cases x
        exact h
      case step ih =>
        intro h y x
        cases x
        case left k i => exact ih true h.left y i
        case right k i => exact ih false h.right y i
    . induction S
      case pure =>
        intro h
        apply h
        apply Elem.here
      case step c k ih =>
        cases c
        case fail =>
          intro
          simp [allPT]
        case choice =>
          intro h
          apply And.intro
          . exact ih true (λ y i => h y (Elem.left i))
          . exact ih false (λ y i => h y (Elem.right i))

  theorem anyP : ∀ (P : a → b → Prop) (S : ND b), anyPT P x S ↔ ∃ b, Elem b S ∧ P x b := by
    intro P S
    apply Iff.intro
    . induction S
      case pure x =>
        intro h
        apply Exists.intro x
        apply And.intro
        . apply Elem.here
        . exact h
      case step c _ ih =>
        cases c
        case fail =>
          intro h
          simp [anyPT] at h
        case choice =>
          intro h
          cases h
          case inl h =>
            cases ih true h
            rename_i x h
            apply Exists.intro x
            apply And.intro
            . apply Elem.left
              exact h.left
            . exact h.right
          case inr h =>
            cases ih false h
            rename_i x h
            apply Exists.intro x
            apply And.intro
            . apply Elem.right
              exact h.left
            . exact h.right
    . induction S
      case pure =>
        intro h
        cases h
        rename_i h
        cases h.left
        exact h.right
      case step c _ ih =>
        cases c
        case fail =>
          intro h
          cases h
          rename_i h
          cases h.left
        case choice =>
          intro h
          cases h
          rename_i x h
          cases h
          rename_i fst snd
          cases fst
          case left h =>
            apply Or.inl
            apply ih
            apply Exists.intro x
            apply And.intro
            . exact h
            . exact snd
          case right h =>
            apply Or.inr
            apply ih
            apply Exists.intro x
            apply And.intro
            . exact h
            . exact snd

  theorem refineAll : (f g : a → ND b) → (wpAll f ⊑ wpAll g) ↔ ((x : a) → g x ⊆' f x) := by
    intro f g
    apply Iff.intro
    . intro h x _ i
      apply Iff.mp (allP (λ _ y' => Elem y' (f x)) (g x))
      . simp [sqsubset, subset, wpAll] at h
        apply (h _ x (Iff.mpr (allP _ (f x)) (λ _ => id)))
      . exact i
    . intro r P x h
      apply Iff.mpr (allP P (g x))
      intro y i
      apply Iff.mp (allP P (f x)) h y (r x y i)

  theorem refineAny : (f g : a → ND b) → (wpAny f ⊑ wpAny g) ↔ ((x : a) → f x ⊆' g x) := by
    intro f g
    apply Iff.intro
    . intro h x y i
      simp [wpAny] at h
      cases Iff.mp (anyP (λ _ y' => y' = y) (g x)) (h _ x (Iff.mpr (anyP _ (f x)) (Exists.intro y (And.intro i rfl))))
      rename_i _ h
      cases h.right
      exact h.left
    . intro r P x h
      cases Iff.mp (anyP P (f x)) h
      rename_i y h
      exact Iff.mpr (anyP P (g x)) (Exists.intro y (And.intro (r x y h.left) h.right))

  inductive Mem {a : Type} : ∀ (_ : a) (_ : List a), Type where
    | head : Mem x (List.cons x xs)
    | tail : Mem x xs → Mem x (List.cons x' xs)

  notation "_∈'_" => Mem
  infix:50 "∈'" => Mem

  def delete {a : Type} {x : a} : (xs : List a) → x ∈' xs → List a
    | []       , h => nomatch h
    | (x :: xs), h => match h with
      | Mem.head   => xs
      | Mem.tail h => x :: delete xs h

  def selectPost [DecidableEq a] : List a → a × List a → Prop :=
    λ xs (y, ys) => ∃ (h : y ∈' xs), delete xs h = ys

  def removeSpec [DecidableEq a] : SpecK (List a) (a × List a) :=
    ⟨K True, selectPost⟩

  def retain : a → a × List a → a × List a :=
    λ x (y, ys) => (y, x :: ys)

  def remove : List a → ND (a × List a)
    | []      => fail
    | x :: xs => choice (Free.pure (x, xs)) (map (retain x) (remove xs))

  def mapPT {a b c : Type} : ∀ P (x x' : a) (S : ND b) (f : b → c), allPT (λ _ y => P x (f y)) x' S → allPT P x (map f S)
    | _, _, _,  Free.pure _,          _, h                   => h
    | _, _, _,  Free.step C.fail _,   _, h                   => h
    | P, x, x', Free.step C.choice k, f, (And.intro fst snd) => And.intro (mapPT P x x' (k true) f fst) (mapPT P x x' (k false) f snd)

  theorem removeCorrect [DecidableEq a] : @wpSpec (List a) (λ _ => (a × List a)) removeSpec ⊑ wpAll remove
    | _, [],      And.intro _ _   => by simp [wpAll, wp, remove, fail, allPT]
    | P, x :: xs, And.intro _ snd => by
      apply And.intro
      . apply snd (x, xs)
        apply Exists.intro (Mem.head)
        rfl
      . apply mapPT P (x :: xs) xs (remove xs)
        apply removeCorrect _ xs
        apply And.intro
        . simp [removeSpec]
        . intro (x', xs') (Exists.intro i h)
          apply snd (x', (x :: xs'))
          apply Exists.intro (Mem.tail i)
          simp at h
          simp [←h, delete]

  theorem trivialCorrect [DecidableEq a] : @wpSpec (List a) (K (a × List a)) removeSpec ⊑ wpAll (K fail) :=
    λ _ _ _ => by simp [wpAll, wp, fail, allPT]

  def inMap {a b : Type} : ∀ (x : a) S (f : a → b), Elem x S → Elem (f x) (map f S)
    | _, Free.pure _,          _, Elem.here    => Elem.here
    | x, Free.step C.choice k, f, Elem.left i  => Elem.left (inMap x (k true) f i)
    | x, Free.step C.choice k, f, Elem.right i => Elem.right (inMap x (k false) f i)

  theorem completeness [eq : DecidableEq a] : (y : a) → (xs ys : List a) → selectPost xs (y, ys) → Elem (y, ys) (remove xs) := by
    intro _ _ _ (Exists.intro h₁ h₂)
    cases h₂
    cases h₁
    case head => exact Elem.left Elem.here
    case tail xs x h => exact Elem.right (inMap _ (remove xs) (retain x) (completeness _ _ _ (Exists.intro h rfl)))
  end Nondeterminism

namespace Recursion
  open Free
  open Maybe

  def recFun (I : Type) (O : I → Type) : Type :=
    (i : I) → Free I O (O i)

  notation "_~~>_" => recFun
  infix:50 "~~>" => recFun

  def call : (i : I) → Free I O (O i) :=
    λ x => Free.step x Free.pure

  def f91 : Nat ~~> K Nat :=
    λ i => if 100 < i then Free.pure (i - 10) else call (i + 11) >>= call

  def f91Post : Nat → Nat → Prop :=
    λ i o => if 100 < i then o = i - 10 else o = 91

  def f91Spec : SpecK Nat Nat :=
    ⟨K True, f91Post⟩

  def invariant {O : I → Type} : (i : I) → Spec I O  → Free I O (O i) → Prop := by
    intro i spec x
    induction x
    case pure x => exact spec.pre i → spec.post i x
    case step j _ ih => exact (spec.pre i → spec.pre j) ∧ ∀ o, spec.post j o → ih o

  def wpRec {O : I → Type} : Spec I O → (I ~~> O) → ((i : I) → O i → Prop) → (I → Prop) :=
    λ spec f P i => wpSpec spec P i ∧ invariant i spec (f i)

  theorem not100Leq91 : (i : Nat) → ¬ (i + 10 ≤ i)
    | Nat.zero,   h => by simp_arith at h
    | Nat.succ i, h => not100Leq91 i (by simp_arith at h)

  theorem plusMinus : ∀ (b c : Nat), (b + c) - c = b := by
    simp [Nat.add_sub_assoc]

  theorem plusPlusMinus : ∀ i, i + 11 - 10 = Nat.succ i :=
    λ i => plusMinus (Nat.succ i) 11

  theorem between : ∀ a b, ¬ (a < b) → a < Nat.succ b → a = b
    | Nat.zero,   Nat.zero,   _,  _ => rfl
    | Nat.zero,   Nat.succ b, hn, _ => False.elim (hn (Nat.zero_lt_succ b))
    | Nat.succ a, Nat.zero,   _,  h => False.elim (Nat.not_lt_zero a (Nat.lt_of_succ_lt_succ h))
    | Nat.succ a, Nat.succ b, hn, h => congrArg Nat.succ (between a b (hn ∘ Nat.succ_le_succ) (Nat.le_of_succ_le_succ h))

  theorem f91PartialCorrectness' : ∀ i o o', ¬ (100 < i) → f91Post (i + 11) o → f91Post o o' → f91Post i o' := by
    intro i o o' h oPost o'Post
    simp [f91Post] at *
    simp [h]
    cases Nat.decLt 100 o
    case isTrue h₁ =>
      simp [h₁] at o'Post
      cases Nat.decLt 100 (i + 11)
      case isTrue h₂ =>
        simp [h₂] at oPost
        simp [oPost] at h₁
        cases between 100 i h (Eq.mp (congrArg (λ i' => 100 < i') (plusPlusMinus i)) h₁)
        simp [oPost] at o'Post
        simp [o'Post]
      case isFalse h₂ =>
        simp [h₂] at oPost
        simp [oPost] at h₁
    case isFalse h₁ =>
      simp [h₁] at o'Post
      exact o'Post

  def f91PartialCorrectness : wpSpec f91Spec ⊑ wpRec f91Spec f91 := by
    intro _ i h
    apply And.intro
    . exact h
    . cases Nat.decLt 100 i
      case isTrue hlt => simp [invariant, f91Spec, f91Post, f91, hlt]
      case isFalse hnlt =>
        simp [invariant, f91Spec, f91Post, f91, hnlt]
        intro o x₁ o' x₂
        have h := f91PartialCorrectness' i o o' hnlt x₁ x₂
        simp [f91Post, hnlt] at h
        exact h

  def petrol (f : I ~~> O) : Free I O a → Nat → Partial a
    | Free.pure x,    _          => Free.pure x
    | Free.step _ _,  Nat.zero   => abort
    | Free.step c k,  Nat.succ n => petrol f (f c >>= k) n

  def mayPT : (a → Prop) → (Partial a → Prop)
    | P, Free.pure x         => P x
    | _, Free.step C.abort _ => True

  theorem invariantCompositionality {O : I → Type} : (spec : Spec I O) → (S : Free I O (O i)) → (k : (O i) → Free I O (O i')) → invariant i spec S → Spec.pre spec i → (∀ o, Spec.post spec i o → invariant i' spec (k o)) → invariant i' spec (S >>= k)
    | _,    Free.pure x,    _, SH,                  preH, kH => kH x (SH preH)
    | spec, Free.step _ k', k, (And.intro fst snd), preH, kH => And.intro (λ _ => fst preH) (λ o postH => invariantCompositionality spec (k' o) k (snd o postH) preH kH)

  theorem soundness' {O : I → Type} : (f : (i : I) → Free I O (O i)) → (spec : Spec I O) → (P : (i : I) → O i → Prop) → (S : Free I O (O i)) → (n : Nat) → (∀ i, wpRec spec f P i) → wpSpec spec P i ∧ invariant i spec S → mayPT (P i) (petrol f S n)
    | _, _,    _, Free.pure x,   _,          _,   (And.intro (And.intro preH postH) invH)  => by
      simp [petrol, mayPT]
      exact postH x (invH preH)
    | _, _,    _, Free.step _ _, Nat.zero,   _,   _                                        => by simp [petrol, abort, mayPT]
    | f, spec, P, Free.step c k, Nat.succ n, wpH, (And.intro specH (And.intro preH postH)) => soundness' f spec P (f c >>= k) n wpH (And.intro specH (invariantCompositionality spec (f c) k (wpH c).right (preH specH.left) postH))

  theorem soundness : (f : I ~~> O) → (spec : Spec I O) → (P : (i : I) → O i → Prop) → (∀ i, wpRec spec f P i) → ∀ n i, mayPT (P i) (petrol f (f i) n) :=
    λ f spec P wpH n i => soundness' f spec P (f i) n wpH (wpH i)
end Recursion

namespace Mix
  open Free
  open Maybe (SpecK wpSpec)

  def SpecVal : Type → Type :=
    SpecK Unit

  inductive I (a : Type) : Type where
    | done : a → I a
    | hole : SpecVal a → I a

  def ptI : I a → (a → Prop) → Prop
    | I.done x,    P => P x
    | I.hole spec, P => wpSpec spec (λ _ => P) ()

  def M (C : Type) (R : C → Type) : Type → Type :=
    λ a => Free C R (I a)

  def isExecutable : M C R a → Prop
    | Free.pure (I.done _) => True
    | Free.pure (I.hole _) => False
    | Free.step _ k        => ∀ r, isExecutable (k r)

  def pt {a : Type u} (ptalgebra : (c : C) → (R c → Prop) → Prop) : Free C R a → (a → Prop) → Prop
    | Free.pure x,   P => P x
    | Free.step c x, P => ptalgebra c (λ r => pt ptalgebra (x r) P)

  def wpCR {a : Type u} {b : a → Type v} (ptalgebra : (c : C) → (R c → Prop) → Prop) : ((x : a) → Free C R (b x)) → ((x : a) → b x → Prop) → (a → Prop) :=
    λ f P x => pt ptalgebra (f x) (P x)

  def wpM {a : Type} {b : a → Type} (ptalgebra : (c : C) → (R c → Prop) → Prop) : ((x : a) → M C R (b x)) → ((x : a) → b x → Prop) → (a → Prop) :=
    λ f P x => wpCR ptalgebra f (λ x ix => ptI ix (P x)) x
end Mix

namespace StateExample
  open Free
  open Maybe (SpecK wpSpec)
  open State

  def SpecVal : Type → Type :=
    SpecK Nat

  inductive I (a : Type) : Type where
    | done : a → I a
    | hole : SpecVal (a × Nat) → I a

  def M : Type → Type :=
    λ a => State Nat (I a)

  def ptI : I a → (a × Nat → Prop) → Nat → Prop
    | I.done x,    P, t => P (x, t)
    | I.hole spec, P, t => wpSpec spec (λ _ => P) t

  def wpM : (a → M b) → (a × Nat → b × Nat → Prop) → (a × Nat → Prop) :=
    λ f P => wpState f (λ i o => ptI o.fst (P i) o.snd)

  def ptM : M a → (Nat → a × Nat → Prop) → (Nat → Prop) :=
    λ S post t => wpM (λ _ => S) (λ _ => (post t)) (Unit, t)

  def bind : M a → (a → M b) → M b
    | Free.pure (I.done x),    f => f x
    | Free.pure (I.hole spec), f => Free.pure (I.hole ⟨spec.pre, λ i ynat => ∀ x, spec.post i (x, i) → ∀ P, wpM f P (x, i) → P (x, i) ynat⟩)
    | Free.step c k,           f => Free.step c (λ r => bind (k r) f)

  instance : Monad M where
    pure := Free.pure ∘ I.done
    bind := bind

  def specV : SpecVal (a × Nat) → M a :=
    λ spec => Free.pure (I.hole spec)

  def done : a → M a :=
    Free.pure ∘ I.done

  def get' : M Nat :=
    Free.step C.get done

  def put' : Nat → M Unit :=
    λ t => Free.step (C.put t) done

  def getPost : Nat → Nat × Nat → Prop :=
    λ t (x, t') => (t = x) ∧ (t = t')

  def putPost : Nat → Nat → Unit × Nat → Prop :=
    λ t _ (_, t') => t = t'

  def forward (Q : a → b → Prop) (P : a → Prop) : b → Prop :=
    λ y => ∃ x, P x ∧ Q x y

  notation "_▹_" => forward
  infix:50 "▹" => forward

  def backward (Q : a → b → Prop) (spec : SpecK a c) : b → c → Prop :=
    λ y z => ∀ x, spec.pre x ∧ Q x y → spec.post x z

  notation "_◃_" => backward
  infix:50 "◃" => backward

  def step : (c : C Nat) → (spec : SpecVal (b × Nat)) → SpecK (R c × Nat) (b × Nat)
    | C.get,   spec => ⟨getPost ▹ spec.pre, getPost ◃ spec⟩
    | C.put x, spec => ⟨putPost x ▹ spec.pre, putPost x ◃ spec⟩

  def intros : SpecK (a × Nat) (b × Nat) → a → SpecVal (b × Nat) :=
    λ spec x => ⟨λ t => spec.pre (x, t), λ t => spec.post (x, t)⟩

  inductive Derivation : ∀ (_ : SpecVal (b × Nat)), Type where
    | done : (x : b) → wpSpec spec ⊑ ptM (done x) → Derivation spec
    | step : (c : C Nat) → (∀ (r : R c), Derivation (intros (step c spec) r)) → Derivation spec

  def extract : (spec : SpecVal (b × Nat)) → Derivation spec → State Nat b
    | _, Derivation.done x _ => Free.pure x
    | _, Derivation.step c k => Free.step c (λ r => extract _ (k r))

  def derivationFun : (spec : SpecK (a × Nat) (b × Nat)) → Type :=
    λ spec => (x : a) → Derivation (intros spec x)

  theorem postLemmaGet (h : wpSpec spec ⊑ wpSpec spec') : ∀ r (x : Nat) o, (∀ i, spec'.pre i ∧ i = r ∧ i = x → spec'.post i o) → ∀ i, spec.pre i ∧ i = r ∧ i = x → spec.post i o :=
    λ _ _ x hi r (And.intro fst snd) => (h spec.post r (And.intro fst (λ _ z => z))).right x (hi r (And.intro (h (λ _ _ => True) r (And.intro fst (λ _ _ => trivial))).left snd))

  theorem postLemmaPut (h : wpSpec spec ⊑ wpSpec spec') : ∀ (t x : Nat) o, (∀ i, spec'.pre i ∧ t = x → spec'.post i o) → ∀ i, spec.pre i ∧ t = x → spec.post i o :=
    λ _ _ x hx₁ x₁ hpre => (h spec.post x₁ (And.intro hpre.left (λ _ z => z))).right x (hx₁ x₁ (And.intro (h (λ _ _ => True) x₁ (And.intro hpre.left (λ _ _ => trivial))).left hpre.right))

  theorem stepMonotone : (c : C Nat) → (r : R c) → wpSpec spec ⊑ wpSpec spec' → wpSpec (intros (step c spec) r) ⊑ wpSpec (intros (step c spec') r)
    | C.get,   r, h, _, x, (And.intro (Exists.intro x₁ fst) snd) => And.intro (Exists.intro x₁ (And.intro ((h (λ _ _ => True) x₁ (And.intro fst.left (λ _ _ => trivial))).left) fst.right)) (λ o hi => snd o (postLemmaGet h r x o hi))
    | C.put t, _, h, _, x, (And.intro (Exists.intro x₁ fst) snd) => And.intro (Exists.intro x₁ (And.intro ((h (λ _ _ => True) x₁ (And.intro fst.left (λ _ _ => trivial))).left) fst.right)) (λ o hi => snd o (postLemmaPut h t x o hi))

  inductive All (P : a → Prop) : List a → Prop where
    | allNil : All P []
    | allCons : P x → All P xs → All P (x :: xs)

  def unAllCons : All P (x :: xs) → All P xs :=
    λ (All.allCons _ x₂) => x₂

  def maxPre : List Nat × Nat → Prop :=
    λ (xs, i) => (i = 0) ∧ (xs ≠ [])

  def maxPost : List Nat × Nat → Nat × Nat → Prop :=
    λ (xs, _) (o, _) => All (o ≥·) xs ∧ (o ∈ xs)

  def maxSpec : SpecK (List Nat × Nat) (Nat × Nat) :=
    ⟨maxPre, maxPost⟩

  def refineDerivation : wpSpec spec ⊑ wpSpec spec' → Derivation spec' → Derivation spec
    | hspec, Derivation.done x h => Derivation.done x (⊑-trans hspec h)
    | hspec, Derivation.step c d => Derivation.step c (λ r => refineDerivation (stepMonotone c r hspec) (d r))

  def maxPost' : List Nat × Nat → Nat × Nat → Prop :=
    λ (xs, i) (o, _) => All (o ≥·) (i :: xs) ∧ (o ∈ (i :: xs))

  theorem maxProof' : ∀ xs, ¬ (xs == []) → ∀ w, (All (λ n => n ≤ w) (0 :: xs)) ∧ (w ∈ (0 :: xs)) → w ∈ xs
    | [],     h, _, _                 => False.elim (h rfl)
    | _ :: _, _, _, And.intro fst snd => by
      cases snd
      case head =>
        cases fst
        rename_i fst
        cases fst
        rename_i fst _
        simp at fst
        simp [fst]
        apply List.Mem.head
      case tail h => exact h

  theorem maxProof : ∀ (xs : List Nat), wpSpec (intros ⟨maxPre, maxPost⟩ xs) ⊑ wpSpec (intros ⟨K True, maxPost'⟩ xs) :=
    λ xs P _ (And.intro (And.intro fst₁ fst₂) snd) => by
      apply And.intro
      . simp [intros]
      . intro _ h
        simp [fst₁] at h
        apply snd
        apply And.intro
        . apply unAllCons
          exact h.left
        . apply maxProof'
          . simp [fst₂]
          . exact h

  theorem max'ProofNil' : ∀ (i : Nat) x, True ∧ (x = i) ∧ (x = i) → (All (λ n => n ≤ i) [x]) ∧ (i ∈ [x]) :=
    λ i _ (And.intro fst (And.intro rfl rfl)) => by
      apply And.intro
      . apply All.allCons
        . apply Nat.le_refl
        . apply All.allNil
      . apply List.Mem.head

  theorem max'ProofNil : ∀ i, wpSpec (intros (step C.get (intros ⟨K True, maxPost'⟩ [])) i) ⊑ ptM (done i) :=
    λ _ _ _ (And.intro _ snd) => by
      apply snd
      simp [intros, step, backward, getPost, maxPost']
      intro x hx
      apply max'ProofNil'
      simp [hx]

  theorem max'Proof₁' (hlt : x < i) : ∀ (x₂ : Nat × Nat), All (λ n => n ≤ x₂.fst) (i :: xs) ∧ x₂.fst ∈ (i :: xs) → ∀ x₃, True ∧ x₃ = i ∧ x₃ = i → All (λ n => n ≤ x₂.fst) (x₃ :: x :: xs) ∧ x₂.fst ∈ (x₃ :: x :: xs) := by
    intro _ h₁ _ h₂
    cases h₂.right.left
    cases h₂.right.right
    cases h₁
    rename_i fst snd
    cases snd
    case head =>
      apply And.intro
      . apply All.allCons
        . apply Nat.le_refl
        . apply All.allCons
          . apply Nat.le_of_lt
            exact hlt
          . cases fst
            assumption
      . apply List.Mem.head
    case tail =>
      apply And.intro
      . cases fst
        rename_i hle _
        apply All.allCons
        . assumption
        . apply All.allCons
          . exact Nat.le_trans (Nat.le_of_lt hlt) hle
          . assumption
      . apply List.Mem.tail
        apply List.Mem.tail
        assumption

  theorem max'Proof₁ : ∀ x xs i, Nat.succ x ≤ i → ∀ (P : Nat → Nat × Nat → Prop) x₁, (∃ x₂, True ∧ x₂ = i ∧ x₂ = x₁) ∧ (∀ x₂, (∀ x₃, True ∧ x₃ = i ∧ x₃ = x₁ → All (λ n => n ≤ x₂.fst) (x₃ :: x :: xs) ∧ x₂.fst ∈ (x₃ :: x :: xs)) → P x₁ x₂) → True ∧ (∀ x₂, All (λ n => n ≤ x₂.fst) (x₁ :: xs) ∧ x₂.fst ∈ (x₁ :: xs) → P x₁ x₂) := by
    intro _ _ _ hle _ _ h
    apply And.intro
    . trivial
    . intro x₂ x₁
      apply h.right
      cases h.left
      rename_i _ h
      cases h.right.left
      cases h.right.right
      exact max'Proof₁' hle x₂ x₁

  theorem max'Proof₂' (hnle : ¬ Nat.succ x ≤ i) : ∀ (x₄ : Nat × Nat), All (λ n => n ≤ x₄.fst) (x :: xs) ∧ x₄.fst ∈ (x :: xs) → ∀ x₃, (∃ x₅, True ∧ x₅ = i ∧ x₅ = x₃) ∧ (x = x) → ∀ x₅, True ∧ x₅ = i ∧ x₅ = x₃ → All (λ n => n ≤ x₄.fst) (x₅ :: x :: xs) ∧ x₄.fst ∈ (x₅ :: x :: xs) := by
    intro _ h₁ _ _ _ h₂
    apply And.intro
    . cases h₁.left
      rename_i hle _
      apply All.allCons
      . simp [h₂]
        exact Nat.le_trans (Eq.mp (Nat.not_lt_eq x i) hnle) hle
      . apply All.allCons
        . assumption
        . assumption
    . apply List.Mem.tail
      exact h₁.right

  theorem max'Proof₂ : ∀ i x xs, (¬ Nat.succ x ≤ i) → ∀ (P : Nat → Nat × Nat → Prop) x₁, (∃ x₂, (∃ x₃, True ∧ x₃ = i ∧ x₃ = x₂) ∧ x = x₁) ∧ (∀ x₂, (∀ x₃, (∃ x₄, True ∧ x₄ = i ∧ x₄ = x₃) ∧ x = x₁ → ∀ x₄, True ∧ x₄ = i ∧ x₄ = x₃ → All (λ n => n ≤ x₂.fst) (x₄ :: x :: xs) ∧ x₂.fst ∈ (x₄ :: x :: xs)) → P x₁ x₂) → True ∧ (∀ x₂, All (λ n => n ≤ x₂.fst) (x₁ :: xs) ∧ x₂.fst ∈ (x₁ :: xs) → P x₁ x₂) := by
    intro _ _ _ hnle _ _ h
    apply And.intro
    . trivial
    . intro x₄ x₁
      apply h.right
      cases h.left
      rename_i _ h
      cases h.right
      exact max'Proof₂' hnle x₄ x₁

  def maxSpec' : SpecK (List Nat × Nat) (Nat × Nat) :=
    ⟨K True, maxPost'⟩

  def max' : (xs : List Nat) → Derivation (intros maxSpec' xs)
    | []      => Derivation.step C.get λ i =>
                 Derivation.done i (max'ProofNil i)
    | x :: xs => Derivation.step C.get λ i =>
                 if h : x < i
                 then refineDerivation (by exact max'Proof₁ x xs i h) (max' xs)
                 else Derivation.step (C.put x) (λ _ => refineDerivation (by exact max'Proof₂ i x xs h) (max' xs))

  def max : derivationFun ⟨maxPre, maxPost⟩ :=
    λ xs => refineDerivation (maxProof xs) (max' xs)
end StateExample
end PredicateTransformers
