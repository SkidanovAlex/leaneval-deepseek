import Mathlib

set_option autoImplicit false

namespace Work.WilC5

open FirstOrder Language

/-!
# Tools for the definable-closure map lemma

This file collects some elementary syntactic/realization lemmas about first order formulas with
free variables in a sum type, together with the explicit formula `funMapBody` used to show that the
set of points definable over a parameter tuple is closed under function symbols.
-/

/-- Auxiliary: the composition of `Sum.elim p y` (with `p : γ ⊕ Fin 1 → X`) with the map
`γ ⊕ Fin 1 → (γ ⊕ Fin 1) ⊕ β` sending the parameters to `Sum.inl`, the special variable to `Sum.inr`
and `Sum.inr j` to `Sum.inr k`. -/
theorem sumElim_comp_sumElim {X : Type} {γ : Type} {β : Type} (p : γ ⊕ Fin 1 → X) (y : β → X)
    (k : β) :
    (Sum.elim p y) ∘ (Sum.elim (Sum.inl ∘ Sum.inl) (fun _ : Fin 1 => Sum.inr k)) =
      Sum.elim (p ∘ Sum.inl) (fun _ : Fin 1 => y k) := by
  funext a
  cases a with
  | inl c => rfl
  | inr j => rfl

/-- Given formulas `φk` (each with free variables `γ ⊕ Fin 1`) and a function symbol `f` of arity
`n`, `funMapBody f φk` is the formula with free variables `(γ ⊕ Fin 1) ⊕ Fin n` expressing
"there are `y k` satisfying `φk k`, and the distinguished variable equals `f y`". -/
noncomputable def funMapBody {L : FirstOrder.Language} {γ : Type} {n : ℕ} (f : L.Functions n)
    (φk : Fin n → L.Formula (γ ⊕ Fin 1)) : L.Formula ((γ ⊕ Fin 1) ⊕ Fin n) :=
  (Formula.iInf fun k : Fin n =>
      (φk k).relabel (Sum.elim (Sum.inl ∘ Sum.inl) (fun _ : Fin 1 => Sum.inr k))) ⊓
    Term.equal (Term.var (Sum.inl (Sum.inr 0))) (Term.func f (fun k => Term.var (Sum.inr k)))

/-- If the formulas `φk` are realized at the tuple `zs` over the parameters `jj`, then
`∃ y, (⋀ φk y_k) ∧ (· = f y)` is realized at `f zs` over `jj`. -/
theorem realize_iExs_funMapBody_const {L : FirstOrder.Language} {N : Type} [L.Structure N]
    {γ : Type} (jj : γ → N) {n : ℕ} (f : L.Functions n) (zs : Fin n → N)
    (φk : Fin n → L.Formula (γ ⊕ Fin 1))
    (hz : ∀ k, (φk k).Realize (Sum.elim jj (fun _ => zs k))) :
    (Formula.iExs (Fin n) (funMapBody f φk)).Realize
      (Sum.elim jj (fun _ => Structure.funMap f zs)) := by
  rw [funMapBody, Formula.realize_iExs]
  refine ⟨zs, ?_⟩
  simp only [Formula.realize_inf, Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
    Term.realize_func, Formula.realize_relabel, sumElim_comp_sumElim, Sum.elim_comp_inl,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun k => hz k, trivial⟩

/-- Uniqueness transfer for functions `Fin 1 → X`: a predicate with a unique witness `t` has a
unique witness of the form `fun _ => n`. -/
theorem existsUnique_const_fin1 {X : Type} {P : (Fin 1 → X) → Prop} :
    (∃! t : Fin 1 → X, P t) → ∃! n : X, P fun _ => n := by
  rintro ⟨t, ht, huniq⟩
  refine ⟨t 0, ?_, ?_⟩
  · have h : (fun _ : Fin 1 => t 0) = t := by
      funext i
      rw [Fin.eq_zero i]
    beta_reduce
    rw [h]
    exact ht
  · intro n hn
    have h : (fun _ : Fin 1 => n) = t := huniq (fun _ => n) hn
    simpa using congrFun h 0

/-- Auxiliary computation of a composition of `Sum.elim`s. -/
theorem comp_sumElim_id {X : Type} {γ : Type} (f : γ → X) (b : γ) :
    f ∘ (Sum.elim id (fun _ : Fin 1 => b)) = Sum.elim f (fun _ : Fin 1 => f b) := by
  funext a
  cases a with
  | inl c => rfl
  | inr i => rfl

/-- Two formulas with free variables `γ ⊕ Fin 1` which are equivalent over the parameters `ii` are
equivalent over the parameters `jj`, provided `ii` and `jj` satisfy the same `γ`-formulas. -/
theorem realize_iff_transfer {L : FirstOrder.Language} {M N : Type} [L.Structure M]
    [L.Structure N] {γ : Type} (ii : γ → M) (jj : γ → N)
    (H : ∀ φ : L.Formula γ, φ.Realize ii ↔ φ.Realize jj)
    {φ ψ : L.Formula (γ ⊕ Fin 1)}
    (h : ∀ v : Fin 1 → M, φ.Realize (Sum.elim ii v) ↔ ψ.Realize (Sum.elim ii v)) :
    ∀ v : Fin 1 → N, φ.Realize (Sum.elim jj v) ↔ ψ.Realize (Sum.elim jj v) := by
  have hθ : (Formula.iAlls (Fin 1) (φ.iff ψ)).Realize ii := by
    rw [Formula.realize_iAlls]
    intro v
    rw [Formula.realize_iff]
    exact h v
  have hθ' : (Formula.iAlls (Fin 1) (φ.iff ψ)).Realize jj := (H _).1 hθ
  rw [Formula.realize_iAlls] at hθ'
  intro v
  simpa only [Formula.realize_iff] using hθ' v

/-- If `φ` defines the singleton `{ii b}` over the parameters `ii`, and `φ` also defines a
singleton over `jj`, then that singleton is `{jj b}`; hence `φ` is realized at `jj b`. -/
theorem realize_const_self {L : FirstOrder.Language} {M N : Type} [L.Structure M]
    [L.Structure N] {γ : Type} (ii : γ → M) (jj : γ → N)
    (H : ∀ φ : L.Formula γ, φ.Realize ii ↔ φ.Realize jj)
    (φ : L.Formula (γ ⊕ Fin 1)) (b : γ)
    (hφ : ∀ v : Fin 1 → M, v 0 = ii b ↔ φ.Realize (Sum.elim ii v)) :
    φ.Realize (Sum.elim jj (fun _ => jj b)) := by
  have h1 : (φ.relabel (Sum.elim id (fun _ : Fin 1 => b))).Realize ii ↔
      φ.Realize (Sum.elim ii (fun _ => ii b)) := by
    rw [Formula.realize_relabel, comp_sumElim_id]
  have h2 : (φ.relabel (Sum.elim id (fun _ : Fin 1 => b))).Realize jj :=
    (H _).1 (h1.2 ((hφ (fun _ => ii b)).1 rfl))
  have h3 : (φ.relabel (Sum.elim id (fun _ : Fin 1 => b))).Realize jj ↔
      φ.Realize (Sum.elim jj (fun _ => jj b)) := by
    rw [Formula.realize_relabel, comp_sumElim_id]
  exact h3.1 h2

end Work.WilC5
