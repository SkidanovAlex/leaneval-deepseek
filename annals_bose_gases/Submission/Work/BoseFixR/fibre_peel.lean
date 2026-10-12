import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators
import Submission.Work.BoseFixR.fibCount_init_eq
import Submission.Work.BoseFixR.fibCount_snoc_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.fibre_peel` — peeling the last particle off a fibre count

For a labelling `σ : Fin (n+1) → ι` write `fibCount σ i = #{d | σ d = i}`
(`Work.BoseFixR.FibrePeelDefs`).  The **fibre** of a multiplicity vector `α : ι →₀ ℕ` is

`{σ : Fin (n+1) → ι // ∀ i, fibCount σ i = α i}`.

This module proves that its cardinality is obtained by removing one particle:

`#{σ : Fin (n+1) → ι | fibCount σ = α}
   = ∑_{k : α k ≠ 0} #{τ : Fin n → ι | fibCount τ = α.update k (α k - 1)}`.

The proof is the peeling bijection.  Its forward map reads off the last particle `k = σ (Fin.last n)`
of `σ` together with the initial segment `τ = Fin.init σ`; `k` lies in the support of `α`
(`fibCount_ne_zero_last`, since the last coordinate alone contributes `1` to the fibre of `k`), and
`τ` realises `α.update k (α k - 1)` (`fibCount_init_eq`).  Its inverse glues a particle of value `k`
onto `τ` as `Fin.snoc τ k`, which realises `α` (`fibCount_snoc_eq`).  The two maps are inverse by
`Fin.snoc_init_self` and `Fin.init_snoc`, and the bijection is turned into the stated identity by
`Fintype.card_congr`, `Equiv.subtypeProdEquivSigmaSubtype` and `Fintype.card_sigma`.
-/

namespace Work.BoseFixR

/-- **Peeling**: a labelling `σ : Fin (n+1) → ι` realising `α` gives its last value
`σ (Fin.last n)` (an element of the support of `α`) together with the initial segment
`Fin.init σ`, which realises `α.update k (α k - 1)`. -/
def peelToFun {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (α : ι →₀ ℕ)
    (σ : {σ : Fin (n+1) → ι // ∀ i, fibCount σ i = α i}) :
    {x : {k : ι // α k ≠ 0} × (Fin n → ι) //
      ∀ i, fibCount x.2 i = (α.update x.1.1 (α x.1.1 - 1)) i} :=
  ⟨(⟨σ.1 (Fin.last n), fibCount_ne_zero_last α σ.1 σ.2⟩, Fin.init σ.1),
   fun i => fibCount_init_eq α σ.1 σ.2 i⟩

/-- **Gluing**: an element `k` of the support of `α` and a labelling `τ : Fin n → ι` realising
`α.update k (α k - 1)` give the labelling `Fin.snoc τ k` realising `α`. -/
def peelInvFun {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (α : ι →₀ ℕ)
    (x : {x : {k : ι // α k ≠ 0} × (Fin n → ι) //
      ∀ i, fibCount x.2 i = (α.update x.1.1 (α x.1.1 - 1)) i}) :
    {σ : Fin (n+1) → ι // ∀ i, fibCount σ i = α i} :=
  ⟨Fin.snoc x.1.2 x.1.1.1, fun i => fibCount_snoc_eq α x.1.1.1 x.1.1.2 x.1.2 x.2 i⟩

theorem peel_left {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (α : ι →₀ ℕ) :
    Function.LeftInverse (peelInvFun n α) (peelToFun n α) := by
  intro σ
  apply Subtype.ext
  show Fin.snoc (Fin.init σ.1) (σ.1 (Fin.last n)) = σ.1
  exact Fin.snoc_init_self σ.1

theorem peel_right {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (α : ι →₀ ℕ) :
    Function.RightInverse (peelInvFun n α) (peelToFun n α) := by
  intro x
  obtain ⟨⟨k, τ⟩, hx⟩ := x
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Fin.snoc_last (α := fun _ => ι) k.1 τ
  · exact Fin.init_snoc (α := fun _ => ι) k.1 τ

/-- **The peeling bijection** between the labellings of `Fin (n+1)` realising `α` and the pairs
of a value `k` in the support of `α` with a labelling of `Fin n` realising `α.update k (α k - 1)`. -/
def peelEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (α : ι →₀ ℕ) :
    {σ : Fin (n+1) → ι // ∀ i, fibCount σ i = α i} ≃
    {x : {k : ι // α k ≠ 0} × (Fin n → ι) //
      ∀ i, fibCount x.2 i = (α.update x.1.1 (α x.1.1 - 1)) i} :=
  ⟨peelToFun n α, peelInvFun n α, peel_left n α, peel_right n α⟩

theorem fibre_peel {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (α : ι →₀ ℕ) :
    Fintype.card {σ : Fin (n+1) → ι // ∀ i, (Finset.univ.filter fun d => σ d = i).card = α i}
      = ∑ k : {k : ι // α k ≠ 0},
          Fintype.card {τ : Fin n → ι // ∀ i, (Finset.univ.filter fun d => τ d = i).card
            = (α.update k (α k - 1)) i} := by
  change Fintype.card {σ : Fin (n+1) → ι // ∀ i, fibCount σ i = α i}
      = ∑ k : {k : ι // α k ≠ 0},
          Fintype.card {τ : Fin n → ι // ∀ i, fibCount τ i = (α.update k (α k - 1)) i}
  rw [Fintype.card_congr (peelEquiv n α)]
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (k : {k : ι // α k ≠ 0}) (τ : Fin n → ι) =>
      ∀ i, fibCount τ i = (α.update k.1 (α k.1 - 1)) i))]
  rw [Fintype.card_sigma]

end Work.BoseFixR
