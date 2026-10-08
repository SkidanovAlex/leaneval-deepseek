import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.step9_global_sums
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.chiGamma_inner`

feat(20): for `Γ` a class function on `G`, `γ : ℂ` with `Γ` taking the value `γ` at every
non-identity element of `Q`, and `ζ₁` a non-trivial linear irreducible character of `Q`,

* `|Q| · ⟨Γ, Ind_Q^G ζ₁⟩_G = Γ 1 - γ`, and
* `|Q| · ⟨Γ, Ind_Q^G 1_Q⟩_G = Γ 1 + (|Q| - 1) · γ`.

Both are immediate from Frobenius reciprocity
(`Work.Induction.frobenius_reciprocity_transposed`), which turns `|Q| · ⟨Γ, Ind_Q^G ζ⟩_G` into
the unnormalised sum `∑_{y ∈ Q} Γ y · conj (ζ y)`, the constancy hypothesis on `Q ∖ 1`, and
the vanishing of `∑_{y ∈ Q} ζ₁ y` for the non-principal irreducible character `ζ₁`
(`Work.CharCore.sum_apply_eq_zero_of_mem_Irr_of_ne_one`).

## A note on `Fintype` instances

`Work.CharCore.cfInner` and `Work.CharCore.Irr` carry a `Fintype` argument.  The hypothesis
`[Fintype ↥Q]` of the statement below is an abstract instance variable, while the library
statement of Frobenius reciprocity fixes the instance derived at its own definition site; the
two are propositionally, but not definitionally, equal (and comparing them definitionally
diverges through `Work.CharCore.Irr`).  As in
`Submission/Work/ZassenhausPSL2/Feit/cfInner_indFun_linear_excl.lean`, we therefore transport
Frobenius reciprocity to the instance supplied by the caller before starting the computation
(`cfInner_inst_indep` and `cfInner_indFun_eq_of_inst` below), so that every subgroup-internal
object in the argument is elaborated at the caller's instance.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open scoped BigOperators

namespace Work.ZassenhausTwoGroup

/-- `Work.CharCore.cfInner` does not depend on the chosen `Fintype` instance. -/
private theorem cfInner_inst_indep {X : Type} (i₁ i₂ : Fintype X) (f g : X → ℂ) :
    @Work.CharCore.cfInner X i₁ f g = @Work.CharCore.cfInner X i₂ f g := by
  have huniv : (@Finset.univ X i₁ : Finset X) = @Finset.univ X i₂ :=
    Finset.ext fun x => by simp
  have hcard : (@Fintype.card X i₁ : ℂ) = (@Fintype.card X i₂ : ℂ) := by
    rw [@Fintype.card_eq_nat_card X i₁, @Fintype.card_eq_nat_card X i₂]
  have hsum : (@Finset.univ X i₁).sum (fun x => f x * starRingEnd ℂ (g x))
      = (@Finset.univ X i₂).sum (fun x => f x * starRingEnd ℂ (g x)) := by
    rw [huniv]
  show (@Fintype.card X i₁ : ℂ)⁻¹ * (@Finset.univ X i₁).sum (fun x => f x * starRingEnd ℂ (g x))
      = (@Fintype.card X i₂ : ℂ)⁻¹ * (@Finset.univ X i₂).sum (fun x => f x * starRingEnd ℂ (g x))
  rw [hcard, hsum]

/-- Frobenius reciprocity `⟨Γ, Ind_H^G ψ⟩_G = ⟨Res_H^G Γ, ψ⟩_H` with the `Fintype ↥H`
instance of the right-hand side chosen by the caller (the library version fixes the instance
derived from `[Fintype G]`). -/
private theorem cfInner_indFun_eq_of_inst {G : Type} [Group G] [Fintype G] {H : Subgroup G}
    [iH : Fintype ↥H] (φ : G → ℂ) (hφ : Work.CharCore.IsClassFun φ) (ψ : H → ℂ) :
    Work.CharCore.cfInner φ (Work.Induction.indFun H ψ)
      = @Work.CharCore.cfInner ↥H iH (Work.Induction.resFun H φ) ψ := by
  rw [Work.Induction.frobenius_reciprocity_transposed H φ ψ hφ]
  exact cfInner_inst_indep _ iH (Work.Induction.resFun H φ) ψ

theorem chiGamma_inner {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1)
    {Γ : G → ℂ} (hΓ : Work.CharCore.IsClassFun Γ) {γ : ℂ}
    (hconst : ∀ y : ↥Q, y ≠ 1 → Γ (y : G) = γ) :
    (Nat.card ↥Q : ℂ) * Work.CharCore.cfInner Γ (Work.Induction.indFun Q ζ₁) = Γ 1 - γ ∧
    (Nat.card ↥Q : ℂ) *
        Work.CharCore.cfInner Γ (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)))
      = Γ 1 + ((Nat.card ↥Q : ℂ) - 1) * γ := by
  classical
  have hQne : (Nat.card ↥Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Nat.card_ne_zero]
    exact ⟨⟨1⟩, inferInstance⟩
  -- Frobenius reciprocity turns `|Q| · ⟨Γ, Ind_Q^G ζ⟩_G` into the unnormalised sum
  -- `∑_{y ∈ Q} Γ y · conj (ζ y)`, which the constancy hypothesis on `Q ∖ 1` splits as
  -- `(Γ 1 - γ) + γ · ∑_{y ∈ Q} conj (ζ y)`.
  have key : ∀ ζ : ↥Q → ℂ, ζ 1 = 1 →
      (Nat.card ↥Q : ℂ) * Work.CharCore.cfInner Γ (Work.Induction.indFun Q ζ)
        = (Γ 1 - γ) + γ * ∑ y : ↥Q, star (ζ y) := by
    intro ζ hζ1'
    -- Frobenius reciprocity, transported to the caller's `Fintype ↥Q` instance
    rw [cfInner_indFun_eq_of_inst Γ hΓ ζ, Work.CharCore.cfInner_apply]
    rw [← Nat.card_eq_fintype_card, ← mul_assoc, mul_inv_cancel₀ hQne, one_mul]
    -- identify `Res_Q^G Γ` and the two conjugate notations
    rw [show (∑ x : ↥Q, Work.Induction.resFun Q Γ x * starRingEnd ℂ (ζ x))
        = ∑ y : ↥Q, Γ (y : G) * star (ζ y) from
      Finset.sum_congr rfl fun y _ => by simp]
    -- split off the `y = 1` term, where `Γ 1 - γ` survives
    have hsplit : ∑ y : ↥Q, Γ (y : G) * star (ζ y)
        = ∑ y : ↥Q, ((Γ (y : G) - γ) * star (ζ y) + γ * star (ζ y)) :=
      Finset.sum_congr rfl fun y _ => by ring
    rw [hsplit, Finset.sum_add_distrib]
    have hA : ∑ y : ↥Q, (Γ (y : G) - γ) * star (ζ y) = (Γ 1 - γ) * star (ζ 1) := by
      rw [Finset.sum_eq_single (1 : ↥Q)]
      · simp
      · intro y _ hy
        rw [hconst y hy, sub_self, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ (1 : ↥Q)) hmem
    have hB : ∑ y : ↥Q, γ * star (ζ y) = γ * ∑ y : ↥Q, star (ζ y) :=
      (Finset.mul_sum ..).symm
    rw [hA, hB, hζ1', star_one, mul_one]
  refine ⟨?_, ?_⟩
  · rw [key ζ₁ hlin]
    have hsum0 : ∑ y : ↥Q, ζ₁ y = 0 :=
      Work.CharCore.sum_apply_eq_zero_of_mem_Irr_of_ne_one hζ hζ1
    have hstar0 : ∑ y : ↥Q, star (ζ₁ y) = 0 := by
      have hconj := congrArg (starRingEnd ℂ) hsum0
      simpa using hconj
    rw [hstar0, mul_zero, add_zero]
  · rw [key (fun _ : ↥Q => (1 : ℂ)) rfl]
    have hsum1 : ∑ y : ↥Q, star ((fun _ : ↥Q => (1 : ℂ)) y) = (Nat.card ↥Q : ℂ) := by
      simp [Finset.sum_const, Nat.card_eq_fintype_card]
    rw [hsum1]
    ring

end Work.ZassenhausTwoGroup
