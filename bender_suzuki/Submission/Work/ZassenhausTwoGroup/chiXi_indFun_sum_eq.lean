import Mathlib
import Submission.Work.ZassenhausTwoGroup.zetaStar_norm
import Submission.Work.ZassenhausTwoGroup.indFun_Q_apply_mem_Q
import Submission.Work.ZassenhausTwoGroup.orbitData
import Submission.Work.CharCore.step9_global_sums

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit's orbit sum: `∑_{y ∈ Q} Ind_Q^G ζ₁(y) = |Q| · |D|`

In the split rank-one set-up `IsSplitRankOne H Q t` (`H = Q ⋊ D` with `D = twoPoint H t`,
`Q ⊴ H`, `Q ⊓ D = ⊥`, `Q ⊔ D = H`) and for a non-trivial **linear** irreducible character
`ζ₁` of `Q`, the induced function `Ξ = Ind_Q^G ζ₁` satisfies

`∑_{y ∈ Q} Ξ(y) = |Q| · |D|`.

This is the "sum" computation used in `chiXi_not_const` (Feit's argument that `Ξ` is not
constant on `Q ∖ {1}` unless `|D| = |Q| - 1`).

The proof uses only the split rank-one structure (the Zassenhaus hypothesis is not needed):

* `Ξ(1) = [G : Q] = (|Q| + 1)·|D|` (`indFun_apply_one`, `Q_index_eq`);
* for `1 ≠ y ∈ Q`, `Ξ(y) = ∑_{d ∈ D} ζ₁(d y d⁻¹)` (`indFun_Q_apply_mem_Q`);
* summing the second identity over `y ∈ Q ∖ {1}` and exchanging the two sums, the inner sum
  `∑_{y ∈ Q ∖ {1}} ζ₁ (d y d⁻¹)` is the sum of the non-trivial linear character `ζ₁` over all of
  `Q ∖ {1}` (conjugation by `d` is a bijection of `Q` fixing `1`), hence `-1`
  (`Work.CharCore.sum_apply_eq_zero_of_mem_Irr_of_ne_one`);
* so the off-`1` contribution is `-|D|` and the total is `Q.index - |D| = |Q|·|D|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- `[G : Q] = (|Q| + 1) · |D|` where `D = twoPoint H t`, from `|G : H| = |Q| + 1`
(`card_quotient_eq`) and `|H| = |Q| · |D|` (`card_H_eq`). -/
private theorem Q_index_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Q.index = (Nat.card ↥Q + 1) * Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have heq : Nat.card ↥Q * Q.index
      = Nat.card ↥Q * ((Nat.card ↥Q + 1) * Nat.card ↥(Submission.Blueprint.twoPoint H t)) := by
    rw [Subgroup.card_mul_index Q, ← Subgroup.card_mul_index H, card_H_eq h,
      Subgroup.index_eq_card H, card_quotient_eq h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hQpos heq

theorem chiXi_indFun_sum_eq {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1) :
    ∑ y : ↥Q, Work.Induction.indFun Q ζ₁ (y : G)
      = (Nat.card ↥Q : ℂ) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) := by
  classical
  -- `ζ₁` is a linear character: the composition of a homomorphism `Q →* ℂˣ` with `ℂˣ → ℂ`.
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥Q →* ℂˣ, ∀ x : ↥Q, ζ₁ x = (φ x : ℂ) := by
    refine (Work.CharCore.linear_char_iff_deg_one hζ).mp ?_
    have hspec := Work.CharCore.irrDeg_spec hζ
    have h1 : (Work.CharCore.irrDeg ζ₁ : ℂ) = 1 := by rw [← hspec, hlin]
    exact_mod_cast h1
  have hζφ : ζ₁ = fun x : ↥Q => (φ x : ℂ) := funext hφ
  -- value at the identity
  have hval1 : Work.Induction.indFun Q ζ₁ ((1 : ↥Q) : G) = (Q.index : ℂ) := by
    have h := Work.Induction.indFun_apply_one Q ζ₁
    rw [hlin, mul_one] at h
    simpa using h
  -- value at `1 ≠ y ∈ Q`
  have hval : ∀ y : ↥Q, y ≠ 1 → Work.Induction.indFun Q ζ₁ (y : G)
      = ∑ d : ↥(Submission.Blueprint.twoPoint H t), ζ₁ (conjQD h d y) := by
    intro y hy
    have h0 : Work.Induction.indFun Q ζ₁ (y : G)
        = ∑ d : ↥(Submission.Blueprint.twoPoint H t), (φ (conjQD h d y) : ℂ) := by
      rw [hζφ]
      exact indFun_Q_apply_mem_Q h φ hy
    rw [h0]
    exact Finset.sum_congr rfl (fun d _ => (hφ (conjQD h d y)).symm)
  -- the sum over `Q ∖ {1}`
  have herase : (∑ y ∈ Finset.univ.erase (1 : ↥Q), Work.Induction.indFun Q ζ₁ (y : G))
      = -(Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) := by
    have hstep : (∑ y ∈ Finset.univ.erase (1 : ↥Q), Work.Induction.indFun Q ζ₁ (y : G))
        = ∑ y ∈ Finset.univ.erase (1 : ↥Q),
            ∑ d : ↥(Submission.Blueprint.twoPoint H t), ζ₁ (conjQD h d y) :=
      Finset.sum_congr rfl (fun y hy => hval y (Finset.mem_erase.mp hy).1)
    rw [hstep, Finset.sum_comm]
    -- conjugation by `d ∈ D` is a bijection of `Q` fixing `1`, so the inner sum is `-1`
    have hinner : ∀ d : ↥(Submission.Blueprint.twoPoint H t),
        (∑ y ∈ Finset.univ.erase (1 : ↥Q), ζ₁ (conjQD h d y)) = -1 := by
      intro d
      have hc1 : conjQD h d (1 : ↥Q) = 1 := by
        apply Subtype.ext
        rw [conjQD_coe]
        simp
      have hfull : (∑ y : ↥Q, ζ₁ (conjQD h d y)) = (∑ y : ↥Q, ζ₁ y) := by
        have hh := Equiv.sum_comp (conjAutD h d).toEquiv (fun y : ↥Q => ζ₁ y)
        simpa [conjAutD_apply] using hh
      have hzero : (∑ y : ↥Q, ζ₁ y) = 0 :=
        Work.CharCore.sum_apply_eq_zero_of_mem_Irr_of_ne_one hζ hζ1
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : ↥Q)), hfull, hzero, hc1, hlin]
      ring
    rw [show (∑ d : ↥(Submission.Blueprint.twoPoint H t),
          ∑ y ∈ Finset.univ.erase (1 : ↥Q), ζ₁ (conjQD h d y))
        = ∑ _d : ↥(Submission.Blueprint.twoPoint H t), (-1 : ℂ) from
      Finset.sum_congr rfl (fun d _ => hinner d)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    ring
  -- reassemble
  rw [← Finset.sum_erase_add (Finset.univ : Finset ↥Q)
    (fun y : ↥Q => Work.Induction.indFun Q ζ₁ (y : G)) (Finset.mem_univ (1 : ↥Q))]
  rw [herase, hval1, Q_index_eq h]
  push_cast
  ring

end Work.ZassenhausTwoGroup
