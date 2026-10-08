import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.conj_mem_Q_iff
import Submission.Work.ZassenhausTwoGroup.card_H_eq
import Submission.Work.ZassenhausTwoGroup.card_quotient_eq
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.zetaStar_aux`

Shared vocabulary for Feit's display (20), `‖Ind_Q^G ζ‖² = |D| + 1` (see `zetaStar_norm`).

In the split rank-one set-up `IsSplitRankOne H Q t` with `D = twoPoint H t = H ⊓ Hᵗ` we have
`H = Q ⋊ D` (`Q ⊴ H`, `Q ⊓ D = ⊥`, `Q ⊔ D = H`).  This file collects

* `conjQ h x q`: the conjugate `x q x⁻¹` of `q ∈ Q` by `x ∈ H`, as an element of `Q`
* `conjQD h d q`: its specialisation to `d ∈ D`
* `qdEquiv h`: the product bijection `Q × D ≃ H`, `(a,d) ↦ a * d`
* `sum_H_eq`: reindexing a sum over `H` through that bijection.

Nothing here is specific to characters.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint
open LeanEval.GroupTheory

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G]

/-- Conjugation of `q ∈ Q` by `x ∈ H`, as an element of `Q` (well defined because
`H ≤ N_G(Q)`). -/
def conjQ {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (x : H) (q : Q) : Q :=
  ⟨(x : G) * (q : G) * (x : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h.normal x.2) (q : G)).mp q.2⟩

@[simp] theorem conjQ_coe {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    (x : H) (q : Q) : ((conjQ h x q : Q) : G) = (x : G) * (q : G) * (x : G)⁻¹ := rfl

/-- Conjugating by a product: `conjQ (a * x) q = a * conjQ x q * a⁻¹` for `a ∈ Q`. -/
theorem conjQ_mul {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    (a : Q) (x : H) (q : Q) :
    conjQ h ⟨(a : G) * (x : G), H.mul_mem (h.le a.2) x.2⟩ q = a * conjQ h x q * a⁻¹ := by
  apply Subtype.ext
  simp only [conjQ_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  group

/-- Conjugation of `q ∈ Q` by `d ∈ D = twoPoint H t`. -/
def conjQD {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (d : twoPoint H t)
    (q : Q) : Q := conjQ h ⟨(d : G), twoPoint_le_H h d.2⟩ q

@[simp] theorem conjQD_coe {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    (d : twoPoint H t) (q : Q) :
    ((conjQD h d q : Q) : G) = (d : G) * (q : G) * (d : G)⁻¹ := rfl

/-- The product bijection `Q × D ≃ H`, `(a, d) ↦ a * d`, from `Q ⊓ D = ⊥` and `Q ⊔ D = H`
together with the cardinality `|H| = |Q| · |D|`. -/
noncomputable def qdEquiv {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) [Fintype G] :
    (Q × twoPoint H t) ≃ H :=
  Equiv.ofBijective
    (fun p : Q × twoPoint H t =>
      (⟨(p.1 : G) * (p.2 : G), H.mul_mem (h.le p.1.2) (twoPoint_le_H h p.2.2)⟩ : H))
    (by
      rw [Nat.bijective_iff_injective_and_card]
      refine ⟨?_, ?_⟩
      · rintro ⟨a₁, d₁⟩ ⟨a₂, d₂⟩ heq
        have hG : (a₁ : G) * (d₁ : G) = (a₂ : G) * (d₂ : G) := Subtype.ext_iff.mp heq
        have hprod : ((a₂⁻¹ * a₁ : Q) : G) = ((d₂ * d₁⁻¹ : twoPoint H t) : G) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv]
          have h1 : (a₂ : G)⁻¹ * ((a₁ : G) * (d₁ : G)) = (d₂ : G) := by
            rw [hG, ← mul_assoc, inv_mul_cancel, one_mul]
          have h2 : (a₂ : G)⁻¹ * (a₁ : G) = (d₂ : G) * (d₁ : G)⁻¹ := by
            have := congrArg (fun z : G => z * (d₁ : G)⁻¹) h1
            simpa [mul_assoc] using this
          exact h2
        have hmem : ((a₂⁻¹ * a₁ : Q) : G) ∈ Q ⊓ twoPoint H t :=
          ⟨(a₂⁻¹ * a₁ : Q).2, by rw [hprod]; exact (d₂ * d₁⁻¹ : twoPoint H t).2⟩
        have hone : ((a₂⁻¹ * a₁ : Q) : G) = 1 := by
          have h : ((a₂⁻¹ * a₁ : Q) : G) ∈ (⊥ : Subgroup G) := by
            rw [← h.inf_eq]; exact hmem
          exact Subgroup.mem_bot.mp h
        have ha : a₂⁻¹ * a₁ = 1 := Subtype.ext hone
        have ha' : a₁ = a₂ := by
          have h := congrArg (fun z : Q => a₂ * z) ha
          simpa using h
        have hd : d₂ * d₁⁻¹ = 1 := by
          apply Subtype.ext
          rw [← hprod, hone, Subgroup.coe_one]
        have hd' : d₁ = d₂ := by
          have h : d₂ = d₁ := by
            have hh := congrArg (fun z : twoPoint H t => z * d₁) hd
            simpa using hh
          exact h.symm
        exact Prod.ext ha' hd'
      · rw [Nat.card_prod, card_H_eq h])

@[simp] theorem qdEquiv_coe {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) [Fintype G]
    (p : Q × twoPoint H t) :
    ((qdEquiv h p : H) : G) = (p.1 : G) * (p.2 : G) := rfl

/-- Reindexing a sum over `H` through the product bijection `Q × D ≃ H`. -/
theorem sum_H_eq {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) [Fintype G]
    (g : H → ℂ) :
    (∑ x : H, g x) = ∑ a : Q, ∑ d : twoPoint H t, g (qdEquiv h (a, d)) := by
  rw [← Fintype.sum_prod_type (fun p : Q × twoPoint H t => g (qdEquiv h p))]
  exact (Equiv.sum_comp (qdEquiv h) g).symm

end Work.ZassenhausTwoGroup
