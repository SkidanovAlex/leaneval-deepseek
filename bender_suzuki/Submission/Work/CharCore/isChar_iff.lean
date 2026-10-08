import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.CharCore.isChar_iff_exists_nat_coeffs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.isChar_iff`

A class function `f` on a finite group is a character if and only if its normalised inner
product `cfInner f χ` with every irreducible character `χ` is a natural number.

The two directions are opposite readings of the two structural results of the area:

* `Work.CharCore.isChar_iff_exists_nat_coeffs` writes a character as `∑_χ c χ • χ` with
  `c χ : ℕ`, and orthonormality `Work.CharCore.irr_orthonormal` collapses
  `⟨f, ψ⟩ = ∑_χ c χ ⟨χ, ψ⟩` to the single coefficient `c ψ`;
* `Work.CharCore.classFun_eq_sum_irr` writes a class function as `∑_χ ⟨f, χ⟩ • χ`, so if
  every `⟨f, χ⟩` is a natural number the expansion exhibits `f` as a non-negative integral
  combination of irreducible characters.
-/

noncomputable section

open Classical Finset

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- Bilinearity of `cfInner` for sums indexed by the subtype `↥(Irr G)`. -/
theorem cfInner_irr_sum_smul_left (c : ↥(Irr G) → ℂ) (ψ : G → ℂ) :
    cfInner (∑ χ : ↥(Irr G), c χ • (χ : G → ℂ)) ψ
      = ∑ χ : ↥(Irr G), c χ * cfInner (χ : G → ℂ) ψ :=
  cfInner_sum_smul_left Finset.univ c (fun χ => (χ : G → ℂ)) ψ

theorem isChar_iff {G : Type*} [Group G] [Fintype G] {f : G → ℂ} (hf : IsClassFun f) :
    IsChar f ↔ ∀ χ ∈ Irr G, ∃ n : ℕ, cfInner f χ = n := by
  constructor
  · -- A character `f = ∑_χ c χ • χ` has `⟨f, ψ⟩ = c ψ ∈ ℕ` by orthonormality.
    intro hchar χ hχ
    obtain ⟨c, hc⟩ := isChar_iff_exists_nat_coeffs.mp hchar
    refine ⟨c ⟨χ, hχ⟩, ?_⟩
    rw [hc, cfInner_irr_sum_smul_left]
    rw [Finset.sum_eq_single (⟨χ, hχ⟩ : ↥(Irr G))]
    · rw [irr_orthonormal χ χ hχ hχ]; simp
    · intro b _ hb
      have hne : (b : G → ℂ) ≠ χ := fun h => hb (Subtype.ext h)
      rw [irr_orthonormal (b : G → ℂ) χ b.2 hχ]
      simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · -- A class function whose inner products with all `χ ∈ Irr G` are natural numbers is
    -- the corresponding non-negative integral combination of the `χ`.
    intro h
    let c : ↥(Irr G) → ℕ := fun χ => Classical.choose (h χ.1 χ.2)
    have hc : ∀ χ : ↥(Irr G), cfInner f (χ : G → ℂ) = (c χ : ℂ) :=
      fun χ => Classical.choose_spec (h (χ : G → ℂ) χ.2)
    rw [isChar_iff_exists_nat_coeffs]
    refine ⟨c, ?_⟩
    have hstep1 : f = ∑ χ : ↥(Irr G), cfInner f (χ : G → ℂ) • (χ : G → ℂ) := by
      conv_lhs => rw [classFun_eq_sum_irr hf]
      rw [← Finset.sum_coe_sort (Irr G) (fun χ : G → ℂ => cfInner f χ • χ)]
    calc f = ∑ χ : ↥(Irr G), cfInner f (χ : G → ℂ) • (χ : G → ℂ) := hstep1
      _ = ∑ χ : ↥(Irr G), (c χ : ℂ) • (χ : G → ℂ) := by
            refine Finset.sum_congr rfl fun χ _ => ?_
            rw [hc χ]

end Work.CharCore
