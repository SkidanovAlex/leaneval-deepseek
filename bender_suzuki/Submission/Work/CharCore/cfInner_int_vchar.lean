import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs
import Submission.Work.CharCore.irr_orthonormal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.cfInner_int_vchar`

The inner product `Work.CharCore.cfInner f g` of two virtual characters of a finite group
is an integer.

## Proof

Write `f = ∑_{χ ∈ Irr G} c χ • χ` and `g = ∑_{ψ ∈ Irr G} d ψ • ψ` with integer
coefficients `c`, `d` (`Work.CharCore.isVChar_iff_exists_int_coeffs`).  Bilinearity of
`cfInner` (`Work.CharCore.cfInner_sum_smul_left`,
`Work.CharCore.cfInner_sum_smul_right`) together with orthonormality of `Irr G`
(`Work.CharCore.irr_orthonormal`) turns the inner product into the single sum

`cfInner f g = ∑_{χ ∈ Irr G} c χ * d χ`,

using `starRingEnd ℂ ((d χ : ℂ)) = (d χ : ℂ)` for the integer `d χ`.  That sum is an
integer, so `cfInner f g` is the image of an integer under the canonical embedding
`ℤ → ℂ`.
-/

noncomputable section

open Classical

namespace Work.CharCore

theorem cfInner_int_vchar {G : Type*} [Group G] [Fintype G] {f g : G → ℂ} (hf : IsVChar f)
    (hg : IsVChar g) : ∃ n : ℤ, cfInner f g = n := by
  obtain ⟨c, rfl⟩ := isVChar_iff_exists_int_coeffs.mp hf
  obtain ⟨d, rfl⟩ := isVChar_iff_exists_int_coeffs.mp hg
  refine ⟨∑ χ : ↥(Irr G), c χ * d χ, ?_⟩
  -- expand the second argument, then the first
  rw [cfInner_sum_smul_left]
  have h1 : ∀ χ : ↥(Irr G),
      cfInner (χ : G → ℂ) (∑ ψ : ↥(Irr G), (d ψ : ℂ) • (ψ : G → ℂ)) = (d χ : ℂ) := by
    intro χ
    rw [cfInner_sum_smul_right]
    -- only the diagonal term survives
    rw [Finset.sum_eq_single χ]
    · rw [irr_orthonormal (χ : G → ℂ) (χ : G → ℂ) χ.2 χ.2]
      simp
    · intro ψ _ hψ
      have hne : (χ : G → ℂ) ≠ (ψ : G → ℂ) := fun h => hψ (Subtype.ext h.symm)
      rw [irr_orthonormal (χ : G → ℂ) (ψ : G → ℂ) χ.2 ψ.2]
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ χ) h
  rw [Finset.sum_congr rfl (fun χ _ => by rw [h1 χ])]
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl (fun χ _ => (Int.cast_mul (c χ) (d χ)).symm)

end Work.CharCore
