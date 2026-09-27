import Mathlib

namespace Work.EQ

open Filter Set

theorem meromorphic_order_nonneg_of_bounded {f : ℂ → ℂ} {x : ℂ} {C : ℝ}
    (hf : MeromorphicAt f x) (h : Filter.Eventually (fun z => ‖f z‖ ≤ C) (nhdsWithin x {x}ᶜ)) :
    0 ≤ meromorphicOrderAt f x := by
  by_contra hc
  rw [not_le] at hc
  -- a meromorphic function of negative order blows up near the point
  have hcob : Tendsto f (nhdsWithin x {x}ᶜ) (Bornology.cobounded ℂ) :=
    (tendsto_cobounded_iff_meromorphicOrderAt_neg hf).2 hc
  have hnorm : Tendsto (fun z => ‖f z‖) (nhdsWithin x {x}ᶜ) atTop :=
    tendsto_norm_atTop_iff_cobounded.2 hcob
  have hgt : ∀ᶠ z in nhdsWithin x {x}ᶜ, C < ‖f z‖ :=
    hnorm.eventually (eventually_gt_atTop C)
  -- ... contradicting the assumed boundedness
  obtain ⟨z, hz1, hz2⟩ := (h.and hgt).exists
  exact absurd hz1 (not_le.mpr hz2)

end Work.EQ
