import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

open Classical Filter Set
open scoped Topology

/-!
# The part of a parameter ray below a given equipotential is preconnected

The parameter ray of angle `θ` is, above level `1`, the image of the interval `(1,∞)` under the
continuous injective map `t ↦ rayPt hN θ t`, and the potential of `rayPt hN θ t` is `log t`.  Hence
the part of the ray on which the potential is `< log R` is exactly the image of the interval
`(1,R)` under this map, which is preconnected.
-/

/-- The part of the parameter ray of angle `θ` carrying potential `< log R` is the image of the
interval `(1,R)` under the level parametrization `t ↦ rayPt hN θ t`. -/
theorem paramRay_lt_eq_image_rayPt {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    (θ : ℝ) {R : ℝ} (hR : 1 < R) :
    {c : ℂ | c ∈ Work.Top.NakaneData.paramRay hN θ ∧ Work.Top.potential Mb Φ c < Real.log R}
      = Work.Top.NakaneData.rayPt hN θ '' Set.Ioo 1 R := by
  ext c
  constructor
  · rintro ⟨⟨hcMb, t, ht, hΦ⟩, hpot⟩
    have htpos : (0 : ℝ) < t := by linarith
    have hpc : Work.Top.potential Mb Φ c = Real.log t := by
      rw [Work.Top.potential_of_not_mem hcMb, hΦ, Work.Top.NakaneData.norm_rayPoint,
        abs_of_pos htpos]
    have htR : t < R :=
      (Real.log_lt_log_iff htpos (by linarith)).mp (by rw [hpc] at hpot; exact hpot)
    exact ⟨t, ⟨ht, htR⟩,
      hN.injOn_Phi (hN.rayPt_notMem ht) hcMb (by rw [hN.Phi_rayPt ht, hΦ])⟩
  · rintro ⟨t, ⟨ht, htR⟩, rfl⟩
    exact ⟨⟨hN.rayPt_notMem ht, t, ht, hN.Phi_rayPt ht⟩,
      by rw [hN.potential_rayPt ht]
         exact (Real.log_lt_log_iff (by linarith) (by linarith)).mpr htR⟩

theorem isPreconnected_paramRay_lt {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ : ℝ)
    {R : ℝ} (hR : 1 < R) :
    IsPreconnected {c : ℂ | c ∈ Work.Top.NakaneData.paramRay hN θ ∧ Work.Top.potential Mb Φ c < Real.log R} := by
  rw [paramRay_lt_eq_image_rayPt hN θ hR]
  exact isPreconnected_Ioo.image (fun t : ℝ => Work.Top.NakaneData.rayPt hN θ t)
    ((continuousOn_rayPt hN θ).mono Set.Ioo_subset_Ioi_self)

end Work.Top
