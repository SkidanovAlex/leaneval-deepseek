import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The straight segment meets a ray piece in a single point

Let `Mb` be the connectedness locus and `Φ` Nakane's parameter Böttcher coordinate, subject to the
abstract interface `NakaneData` (`Submission/Work/Top/Defs.lean`).

Let `S = segment ℝ x y ∩ paramRay hN β` be the part of the parameter ray of angle `β` which lies on
a straight segment, and let `E ∈ S` be a point where the potential attains its maximum on `S`.
If moreover `potential Mb Φ E ≤ log R`, then the ray piece of angle `β` between the levels
`potential Mb Φ E` and `R` meets the segment exactly in `E`:

  `segment ℝ x y ∩ rayPiece hN β (potential Mb Φ E) R = {E}`.

The content is that on a parameter ray the potential determines the point: a point `c` of the ray
of angle `β` equals `rayPt hN β ‖Φ c‖`, and `potential Mb Φ c = log ‖Φ c‖`.  Hence a point `c` of
the ray piece which also lies on the segment has, by maximality of `E` and by the lower bound
`potential Mb Φ E ≤ potential Mb Φ c` defining the ray piece, the same potential as `E`, so
`‖Φ c‖ = ‖Φ E‖` and `c = E`.
-/

open Classical Filter Set
open scoped Topology

namespace Work.Top

/-- A point of the parameter ray of angle `β` is the point `rayPt hN β t` of that ray at level
`t = ‖Φ c‖`, and its potential is `log ‖Φ c‖`. -/
theorem segment_inter_rayPiece_aux {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {β : ℝ} {z : ℂ} (hz : z ∈ Work.Top.NakaneData.paramRay hN β) :
    z = Work.Top.NakaneData.rayPt hN β ‖Φ z‖ ∧
      Work.Top.potential Mb Φ z = Real.log ‖Φ z‖ := by
  obtain ⟨hzMb, t, ht, hΦ⟩ := hz
  have hnorm : ‖Φ z‖ = t := by
    rw [hΦ, NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
  have hz_eq : z = NakaneData.rayPt hN β t :=
    hN.injOn_Phi hzMb (hN.rayPt_notMem ht) (by rw [hN.Phi_rayPt ht]; exact hΦ)
  exact ⟨by rw [hnorm]; exact hz_eq, potential_of_not_mem hzMb⟩

theorem segment_inter_rayPiece_eq_singleton {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {x y E : ℂ} {β R : ℝ}
    (hE : E ∈ segment ℝ x y ∩ Work.Top.NakaneData.paramRay hN β)
    (hmax : ∀ c ∈ segment ℝ x y ∩ Work.Top.NakaneData.paramRay hN β,
      Work.Top.potential Mb Φ c ≤ Work.Top.potential Mb Φ E)
    (hle : Work.Top.potential Mb Φ E ≤ Real.log R) :
    segment ℝ x y ∩ Work.Top.NakaneData.rayPiece hN β (Work.Top.potential Mb Φ E) R = {E} := by
  have hEseg : E ∈ segment ℝ x y := hE.1
  have hEray : E ∈ NakaneData.paramRay hN β := hE.2
  -- `E` itself belongs to the ray piece.
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨hEseg, hEray, le_refl _, hle⟩, ?_⟩
  -- conversely, a point of the intersection has the same potential as `E`.
  rintro c ⟨hcseg, hcray, hcle, _⟩
  have hpot : potential Mb Φ c = potential Mb Φ E :=
    le_antisymm (hmax c ⟨hcseg, hcray⟩) hcle
  obtain ⟨hc_eq, hpc⟩ := segment_inter_rayPiece_aux hN hcray
  obtain ⟨hE_eq, hpE⟩ := segment_inter_rayPiece_aux hN hEray
  rw [hpc, hpE] at hpot
  -- `‖Φ c‖ = ‖Φ E‖` because the logarithm is injective on the positive reals.
  have hcpos : (0 : ℝ) < ‖Φ c‖ := lt_trans zero_lt_one (hN.Phi_mem_exteriorDisc hcray.1)
  have hEpos : (0 : ℝ) < ‖Φ E‖ := lt_trans zero_lt_one (hN.Phi_mem_exteriorDisc hEray.1)
  have hnorm : ‖Φ c‖ = ‖Φ E‖ := Real.log_injOn_pos hcpos hEpos hpot
  rw [hc_eq, hnorm, ← hE_eq]

end Work.Top
