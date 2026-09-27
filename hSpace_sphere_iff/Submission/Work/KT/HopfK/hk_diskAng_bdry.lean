import Mathlib
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.hk_relprod

namespace Work.KT.HopfK

/-- On the boundary `∂(D × D)` of the cell the disk angle `diskAng m` agrees with the base angle
`chiB m` composed with the Hopf construction `hopfKMap m μ`: at a boundary point one of the two
coordinates has norm `1`, and the corresponding height formula (`tgtHeight_eq_of_norm_snd_eq_one`
resp. `tgtHeight_eq_of_norm_fst_eq_one`) turns the (vanishing) remaining square-root term into the
matching one. -/
theorem hk_diskAng_bdry (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) :
    ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      diskAng m z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) := by
  intro z hz
  have hmax : max ‖(z : Eu m × Eu m).1‖ ‖(z : Eu m × Eu m).2‖ = 1 := by
    rw [← Prod.norm_def]; exact hz
  rcases eq_or_ne ‖(z : Eu m × Eu m).2‖ 1 with h2 | h2
  · have ht := tgtHeight_eq_of_norm_snd_eq_one m μ
        ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩ (by simpa using h2)
    have hs2 : Real.sqrt (1 - ‖(z : Eu m × Eu m).2‖ ^ 2) = 0 := by rw [h2]; norm_num
    have harg : 1 / 2 + Real.sqrt (1 - ‖(z : Eu m × Eu m).1‖ ^ 2)
          - Real.sqrt (1 - ‖(z : Eu m × Eu m).2‖ ^ 2)
        = tgtHeight m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)
          + 1 / 2 := by
      rw [ht, hs2]; ring
    rw [diskAng_apply, chiB_apply, harg]
  · have ha1 : ‖(z : Eu m × Eu m).1‖ = 1 := by
      rcases max_eq_iff.mp hmax with ⟨ha, _⟩ | ⟨hb, _⟩
      · exact ha
      · exact absurd hb h2
    have ht := tgtHeight_eq_of_norm_fst_eq_one m μ
        ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩ (by simpa using ha1)
    have hs1 : Real.sqrt (1 - ‖(z : Eu m × Eu m).1‖ ^ 2) = 0 := by rw [ha1]; norm_num
    have harg : 1 / 2 + Real.sqrt (1 - ‖(z : Eu m × Eu m).1‖ ^ 2)
          - Real.sqrt (1 - ‖(z : Eu m × Eu m).2‖ ^ 2)
        = tgtHeight m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)
          + 1 / 2 := by
      rw [ht, hs1]; ring
    rw [diskAng_apply, chiB_apply, harg]

end Work.KT.HopfK
