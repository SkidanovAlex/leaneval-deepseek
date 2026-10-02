import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- Membership in a ray piece: a point of the ray of angle `β` whose potential lies between
`t₀` and `log R`. -/
theorem mem_rayPiece_iff {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (β t₀ R : ℝ) (z : ℂ) :
    z ∈ Work.EL.rayPiece hN β t₀ R ↔
      z ∈ Work.EL.paramRay hN β ∧ t₀ ≤ Work.EL.pot hN z ∧ Work.EL.pot hN z ≤ Real.log R := by
  simp only [Work.EL.rayPiece, Work.Top.NakaneData.rayPiece, Set.mem_ofPred_eq, Work.EL.pot_apply]

theorem rayPiece_eq_image {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {β R : ℝ} (hR : 1 < R) :
    Work.EL.rayPiece hN β 0 R = (fun t : ℝ => Work.EL.rayPt hN β t) '' Set.Ioc 1 R := by
  ext z
  rw [mem_rayPiece_iff]
  constructor
  · intro hz
    obtain ⟨hzray, _hz0, hzR⟩ := hz
    change z ∈ Work.Top.NakaneData.paramRay hN β at hzray
    rw [Work.Top.NakaneData.paramRay_eq_range] at hzray
    obtain ⟨t, ht⟩ := hzray
    refine ⟨t.1, ⟨t.2, ?_⟩, ht⟩
    rw [← ht, Work.EL.pot_rayPt hN t.2] at hzR
    exact (Real.log_le_log_iff (by linarith [t.2]) (by linarith)).mp hzR
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Work.EL.rayPt_mem_paramRay hN ht.1, ?_, ?_⟩
    · rw [Work.EL.pot_rayPt hN ht.1]; exact le_of_lt (Real.log_pos (by linarith [ht.1]))
    · rw [Work.EL.pot_rayPt hN ht.1]
      exact (Real.log_le_log_iff (by linarith [ht.1]) (by linarith)).mpr ht.2

end Work.ELTop
