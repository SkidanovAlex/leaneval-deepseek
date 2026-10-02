import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open Classical Filter Set Function

/-! ## Auxiliary lemmas for the invariance of `glueMu` -/

/-- `nonEsc F R` is exactly the set of points whose orbit never reaches radius `R`. -/
theorem mem_nonEsc_iff {F : ℂ → ℂ} {R : ℝ} {z : ℂ} :
    z ∈ nonEsc F R ↔ ¬ ∃ n : ℕ, R ≤ ‖(F^[n]) z‖ := by
  simp only [nonEsc, Set.mem_setOf_eq, not_exists, not_le]

/-- The `pullIter` operator is antitone-shifted: `pullIter F (n+1) z = pullRev (pullIter F n) F z`. -/
theorem pullIter_succ (F : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    pullIter F (n + 1) z = Work.MRMT.Found.pullRev (pullIter F n) F z := by
  show (fun ν : ℂ → ℂ => Work.MRMT.Found.pullRev ν F)^[n + 1] 0 z = _
  rw [Function.iterate_succ_apply']
  rfl

/-- `pullIter F 0` is the zero coefficient. -/
theorem pullIter_zero (F : ℂ → ℂ) (z : ℂ) : pullIter F 0 z = 0 := rfl

/-- `pullRev` only depends on the value of the coefficient at `F z`. -/
theorem pullRev_congr {F : ℂ → ℂ} {ν ν' : ℂ → ℂ} {z : ℂ}
    (h : ν (F z) = ν' (F z)) :
    Work.MRMT.Found.pullRev ν F z = Work.MRMT.Found.pullRev ν' F z := by
  unfold Work.MRMT.Found.pullRev
  rw [h]

/-- Unfolding of `glueMu` at a point that does hit the far region. -/
theorem glueMu_eq_pullIter {F : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (h : ∃ n : ℕ, R ≤ ‖(F^[n]) z‖) :
    glueMu F R z = pullIter F (Nat.find h) z := dif_pos h

/-- Unfolding of `glueMu` at a point that never hits the far region. -/
theorem glueMu_of_not_hit {F : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (h : ¬ ∃ n : ℕ, R ≤ ‖(F^[n]) z‖) : glueMu F R z = 0 := dif_neg h

/-- Stepping the orbit forward shifts the hitting condition by one. -/
theorem hit_shift {F : ℂ → ℂ} {R : ℝ} {z : ℂ} {n : ℕ} :
    R ≤ ‖(F^[n + 1]) z‖ ↔ R ≤ ‖(F^[n]) (F z)‖ := by
  rw [Function.iterate_succ_apply]

/-- If `z` hits the far region first at time `m + 1`, then `F z` hits it first at time `m`. -/
theorem glueMu_forward {F : ℂ → ℂ} {R : ℝ} {z : ℂ} (hz : ∃ n : ℕ, R ≤ ‖(F^[n]) z‖)
    {m : ℕ} (hm : Nat.find hz = m + 1) :
    glueMu F R (F z) = pullIter F m (F z) := by
  have hspec : R ≤ ‖(F^[m]) (F z)‖ := by
    have := Nat.find_spec hz
    rw [hm, Function.iterate_succ_apply] at this
    exact this
  have hzF : ∃ n : ℕ, R ≤ ‖(F^[n]) (F z)‖ := ⟨m, hspec⟩
  have hfind : Nat.find hzF = m := by
    refine le_antisymm (Nat.find_min' hzF hspec) ?_
    by_contra hlt
    push_neg at hlt
    have h1 : R ≤ ‖(F^[Nat.find hzF]) (F z)‖ := Nat.find_spec hzF
    have h2 : R ≤ ‖(F^[Nat.find hzF + 1]) z‖ := by
      rw [hit_shift]; exact h1
    have h3 : Nat.find hzF + 1 < Nat.find hz := by rw [hm]; omega
    exact Nat.find_min hz h3 h2
  rw [glueMu_eq_pullIter hzF, hfind]

/-! ## The invariance of `glueMu` -/

theorem glueMu_invariant {F : ℂ → ℂ} {R : ℝ}
    (hK : ∀ z ∈ Work.FBif.nonEsc F R, Work.MRMT.dz F z = 0)
    (hfar : ∀ z : ℂ, R ≤ ‖z‖ → Work.MRMT.dz F z = 0)
    (hW : ∀ z : ℂ, R ≤ ‖z‖ → R ≤ ‖F z‖) :
    ∀ z : ℂ, Work.FBif.glueMu F R z =
      Work.MRMT.Found.pullRev (Work.FBif.glueMu F R) F z := by
  intro z
  by_cases hz : ∃ n : ℕ, R ≤ ‖(F^[n]) z‖
  · rcases Nat.eq_zero_or_pos (Nat.find hz) with h0 | hpos
    · -- the first hitting time is `0`: `z` itself is already in the far region
      have hRz : R ≤ ‖z‖ := by
        have := Nat.find_spec hz
        rw [h0, Function.iterate_zero] at this
        simpa using this
      have hdz : Work.MRMT.dz F z = 0 := hfar z hRz
      have hspec0 : R ≤ ‖(F^[0]) (F z)‖ := by
        rw [Function.iterate_zero]; simpa using hW z hRz
      have hFz : ∃ k : ℕ, R ≤ ‖(F^[k]) (F z)‖ := ⟨0, hspec0⟩
      have hfind0 : Nat.find hFz = 0 :=
        le_antisymm (Nat.find_min' hFz hspec0) (Nat.zero_le _)
      have hglue_z : glueMu F R z = 0 := by
        rw [glueMu_eq_pullIter hz, h0, pullIter_zero]
      have hglue_Fz : glueMu F R (F z) = 0 := by
        rw [glueMu_eq_pullIter hFz, hfind0, pullIter_zero]
      rw [hglue_z]
      unfold Work.MRMT.Found.pullRev
      rw [hglue_Fz, hdz]
      simp
    · -- the first hitting time is `m + 1`
      obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.find hz = m + 1 := ⟨Nat.find hz - 1, by omega⟩
      have hglue_z : glueMu F R z = Work.MRMT.Found.pullRev (pullIter F m) F z := by
        rw [glueMu_eq_pullIter hz, hm, pullIter_succ]
      have hglue_Fz : glueMu F R (F z) = pullIter F m (F z) := glueMu_forward hz hm
      rw [hglue_z]
      exact pullRev_congr hglue_Fz.symm
  · -- `z` never hits the far region
    have hzmem : z ∈ nonEsc F R := mem_nonEsc_iff.mpr hz
    have hFzmem : F z ∈ nonEsc F R := nonEsc_forward hzmem
    have hglue_z : glueMu F R z = 0 := glueMu_of_not_hit hz
    have hglue_Fz : glueMu F R (F z) = 0 :=
      glueMu_of_not_hit (mem_nonEsc_iff.mp hFzmem)
    have hdz : Work.MRMT.dz F z = 0 := hK z hzmem
    rw [hglue_z]
    unfold Work.MRMT.Found.pullRev
    rw [hglue_Fz, hdz]
    simp

end Work.FBif
