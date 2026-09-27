import Mathlib
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.sqDisk_surjective
import Submission.Work.Drive.sqDisk_injective

/-!
# `sqDisk ∘ foldBox` is a bijection from the unit square onto the closed disk

`Work.Drive.foldFun x = (1 - cos (π x)) / 2` is strictly increasing and continuous on `[0,1]`, with
`foldFun 0 = 0` and `foldFun 1 = 1`; hence `foldFun` is a bijection of `[0,1]` onto itself, and the
folded square coordinates `Work.Drive.foldBox` restrict to a bijection of the unit square `[0,1]²`.
Composing with the square-to-disk map `Work.Drive.sqDisk`, which is a bijection of the unit square
onto the closed unit disk (`Work.Drive.sqDisk_surjective`, `Work.Drive.sqDisk_injective`), gives the
unique-point statement below: every point of the closed disk is the image of exactly one point of the
unit square under `sqDisk ∘ foldBox`.
-/

namespace Work.Drive

open scoped Topology

/-- The fold `x ↦ (1 - cos (π x))/2` is injective on `[0,1]` (where `cos (π ·)` is strictly
antitone). -/
lemma foldFun_injOn_Icc : Set.InjOn foldFun (Set.Icc (0 : ℝ) 1) := by
  intro x hx x' hx' h
  have hcos : Real.cos (Real.pi * x) = Real.cos (Real.pi * x') := by
    simp only [foldFun] at h
    linarith
  have hxpi : Real.pi * x ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le hx.1, by nlinarith [hx.2, Real.pi_pos]⟩
  have hx'pi : Real.pi * x' ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le hx'.1, by nlinarith [hx'.2, Real.pi_pos]⟩
  have h2 := Real.strictAntiOn_cos.injOn hxpi hx'pi hcos
  exact mul_left_cancel₀ (ne_of_gt Real.pi_pos) h2

/-- The fold maps `[0,1]` onto `[0,1]` (it is continuous with `foldFun 0 = 0`, `foldFun 1 = 1`). -/
lemma foldFun_surjOn_Icc :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ x ∈ Set.Icc (0 : ℝ) 1, foldFun x = t := by
  intro t ht
  have hcont : ContinuousOn foldFun (Set.Icc (0 : ℝ) 1) :=
    foldFun_contDiff.continuous.continuousOn
  have ht' : t ∈ Set.Icc (foldFun 0) (foldFun 1) := by
    rw [foldFun_zero, foldFun_one]; exact ht
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont ht'
  exact ⟨x, hx, hxt⟩

/-- The folded square coordinates are injective on the unit square. -/
lemma foldBox_injOn_unitBox : Set.InjOn foldBox (Submission.Drive.unitBox 1) := by
  intro y hy y' hy' h
  have h0 : y 0 = y' 0 := foldFun_injOn_Icc (hy 0) (hy' 0) (by
    have := congrArg (fun w => w 0) h
    simpa [foldBox] using this)
  have h1 : y 1 = y' 1 := foldFun_injOn_Icc (hy 1) (hy' 1) (by
    have := congrArg (fun w => w 1) h
    simpa [foldBox] using this)
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- The folded square coordinates map the unit square onto itself. -/
lemma foldBox_surjOn_unitBox :
    Set.SurjOn foldBox (Submission.Drive.unitBox 1) (Submission.Drive.unitBox 1) := by
  intro y₀ hy₀
  obtain ⟨s, hs, hfs⟩ := foldFun_surjOn_Icc (y₀ 0) (hy₀ 0)
  obtain ⟨t, ht, hft⟩ := foldFun_surjOn_Icc (y₀ 1) (hy₀ 1)
  refine ⟨mk2 s t, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [mk2] using hs
    · simpa [mk2] using ht
  · rw [foldBox, mk2_apply_zero, mk2_apply_one, hfs, hft]
    exact mk2_eta y₀

/-- The composite square-to-disk parametrisation `sqDisk ∘ foldBox` is a bijection from the unit square onto the closed disk. -/
theorem sqDisk_foldBox_existsUnique (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∃! y : EuclideanSpace ℝ (Fin 2),
      y ∈ Submission.Drive.unitBox 1 ∧ sqDisk (foldBox y) = z := by
  obtain ⟨y₀, hy₀, hy₀z⟩ := sqDisk_surjective z hz
  obtain ⟨y, hy, hyfold⟩ := foldBox_surjOn_unitBox hy₀
  refine ⟨y, ⟨hy, ?_⟩, ?_⟩
  · rw [hyfold, hy₀z]
  · rintro y' ⟨hy', hy'z⟩
    have hfe : foldBox y' = foldBox y :=
      sqDisk_injective (foldBox y') (foldBox y) (foldBox_mem_unitBox y') (foldBox_mem_unitBox y)
        (by rw [hy'z, ← hy₀z, ← hyfold])
    exact foldBox_injOn_unitBox hy' hy hfe

end Work.Drive
