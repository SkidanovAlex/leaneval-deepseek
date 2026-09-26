import Mathlib
import Submission.Work.Drive.Mono.SlabCaps

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

noncomputable section

/-- The closure of Pardon's box is contained in the *closed* box, coordinate by coordinate. -/
theorem closure_PBox_coord_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} :
    closure (Submission.PBox s c σ) ⊆
      {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
  refine closure_minimal (fun y hy i => le_of_lt (hy i)) ?_
  have hset : {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s}
      = ⋂ i, {y : R3 | |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
    ext y; simp
  rw [hset]
  exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)

/-- **A convex combination of an interior point and a closed-box point is interior**, the strictness
coming from the interior point.  (`θ • y + (1 - θ) • z` for `0 < θ < 1`.) -/
theorem smul_combo_mem_PBox {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y z : R3}
    (hy : y ∈ Submission.PBox s c σ)
    (hz : ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s)
    {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) :
    θ • y + (1 - θ) • z ∈ Submission.PBox s c σ := by
  intro i
  have h1i : |y (σ i) - c (σ i)| < Submission.boxSide i * s := hy i
  have h2i : |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s := hz i
  calc |(θ • y + (1 - θ) • z) (σ i) - c (σ i)|
      = |θ * (y (σ i) - c (σ i)) + (1 - θ) * (z (σ i) - c (σ i))| := by
        congr 1
        simp
        ring
    _ ≤ |θ * (y (σ i) - c (σ i))| + |(1 - θ) * (z (σ i) - c (σ i))| := abs_add_le _ _
    _ = θ * |y (σ i) - c (σ i)| + (1 - θ) * |z (σ i) - c (σ i)| := by
        rw [abs_mul, abs_mul, abs_of_pos hθ, abs_of_pos (by linarith : (0 : ℝ) < 1 - θ)]
    _ < θ * (Submission.boxSide i * s) + (1 - θ) * (Submission.boxSide i * s) := by
        have hlt : θ * |y (σ i) - c (σ i)| < θ * (Submission.boxSide i * s) :=
          mul_lt_mul_of_pos_left h1i hθ
        have hle : (1 - θ) * |z (σ i) - c (σ i)| ≤ (1 - θ) * (Submission.boxSide i * s) :=
          mul_le_mul_of_nonneg_left h2i (by linarith)
        linarith
    _ = Submission.boxSide i * s := by ring

/-- The distance from a convex combination to its closed-box end. -/
theorem dist_smul_combo (y z : R3) {θ : ℝ} (hθ : 0 < θ) :
    dist (θ • y + (1 - θ) • z) z = θ * dist y z := by
  have key : θ • y + (1 - θ) • z = z + θ • (y - z) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  calc dist (θ • y + (1 - θ) • z) z = dist (z + θ • (y - z)) z := by rw [key]
    _ = ‖θ • (y - z)‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    _ = θ * ‖y - z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
    _ = θ * dist y z := by rw [dist_eq_norm]

/-- `inner` is affine on the segment `θ • y + (1 - θ) • z`. -/
theorem inner_smul_combo (v y z : R3) (θ a : ℝ) :
    inner ℝ v (θ • y + (1 - θ) • z) - a
      = θ * (inner ℝ v y - a) + (1 - θ) * (inner ℝ v z - a) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  ring

/-- **There is a point of the open box on the segment towards an interior point, arbitrarily close
to the closed-box end.** -/
theorem exists_smul_combo_mem_PBox_near {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y z : R3}
    (hy : y ∈ Submission.PBox s c σ)
    (hz : ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ θ • y + (1 - θ) • z ∈ Submission.PBox s c σ ∧
      dist (θ • y + (1 - θ) • z) z < ε := by
  have hd0 : 0 ≤ dist y z := dist_nonneg
  have hden : 0 < 2 * (dist y z + 1) := by linarith
  have hθ0 : 0 < min (1 / 2 : ℝ) (ε / (2 * (dist y z + 1))) :=
    lt_min (by norm_num) (div_pos hε hden)
  have hθ1 : min (1 / 2 : ℝ) (ε / (2 * (dist y z + 1))) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨min (1 / 2 : ℝ) (ε / (2 * (dist y z + 1))), hθ0, hθ1,
    smul_combo_mem_PBox hy hz hθ0 hθ1, ?_⟩
  rw [dist_smul_combo y z hθ0]
  have key : (ε / (2 * (dist y z + 1))) * dist y z < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [hε, hd0]
  calc min (1 / 2 : ℝ) (ε / (2 * (dist y z + 1))) * dist y z
      ≤ (ε / (2 * (dist y z + 1))) * dist y z :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hd0
    _ < ε := key

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem exists_mem_PBox_abs_inner_gt_near {s a h : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v z : R3}
    (hcut : Work.Drive.Mono.SlabCutsBox s c σ a h v) (hz : z ∈ closure (Submission.PBox s c σ))
    (hzface : h ≤ |inner ℝ v z - a|) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ Submission.PBox s c σ, dist u z < ε ∧ h < |inner ℝ v u - a| := by
  obtain ⟨yp, hyp_mem, hyp_gt⟩ := hcut.1
  obtain ⟨ym, hym_mem, hym_lt⟩ := hcut.2
  have hzc : ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s :=
    closure_PBox_coord_le hz
  by_cases hh : h < 0
  · -- `h` is negative, so the strict inequality in the absolute value is free
    obtain ⟨θ, hθ0, hθ1, hmem, hdist⟩ := exists_smul_combo_mem_PBox_near hyp_mem hzc hε
    exact ⟨θ • yp + (1 - θ) • z, hmem, hdist, lt_of_lt_of_le hh (abs_nonneg _)⟩
  · push Not at hh
    by_cases hA : h ≤ inner ℝ v z - a
    · -- the point `z` sits on the upper side: move towards the upper interior point
      obtain ⟨θ, hθ0, hθ1, hmem, hdist⟩ := exists_smul_combo_mem_PBox_near hyp_mem hzc hε
      refine ⟨θ • yp + (1 - θ) • z, hmem, hdist, ?_⟩
      have hinner := inner_smul_combo v yp z θ a
      have hgt : h < inner ℝ v (θ • yp + (1 - θ) • z) - a := by
        rw [hinner]
        nlinarith [hyp_gt, hA, hθ0, hθ1]
      exact lt_of_lt_of_le hgt (le_abs_self _)
    · push Not at hA
      -- `inner v z - a < h ≤ |inner v z - a|` forces `inner v z - a ≤ -h`
      have hzle : inner ℝ v z - a ≤ -h := by
        rcases lt_or_ge (inner ℝ v z - a) 0 with hx | hx
        · rw [abs_of_neg hx] at hzface; linarith
        · rw [abs_of_nonneg hx] at hzface; linarith
      -- move towards the lower interior point
      obtain ⟨θ, hθ0, hθ1, hmem, hdist⟩ := exists_smul_combo_mem_PBox_near hym_mem hzc hε
      refine ⟨θ • ym + (1 - θ) • z, hmem, hdist, ?_⟩
      have hinner := inner_smul_combo v ym z θ a
      have hlt : inner ℝ v (θ • ym + (1 - θ) • z) - a < -h := by
        rw [hinner]
        nlinarith [hym_lt, hzle, hθ0, hθ1]
      have hneg : inner ℝ v (θ • ym + (1 - θ) • z) - a < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith

end

end Work.Drive.Mono
