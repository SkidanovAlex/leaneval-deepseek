import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Smooth.Morse.Immersion.isImmersion

/-!
# The box width and the cutting points of the thin slab

Elementary bookkeeping for the thin-slab tilt data: the width `boxWidth s σ v` of the box
`PBox s c σ` in the direction `v` (the supremum of `⟪v, y - c⟫` over the box), and the *cutting
points* witnessing that a slab `{|⟪v,·⟫ - (⟪v,c⟫ + u)| ≤ h}` with `h < boxWidth s σ v - |u|`
really cuts the box — there are points of `PBox s c σ` strictly above and strictly below it.

Used by `Work.Drive.Mono.ThinSlabData_holds` and by `Work.Drive.Mono.BandData`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

noncomputable section


theorem inner_eq_sum (v w : R3) : inner ℝ v w = ∑ j : Fin 3, w j * v j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.inner_apply]
  simp

/-- The supremum of `⟪v, y - c⟫` over the open box `PBox s c σ`. -/
def boxWidth (s : ℝ) (σ : Equiv.Perm (Fin 3)) (v : R3) : ℝ :=
  ∑ i : Fin 3, Submission.boxSide i * s * |inner ℝ v (EuclideanSpace.single (σ i) (1 : ℝ))|

theorem boxWidth_eq (s : ℝ) (σ : Equiv.Perm (Fin 3)) (v : R3) :
    boxWidth s σ v = ∑ j : Fin 3, Submission.boxSide (σ.symm j) * s * |v j| := by
  rw [boxWidth]
  rw [← Equiv.sum_comp σ (fun i : Fin 3 => Submission.boxSide (σ.symm i) * s * |v i|)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_single_right]
  simp

theorem boxWidth_nonneg (s : ℝ) (hs : 0 < s) (σ : Equiv.Perm (Fin 3)) (v : R3) :
    0 ≤ boxWidth s σ v :=
  Finset.sum_nonneg fun i _ => by
    have h := Submission.boxSide_pos i
    exact mul_nonneg (mul_nonneg (le_of_lt h) (le_of_lt hs)) (abs_nonneg _)

theorem boxWidth_lower (s : ℝ) (hs : 0 < s) (σ : Equiv.Perm (Fin 3)) (v : R3) :
    Submission.boxSide 2 * s * |inner ℝ v (Work.BoxShrink.shiftVσ σ 1)| ≤ boxWidth s σ v := by
  have h := Finset.single_le_sum (f := fun i : Fin 3 =>
    Submission.boxSide i * s * |inner ℝ v (EuclideanSpace.single (σ i) (1 : ℝ))|)
    (fun i _ => by
      have hb := Submission.boxSide_pos i
      exact mul_nonneg (mul_nonneg (le_of_lt hb) (le_of_lt hs)) (abs_nonneg _))
    (Finset.mem_univ (σ.symm (σ 2)))
  have he : Work.BoxShrink.shiftVσ σ 1 = EuclideanSpace.single (σ 2) (1 : ℝ) := by
    ext m; rw [Work.BoxShrink.shiftVσ_apply]; simp [PiLp.single_apply]
  rw [boxWidth]
  simpa [he, Equiv.apply_symm_apply] using h

theorem boxWidth_ge (s : ℝ) (hs : 0 < s) (σ : Equiv.Perm (Fin 3)) {v : R3}
    (hv : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8) :
    7 / 8 * s ≤ boxWidth s σ v := by
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have he1 : ‖e‖ = 1 := Work.Drive.EpsForm.norm_shiftVσ_one σ
  have h2 : 7 / 8 ≤ |inner ℝ v e| := by
    have hc : inner ℝ v e = 1 - inner ℝ (e - v) e := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, he1]; norm_num
    have hb : |inner ℝ (e - v) e| ≤ 1 / 8 := by
      have h6 := abs_real_inner_le_norm (e - v) e
      rw [he1, mul_one] at h6
      have h7 : ‖e - v‖ = ‖v - e‖ := (norm_sub_rev v e).symm
      rw [h7] at h6
      exact le_trans h6 hv
    have h9 : (1:ℝ) - |inner ℝ (e - v) e| ≤ |inner ℝ v e| := by
      rw [hc]
      have := abs_sub_abs_le_abs_sub (1:ℝ) (inner ℝ (e - v) e)
      simpa using this
    linarith
  have h1 := boxWidth_lower s hs σ v
  have hb2 : 1 ≤ Submission.boxSide 2 := Submission.one_le_boxSide 2
  have hA : 0 ≤ |inner ℝ v e| * s := mul_nonneg (abs_nonneg _) (le_of_lt hs)
  calc 7 / 8 * s = 7 / 8 * s * 1 := by ring
    _ ≤ |inner ℝ v e| * s * 1 := by nlinarith [h2, hs]
    _ ≤ |inner ℝ v e| * s * Submission.boxSide 2 := by nlinarith [hA, hb2]
    _ = Submission.boxSide 2 * s * |inner ℝ v e| := by ring
    _ = Submission.boxSide 2 * s * |inner ℝ v (Work.BoxShrink.shiftVσ σ 1)| := by rw [he]
    _ ≤ boxWidth s σ v := h1

/-- The corner point of the box in the direction of the signs of `⟪v, e_{σ i}⟫`, scaled by `t`. -/
def cutPoint (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (t : ℝ) : R3 :=
  c + WithLp.toLp 2 (fun j : Fin 3 =>
    if 0 ≤ v j then t * (Submission.boxSide (σ.symm j) * s)
      else -(t * (Submission.boxSide (σ.symm j) * s)))

theorem cutPoint_apply (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (t : ℝ) (j : Fin 3) :
    cutPoint s c σ v t j =
      c j + (if 0 ≤ v j then t * (Submission.boxSide (σ.symm j) * s)
        else -(t * (Submission.boxSide (σ.symm j) * s))) := by
  rw [cutPoint]; simp

theorem cutPoint_sub (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (t : ℝ) (i : Fin 3) :
    (cutPoint s c σ v t - c) (σ i) =
      (if 0 ≤ v (σ i) then t * (Submission.boxSide i * s)
        else -(t * (Submission.boxSide i * s))) := by
  rw [PiLp.sub_apply, cutPoint_apply]
  simp

theorem cutPoint_mem_PBox (s : ℝ) (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : cutPoint s c σ v t ∈ Submission.PBox s c σ := by
  rw [Submission.mem_PBox]
  intro i
  rw [cutPoint_apply]
  simp only [Equiv.symm_apply_apply, add_sub_cancel_left]
  have hb : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
  split_ifs with hh
  · rw [abs_of_nonneg (by positivity)]; nlinarith
  · rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith

theorem inner_cutPoint (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (t : ℝ) :
    inner ℝ v (cutPoint s c σ v t - c) = t * boxWidth s σ v := by
  rw [inner_eq_sum, boxWidth_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.sub_apply, cutPoint_apply]
  simp only [Equiv.symm_apply_apply]
  split_ifs with hj
  · rw [abs_of_nonneg hj]; ring
  · rw [abs_of_neg (lt_of_not_ge hj)]; ring


theorem exists_cut_above (s : ℝ) (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    {h u : ℝ} (hW : 0 < boxWidth s σ v) (hh : h + u < boxWidth s σ v) :
    ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y := by
  set W := boxWidth s σ v with hWdef
  set d : ℝ := (h + u) / W with hd
  have hdlt : d < 1 := by rw [hd]; exact (div_lt_one hW).mpr hh
  set t : ℝ := (max 0 d + 1) / 2 with ht
  have ht0 : 0 < t := by
    rw [ht]; have : (0:ℝ) ≤ max 0 d := le_max_left _ _; linarith
  have ht1 : t < 1 := by
    rw [ht]; have : max 0 d < 1 := max_lt (by norm_num) hdlt; linarith
  have htd : d < t := by
    rw [ht]; have : d ≤ max 0 d := le_max_right _ _; linarith
  refine ⟨cutPoint s c σ v t, cutPoint_mem_PBox s hs c σ v ht0 ht1, ?_⟩
  have hmul : h + u < t * W := by
    have h1 := mul_lt_mul_of_pos_right htd hW
    rwa [hd, div_mul_cancel₀ _ (ne_of_gt hW)] at h1
  rw [show cutPoint s c σ v t = c + (cutPoint s c σ v t - c) from by abel, inner_add_right]
  rw [inner_cutPoint]
  linarith

theorem exists_cut_below (s : ℝ) (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    {h u : ℝ} (hW : 0 < boxWidth s σ v) (hh : h - u < boxWidth s σ v) :
    ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h := by
  set W := boxWidth s σ v with hWdef
  set d : ℝ := (h - u) / W with hd
  have hdlt : d < 1 := by rw [hd]; exact (div_lt_one hW).mpr hh
  set t : ℝ := (max 0 d + 1) / 2 with ht
  have ht0 : 0 < t := by
    rw [ht]; have : (0:ℝ) ≤ max 0 d := le_max_left _ _; linarith
  have ht1 : t < 1 := by
    rw [ht]; have : max 0 d < 1 := max_lt (by norm_num) hdlt; linarith
  have htd : d < t := by
    rw [ht]; have : d ≤ max 0 d := le_max_right _ _; linarith
  have hmul : h - u < t * W := by
    have h1 := mul_lt_mul_of_pos_right htd hW
    rwa [hd, div_mul_cancel₀ _ (ne_of_gt hW)] at h1
  refine ⟨2 • c - cutPoint s c σ v t, ?_, ?_⟩
  · rw [Submission.mem_PBox]
    intro i
    have hmem := cutPoint_mem_PBox s hs c σ v ht0 ht1
    have hcoord : 2 • c - cutPoint s c σ v t - c = -(cutPoint s c σ v t - c) := by abel
    show |(2 • c - cutPoint s c σ v t - c) (σ i)| < Submission.boxSide i * s
    rw [hcoord]
    simpa [abs_sub_comm] using hmem i
  · have h2 : inner ℝ v (2 • c - cutPoint s c σ v t)
        = inner ℝ v c - inner ℝ v (cutPoint s c σ v t - c) := by
      have hcoord : 2 • c - cutPoint s c σ v t = c - (cutPoint s c σ v t - c) := by abel
      rw [hcoord, inner_sub_right]
    have h3 : inner ℝ v (cutPoint s c σ v t - c) = t * W := by
      rw [inner_cutPoint, hWdef]
    rw [h3] at h2
    linarith



end

end Work.Drive.Mono
