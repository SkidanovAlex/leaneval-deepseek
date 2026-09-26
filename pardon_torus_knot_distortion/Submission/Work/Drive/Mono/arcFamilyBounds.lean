import Mathlib
import Submission.Work.Drive.Mono.NoGrazeDefs

/-!
# Uniform derivative bounds for a finite family of `C³` curves

Let `γ : Fin N → ℝ → R3` be a finite family of curves, each `C³` on the closed interval
`[-η, η]` with `η > 0`.  Then there are constants `M1, M2, M4 > 0` (depending on the family and on
`η` only) such that on the half interval `|t| ≤ η/2`:

* the velocity is bounded: `‖γ k ' t‖ ≤ M1`;
* the velocity is Lipschitz: `‖γ k ' t - γ k ' 0‖ ≤ M2 * |t|`;
* and, if the acceleration of `γ k` vanishes at `0`, the velocity is *quadratic* at `0`:
  `‖γ k ' t - γ k ' 0‖ ≤ M4 * t ^ 2`.

The proof is compactness plus the mean value inequality:

* `γ k` is `C³` on the open interval `(-η, η)`, hence so are `γ k'`, `γ k''` and `γ k'''`; the
  first three derivatives are therefore continuous, hence bounded, on the compact set
  `[-η/2, η/2]`;
* one application of the mean value inequality to `γ k'` (whose derivative `γ k''` is bounded)
  gives the Lipschitz bound;
* two applications of the mean value inequality, to `γ k''` (whose derivative `γ k'''` is bounded)
  and then to `γ k'`, give the quadratic bound when `γ k'' 0 = 0`.

The constants are made uniform in `k` by summing the finitely many per-curve constants.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace

noncomputable section

/-! ## The mean value inequality, twice

If `‖deriv (deriv w)‖ ≤ M` on `[a, b]` and `deriv w` vanishes at one endpoint, then `w` moves by
at most `M (b - a)²` across `[a, b]`.  These are the `[a,b]`-local versions of the corresponding
estimates in `Submission/Work/Drive/Mono/exists_uniform_sq_bound_vertVel.lean`. -/

theorem norm_sub_le_sq_local_left {w : ℝ → R3} {a b M : ℝ} (hab : a ≤ b)
    (hw : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ w x)
    (hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (deriv w) x)
    (hM : ∀ x ∈ Set.Icc a b, ‖deriv (deriv w) x‖ ≤ M)
    (h0 : deriv w a = 0) : ‖w b - w a‖ ≤ M * (b - a) ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM a (left_mem_Icc.mpr hab))
  have hbd : ∀ x ∈ Set.Icc a b, ‖deriv w x‖ ≤ M * (b - a) := by
    intro x hx
    have hax : a ≤ x := hx.1
    have hxb : x ≤ b := hx.2
    have hsub : Set.Icc a x ⊆ Set.Icc a b := fun y hy => ⟨hy.1, le_trans hy.2 hxb⟩
    have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv w) (s := Set.Icc a x)
      (C := M) (fun y hy => hd y (hsub hy)) (fun y hy => hM y (hsub hy)) (convex_Icc a x)
      (left_mem_Icc.mpr hax) (right_mem_Icc.mpr hax)
    simp only [h0, sub_zero, Real.norm_eq_abs] at key
    calc ‖deriv w x‖ ≤ M * |x - a| := key
      _ = M * (x - a) := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - a)]
      _ ≤ M * (b - a) := mul_le_mul_of_nonneg_left (by linarith) hM0
  have key2 := Convex.norm_image_sub_le_of_norm_deriv_le (f := w) (s := Set.Icc a b)
    (C := M * (b - a)) (fun x hx => hw x hx) hbd (convex_Icc a b)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at key2
  calc ‖w b - w a‖ ≤ (M * (b - a)) * (b - a) := key2
    _ = M * (b - a) ^ 2 := by ring

theorem norm_sub_le_sq_local_right {w : ℝ → R3} {a b M : ℝ} (hab : a ≤ b)
    (hw : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ w x)
    (hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (deriv w) x)
    (hM : ∀ x ∈ Set.Icc a b, ‖deriv (deriv w) x‖ ≤ M)
    (h0 : deriv w b = 0) : ‖w b - w a‖ ≤ M * (b - a) ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM b (right_mem_Icc.mpr hab))
  have hbd : ∀ x ∈ Set.Icc a b, ‖deriv w x‖ ≤ M * (b - a) := by
    intro x hx
    have hax : a ≤ x := hx.1
    have hxb : x ≤ b := hx.2
    have hsub : Set.Icc x b ⊆ Set.Icc a b := fun y hy => ⟨le_trans hax hy.1, hy.2⟩
    have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv w) (s := Set.Icc x b)
      (C := M) (fun y hy => hd y (hsub hy)) (fun y hy => hM y (hsub hy)) (convex_Icc x b)
      (right_mem_Icc.mpr hxb) (left_mem_Icc.mpr hxb)
    simp only [h0, sub_zero, Real.norm_eq_abs] at key
    calc ‖deriv w x‖ ≤ M * |x - b| := key
      _ = M * (b - x) := by rw [abs_of_nonpos (by linarith : x - b ≤ 0)]; ring
      _ ≤ M * (b - a) := mul_le_mul_of_nonneg_left (by linarith) hM0
  have key2 := Convex.norm_image_sub_le_of_norm_deriv_le (f := w) (s := Set.Icc a b)
    (C := M * (b - a)) (fun x hx => hw x hx) hbd (convex_Icc a b)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at key2
  calc ‖w b - w a‖ ≤ (M * (b - a)) * (b - a) := key2
    _ = M * (b - a) ^ 2 := by ring

/-! ## The bounds for a single curve -/

/-- For a single curve `w` which is `C³` on `[-η, η]` there are constants `C1, C2 ≥ 0` bounding,
on `|t| ≤ η/2`, the velocity (`C1`), the oscillation of the velocity (`C2`), and — when the
acceleration at `0` vanishes — the oscillation of the velocity quadratically (`C2` again). -/
theorem arcBounds_of_contDiffOn {w : ℝ → R3} {η : ℝ} (hη : 0 < η)
    (hw : ContDiffOn ℝ 3 w (Set.Icc (-η) η)) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧
      (∀ t : ℝ, |t| ≤ η / 2 → ‖deriv w t‖ ≤ C1) ∧
      (∀ t : ℝ, |t| ≤ η / 2 → ‖deriv w t - deriv w 0‖ ≤ C2 * |t|) ∧
      (deriv (deriv w) 0 = 0 →
        ∀ t : ℝ, |t| ≤ η / 2 → ‖deriv w t - deriv w 0‖ ≤ C2 * t ^ 2) := by
  have hsub : Set.Icc (-(η/2)) (η/2) ⊆ Set.Ioo (-η) η := fun x hx =>
    ⟨by linarith [hx.1, hη], by linarith [hx.2, hη]⟩
  have hw' : ContDiffOn ℝ 3 w (Set.Ioo (-η) η) := hw.mono Set.Ioo_subset_Icc_self
  have hd1 : ContDiffOn ℝ 2 (deriv w) (Set.Ioo (-η) η) :=
    hw'.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2 : ContDiffOn ℝ 1 (deriv (deriv w)) (Set.Ioo (-η) η) :=
    hd1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd3 : ContDiffOn ℝ 0 (deriv (deriv (deriv w))) (Set.Ioo (-η) η) :=
    hd2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hc1 : ContinuousOn (deriv w) (Set.Icc (-(η/2)) (η/2)) := hd1.continuousOn.mono hsub
  have hc2 : ContinuousOn (deriv (deriv w)) (Set.Icc (-(η/2)) (η/2)) := hd2.continuousOn.mono hsub
  have hc3 : ContinuousOn (deriv (deriv (deriv w))) (Set.Icc (-(η/2)) (η/2)) :=
    hd3.continuousOn.mono hsub
  obtain ⟨c1, hc1b⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨c2, hc2b⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  obtain ⟨c3, hc3b⟩ := isCompact_Icc.exists_bound_of_continuousOn hc3
  have hfd1 : ∀ x ∈ Set.Icc (-(η/2)) (η/2), DifferentiableAt ℝ (deriv w) x :=
    fun x hx =>
      (hd1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
  have hfd2 : ∀ x ∈ Set.Icc (-(η/2)) (η/2), DifferentiableAt ℝ (deriv (deriv w)) x :=
    fun x hx =>
      (hd2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
  have h0S : (0:ℝ) ∈ Set.Icc (-(η/2)) (η/2) := ⟨by linarith, by linarith⟩
  refine ⟨max c1 0, max (max c2 0) (max c3 0), le_max_right _ _, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_right c2 0) (le_max_left _ _)
  · intro t ht
    have htS : t ∈ Set.Icc (-(η/2)) (η/2) := by
      rw [abs_le] at ht; exact ⟨ht.1, ht.2⟩
    exact le_trans (hc1b t htS) (le_max_left _ _)
  · intro t ht
    have htS : t ∈ Set.Icc (-(η/2)) (η/2) := by
      rw [abs_le] at ht; exact ⟨ht.1, ht.2⟩
    have hbd : ∀ x ∈ Set.Icc (-(η/2)) (η/2),
        ‖deriv (deriv w) x‖ ≤ max (max c2 0) (max c3 0) :=
      fun x hx => le_trans (hc2b x hx) (le_trans (le_max_left c2 0) (le_max_left _ _))
    have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv w)
      (s := Set.Icc (-(η/2)) (η/2)) (C := max (max c2 0) (max c3 0)) hfd1 hbd
      (convex_Icc _ _) h0S htS
    rwa [sub_zero, Real.norm_eq_abs] at key
  · intro h0zero t ht
    have htS : t ∈ Set.Icc (-(η/2)) (η/2) := by
      rw [abs_le] at ht; exact ⟨ht.1, ht.2⟩
    have hbd3 : ∀ x ∈ Set.Icc (-(η/2)) (η/2),
        ‖deriv (deriv (deriv w)) x‖ ≤ max (max c2 0) (max c3 0) :=
      fun x hx => le_trans (hc3b x hx) (le_trans (le_max_left c3 0) (le_max_right _ _))
    rcases le_total 0 t with hle | hle
    · have hsub2 : Set.Icc 0 t ⊆ Set.Icc (-(η/2)) (η/2) :=
        fun y hy => ⟨le_trans h0S.1 hy.1, le_trans hy.2 htS.2⟩
      have key := norm_sub_le_sq_local_left (w := deriv w) (a := 0) (b := t)
        (M := max (max c2 0) (max c3 0)) hle
        (fun y hy => hfd1 y (hsub2 hy)) (fun y hy => hfd2 y (hsub2 hy))
        (fun y hy => hbd3 y (hsub2 hy)) h0zero
      rwa [sub_zero] at key
    · have hsub2 : Set.Icc t 0 ⊆ Set.Icc (-(η/2)) (η/2) :=
        fun y hy => ⟨le_trans htS.1 hy.1, le_trans hy.2 h0S.2⟩
      have key := norm_sub_le_sq_local_right (w := deriv w) (a := t) (b := 0)
        (M := max (max c2 0) (max c3 0)) hle
        (fun y hy => hfd1 y (hsub2 hy)) (fun y hy => hfd2 y (hsub2 hy))
        (fun y hy => hbd3 y (hsub2 hy)) h0zero
      have h1 : ‖deriv w t - deriv w 0‖ = ‖deriv w 0 - deriv w t‖ := norm_sub_rev _ _
      rw [h1]
      calc ‖deriv w 0 - deriv w t‖ ≤ max (max c2 0) (max c3 0) * (0 - t) ^ 2 := key
        _ = max (max c2 0) (max c3 0) * t ^ 2 := by ring

/-! ## Uniformity in the family -/

theorem arcFamilyBounds {N : ℕ} {γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    {η : ℝ} (hη : 0 < η)
    (hγ : ∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η)) :
    ∃ M1 M2 M4 : ℝ, 0 < M1 ∧ 0 < M2 ∧ 0 < M4 ∧
      ∀ k (t : ℝ), t ∈ Set.Ioo (-η) η → |t| ≤ η / 2 →
        ‖deriv (γ k) t‖ ≤ M1 ∧
        ‖deriv (γ k) t - deriv (γ k) 0‖ ≤ M2 * |t| ∧
        (deriv (deriv (γ k)) 0 = 0 →
          ‖deriv (γ k) t - deriv (γ k) 0‖ ≤ M4 * t ^ 2) := by
  classical
  choose C1 C2 hC1 hC2 hb1 hb2 hb4 using fun k => arcBounds_of_contDiffOn (w := γ k) hη (hγ k)
  have hsum1 : 0 ≤ ∑ k : Fin N, C1 k := Finset.sum_nonneg (fun k _ => hC1 k)
  have hsum2 : 0 ≤ ∑ k : Fin N, C2 k := Finset.sum_nonneg (fun k _ => hC2 k)
  refine ⟨1 + ∑ k : Fin N, C1 k, 1 + ∑ k : Fin N, C2 k, 1 + ∑ k : Fin N, C2 k,
    by linarith, by linarith, by linarith, ?_⟩
  intro k t _ht htk
  have hle1 : C1 k ≤ ∑ k : Fin N, C1 k :=
    Finset.single_le_sum (fun b _ => hC1 b) (Finset.mem_univ k)
  have hle2 : C2 k ≤ ∑ k : Fin N, C2 k :=
    Finset.single_le_sum (fun b _ => hC2 b) (Finset.mem_univ k)
  exact ⟨le_trans (hb1 k t htk) (by linarith),
    le_trans (hb2 k t htk) (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg t)),
    fun h0 => le_trans (hb4 k h0 t htk)
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t))⟩

end

end Work.Drive.Mono
