import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.vertical_ray_shift
import Submission.Work.CKFinal.LineDecay.Khat_second_residue
import Submission.Work.CKFinal.LineDecay.Kfun_second_limits
import Submission.Work.CKFinal.LineDecay.Khat_ray_far_bound
import Submission.Work.CKFinal.LineDecay.khat_shift_cont_diff
import Submission.Work.CKFinal.LineDecay.khat_strip_orbit
import Submission.Work.CKFinal.LineDecay.F1Half.Basic
import Submission.Work.CKFinal.LineDecay.shift_ray_center_minus_aux
import Submission.Work.CKFinal.LineDecay.f2fun_khat_top_edge
import Submission.Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two

/-!
# The two half-strip shifts for `K̂`, with the weak growth hypotheses

The sibling lemmas `shift_ray_center_minus` / `shift_ray_center_plus` assume the growth of `K̂`
on the whole strip `|Re| ≤ 1`, `Im ≥ 1`.  Here the same identities are proved from the two
weaker bounds supplied by `Work.CKFinal.LineDecay.Khat_ray_far_bound`: the ray bound (for the
integrability of the two vertical tails) and the far-strip bound (for the decay of the top
edge).  No bound between heights `1` and `T` is needed.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

/-! ## The top edges -/

/-- `‖kerExp r (x + iR)‖ = e^{-πr²R}`. -/
lemma norm_kerExp_of_add_mul_I (r x R : ℝ) :
    ‖Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)‖
      = Real.exp (-(Real.pi * r ^ 2 * R)) := by
  rw [Work.Asymptotics.kerExp, Complex.norm_exp]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The top edge of the `K̂(τ, ·+1)` shift decays**, from the far-strip bound. -/
lemma topEdge_weak_plus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C T : ℝ} {M : ℕ} (hr : 2 < r ^ 2) (hC : 0 ≤ C) (hT : 0 < T)
    (hfar : ∀ (x t : ℝ), -1 ≤ x → x ≤ 1 → T ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    Filter.Tendsto (fun R : ℝ => ∫ x in (-1 : ℝ)..0,
        Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I + 1))
          * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
  set c : ℝ := Real.pi * (r ^ 2 - 2) with hcdef
  have hc : 0 < c := by
    rw [hcdef]; exact mul_pos Real.pi_pos (by linarith)
  have hpt : ∀ x R : ℝ, -1 ≤ x → x ≤ 0 → T ≤ R →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I + 1))
        * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)‖
        ≤ C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R)) := by
    intro x R hx1 hx2 hR
    have hz : (x : ℂ) + (R : ℂ) * Complex.I + 1 = ((x + 1 : ℝ) : ℂ) + (R : ℂ) * Complex.I := by
      push_cast; ring
    have hK := hfar (x + 1) R (by linarith) (by linarith) hR
    have hK' : ‖Work.Kernels.Khat ℓ d τ
        (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I + 1))‖
        ≤ C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) := by
      rw [hz]; exact hK
    simp only [norm_mul, norm_kerExp_of_add_mul_I]
    exact mul_le_mul_of_nonneg_right hK' (Real.exp_nonneg _)
  have hint : ∀ R : ℝ, T ≤ R →
      ‖∫ x in (-1 : ℝ)..0, Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I + 1))
          * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)‖
        ≤ C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R)) := by
    intro R hR
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := (0 : ℝ))
      (C := C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R)))
      (f := fun x : ℝ => Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I + 1))
          * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
        exact hpt x R (le_of_lt hx.1) (by linarith [hx.2]) hR)
    rwa [show |(0 : ℝ) - (-1)| = 1 by norm_num, mul_one] at h
  have hkey : ∀ R : ℝ, C * ((1 + R) ^ M * Real.exp (-(c * R)))
      = C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R)) := by
    intro R
    have hE : Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R))
        = Real.exp (-(c * R)) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    calc C * ((1 + R) ^ M * Real.exp (-(c * R)))
        = C * ((1 + R) ^ M * (Real.exp (2 * Real.pi * R)
            * Real.exp (-(Real.pi * r ^ 2 * R)))) := by rw [hE]
      _ = C * (1 + R) ^ M * Real.exp (2 * Real.pi * R)
            * Real.exp (-(Real.pi * r ^ 2 * R)) := by ring
  have hmain : Filter.Tendsto (fun R : ℝ => C * (1 + R) ^ M * Real.exp (2 * Real.pi * R)
      * Real.exp (-(Real.pi * r ^ 2 * R))) Filter.atTop (nhds 0) := by
    have h := (tendsto_one_add_pow_mul_exp_neg M c hc).const_mul C
    simp only [mul_zero] at h
    exact h.congr' (by filter_upwards with R; exact hkey R)
  refine squeeze_zero_norm' ?_ hmain
  filter_upwards [eventually_ge_atTop T] with R hR
  exact hint R hR

/-- **The top edge of the `K̂(τ, ·-1)` shift decays**, from the far-strip bound. -/
lemma topEdge_weak_minus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C T : ℝ} {M : ℕ} (hr : 2 < r ^ 2) (hC : 0 ≤ C) (hT : 0 < T)
    (hfar : ∀ (x t : ℝ), -1 ≤ x → x ≤ 1 → T ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..1,
        Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I - 1))
          * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
  set c : ℝ := Real.pi * (r ^ 2 - 2) with hcdef
  have hc : 0 < c := by
    rw [hcdef]; exact mul_pos Real.pi_pos (by linarith)
  have hpt : ∀ x R : ℝ, 0 ≤ x → x ≤ 1 → T ≤ R →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I - 1))
        * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)‖
        ≤ C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R)) := by
    intro x R hx1 hx2 hR
    have hz : (x : ℂ) + (R : ℂ) * Complex.I - 1 = ((x - 1 : ℝ) : ℂ) + (R : ℂ) * Complex.I := by
      push_cast; ring
    have hK := hfar (x - 1) R (by linarith) (by linarith) hR
    have hK' : ‖Work.Kernels.Khat ℓ d τ
        (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I - 1))‖
        ≤ C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) := by
      rw [hz]; exact hK
    simp only [norm_mul, norm_kerExp_of_add_mul_I]
    exact mul_le_mul_of_nonneg_right hK' (Real.exp_nonneg _)
  have hint : ∀ R : ℝ, T ≤ R →
      ‖∫ x in (0 : ℝ)..1, Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I - 1))
          * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)‖
        ≤ C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R)) := by
    intro R hR
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (C := C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R)))
      (f := fun x : ℝ => Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I - 1))
          * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        exact hpt x R (le_of_lt hx.1) (by linarith [hx.2]) hR)
    rwa [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at h
  have hkey : ∀ R : ℝ, C * ((1 + R) ^ M * Real.exp (-(c * R)))
      = C * (1 + R) ^ M * Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R)) := by
    intro R
    have hE : Real.exp (2 * Real.pi * R) * Real.exp (-(Real.pi * r ^ 2 * R))
        = Real.exp (-(c * R)) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    calc C * ((1 + R) ^ M * Real.exp (-(c * R)))
        = C * ((1 + R) ^ M * (Real.exp (2 * Real.pi * R)
            * Real.exp (-(Real.pi * r ^ 2 * R)))) := by rw [hE]
      _ = C * (1 + R) ^ M * Real.exp (2 * Real.pi * R)
            * Real.exp (-(Real.pi * r ^ 2 * R)) := by ring
  have hmain : Filter.Tendsto (fun R : ℝ => C * (1 + R) ^ M * Real.exp (2 * Real.pi * R)
      * Real.exp (-(Real.pi * r ^ 2 * R))) Filter.atTop (nhds 0) := by
    have h := (tendsto_one_add_pow_mul_exp_neg M c hc).const_mul C
    simp only [mul_zero] at h
    exact h.congr' (by filter_upwards with R; exact hkey R)
  refine squeeze_zero_norm' ?_ hmain
  filter_upwards [eventually_ge_atTop T] with R hR
  exact hint R hR

/-! ## The two rays -/

/-- The two vertical tails of the `K̂(τ, ·+1)` integrand are integrable. -/
lemma rays_integrable_weak_plus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C : ℝ} {M : ℕ} (hr : 2 < r ^ 2)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) (hC : 0 ≤ C)
    (hray : ∀ (x t : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → 1 ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    MeasureTheory.IntegrableOn (fun y : ℝ => Work.Kernels.Khat ℓ d τ
        (UpperHalfPlane.ofComplex (((0 : ℂ) + (y : ℂ) * Complex.I) + 1))
        * Work.Asymptotics.kerExp r ((0 : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
    ∧ MeasureTheory.IntegrableOn (fun y : ℝ => Work.Kernels.Khat ℓ d τ
        (UpperHalfPlane.ofComplex (((-1 : ℂ) + (y : ℂ) * Complex.I) + 1))
        * Work.Asymptotics.kerExp r ((-1 : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) := by
  have hp := (integrableOn_Kax_gauss_ray ℓ d hd τ hr hre him hC hray
    (Or.inr (Or.inr rfl))).mono_set Set.Ioi_subset_Ici_self
  have hm := (integrableOn_Kax_gauss_ray ℓ d hd τ hr hre him hC hray
    (Or.inr (Or.inl rfl))).mono_set Set.Ioi_subset_Ici_self
  constructor
  · refine MeasureTheory.IntegrableOn.congr_fun hp (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := by linarith [Set.mem_Ioi.mp hy]
    rw [Kax_eq_K_ofComplex _ τ 1 y hy0]
    rw [show (0 : ℂ) + (y : ℂ) * Complex.I = (y : ℂ) * Complex.I by ring, kerExp_mul_I]
    congr 2
    push_cast; ring
  · refine MeasureTheory.IntegrableOn.congr_fun
      (hm.const_mul (Work.Asymptotics.kerExp r (-1 : ℂ))) (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := by linarith [Set.mem_Ioi.mp hy]
    have h1 : Kax (Work.Kernels.Khat ℓ d) τ 0 y
        = Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((0 : ℂ) + (y : ℂ) * Complex.I)) :=
      Kax_eq_K_ofComplex _ τ 0 y hy0
    have h2 : Work.Asymptotics.kerExp r ((-1 : ℂ) + (y : ℂ) * Complex.I)
        = Work.Asymptotics.kerExp r (-1 : ℂ) * Work.Asymptotics.gaussWeight r y := by
      rw [show ((-1 : ℂ) + (y : ℂ) * Complex.I) = (((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I by
        push_cast; ring]
      simpa using kerExp_decomp r (-1) y
    have h3 : ((-1 : ℂ) + (y : ℂ) * Complex.I) + 1 = (0 : ℂ) + (y : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, h2, h3]
    ring

/-- The two vertical tails of the `K̂(τ, ·-1)` integrand are integrable. -/
lemma rays_integrable_weak_minus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C : ℝ} {M : ℕ} (hr : 2 < r ^ 2)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) (hC : 0 ≤ C)
    (hray : ∀ (x t : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → 1 ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    MeasureTheory.IntegrableOn (fun y : ℝ => Work.Kernels.Khat ℓ d τ
        (UpperHalfPlane.ofComplex (((1 : ℂ) + (y : ℂ) * Complex.I) - 1))
        * Work.Asymptotics.kerExp r ((1 : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
    ∧ MeasureTheory.IntegrableOn (fun y : ℝ => Work.Kernels.Khat ℓ d τ
        (UpperHalfPlane.ofComplex (((0 : ℂ) + (y : ℂ) * Complex.I) - 1))
        * Work.Asymptotics.kerExp r ((0 : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) := by
  have h0 := (integrableOn_Kax_gauss_ray ℓ d hd τ hr hre him hC hray
    (Or.inr (Or.inl rfl))).mono_set Set.Ioi_subset_Ici_self
  have hm := (integrableOn_Kax_gauss_ray ℓ d hd τ hr hre him hC hray
    (Or.inl rfl)).mono_set Set.Ioi_subset_Ici_self
  constructor
  · refine MeasureTheory.IntegrableOn.congr_fun
      (h0.const_mul (Work.Asymptotics.kerExp r (1 : ℂ))) (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := by linarith [Set.mem_Ioi.mp hy]
    have h1 : Kax (Work.Kernels.Khat ℓ d) τ 0 y
        = Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((0 : ℂ) + (y : ℂ) * Complex.I)) :=
      Kax_eq_K_ofComplex _ τ 0 y hy0
    have h2 : Work.Asymptotics.kerExp r ((1 : ℂ) + (y : ℂ) * Complex.I)
        = Work.Asymptotics.kerExp r (1 : ℂ) * Work.Asymptotics.gaussWeight r y := by
      rw [show ((1 : ℂ) + (y : ℂ) * Complex.I) = (((1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I by
        push_cast; ring]
      simpa using kerExp_decomp r 1 y
    have h3 : ((1 : ℂ) + (y : ℂ) * Complex.I) - 1 = (0 : ℂ) + (y : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, h2, h3]
    ring
  · refine MeasureTheory.IntegrableOn.congr_fun hm (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := by linarith [Set.mem_Ioi.mp hy]
    rw [Kax_eq_K_ofComplex _ τ (-1) y hy0]
    rw [show (0 : ℂ) + (y : ℂ) * Complex.I = (y : ℂ) * Complex.I by ring, kerExp_mul_I]
    congr 2
    push_cast; ring

/-! ## The two shifts -/

/-- **The `K̂(τ, ·+1)` half-strip shift**, from the ray and far-strip bounds. -/
theorem shift_ray_weak_plus_self (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C T : ℝ} {M : ℕ} (hr : 2 < r ^ 2)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) (hC : 0 ≤ C) (hT : 0 < T)
    (hray : ∀ (x t : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → 1 ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t))
    (hfar : ∀ (x t : ℝ), -1 ≤ x → x ≤ 1 → T ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    (∫ x in (-1 : ℝ)..0, Kax (Work.Kernels.Khat ℓ d) τ (x + 1) 1
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
            * ((x : ℂ) + (1 : ℂ) * Complex.I)))
      = - Complex.I * (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ 1 t
              * Work.Asymptotics.gaussWeight r t)
        + Complex.I * Work.Asymptotics.kerExp r (-1 : ℂ)
          * (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ 0 t
              * Work.Asymptotics.gaussWeight r t) := by
  set F : ℂ → ℂ := fun z => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z + 1)) * Work.Asymptotics.kerExp r z with hF
  have htop := topEdge_weak_plus ℓ d hd τ hr hC hT hfar
  have hint := rays_integrable_weak_plus ℓ d hd τ hr hre him hC hray
  have hzne : Work.Residues.jprime τ ≠ 0 :=
    Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two τ (by linarith)
  have hres0 : Work.Residues.HasResidue (fun ζ : UpperHalfPlane => Work.Kernels.Khat ℓ d τ ζ) τ 0 :=
    (Khat_second_residue ℓ d hd τ hzne).1
  have hres1 : Work.Residues.HasResidue (fun ζ : UpperHalfPlane => Work.Kernels.Khat ℓ d τ ζ)
      ((1 : ℝ) +ᵥ τ) 0 := (Khat_second_residue ℓ d hd τ hzne).2
  have hint_ray0 : MeasureTheory.IntegrableOn (fun y : ℝ => F ((0 : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) := by
    simpa only [hF] using hint.1
  have hint_raym : MeasureTheory.IntegrableOn (fun y : ℝ => F ((-1 : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) :=
    hint.2
  have hint_raym' : MeasureTheory.IntegrableOn (fun y : ℝ => F ((((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) := by
    rw [show (((-1 : ℝ)) : ℂ) = (-1 : ℂ) from by norm_num]
    exact hint_raym
  have htop' : Filter.Tendsto (fun R : ℝ => ∫ x in (-1 : ℝ)..0, F ((x : ℂ) + (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    simpa only [hF] using htop
  have hgeom : (∫ x in (-1 : ℝ)..0, F ((x : ℂ) + (1 : ℂ) * Complex.I))
      = Complex.I * (∫ y in Set.Ioi (1 : ℝ), F ((-1 : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y in Set.Ioi (1 : ℝ), F ((0 : ℂ) + (y : ℂ) * Complex.I)) := by
    rcases hre with hre | hre
    · -- τ.re = 1/2, pole at z₀ = τ - 1 (whose shifted kernel argument is τ)
      set F2 : ℂ → ℂ := fun z => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z + 1)) * Work.Asymptotics.kerExp r z with hF2
      have hclean : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 0 → 1 ≤ z.im → z ≠ (τ : ℂ) - 1 →
          Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z + 1)) := by
        intro z h1 h2 h3 hne hjeq
        have h4 : 0 ≤ (z + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
        have h5 : (z + 1).re ≤ 1 := by simp only [Complex.add_re, Complex.one_re]; linarith
        have h6 : 1 ≤ (z + 1).im := by simp only [Complex.add_im, Complex.one_im]; linarith
        rcases khat_strip_orbit τ (z + 1) (Or.inl hre) him h4 h5 h6 hjeq with h | h
        · have hz : z = (τ : ℂ) - 1 := by
            have h' : (z + 1 : ℂ) = (τ : ℂ) := by
              have hcoe := congrArg (fun w : UpperHalfPlane => (w : ℂ)) h
              rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simp only [Complex.add_im, Complex.one_im]; linarith)] at hcoe
              exact hcoe
            linear_combination h'
          exact hne hz
        · have hz : z = (τ : ℂ) := by
            have h' : (z + 1 : ℂ) = (τ : ℂ) + 1 := by
              have hcoe := congrArg (fun w : UpperHalfPlane => (w : ℂ)) h
              rw [UpperHalfPlane.coe_vadd] at hcoe
              rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simp only [Complex.add_im, Complex.one_im]; linarith)] at hcoe
              have hcoe' : (z + 1 : ℂ) = (((1 : ℝ) : ℂ) + (τ : ℂ)) := hcoe
              rw [hcoe']; push_cast; ring
            linear_combination h'
          rw [hz] at h2
          simp only [UpperHalfPlane.coe_re, hre] at h2
          norm_num at h2
      obtain ⟨hcont, hhol⟩ := khat_shift_cont_diff ℓ d hd τ r (z₀ := (τ : ℂ) - 1) hclean
      have hcont' : ContinuousOn F ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 1 ≤ z.im} \ {((τ : ℂ) - 1)}) := by
        simpa only [hF] using hcont
      have hhol' : ∀ z : ℂ, -1 < z.re → z.re < 0 → 1 < z.im → z ≠ ((τ : ℂ) - 1) → DifferentiableAt ℂ F z := by
        intro z a b c dd
        simpa only [hF] using hhol z a b c dd
      have hreslim : Filter.Tendsto (fun z : ℂ => (z - ((τ : ℂ) - 1)) * F z)
          (nhdsWithin ((τ : ℂ) - 1) {((τ : ℂ) - 1)}ᶜ) (nhds 0) := by
        have h1 := tendsto_shift_comp (F := fun w : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex w))
          (ζ₀ := (τ : ℂ)) (c := 0) (d := 1) (tendsto_of_hasResidue_ofComplex hres0)
        have h2 : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerExp r z)
            (nhdsWithin ((τ : ℂ) - 1) {((τ : ℂ) - 1)}ᶜ) (nhds (Work.Asymptotics.kerExp r ((τ : ℂ) - 1))) :=
          (((continuous_kerExp r).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
        have h3 := h1.mul h2
        simp only [zero_mul] at h3
        refine h3.congr' ?_
        filter_upwards with z
        simp only [hF]
        ring
      have hx₁ : (-1 : ℝ) < ((τ : ℂ) - 1).re := by
        simp only [Complex.sub_re, UpperHalfPlane.coe_re, hre]; norm_num
      have hx₂ : ((τ : ℂ) - 1).re < 0 := by
        simp only [Complex.sub_re, UpperHalfPlane.coe_re, hre]; norm_num
      have hy₁ : (1 : ℝ) < ((τ : ℂ) - 1).im := by
        have h : ((τ : ℂ) - 1).im = τ.im := by simp
        rw [h]; linarith
      have hshift := vertical_ray_shift (f := F)
        (z₀ := (τ : ℂ) - 1) (c := 0) (x₁ := -1) (x₂ := 0) (y₁ := 1)
        hx₁ hx₂ hy₁ hcont' hhol' hreslim htop' hint_raym' hint_ray0
      have hshift' : ((Complex.I * ∫ (y : ℝ) in Set.Ioi 1, F ((0 : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I * ∫ (y : ℝ) in Set.Ioi 1, F ((-1 : ℂ) + (y : ℂ) * Complex.I)) +
          ∫ (x : ℝ) in -1..0, F ((x : ℂ) + (1 : ℂ) * Complex.I) = 0 := by
        rw [show (2 : ℂ) * ↑Real.pi * Complex.I * 0 = 0 by ring] at hshift
        convert hshift using 2 <;> norm_num
      have hCsol := eq_neg_of_add_eq_zero_right hshift'
      rw [hCsol]; ring
    · -- τ.re = -1/2, pole at z₀ = τ (whose shifted kernel argument is τ + 1)
      have hclean : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 0 → 1 ≤ z.im → z ≠ (τ : ℂ) →
          Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z + 1)) := by
        intro z h1 h2 h3 hne hjeq
        have h4 : 0 ≤ (z + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
        have h5 : (z + 1).re ≤ 1 := by simp only [Complex.add_re, Complex.one_re]; linarith
        have h6 : 1 ≤ (z + 1).im := by simp only [Complex.add_im, Complex.one_im]; linarith
        rcases khat_strip_orbit τ (z + 1) (Or.inr hre) him h4 h5 h6 hjeq with h | h
        · have hz : z = (τ : ℂ) - 1 := by
            have h' : (z + 1 : ℂ) = (τ : ℂ) := by
              have hcoe := congrArg (fun w : UpperHalfPlane => (w : ℂ)) h
              rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simp only [Complex.add_im, Complex.one_im]; linarith)] at hcoe
              exact hcoe
            linear_combination h'
          rw [hz] at h1
          simp only [Complex.sub_re, UpperHalfPlane.coe_re, hre] at h1
          norm_num at h1
        · have hz : z = (τ : ℂ) := by
            have h' : (z + 1 : ℂ) = (τ : ℂ) + 1 := by
              have hcoe := congrArg (fun w : UpperHalfPlane => (w : ℂ)) h
              rw [UpperHalfPlane.coe_vadd] at hcoe
              rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simp only [Complex.add_im, Complex.one_im]; linarith)] at hcoe
              have hcoe' : (z + 1 : ℂ) = (((1 : ℝ) : ℂ) + (τ : ℂ)) := hcoe
              rw [hcoe']; push_cast; ring
            linear_combination h'
          exact hne hz
      obtain ⟨hcont, hhol⟩ := khat_shift_cont_diff ℓ d hd τ r (z₀ := (τ : ℂ)) hclean
      have hcont' : ContinuousOn F ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 1 ≤ z.im} \ {((τ : ℂ))}) := by
        simpa only [hF] using hcont
      have hhol' : ∀ z : ℂ, -1 < z.re → z.re < 0 → 1 < z.im → z ≠ ((τ : ℂ)) → DifferentiableAt ℂ F z := by
        intro z a b c dd
        simpa only [hF] using hhol z a b c dd
      have hreslim : Filter.Tendsto (fun z : ℂ => (z - ((τ : ℂ))) * F z)
          (nhdsWithin ((τ : ℂ)) {((τ : ℂ))}ᶜ) (nhds 0) := by
        have h1 := tendsto_shift_comp (F := fun w : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex w))
          (ζ₀ := (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)) (c := 0) (d := 1) (tendsto_of_hasResidue_ofComplex hres1)
        rw [show ((((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)) - 1 = (τ : ℂ) by
          rw [UpperHalfPlane.coe_vadd]; push_cast; ring] at h1
        have h2 : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerExp r z)
            (nhdsWithin ((τ : ℂ)) {((τ : ℂ))}ᶜ) (nhds (Work.Asymptotics.kerExp r ((τ : ℂ)))) :=
          (((continuous_kerExp r).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
        have h3 := h1.mul h2
        simp only [zero_mul] at h3
        refine h3.congr' ?_
        filter_upwards with z
        simp only [hF]
        ring
      have hx₁ : (-1 : ℝ) < ((τ : ℂ)).re := by
        simp only [UpperHalfPlane.coe_re, hre]; norm_num
      have hx₂ : ((τ : ℂ)).re < 0 := by
        simp only [UpperHalfPlane.coe_re, hre]; norm_num
      have hy₁ : (1 : ℝ) < ((τ : ℂ)).im := by
        simp only [UpperHalfPlane.coe_im]; linarith
      have hshift := vertical_ray_shift (f := F)
        (z₀ := (τ : ℂ)) (c := 0) (x₁ := -1) (x₂ := 0) (y₁ := 1)
        hx₁ hx₂ hy₁ hcont' hhol' hreslim htop' hint_raym' hint_ray0
      have hshift' : ((Complex.I * ∫ (y : ℝ) in Set.Ioi 1, F ((0 : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I * ∫ (y : ℝ) in Set.Ioi 1, F ((-1 : ℂ) + (y : ℂ) * Complex.I)) +
          ∫ (x : ℝ) in -1..0, F ((x : ℂ) + (1 : ℂ) * Complex.I) = 0 := by
        rw [show (2 : ℂ) * ↑Real.pi * Complex.I * 0 = 0 by ring] at hshift
        convert hshift using 2 <;> norm_num
      have hCsol := eq_neg_of_add_eq_zero_right hshift'
      rw [hCsol]; ring
  -- convert each of the three integrals in `hgeom` into the form of the statement
  have hL : (∫ x in (-1 : ℝ)..0, F ((x : ℂ) + (1 : ℂ) * Complex.I))
      = ∫ x in (-1 : ℝ)..0, Kax (Work.Kernels.Khat ℓ d) τ (x + 1) 1
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + (1 : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hF]
    rw [Kax_eq_K_ofComplex (K := Work.Kernels.Khat ℓ d) τ (x + 1) 1 (by norm_num)]
    rw [show (((x + 1 : ℝ)) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I
        = (x : ℂ) + (1 : ℂ) * Complex.I + 1 by push_cast; ring]
    rw [kerExp_eq_phase]
    rw [show (Real.pi * r ^ 2 : ℝ) = Real.pi * r ^ 2 from rfl]
    ring_nf
  have hR1 : (∫ y in Set.Ioi (1 : ℝ), F ((0 : ℂ) + (y : ℂ) * Complex.I))
      = ∫ t in Set.Ioi (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 1 t * Work.Asymptotics.gaussWeight r t := by
    have hpt : ∀ y : ℝ, y ∈ Set.Ioi (1 : ℝ) → F ((0 : ℂ) + (y : ℂ) * Complex.I)
        = Kax (Work.Kernels.Khat ℓ d) τ 1 y * Work.Asymptotics.gaussWeight r y := by
      intro y hy
      have hy0 : 0 < y := by linarith [Set.mem_Ioi.mp hy]
      simp only [hF]
      rw [Kax_eq_K_ofComplex (K := Work.Kernels.Khat ℓ d) τ 1 y hy0]
      rw [show (((1 : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I
          = (0 : ℂ) + (y : ℂ) * Complex.I + 1 by push_cast; ring]
      rw [show ((0 : ℂ) + (y : ℂ) * Complex.I) = (y : ℂ) * Complex.I by ring, kerExp_mul_I]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt]
  have hR2 : (∫ y in Set.Ioi (1 : ℝ), F ((-1 : ℂ) + (y : ℂ) * Complex.I))
      = Work.Asymptotics.kerExp r (-1 : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
          Kax (Work.Kernels.Khat ℓ d) τ 0 t * Work.Asymptotics.gaussWeight r t := by
    have hpt : ∀ y : ℝ, y ∈ Set.Ioi (1 : ℝ) → F ((-1 : ℂ) + (y : ℂ) * Complex.I)
        = Work.Asymptotics.kerExp r (-1) * (Kax (Work.Kernels.Khat ℓ d) τ 0 y
            * Work.Asymptotics.gaussWeight r y) := by
      intro y hy
      have hy0 : 0 < y := by linarith [Set.mem_Ioi.mp hy]
      simp only [hF]
      rw [Kax_eq_K_ofComplex (K := Work.Kernels.Khat ℓ d) τ 0 y hy0]
      rw [show ((-1 : ℂ) + (y : ℂ) * Complex.I) + 1 = (((0 : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [show ((-1 : ℂ) + (y : ℂ) * Complex.I) = ((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I by norm_num,
        kerExp_decomp]
      rw [show ((-1 : ℝ) : ℂ) = (-1 : ℂ) from by norm_num]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt]
    rw [MeasureTheory.integral_const_mul]
  rw [hL, hR1, hR2] at hgeom
  rw [hgeom]
  ring

/-! ## The `K̂(τ, ·-1)` shift -/

namespace KhatShiftContDiffMinus

/-- **Continuity of the shifted kernel `z ↦ K̂(τ,z-1) e^{iπr²z}` on a clean set.** -/
lemma continuousOn_khat_shift_minus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (S : Set ℂ)
    (him : ∀ z ∈ S, 0 < (z - 1).im)
    (hj : ∀ z ∈ S, Work.Kernels.jInvariantFun τ ≠
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1))) :
    ContinuousOn (fun z : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z - 1))
      * Work.Asymptotics.kerExp r z) S := by
  have hKCdiff : DifferentiableOn ℂ
      (fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (UpperHalfPlane.mdifferentiable_iff).mp (Work.Kernels.KernelClear_growth_z ℓ d hd τ).2.1
  have hshift : ContinuousOn (fun z : ℂ => z - 1) S :=
    (continuous_id.sub continuous_const).continuousOn
  have hmapshift : Set.MapsTo (fun z : ℂ => z - 1) S {u : ℂ | 0 < u.im} := fun z hz => him z hz
  have h₁ : ContinuousOn (fun z : ℂ =>
      Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex (z - 1))) S :=
    hKCdiff.continuousOn.comp hshift hmapshift
  have hgpc : ContinuousOn
      (fun u : ℂ => Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (KhatShiftContDiff.continuous_growthPrefactor_snd d τ).comp_continuousOn
      Work.Asymptotics.continuousOn_ofComplex_of_im_pos
  have h₂ : ContinuousOn (fun z : ℂ =>
      Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex (z - 1))) S :=
    hgpc.comp hshift hmapshift
  have hne : ∀ z ∈ S, Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex (z - 1)) ≠ 0 :=
    fun z hz => KhatShiftContDiff.growthPrefactor_ne_zero d (hj z hz)
  have h₄ := (h₁.div h₂ hne).mul (KhatShiftContDiff.continuous_kerExp r).continuousOn
  exact h₄.congr (fun z hz => by
    show Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z - 1)) * Work.Asymptotics.kerExp r z
      = (Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex (z - 1))
          / Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex (z - 1)))
        * Work.Asymptotics.kerExp r z
    rw [KhatShiftContDiff.khat_eq_khatClear_div ℓ d hd (hj z hz)])

/-- **Holomorphy of the shifted kernel `z ↦ K̂(τ,z-1) e^{iπr²z}` at a clean point.** -/
lemma differentiableAt_khat_shift_minus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) {z : ℂ} (him : 0 < (z - 1).im)
    (hj : Work.Kernels.jInvariantFun τ ≠
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1))) :
    DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z - 1))
      * Work.Asymptotics.kerExp r z) z := by
  have hcoe : ((UpperHalfPlane.ofComplex (z - 1) : UpperHalfPlane) : ℂ) = z - 1 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hMD := Work.Residues.mdifferentiableAt_Khat_snd ℓ d hd τ
    (UpperHalfPlane.ofComplex (z - 1)) hj.symm
  have hdiff₁ : DifferentiableAt ℂ
      (fun u : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex u)) (z - 1) := by
    have h := (UpperHalfPlane.mdifferentiableAt_iff).mp hMD
    rwa [hcoe] at h
  have hdiff₂ : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (w - 1))) z :=
    hdiff₁.comp z (differentiableAt_id.sub_const 1)
  exact hdiff₂.mul (KhatShiftContDiff.differentiable_kerExp r z)

end KhatShiftContDiffMinus

/-- **Continuity and holomorphy of `z ↦ K̂(τ,z-1) e^{iπr²z}` on the right strip.** -/
theorem khat_shift_cont_diff_minus (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) {z₀ : ℂ}
    (hclean : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im → z ≠ z₀ →
      Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1))) :
    ContinuousOn (fun z : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z - 1))
        * Work.Asymptotics.kerExp r z) ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im} \ {z₀})
      ∧ (∀ z : ℂ, 0 < z.re → z.re < 1 → 1 < z.im → z ≠ z₀ →
          DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.Khat ℓ d τ
            (UpperHalfPlane.ofComplex (z - 1)) * Work.Asymptotics.kerExp r z) z) := by
  constructor
  · refine KhatShiftContDiffMinus.continuousOn_khat_shift_minus ℓ d hd τ r _ ?_ ?_
    · intro z hz
      rcases hz with ⟨hzA, hz0⟩
      simp only [Set.mem_ofPred_eq] at hzA
      obtain ⟨h1, h2, h3⟩ := hzA
      simp only [Complex.sub_im, Complex.one_im, sub_zero]
      linarith
    · intro z hz
      rcases hz with ⟨hzA, hz0⟩
      simp only [Set.mem_ofPred_eq] at hzA
      simp only [Set.mem_singleton_iff] at hz0
      obtain ⟨h1, h2, h3⟩ := hzA
      exact hclean z h1 h2 h3 hz0
  · intro z h1 h2 h3 hz0
    refine KhatShiftContDiffMinus.differentiableAt_khat_shift_minus ℓ d hd τ r ?_ ?_
    · simp only [Complex.sub_im, Complex.one_im, sub_zero]
      linarith
    · exact hclean z (le_of_lt h1) (le_of_lt h2) (le_of_lt h3) hz0

/-- **The `K̂(τ, ·-1)` half-strip shift**, from the ray and far-strip bounds. -/
theorem shift_ray_weak_minus_self (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C T : ℝ} {M : ℕ} (hr : 2 < r ^ 2)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) (hC : 0 ≤ C) (hT : 0 < T)
    (hray : ∀ (x t : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → 1 ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t))
    (hfar : ∀ (x t : ℝ), -1 ≤ x → x ≤ 1 → T ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    (∫ x in (0 : ℝ)..1, Kax (Work.Kernels.Khat ℓ d) τ (x - 1) 1
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
            * ((x : ℂ) + (1 : ℂ) * Complex.I)))
      = - Complex.I * Work.Asymptotics.kerExp r (1 : ℂ)
          * (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ 0 t
              * Work.Asymptotics.gaussWeight r t)
        + Complex.I * (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ (-1) t
              * Work.Asymptotics.gaussWeight r t) := by
  set F : ℂ → ℂ := fun z => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z - 1))
    * Work.Asymptotics.kerExp r z with hF
  have htop := topEdge_weak_minus ℓ d hd τ hr hC hT hfar
  have hint := rays_integrable_weak_minus ℓ d hd τ hr hre him hC hray
  have hzne : Work.Residues.jprime τ ≠ 0 :=
    Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two τ (by linarith)
  have hres0 : Work.Residues.HasResidue (fun ζ : UpperHalfPlane => Work.Kernels.Khat ℓ d τ ζ) τ 0 :=
    (Khat_second_residue ℓ d hd τ hzne).1
  have hresm : Work.Residues.HasResidue (fun ζ : UpperHalfPlane => Work.Kernels.Khat ℓ d τ ζ)
      (((-1 : ℝ)) +ᵥ τ) 0 := by
    rw [← Work.Residues.T_inv_smul_eq]
    exact Work.Residues.hasResidue_Khat_second ℓ d hd τ hzne
  have hint_ray1 : MeasureTheory.IntegrableOn (fun y : ℝ => F ((1 : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi (1 : ℝ)) := by
    simpa only [hF] using hint.1
  have hint_ray0 : MeasureTheory.IntegrableOn (fun y : ℝ => F ((0 : ℂ) + (y : ℂ) * Complex.I))
      (Set.Ioi (1 : ℝ)) := by
    simpa only [hF] using hint.2
  have htop' : Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..1, F ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
    simpa only [hF] using htop
  have hgeom : (∫ x in (0 : ℝ)..1, F ((x : ℂ) + (1 : ℂ) * Complex.I))
      = Complex.I * (∫ y in Set.Ioi (1 : ℝ), F ((0 : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y in Set.Ioi (1 : ℝ), F ((1 : ℂ) + (y : ℂ) * Complex.I)) := by
    rcases hre with hre | hre
    · -- τ.re = 1/2, pole at z₀ = τ (whose shifted kernel argument is τ - 1)
      have hclean : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im → z ≠ poleAtTau τ →
          Work.Kernels.jInvariantFun τ ≠
            Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1)) :=
        fun z a b c dd => ofComplex_sub_one_clean_pos τ hre him z a b c dd
      obtain ⟨hcont, hhol⟩ := khat_shift_cont_diff_minus ℓ d hd τ r (z₀ := (τ : ℂ))
        (by intro z a b c dd; exact hclean z a b c (by simpa only [poleAtTau] using dd))
      have hcont' : ContinuousOn F ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im} \ {((τ : ℂ))}) := by
        simpa only [hF] using hcont
      have hhol' : ∀ z : ℂ, 0 < z.re → z.re < 1 → 1 < z.im → z ≠ ((τ : ℂ)) →
          DifferentiableAt ℂ F z := by
        intro z a b c dd
        simpa only [hF] using hhol z a b c dd
      have hreslim : Filter.Tendsto (fun z : ℂ => (z - ((τ : ℂ))) * F z)
          (nhdsWithin ((τ : ℂ)) {((τ : ℂ))}ᶜ) (nhds 0) := by
        have h1 := tendsto_shift_comp (F := fun w : ℂ => Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex w)) (ζ₀ := (((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ))
          (c := 0) (d := -1) (tendsto_of_hasResidue_ofComplex hresm)
        rw [show (((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) - -1 = (τ : ℂ) by
          rw [UpperHalfPlane.coe_vadd]; push_cast; ring] at h1
        have h2 : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerExp r z)
            (nhdsWithin ((τ : ℂ)) {((τ : ℂ))}ᶜ) (nhds (Work.Asymptotics.kerExp r ((τ : ℂ)))) :=
          (((continuous_kerExp r).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
        have h3 := h1.mul h2
        simp only [zero_mul] at h3
        refine h3.congr' ?_
        filter_upwards with z
        simp only [hF]
        ring
      have hx₁ : (0 : ℝ) < ((τ : ℂ)).re := by
        simp only [UpperHalfPlane.coe_re, hre]; norm_num
      have hx₂ : ((τ : ℂ)).re < 1 := by
        simp only [UpperHalfPlane.coe_re, hre]; norm_num
      have hy₁ : (1 : ℝ) < ((τ : ℂ)).im := by
        simp only [UpperHalfPlane.coe_im]; linarith
      have hshift := vertical_ray_shift (f := F)
        (z₀ := (τ : ℂ)) (c := 0) (x₁ := 0) (x₂ := 1) (y₁ := 1)
        hx₁ hx₂ hy₁ hcont' hhol' hreslim htop' hint_ray0 hint_ray1
      have hshift' : ((Complex.I * ∫ (y : ℝ) in Set.Ioi 1, F ((1 : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I * ∫ (y : ℝ) in Set.Ioi 1, F ((0 : ℂ) + (y : ℂ) * Complex.I)) +
          ∫ (x : ℝ) in 0..1, F ((x : ℂ) + (1 : ℂ) * Complex.I) = 0 := by
        rw [show (2 : ℂ) * ↑Real.pi * Complex.I * 0 = 0 by ring] at hshift
        convert hshift using 2 <;> norm_num
      have hCsol := eq_neg_of_add_eq_zero_right hshift'
      rw [hCsol]; ring
    · -- τ.re = -1/2, pole at z₀ = τ + 1 (whose shifted kernel argument is τ)
      have hclean : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im → z ≠ poleAtTauAddOne τ →
          Work.Kernels.jInvariantFun τ ≠
            Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z - 1)) :=
        fun z a b c dd => ofComplex_sub_one_clean_neg τ hre him z a b c dd
      have hz0 : (poleAtTauAddOne τ : ℂ) = (τ : ℂ) + 1 := by
        rw [poleAtTauAddOne, UpperHalfPlane.coe_vadd]; push_cast; ring
      obtain ⟨hcont, hhol⟩ := khat_shift_cont_diff_minus ℓ d hd τ r (z₀ := (τ : ℂ) + 1)
        (by intro z a b c dd
            exact hclean z a b c (fun h => dd (by simpa only [hz0] using h)))
      have hcont' : ContinuousOn F ({z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im} \ {((τ : ℂ) + 1)}) := by
        simpa only [hF] using hcont
      have hhol' : ∀ z : ℂ, 0 < z.re → z.re < 1 → 1 < z.im → z ≠ ((τ : ℂ) + 1) →
          DifferentiableAt ℂ F z := by
        intro z a b c dd
        simpa only [hF] using hhol z a b c dd
      have hreslim : Filter.Tendsto (fun z : ℂ => (z - ((τ : ℂ) + 1)) * F z)
          (nhdsWithin ((τ : ℂ) + 1) {((τ : ℂ) + 1)}ᶜ) (nhds 0) := by
        have h1 := tendsto_shift_comp (F := fun w : ℂ => Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex w)) (ζ₀ := (τ : ℂ)) (c := 0) (d := -1)
          (tendsto_of_hasResidue_ofComplex hres0)
        rw [show (τ : ℂ) - -1 = (τ : ℂ) + 1 by ring] at h1
        have h2 : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerExp r z)
            (nhdsWithin ((τ : ℂ) + 1) {((τ : ℂ) + 1)}ᶜ)
            (nhds (Work.Asymptotics.kerExp r ((τ : ℂ) + 1))) :=
          (((continuous_kerExp r).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
        have h3 := h1.mul h2
        simp only [zero_mul] at h3
        refine h3.congr' ?_
        filter_upwards with z
        simp only [hF]
        ring
      have hx₁ : (0 : ℝ) < ((τ : ℂ) + 1).re := by
        simp only [Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re, hre]; norm_num
      have hx₂ : ((τ : ℂ) + 1).re < 1 := by
        simp only [Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re, hre]; norm_num
      have hy₁ : (1 : ℝ) < ((τ : ℂ) + 1).im := by
        simp only [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im]; linarith
      have hshift := vertical_ray_shift (f := F)
        (z₀ := (τ : ℂ) + 1) (c := 0) (x₁ := 0) (x₂ := 1) (y₁ := 1)
        hx₁ hx₂ hy₁ hcont' hhol' hreslim htop' hint_ray0 hint_ray1
      have hshift' : ((Complex.I * ∫ (y : ℝ) in Set.Ioi 1, F ((1 : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I * ∫ (y : ℝ) in Set.Ioi 1, F ((0 : ℂ) + (y : ℂ) * Complex.I)) +
          ∫ (x : ℝ) in 0..1, F ((x : ℂ) + (1 : ℂ) * Complex.I) = 0 := by
        rw [show (2 : ℂ) * ↑Real.pi * Complex.I * 0 = 0 by ring] at hshift
        convert hshift using 2 <;> norm_num
      have hCsol := eq_neg_of_add_eq_zero_right hshift'
      rw [hCsol]; ring
  -- convert each of the three integrals into the form of the statement
  have hL : (∫ x in (0 : ℝ)..1, F ((x : ℂ) + (1 : ℂ) * Complex.I))
      = ∫ x in (0 : ℝ)..1, Kax (Work.Kernels.Khat ℓ d) τ (x - 1) 1
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + (1 : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hF]
    rw [Kax_eq_K_ofComplex (K := Work.Kernels.Khat ℓ d) τ (x - 1) 1 (by norm_num)]
    rw [show (((x - 1 : ℝ)) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I
        = (x : ℂ) + (1 : ℂ) * Complex.I - 1 by push_cast; ring]
    rw [kerExp_eq_phase]
    rw [show (Real.pi * r ^ 2 : ℝ) = Real.pi * r ^ 2 from rfl]
    ring_nf
  have hR1 : (∫ y in Set.Ioi (1 : ℝ), F ((1 : ℂ) + (y : ℂ) * Complex.I))
      = Work.Asymptotics.kerExp r (1 : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
          Kax (Work.Kernels.Khat ℓ d) τ 0 t * Work.Asymptotics.gaussWeight r t := by
    have hpt : ∀ y : ℝ, y ∈ Set.Ioi (1 : ℝ) → F ((1 : ℂ) + (y : ℂ) * Complex.I)
        = Work.Asymptotics.kerExp r (1) * (Kax (Work.Kernels.Khat ℓ d) τ 0 y
            * Work.Asymptotics.gaussWeight r y) := by
      intro y hy
      have hy0 : 0 < y := by linarith [Set.mem_Ioi.mp hy]
      simp only [hF]
      rw [Kax_eq_K_ofComplex (K := Work.Kernels.Khat ℓ d) τ 0 y hy0]
      rw [show ((1 : ℂ) + (y : ℂ) * Complex.I) - 1 = (((0 : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [show ((1 : ℂ) + (y : ℂ) * Complex.I) = ((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I by norm_num,
        kerExp_decomp]
      rw [show ((1 : ℝ) : ℂ) = (1 : ℂ) from by norm_num]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt]
    rw [MeasureTheory.integral_const_mul]
  have hR2 : (∫ y in Set.Ioi (1 : ℝ), F ((0 : ℂ) + (y : ℂ) * Complex.I))
      = ∫ t in Set.Ioi (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ (-1) t
          * Work.Asymptotics.gaussWeight r t := by
    have hpt : ∀ y : ℝ, y ∈ Set.Ioi (1 : ℝ) → F ((0 : ℂ) + (y : ℂ) * Complex.I)
        = Kax (Work.Kernels.Khat ℓ d) τ (-1) y * Work.Asymptotics.gaussWeight r y := by
      intro y hy
      have hy0 : 0 < y := by linarith [Set.mem_Ioi.mp hy]
      simp only [hF]
      rw [Kax_eq_K_ofComplex (K := Work.Kernels.Khat ℓ d) τ (-1) y hy0]
      rw [show (((-1 : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I
          = (0 : ℂ) + (y : ℂ) * Complex.I - 1 by push_cast; ring]
      rw [show ((0 : ℂ) + (y : ℂ) * Complex.I) = (y : ℂ) * Complex.I by ring, kerExp_mul_I]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [hL, hR1, hR2] at hgeom
  rw [hgeom]
  ring

end

end Work.CKFinal.LineDecay
