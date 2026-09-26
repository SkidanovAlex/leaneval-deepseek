import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.orbit_classification
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.Aexp_gauss_integrable
import Submission.Work.CKFinal.LineDecay.j_eq_tau_of_lines
import Submission.Work.Asymptotics.FunnelAsm.aexpClosed
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.CKFinal.LineDecay.Khat_ray_far_bound
import Submission.Work.CKFinal.LineDecay.shift_ray_weak_self

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

noncomputable section

/-! ## The reduction of `paperLayerK` and the pieces `P₂`, `P₃`

The contour shifts themselves live in the modules `Khat_ray_far_bound` (the growth of `K̂` along
the rays and in the far half-strip), `shift_ray_weak_minus` and `shift_ray_weak_plus` (the two
half-strip shifts).  Here we record what the assembly of `shift_identity_khat` adds on top:
`paperLayerK` is `P₁` plus `sinSqC r` times the ray at `Re w = 0`, `P₃` is the second difference
of the three rays, and the two shifts recombine `P₂`.
-/

/-- `t ↦ t ^ k · e^{-ct}` is integrable on `[1,∞)` for `c > 0`. -/
private lemma integrableOn_pow_exp_neg_Ici_one {c : ℝ} (hc : 0 < c) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(c * t))) (Set.Ici 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := c)
    (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith) (by norm_num) hc
  refine (h.congr_fun (fun x hx => ?_) measurableSet_Ioi).mono_set ?_
  · simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]
  · intro x hx
    simp only [Set.mem_Ioi, Set.mem_Ici] at hx ⊢
    linarith

/-- `t ↦ e^{-ct}` is integrable on `[1,∞)` for `c > 0`. -/
private lemma integrableOn_exp_neg_Ici_one {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Set.Ici 1) := by
  refine (integrableOn_pow_exp_neg_Ici_one hc 0).congr_fun (fun x hx => ?_) measurableSet_Ici
  simp

/-- **The model tail integrand is integrable for any coefficient function `G`**, for `2 < r²`:
`Aexp G τ t = G₀₀ + t·iG₀₁ + e^{2πt}(G₁₀ + t·iG₁₁)` and `e^{2πt}e^{-πr²t} = e^{-(πr²-2π)t}`. -/
lemma Aexp_gauss_integrable_of (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t : ℝ => Work.Asymptotics.Aexp G τ t
      * Work.Asymptotics.gaussWeight r t) (Set.Ici 1) := by
  have hr2 : 0 < r ^ 2 := by linarith
  have hc1 : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos hr2
  have hc2 : 0 < Real.pi * (r ^ 2 - 2) := mul_pos Real.pi_pos (by linarith)
  refine MeasureTheory.Integrable.mono'
    (g := fun t : ℝ => ‖G 0 0 τ‖ * Real.exp (-(Real.pi * r ^ 2 * t))
      + ‖G 0 1 τ‖ * (t * Real.exp (-(Real.pi * r ^ 2 * t)))
      + ‖G 1 0 τ‖ * Real.exp (-(Real.pi * (r ^ 2 - 2) * t))
      + ‖G 1 1 τ‖ * (t * Real.exp (-(Real.pi * (r ^ 2 - 2) * t)))) ?_ ?_ ?_
  · have h0 : IntegrableOn (fun t : ℝ => ‖G 0 0 τ‖ * Real.exp (-(Real.pi * r ^ 2 * t)))
        (Set.Ici 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_exp_neg_Ici_one hc1) ‖G 0 0 τ‖
    have h1raw := MeasureTheory.Integrable.const_mul
      (integrableOn_pow_exp_neg_Ici_one hc1 1) ‖G 0 1 τ‖
    have h1 : IntegrableOn (fun t : ℝ => ‖G 0 1 τ‖ * (t * Real.exp (-(Real.pi * r ^ 2 * t))))
        (Set.Ici 1) :=
      MeasureTheory.IntegrableOn.congr_fun h1raw (fun t ht => by simp) measurableSet_Ici
    have h2 : IntegrableOn (fun t : ℝ => ‖G 1 0 τ‖ * Real.exp (-(Real.pi * (r ^ 2 - 2) * t)))
        (Set.Ici 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_exp_neg_Ici_one hc2) ‖G 1 0 τ‖
    have h3raw := MeasureTheory.Integrable.const_mul
      (integrableOn_pow_exp_neg_Ici_one hc2 1) ‖G 1 1 τ‖
    have h3 : IntegrableOn (fun t : ℝ => ‖G 1 1 τ‖ * (t * Real.exp (-(Real.pi * (r ^ 2 - 2) * t))))
        (Set.Ici 1) :=
      MeasureTheory.IntegrableOn.congr_fun h3raw (fun t ht => by simp) measurableSet_Ici
    exact MeasureTheory.IntegrableOn.add (MeasureTheory.IntegrableOn.add
      (MeasureTheory.IntegrableOn.add h0 h1) h2) h3
  · have hcont : Continuous (fun t : ℝ => Work.Asymptotics.Aexp G τ t
        * Work.Asymptotics.gaussWeight r t) := by
      unfold Work.Asymptotics.Aexp Work.Asymptotics.gaussWeight
      fun_prop
    exact hcont.aestronglyMeasurable.restrict
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr ?_
    filter_upwards with t ht
    rw [Set.mem_Ici] at ht
    have hnormt : ‖(t : ℂ)‖ = t := (RCLike.norm_ofReal t).trans (abs_of_nonneg (by linarith))
    have hexpn : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
      have harg : (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) := by
        push_cast; ring
      rw [harg, Complex.norm_exp, Complex.ofReal_re]
    have hExp : Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * r ^ 2 * t))
        = Real.exp (-(Real.pi * (r ^ 2 - 2) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hA : ‖Work.Asymptotics.Aexp G τ t‖
        ≤ ‖G 0 0 τ‖ + t * ‖G 0 1 τ‖ + Real.exp (2 * Real.pi * t) * (‖G 1 0 τ‖
            + t * ‖G 1 1 τ‖) := by
      rw [Work.Asymptotics.Aexp]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, norm_mul, Complex.norm_I, hnormt, mul_one]
      · rw [norm_mul, hexpn]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, norm_mul, Complex.norm_I, hnormt, mul_one]
    calc ‖Work.Asymptotics.Aexp G τ t * Work.Asymptotics.gaussWeight r t‖
        = ‖Work.Asymptotics.Aexp G τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t)) := by
          rw [norm_mul, Work.Asymptotics.norm_gaussWeight]
      _ ≤ (‖G 0 0 τ‖ + t * ‖G 0 1 τ‖ + Real.exp (2 * Real.pi * t) * (‖G 1 0 τ‖
            + t * ‖G 1 1 τ‖)) * Real.exp (-(Real.pi * r ^ 2 * t)) :=
          mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
      _ = (‖G 0 0 τ‖ * Real.exp (-(Real.pi * r ^ 2 * t))
          + ‖G 0 1 τ‖ * (t * Real.exp (-(Real.pi * r ^ 2 * t)))
          + ‖G 1 0 τ‖ * Real.exp (-(Real.pi * (r ^ 2 - 2) * t))
          + ‖G 1 1 τ‖ * (t * Real.exp (-(Real.pi * (r ^ 2 - 2) * t)))) := by
          rw [← hExp]; ring

/-- **`highPart` is the tail of the model for *any* `G`**, when `2 < r²` (so that the
`e^{2πt}`-row of the model decays and no regularisation hypothesis is needed). -/
lemma highPart_eq_integral_of (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    {r : ℝ} (hr : 2 < r ^ 2) :
    Work.Asymptotics.highPart G τ r
      = Work.Asymptotics.sinSqC r * ∫ t in Set.Ioi (1 : ℝ),
          Work.Asymptotics.Aexp G τ t * Work.Asymptotics.gaussWeight r t := by
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hr; norm_num at hr
  have hclosed := Work.Asymptotics.FunnelAsm.aexp_integral_closed G τ (B := 1) le_rfl hr0 (by
    intro hle
    have hpos : 0 < Real.pi * r ^ 2 - 2 * Real.pi := by nlinarith [Real.pi_pos, hr]
    exact absurd hle (not_le.mpr hpos))
  simp only [Complex.ofReal_one, mul_one] at hclosed
  rw [Work.Asymptotics.highPart_eq_closed, ← hclosed]
  rfl

/-! ## The three pieces of the contour identity

`paperLayerK` splits into `P₁` plus `sinSqC r` times the ray at `Re w = 0`; `P₃` is the second
difference of the three rays; and the two half-strip shifts (`shift_ray_center_minus`,
`shift_ray_center_plus`) recombine `P₂` the same way.  Here we record the three reductions and the
final one-line algebra.
-/

/-- `sinSqC r = 2 - e^{iλ} - e^{-iλ}` in the `kerExp` normalisation. -/
lemma sinSqC_eq_two_sub_kerExp' (r : ℝ) :
    Work.Asymptotics.sinSqC r
      = 2 - Work.Asymptotics.kerExp r (1 : ℂ) - Work.Asymptotics.kerExp r ((-1 : ℂ)) := by
  have h1 : Work.Asymptotics.kerExp r (1 : ℂ)
      = Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2) := by
    rw [Work.Asymptotics.kerExp]; congr 1; ring
  have h2 : Work.Asymptotics.kerExp r ((-1 : ℂ))
      = Complex.exp (-(Real.pi * Complex.I * (r : ℂ) ^ 2)) := by
    rw [Work.Asymptotics.kerExp]; congr 1; ring
  rw [sinSqC_eq_two_sub_exp, h1, h2]

/-- **The `paperLayerK` reduction**: the layer of the hatted kernel is `P₁` plus `sinSqC r` times
the ray at `Re w = 0` above height `1` (the `trunc` and `high` pieces reassemble, since `highPart`
is the tail of the model for `2 < r²`). -/
lemma paperLayerK_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C : ℝ} {M : ℕ} (hr : 2 < r ^ 2)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) (hC : 0 ≤ C)
    (hray : ∀ (x t : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → 1 ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ
      = P1 (Work.Kernels.Khat ℓ d) r τ
        + Work.Asymptotics.sinSqC r * ∫ t in Set.Ici (1 : ℝ),
            Kax (Work.Kernels.Khat ℓ d) τ 0 t * Work.Asymptotics.gaussWeight r t := by
  have hKax : IntegrableOn (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ 0 t
      * Work.Asymptotics.gaussWeight r t) (Set.Ici 1) :=
    integrableOn_Kax_gauss_ray ℓ d hd τ hr hre him hC hray (Or.inr (Or.inl rfl))
  have hAexp : IntegrableOn (fun t : ℝ => Work.Asymptotics.Aexp (Ghat ℓ d) τ t
      * Work.Asymptotics.gaussWeight r t) (Set.Ici 1) :=
    Aexp_gauss_integrable_of (Ghat ℓ d) τ hr
  have hsub : (∫ t in Set.Ici (1 : ℝ), (Kax (Work.Kernels.Khat ℓ d) τ 0 t
        - Work.Asymptotics.Aexp (Ghat ℓ d) τ t) * Work.Asymptotics.gaussWeight r t)
      = (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 0 t
          * Work.Asymptotics.gaussWeight r t)
        - ∫ t in Set.Ici (1 : ℝ), Work.Asymptotics.Aexp (Ghat ℓ d) τ t
          * Work.Asymptotics.gaussWeight r t := by
    rw [← MeasureTheory.integral_sub hKax hAexp]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun t ht => by ring)
  have hHP := highPart_eq_integral_of (Ghat ℓ d) τ hr
  have hIci : (∫ t in Set.Ioi (1 : ℝ), Work.Asymptotics.Aexp (Ghat ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t)
      = ∫ t in Set.Ici (1 : ℝ), Work.Asymptotics.Aexp (Ghat ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t := (MeasureTheory.integral_Ici_eq_integral_Ioi).symm
  rw [paperLayerK, layerLowK, layerTruncK, hHP, P1]
  simp only [hsplit]
  rw [hIci, hsub]
  ring

/-- **`P₃` is the second difference of the three rays**: by definition `Phi` is
`2K̂(τ,·) - K̂(τ,·-1) - K̂(τ,·+1)` and the ray integrands are integrable. -/
lemma P3_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C : ℝ} {M : ℕ} (hr : 2 < r ^ 2)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) (hC : 0 ≤ C)
    (hray : ∀ (x t : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → 1 ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    P3 (Work.Kernels.Khat ℓ d) r τ
      = 2 * (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 0 t
            * Work.Asymptotics.gaussWeight r t)
        - (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ (-1) t
            * Work.Asymptotics.gaussWeight r t)
        - (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 1 t
            * Work.Asymptotics.gaussWeight r t) := by
  have hu : Integrable (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ 0 t
      * Work.Asymptotics.gaussWeight r t) (volume.restrict (Set.Ici 1)) :=
    integrableOn_Kax_gauss_ray ℓ d hd τ hr hre him hC hray (Or.inr (Or.inl rfl))
  have hv : Integrable (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ (-1) t
      * Work.Asymptotics.gaussWeight r t) (volume.restrict (Set.Ici 1)) :=
    integrableOn_Kax_gauss_ray ℓ d hd τ hr hre him hC hray (Or.inl rfl)
  have hw : Integrable (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ 1 t
      * Work.Asymptotics.gaussWeight r t) (volume.restrict (Set.Ici 1)) :=
    integrableOn_Kax_gauss_ray ℓ d hd τ hr hre him hC hray (Or.inr (Or.inr rfl))
  have hu2 : Integrable (fun t : ℝ => 2 * (Kax (Work.Kernels.Khat ℓ d) τ 0 t
      * Work.Asymptotics.gaussWeight r t)) (volume.restrict (Set.Ici 1)) :=
    MeasureTheory.Integrable.const_mul hu 2
  have huv : Integrable (fun t : ℝ => 2 * (Kax (Work.Kernels.Khat ℓ d) τ 0 t
      * Work.Asymptotics.gaussWeight r t)
        - Kax (Work.Kernels.Khat ℓ d) τ (-1) t * Work.Asymptotics.gaussWeight r t)
      (volume.restrict (Set.Ici 1)) :=
    MeasureTheory.Integrable.sub hu2 hv
  have hfun : (fun t : ℝ => Phi (Work.Kernels.Khat ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
      = fun t : ℝ => 2 * (Kax (Work.Kernels.Khat ℓ d) τ 0 t * Work.Asymptotics.gaussWeight r t)
          - Kax (Work.Kernels.Khat ℓ d) τ (-1) t * Work.Asymptotics.gaussWeight r t
          - Kax (Work.Kernels.Khat ℓ d) τ 1 t * Work.Asymptotics.gaussWeight r t := by
    funext t; rw [Phi]; ring
  have hStep1 : (∫ t in Set.Ici (1 : ℝ), (2 * (Kax (Work.Kernels.Khat ℓ d) τ 0 t
        * Work.Asymptotics.gaussWeight r t) - Kax (Work.Kernels.Khat ℓ d) τ (-1) t
        * Work.Asymptotics.gaussWeight r t - Kax (Work.Kernels.Khat ℓ d) τ 1 t
        * Work.Asymptotics.gaussWeight r t))
      = (∫ t in Set.Ici (1 : ℝ), (2 * (Kax (Work.Kernels.Khat ℓ d) τ 0 t
          * Work.Asymptotics.gaussWeight r t) - Kax (Work.Kernels.Khat ℓ d) τ (-1) t
          * Work.Asymptotics.gaussWeight r t))
        - (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 1 t
          * Work.Asymptotics.gaussWeight r t) :=
    MeasureTheory.integral_sub huv hw
  have hStep2 : (∫ t in Set.Ici (1 : ℝ), (2 * (Kax (Work.Kernels.Khat ℓ d) τ 0 t
        * Work.Asymptotics.gaussWeight r t) - Kax (Work.Kernels.Khat ℓ d) τ (-1) t
        * Work.Asymptotics.gaussWeight r t))
      = (∫ t in Set.Ici (1 : ℝ), 2 * (Kax (Work.Kernels.Khat ℓ d) τ 0 t
          * Work.Asymptotics.gaussWeight r t))
        - (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ (-1) t
          * Work.Asymptotics.gaussWeight r t) :=
    MeasureTheory.integral_sub hu2 hv
  have hStep3 : (∫ t in Set.Ici (1 : ℝ), 2 * (Kax (Work.Kernels.Khat ℓ d) τ 0 t
        * Work.Asymptotics.gaussWeight r t))
      = 2 * (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 0 t
          * Work.Asymptotics.gaussWeight r t) :=
    MeasureTheory.integral_const_mul 2 _
  rw [P3, hsplit, hfun, hStep1, hStep2, hStep3]

/-- **`P₂` from the two half-strip shifts.**  Combining the two shift identities
(`shift_ray_center_minus`, `shift_ray_center_plus`) gives
`P₂ = Bm + Bp - (e^{iλ} + e^{-iλ})·B₀`. -/
lemma P2_eq_of_shifts (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) {r : ℝ}
    (hminus : (∫ x in (0 : ℝ)..1, Kax (Work.Kernels.Khat ℓ d) τ (x - 1) 1
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
            * ((x : ℂ) + (1 : ℂ) * Complex.I)))
      = - Complex.I * Work.Asymptotics.kerExp r (1 : ℂ)
          * (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ 0 t
              * Work.Asymptotics.gaussWeight r t)
        + Complex.I * (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ (-1) t
              * Work.Asymptotics.gaussWeight r t))
    (hplus : (∫ x in (-1 : ℝ)..0, Kax (Work.Kernels.Khat ℓ d) τ (x + 1) 1
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
            * ((x : ℂ) + (1 : ℂ) * Complex.I)))
      = - Complex.I * (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ 1 t
              * Work.Asymptotics.gaussWeight r t)
        + Complex.I * Work.Asymptotics.kerExp r (-1 : ℂ)
          * (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ 0 t
              * Work.Asymptotics.gaussWeight r t)) :
    P2 (Work.Kernels.Khat ℓ d) r τ
      = (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ (-1) t
            * Work.Asymptotics.gaussWeight r t)
        + (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 1 t
            * Work.Asymptotics.gaussWeight r t)
        - (Work.Asymptotics.kerExp r (1 : ℂ) + Work.Asymptotics.kerExp r (-1 : ℂ))
          * (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 0 t
              * Work.Asymptotics.gaussWeight r t) := by
  set I1 := (∫ x in (0 : ℝ)..1, Kax (Work.Kernels.Khat ℓ d) τ (x - 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
          * ((x : ℂ) + (1 : ℂ) * Complex.I))) with hI1
  set I2 := (∫ x in (-1 : ℝ)..0, Kax (Work.Kernels.Khat ℓ d) τ (x + 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
          * ((x : ℂ) + (1 : ℂ) * Complex.I))) with hI2
  set U0 := (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ 0 t
      * Work.Asymptotics.gaussWeight r t) with hU0
  set Um := (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ (-1) t
      * Work.Asymptotics.gaussWeight r t) with hUm
  set Up := (∫ t in Set.Ioi 1, Kax (Work.Kernels.Khat ℓ d) τ 1 t
      * Work.Asymptotics.gaussWeight r t) with hUp
  have h1 : I1 = - Complex.I * Work.Asymptotics.kerExp r (1 : ℂ) * U0 + Complex.I * Um := by
    rw [hI1, hU0, hUm]; exact hminus
  have h2 : I2 = - Complex.I * Up + Complex.I * Work.Asymptotics.kerExp r (-1 : ℂ) * U0 := by
    rw [hI2, hUp, hU0]; exact hplus
  have hP2 : P2 (Work.Kernels.Khat ℓ d) r τ = - Complex.I * I1 + Complex.I * I2 := by
    rw [P2]
    simp only [hsplit, Complex.ofReal_one]
    rw [← hI1, ← hI2]
  have e0 : (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 0 t
      * Work.Asymptotics.gaussWeight r t) = U0 := by
    rw [hU0]; exact MeasureTheory.integral_Ici_eq_integral_Ioi
  have em : (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ (-1) t
      * Work.Asymptotics.gaussWeight r t) = Um := by
    rw [hUm]; exact MeasureTheory.integral_Ici_eq_integral_Ioi
  have ep : (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 1 t
      * Work.Asymptotics.gaussWeight r t) = Up := by
    rw [hUp]; exact MeasureTheory.integral_Ici_eq_integral_Ioi
  rw [hP2, h1, h2, e0, em, ep]
  calc -Complex.I * (-Complex.I * Work.Asymptotics.kerExp r (1 : ℂ) * U0 + Complex.I * Um)
        + Complex.I * (-Complex.I * Up + Complex.I * Work.Asymptotics.kerExp r (-1 : ℂ) * U0)
      = (Complex.I * Complex.I) * ((Work.Asymptotics.kerExp r (1 : ℂ)
          + Work.Asymptotics.kerExp r (-1 : ℂ)) * U0 - Um - Up) := by ring
    _ = Um + Up - (Work.Asymptotics.kerExp r (1 : ℂ) + Work.Asymptotics.kerExp r (-1 : ℂ)) * U0 := by
        rw [Complex.I_mul_I]; ring

/-- **The final algebra of the contour identity.**  From the three reductions
`paperLayerK = P₁ + sinSqC·B₀`, `P₃ = 2B₀ - Bm - Bp` and `P₂ = Bm + Bp - (e^{iλ}+e^{-iλ})·B₀`,
together with `sinSqC r = 2 - e^{iλ} - e^{-iλ}`, the identity follows. -/
theorem shift_identity_khat_core (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {τ : UpperHalfPlane} {r : ℝ}
    (hA : paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ
      = P1 (Work.Kernels.Khat ℓ d) r τ
        + Work.Asymptotics.sinSqC r * ∫ t in Set.Ici (1 : ℝ),
            Kax (Work.Kernels.Khat ℓ d) τ 0 t * Work.Asymptotics.gaussWeight r t)
    (hB : P3 (Work.Kernels.Khat ℓ d) r τ
      = 2 * (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 0 t
            * Work.Asymptotics.gaussWeight r t)
        - (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ (-1) t
            * Work.Asymptotics.gaussWeight r t)
        - (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 1 t
            * Work.Asymptotics.gaussWeight r t))
    (hC : P2 (Work.Kernels.Khat ℓ d) r τ
      = (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ (-1) t
            * Work.Asymptotics.gaussWeight r t)
        + (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 1 t
            * Work.Asymptotics.gaussWeight r t)
        - (Work.Asymptotics.kerExp r (1 : ℂ) + Work.Asymptotics.kerExp r (-1 : ℂ))
          * (∫ t in Set.Ici (1 : ℝ), Kax (Work.Kernels.Khat ℓ d) τ 0 t
              * Work.Asymptotics.gaussWeight r t)) :
    paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ
      = P1 (Work.Kernels.Khat ℓ d) r τ
        + P2 (Work.Kernels.Khat ℓ d) r τ
        + P3 (Work.Kernels.Khat ℓ d) r τ := by
  rw [hA, hB, hC, sinSqC_eq_two_sub_kerExp']
  ring


/-- **The contour shift `F̃ = P₁+P₂+P₃` for the hatted kernel `K̂`, for `2 < r²`** (CKMRV (5.12)
with `K̂` in place of `K`).  This is the hatted companion of `shift_identity_kfun`; the two are
needed as the input of the analytic continuation of the identity in `λ = πr²` (both sides are
holomorphic on `{z : -π < z.re}` and agree on the real interval `(2π, ∞)`).

`Work.CKFinal.P2` was repaired on 2026-09-26: its two interval integrals are now explicitly
parenthesised.  Before that repair Lean's interval-integral notation absorbed the trailing `+` into
the first integrand, which is why an earlier attempt at this identity was correctly declared FALSE.
With the repaired `P2` the identity is true.

Route: write `sinSqC r = 2 - e^{iλ} - e^{-iλ}` and turn `∫_1^∞ K̂(τ,it)e^{-λt}dt` into the three
vertical rays at `Re w = 0, ±1` (split at height `hsplit = 1`); for `λ > 2π` the rays at `Re w = ±1`
may be shifted to `Re w = 0` through the half-strips `[0,1]×[1,∞)` and `[-1,0]×[1,∞)` of
`Work.Asymptotics.rectInt_eq_residue`, the top edges vanishing because `K̂(τ,·)` is
`O(poly·e^{-π Im})` there.  All residues vanish — `Work.Residues.hasResidue_Khat_second` and the
diagonal residues `hasResidue_KPlus_self`/`hasResidue_KMinus_self` — so no Gaussian term appears;
the two remaining rays at `Re w = 0` recombine, via the second difference, into `P₃`, and the two
bottom edges are exactly the two summands of `P₂`.  The only orbit points involved are `τ, τ±1`
(`LineDecay/orbit_classification`). -/
theorem shift_identity_khat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2) :
    (τ.re = 1 / 2 ∨ τ.re = - 1 / 2) → 12 ≤ τ.im →
    Work.CKFinal.paperLayerK (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) r τ
      = Work.CKFinal.P1 (Work.Kernels.Khat ℓ d) r τ
        + Work.CKFinal.P2 (Work.Kernels.Khat ℓ d) r τ
        + Work.CKFinal.P3 (Work.Kernels.Khat ℓ d) r τ := by
  intro hre him
  obtain ⟨C, hC, M, T, hT, hray, hfar⟩ := Khat_ray_far_bound ℓ d hd τ hre him
  exact shift_identity_khat_core ℓ d
    (paperLayerK_eq ℓ d hd τ hr hre him hC hray)
    (P3_eq ℓ d hd τ hr hre him hC hray)
    (P2_eq_of_shifts ℓ d τ
      (shift_ray_weak_minus_self ℓ d hd τ hr hre him hC hT hray hfar)
      (shift_ray_weak_plus_self ℓ d hd τ hr hre him hC hT hray hfar))

end

end Work.CKFinal.LineDecay
