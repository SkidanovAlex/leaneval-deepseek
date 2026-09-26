/-
# Atom bounds on the axis below the diagonal

This file sets up the bookkeeping used to bound the explicit kernel `K_+^{(d)}` on the
imaginary axis `z = i t`, in the region

  `τ ∈ 𝒟` (the CKMRV fundamental domain `DomainD`), `2 ≤ Im τ`, `1 ≤ t ≤ Im τ - 1`.

Every `τ`-atom (`E₂(τ)`, `E₄(τ)`, `Δ(τ)`, `φ₀(τ) = τE₂(τ) - 3i/π`, …) and every `z`-atom
(`E₄(it)`, `Δ(it)`, `E₂ˢ(it)`, `j(τ) - j(it)`, …) is bounded by

  `C * (scale τ)^N * (1+t)^M * exp (a*t + b*Im τ)`,

which is the predicate `BddAX H a b f` (`H` is a lower bound for `Im τ`, needed only for the
lower bound on `‖j(τ) - j(it)‖`).  The closure lemmas (`add`, `mul`, `const`, `sub`, …) make
the entrywise estimates of `K_+^{(8)}` and `K_+^{(24)}` purely mechanical, and the two
conversion lemmas `to_target1` / `to_target2` turn such a bound into the shape required by
`funnelKernelPre`: on the region `t ≤ Im τ - 1` one has `exp (a t + b Im τ) ≤ exp ((a+b) t)`
when `b ≤ 0`, so an exponent `a + b ≤ 0` is absorbed into the polynomial part and an exponent
`a + b ≤ 2π` into the factor `e^{2πt}` allowed in dimension 24.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.E4Fun_upper_half
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop
import Submission.Work.Residues.kpre_inv_axis_bound
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Asymptotics.KPlus_eight_decomposition

namespace Work.Asymptotics

noncomputable section

open UpperHalfPlane
open scoped Topology

open Work.Kernels

/-! ## The point `it` of the imaginary axis, as a total function of `t` -/

/-- The point `it` of the imaginary axis, as a total function of `t` (junk for `t ≤ 0`). -/
def cti (t : ℝ) : ℍ := if h : 0 < t then imagAxis t h else ⟨Complex.I, by simp⟩

lemma cti_eq_imagAxis {t : ℝ} (h : 0 < t) : cti t = imagAxis t h := by
  simp [cti, h]

lemma cti_im {t : ℝ} (h : 0 < t) : (cti t).im = t := by
  rw [cti_eq_imagAxis h]
  simp [Work.Kernels.imagAxis]

lemma cti_coe {t : ℝ} (h : 0 < t) : ((cti t : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
  rw [cti_eq_imagAxis h]
  rfl

lemma norm_cti_coe {t : ℝ} (h : 0 < t) : ‖((cti t : ℍ) : ℂ)‖ = t := by
  have hcoe := cti_coe h
  have hsq : ‖((cti t : ℍ) : ℂ)‖ ^ 2 = t ^ 2 := by
    rw [hcoe, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
    ring
  have hnn : (0:ℝ) ≤ ‖((cti t : ℍ) : ℂ)‖ := norm_nonneg _
  nlinarith [hsq, hnn, h]

/-! ## The bookkeeping predicate -/

/-- `BddAX H a b f` : on the funnel `τ ∈ 𝒟`, `2 ≤ Im τ`, `H ≤ Im τ`, `1 ≤ t ≤ Im τ - 1`,
the function `f` is bounded by `C (scale τ)^N (1+t)^M e^{a t + b Im τ}`. -/
def BddAX (H : ℝ) (a b : ℝ) (f : ℍ → ℝ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖f τ t‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M * Real.exp (a * t + b * τ.im)

/-- Convert a plain estimate into a `BddAX` estimate. -/
lemma BddAX.of_bound {H a b C N M : ℝ} (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    {f : ℍ → ℝ → ℂ}
    (h : ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖f τ t‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M * Real.exp (a * t + b * τ.im)) :
    BddAX H a b f := ⟨C, N, M, hC, hN, hM, h⟩

/-- A function bounded by a constant. -/
lemma BddAX.of_le_const {H : ℝ} {c : ℝ} {f : ℍ → ℝ → ℂ}
    (h : ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 → ‖f τ t‖ ≤ c) :
    BddAX H 0 0 f := by
  refine ⟨max 1 c, 0, 0, lt_of_lt_of_le (zero_lt_one : (0:ℝ) < 1) (le_max_left _ _),
    le_rfl, le_rfl, fun τ t hF hH h1 h2 => ?_⟩
  have := le_trans (h τ t hF hH h1 h2) (le_max_right (1:ℝ) c)
  simpa using this

/-- A function bounded by a polynomial in `scale τ` and `1 + t` (with `a = b = 0`). -/
lemma BddAX.of_le_poly {H : ℝ} {C N M : ℝ} (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    {f : ℍ → ℝ → ℂ}
    (h : ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖f τ t‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M) : BddAX H 0 0 f :=
  ⟨C, N, M, hC, hN, hM, fun τ t hF hH h1 h2 => by simpa using h τ t hF hH h1 h2⟩

/-- A function bounded by `C e^{a t + b Im τ}`. -/
lemma BddAX.of_le_exp {H a b C : ℝ} (hC : 0 < C) {f : ℍ → ℝ → ℂ}
    (h : ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖f τ t‖ ≤ C * Real.exp (a * t + b * τ.im)) : BddAX H a b f :=
  ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ t hF hH h1 h2 => by simpa using h τ t hF hH h1 h2⟩

/-! ## Closure properties -/

lemma mul_rpow_rpow_exp_mono {S T C N N' M M' E E' : ℝ} (hC : 0 ≤ C) (hS : 1 ≤ S)
    (hT : 1 ≤ T) (hN : N ≤ N') (hM : M ≤ M') (hE : 0 ≤ E) (hEE : E ≤ E') :
    C * S ^ N * T ^ M * E ≤ C * S ^ N' * T ^ M' * E' := by
  have h1 : C * S ^ N ≤ C * S ^ N' := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hS hN) hC
  have h2 : C * S ^ N * T ^ M ≤ C * S ^ N' * T ^ M' :=
    mul_le_mul h1 (Real.rpow_le_rpow_of_exponent_le hT hM) (Real.rpow_nonneg (by linarith) _)
      (by positivity)
  exact (mul_le_mul_of_nonneg_right h2 hE).trans (mul_le_mul_of_nonneg_left hEE (by positivity))

lemma exp_le_exp_max_l (a1 b1 a2 b2 : ℝ) {τ : ℍ} {t : ℝ} (hτ : 2 ≤ τ.im) (ht : 1 ≤ t) :
    Real.exp (a1 * t + b1 * τ.im) ≤ Real.exp (max a1 a2 * t + max b1 b2 * τ.im) := by
  apply Real.exp_le_exp.mpr
  have ht0 : (0:ℝ) ≤ t := by linarith
  have him0 : (0:ℝ) ≤ τ.im := by linarith
  have h1 : a1 * t ≤ max a1 a2 * t := mul_le_mul_of_nonneg_right (le_max_left a1 a2) ht0
  have h2 : b1 * τ.im ≤ max b1 b2 * τ.im := mul_le_mul_of_nonneg_right (le_max_left b1 b2) him0
  linarith

lemma exp_le_exp_max_r (a1 b1 a2 b2 : ℝ) {τ : ℍ} {t : ℝ} (hτ : 2 ≤ τ.im) (ht : 1 ≤ t) :
    Real.exp (a2 * t + b2 * τ.im) ≤ Real.exp (max a1 a2 * t + max b1 b2 * τ.im) := by
  apply Real.exp_le_exp.mpr
  have ht0 : (0:ℝ) ≤ t := by linarith
  have him0 : (0:ℝ) ≤ τ.im := by linarith
  have h1 : a2 * t ≤ max a1 a2 * t := mul_le_mul_of_nonneg_right (le_max_right a1 a2) ht0
  have h2 : b2 * τ.im ≤ max b1 b2 * τ.im := mul_le_mul_of_nonneg_right (le_max_right b1 b2) him0
  linarith

lemma BddAX.mono {H a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') {f : ℍ → ℝ → ℂ}
    (h : BddAX H a b f) : BddAX H a' b' f := by
  obtain ⟨C, N, M, hC, hN, hM, hbnd⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ t hF hH h1 h2 => ?_⟩
  refine le_trans (hbnd τ t hF hH h1 h2) ?_
  have hexp : Real.exp (a * t + b * τ.im) ≤ Real.exp (a' * t + b' * τ.im) := by
    apply Real.exp_le_exp.mpr
    have ht0 : (0:ℝ) ≤ t := by linarith
    have him0 : (0:ℝ) ≤ τ.im := by linarith
    have hA : a * t ≤ a' * t := mul_le_mul_of_nonneg_right ha ht0
    have hB : b * τ.im ≤ b' * τ.im := mul_le_mul_of_nonneg_right hb him0
    linarith
  exact mul_rpow_rpow_exp_mono hC.le (one_le_scale τ) (by linarith) le_rfl le_rfl
    (Real.exp_nonneg _) hexp

lemma BddAX.congr {H a b : ℝ} {f g : ℍ → ℝ → ℂ} (h : BddAX H a b f)
    (hfg : ∀ τ t, f τ t = g τ t) : BddAX H a b g := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ t hF hH h1 h2 => by rw [← hfg τ t]; exact hb τ t hF hH h1 h2⟩

/-- Congruence of `BddAX` bounds along an equality valid on the region. -/
lemma BddAX.congr_region {H a b : ℝ} {f g : ℍ → ℝ → ℂ} (h : BddAX H a b f)
    (hfg : ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 → f τ t = g τ t) :
    BddAX H a b g := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM,
    fun τ t hF hH h1 h2 => by rw [← hfg τ t hF hH h1 h2]; exact hb τ t hF hH h1 h2⟩

/-- Adjusting the exponents by zero. -/
lemma BddAX.congr_exp {H a b a' b' : ℝ} (ha : a' = a) (hb : b' = b) {f : ℍ → ℝ → ℂ}
    (h : BddAX H a b f) : BddAX H a' b' f := by rw [ha, hb]; exact h

lemma BddAX.const {H : ℝ} (c : ℂ) : BddAX H 0 0 (fun (_ : ℍ) (_ : ℝ) => c) := by
  refine ⟨max 1 ‖c‖, 0, 0, lt_of_lt_of_le (zero_lt_one : (0:ℝ) < 1) (le_max_left _ _),
    le_rfl, le_rfl, fun τ t hF hH h1 h2 => ?_⟩
  have : ‖c‖ ≤ max 1 ‖c‖ := le_max_right _ _
  simpa using this

lemma BddAX.add {H a1 b1 a2 b2 : ℝ} {f g : ℍ → ℝ → ℂ} (hf : BddAX H a1 b1 f)
    (hg : BddAX H a2 b2 g) : BddAX H (max a1 a2) (max b1 b2) (fun τ t => f τ t + g τ t) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by positivity, le_trans hN1 (le_max_left _ _),
    le_trans hM1 (le_max_left _ _), fun τ t hF hH h1 h2 => ?_⟩
  have hτ : 2 ≤ τ.im := hF.2
  have hE1 := exp_le_exp_max_l a1 b1 a2 b2 hτ h1
  have hE2 := exp_le_exp_max_r a1 b1 a2 b2 hτ h1
  have hb1' : ‖f τ t‖ ≤ C1 * scale τ ^ (max N1 N2) * (1 + t) ^ (max M1 M2) *
      Real.exp (max a1 a2 * t + max b1 b2 * τ.im) :=
    (hb1 τ t hF hH h1 h2).trans (mul_rpow_rpow_exp_mono hC1.le (one_le_scale τ) (by linarith)
      (le_max_left _ _) (le_max_left _ _) (Real.exp_nonneg _) hE1)
  have hb2' : ‖g τ t‖ ≤ C2 * scale τ ^ (max N1 N2) * (1 + t) ^ (max M1 M2) *
      Real.exp (max a1 a2 * t + max b1 b2 * τ.im) :=
    (hb2 τ t hF hH h1 h2).trans (mul_rpow_rpow_exp_mono hC2.le (one_le_scale τ) (by linarith)
      (le_max_right _ _) (le_max_right _ _) (Real.exp_nonneg _) hE2)
  calc ‖f τ t + g τ t‖ ≤ ‖f τ t‖ + ‖g τ t‖ := norm_add_le _ _
    _ ≤ C1 * scale τ ^ (max N1 N2) * (1 + t) ^ (max M1 M2) *
          Real.exp (max a1 a2 * t + max b1 b2 * τ.im)
        + C2 * scale τ ^ (max N1 N2) * (1 + t) ^ (max M1 M2) *
          Real.exp (max a1 a2 * t + max b1 b2 * τ.im) := add_le_add hb1' hb2'
    _ = (C1 + C2) * scale τ ^ (max N1 N2) * (1 + t) ^ (max M1 M2) *
          Real.exp (max a1 a2 * t + max b1 b2 * τ.im) := by ring

lemma BddAX.mul {H a1 b1 a2 b2 : ℝ} {f g : ℍ → ℝ → ℂ} (hf : BddAX H a1 b1 f)
    (hg : BddAX H a2 b2 g) : BddAX H (a1 + a2) (b1 + b2) (fun τ t => f τ t * g τ t) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨C1 * C2, N1 + N2, M1 + M2, by positivity, by linarith, by linarith,
    fun τ t hF hH h1 h2 => ?_⟩
  have hSpos : (0:ℝ) < scale τ := scale_pos τ
  rw [norm_mul]
  have h1' := hb1 τ t hF hH h1 h2
  have h2' := hb2 τ t hF hH h1 h2
  have hpow : (scale τ) ^ N1 * (scale τ) ^ N2 = (scale τ) ^ (N1 + N2) :=
    (Real.rpow_add hSpos N1 N2).symm
  have hpowT : (1 + t) ^ M1 * (1 + t) ^ M2 = (1 + t) ^ (M1 + M2) :=
    (Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M1 M2).symm
  have hexp : Real.exp (a1 * t + b1 * τ.im) * Real.exp (a2 * t + b2 * τ.im)
      = Real.exp ((a1 + a2) * t + (b1 + b2) * τ.im) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖f τ t‖ * ‖g τ t‖
      ≤ (C1 * scale τ ^ N1 * (1 + t) ^ M1 * Real.exp (a1 * t + b1 * τ.im)) *
        (C2 * scale τ ^ N2 * (1 + t) ^ M2 * Real.exp (a2 * t + b2 * τ.im)) :=
        mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
    _ = (C1 * C2) * (scale τ ^ N1 * scale τ ^ N2) * ((1 + t) ^ M1 * (1 + t) ^ M2) *
          (Real.exp (a1 * t + b1 * τ.im) * Real.exp (a2 * t + b2 * τ.im)) := by ring
    _ = (C1 * C2) * scale τ ^ (N1 + N2) * (1 + t) ^ (M1 + M2) *
          Real.exp ((a1 + a2) * t + (b1 + b2) * τ.im) := by rw [hpow, hpowT, hexp]

lemma BddAX.const_mul {H a b : ℝ} (c : ℂ) {f : ℍ → ℝ → ℂ} (h : BddAX H a b f) :
    BddAX H a b (fun τ t => c * f τ t) := by
  have := BddAX.mul (BddAX.const (H := H) c) h
  simpa using this

lemma BddAX.neg {H a b : ℝ} {f : ℍ → ℝ → ℂ} (h : BddAX H a b f) :
    BddAX H a b (fun τ t => -f τ t) := by
  have := BddAX.mul (BddAX.const (H := H) (-1)) h
  simpa using this

lemma BddAX.sub {H a1 b1 a2 b2 : ℝ} {f g : ℍ → ℝ → ℂ} (hf : BddAX H a1 b1 f)
    (hg : BddAX H a2 b2 g) : BddAX H (max a1 a2) (max b1 b2) (fun τ t => f τ t - g τ t) := by
  refine (BddAX.add hf (BddAX.neg hg)).congr (fun τ t => ?_)
  show f τ t + -g τ t = f τ t - g τ t
  ring

/-- On the region, an exponent `a t + b Im τ` with `b ≤ 0` is at most `(a+b) t`. -/
lemma BddAX.norm_b {H a b : ℝ} {f : ℍ → ℝ → ℂ} (hb : b ≤ 0) (h : BddAX H a b f) :
    BddAX H (a + b) 0 f := by
  obtain ⟨C, N, M, hC, hN, hM, hbnd⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ t hF hH h1 h2 => ?_⟩
  refine le_trans (hbnd τ t hF hH h1 h2) ?_
  have hexp : Real.exp (a * t + b * τ.im) ≤ Real.exp ((a + b) * t + 0 * τ.im) := by
    apply Real.exp_le_exp.mpr
    have h2' : (0:ℝ) ≤ τ.im - t := by linarith [hF.2]
    have : b * (τ.im - t) ≤ 0 := by nlinarith
    nlinarith
  exact mul_rpow_rpow_exp_mono hC.le (one_le_scale τ) (by linarith) le_rfl le_rfl
    (Real.exp_nonneg _) hexp

/-- Conversion to the shape required by `funnelKernelPre` in dimension `8`. -/
lemma BddAX.to_target1 {H a b : ℝ} {f : ℍ → ℝ → ℂ} (hb : b ≤ 0) (hab : a + b ≤ 0)
    (h : BddAX H a b f) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im →
      1 ≤ t → t ≤ τ.im - 1 → ‖f τ t‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, M, hC, hN, hM, hbnd⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ t hF hH h1 h2 => ?_⟩
  refine le_trans (hbnd τ t hF hH h1 h2) ?_
  have hexp : Real.exp (a * t + b * τ.im) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h2' : (0:ℝ) ≤ τ.im - t := by linarith [hF.2]
    have hb' : b * (τ.im - t) ≤ 0 := by nlinarith
    have ht0 : (0:ℝ) ≤ t := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hab ht0]
  have hnn : (0:ℝ) ≤ C * (scale τ) ^ N * (1 + t) ^ M :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (scale_pos τ).le N))
      (Real.rpow_nonneg (by linarith) M)
  calc C * (scale τ) ^ N * (1 + t) ^ M * Real.exp (a * t + b * τ.im)
      ≤ C * (scale τ) ^ N * (1 + t) ^ M * 1 := mul_le_mul_of_nonneg_left hexp hnn
    _ = C * (scale τ) ^ N * (1 + t) ^ M := by ring

/-- Conversion to the shape required by `funnelKernelPre` in dimension `24`. -/
lemma BddAX.to_target2 {H a b : ℝ} {f : ℍ → ℝ → ℂ} (hb : b ≤ 0) (hab : a + b ≤ 2 * Real.pi)
    (h : BddAX H a b f) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im →
      1 ≤ t → t ≤ τ.im - 1 →
      ‖f τ t‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M * Real.exp (2 * Real.pi * t) := by
  obtain ⟨C, N, M, hC, hN, hM, hbnd⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ t hF hH h1 h2 => ?_⟩
  refine le_trans (hbnd τ t hF hH h1 h2) ?_
  have hexp : Real.exp (a * t + b * τ.im) ≤ Real.exp (2 * Real.pi * t) := by
    apply Real.exp_le_exp.mpr
    have h2' : (0:ℝ) ≤ τ.im - t := by linarith [hF.2]
    have hb' : b * (τ.im - t) ≤ 0 := by nlinarith
    have ht0 : (0:ℝ) ≤ t := by linarith
    have := mul_le_mul_of_nonneg_right hab ht0
    nlinarith
  have hnn : (0:ℝ) ≤ C * (scale τ) ^ N * (1 + t) ^ M :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (scale_pos τ).le N))
      (Real.rpow_nonneg (by linarith) M)
  exact mul_le_mul_of_nonneg_left hexp hnn

/-! ## The lower bound for `‖j(τ) - j(it)‖` -/

/-- The threshold beyond which `‖E₄ τ‖ ≥ 1/2`. -/
noncomputable def Hj : ℝ := max (Classical.choose exists_bound_norm_E4Fun_atImInfty) 1

lemma Hj_spec : ∀ τ : ℍ, Hj ≤ τ.im → (1/2 : ℝ) ≤ ‖E4Fun τ‖ :=
  fun τ h => Classical.choose_spec exists_bound_norm_E4Fun_atImInfty τ
    (le_trans (le_max_left _ _) h)

lemma Hj_nonneg : (0:ℝ) ≤ Hj := le_trans (zero_le_one) (le_max_right _ _)

/-- On the region `t ≤ Im τ - 1`, the divisor `j(τ) - j(it)` is bounded below by a constant
times `e^{2π Im τ}`.  This is `Work.Residues.jInvariant_axis_diff_lower` with the threshold
`Hj` of `exists_bound_norm_E4Fun_atImInfty`. -/
lemma jDiff_lower_H :
    ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), Hj ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      (1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im)
        ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ :=
  fun τ t ht hτ ht1 htle => Work.Residues.jInvariant_axis_diff_lower
    (fun τ hτ => DeltaFun_upper_sharp τ hτ)
    (fun t ht ht1 => DeltaFun_imagAxis_lower_sharp t ht ht1)
    (fun τ hτ => E4Fun_upper_half τ hτ)
    (A := Hj) (fun τ hτ => Hj_spec τ hτ)
    τ t ht (max_le hτ (by linarith)) ht1 htle

/-- `‖(j(τ) - j(it))⁻¹‖ ≤ (1/16 - (27/4)e^{-2π})⁻¹ e^{-2π Im τ}`. -/
lemma BddAX.J_inv {H : ℝ} (hH : Hj ≤ H) :
    BddAX H 0 (-(2*Real.pi))
      (fun τ t => (jInvariantFun τ - jInvariantFun (cti t))⁻¹) := by
  have hc : (0:ℝ) < 1/16 - 27/4 * Real.exp (-(2*Real.pi)) :=
    Work.Residues.kpre_axis_const_pos
  refine BddAX.of_le_exp (C := (1/16 - 27/4 * Real.exp (-(2*Real.pi)))⁻¹)
    (inv_pos.mpr hc) (fun τ t hF hH' h1 h2 => ?_)
  have ht0 : 0 < t := by linarith
  have hrew : jInvariantFun (cti t) = jInvariantFun (imagAxis t ht0) := by
    rw [cti_eq_imagAxis ht0]
  rw [hrew, norm_inv]
  have hl := jDiff_lower_H τ t ht0 (le_trans hH hH') h1 h2
  have hpos : (0:ℝ) < (1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im) :=
    mul_pos hc (Real.exp_pos _)
  have hinv : ‖jInvariantFun τ - jInvariantFun (imagAxis t ht0)‖⁻¹
      ≤ ((1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos hl
  calc ‖jInvariantFun τ - jInvariantFun (imagAxis t ht0)‖⁻¹
      ≤ ((1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im))⁻¹ := hinv
    _ = (1/16 - 27/4 * Real.exp (-(2*Real.pi)))⁻¹ * Real.exp (-(2*Real.pi*τ.im)) := by
        rw [mul_inv]
        congr 1
        exact (Real.exp_neg (2*Real.pi*τ.im)).symm
    _ = (1/16 - 27/4 * Real.exp (-(2*Real.pi)))⁻¹ *
          Real.exp (0 * t + (-(2*Real.pi)) * τ.im) := by congr 1; ring

/-! ## The `τ`-atoms -/

lemma BddAX.self_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => (τ : ℂ)) := by
  refine BddAX.of_le_poly (C := 1) (N := 1) (M := 0) one_pos (by norm_num) le_rfl ?_
  intro τ t hF hH h1 h2
  have hle : ‖(τ : ℂ)‖ ≤ scale τ := by
    have hdef : scale τ = 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := rfl
    have hpos : 0 < (τ.im)⁻¹ := inv_pos.mpr τ.im_pos
    linarith [hdef, hpos]
  calc ‖(τ : ℂ)‖ ≤ scale τ := hle
    _ = 1 * scale τ ^ (1:ℝ) * (1 + t) ^ (0:ℝ) := by
        rw [Real.rpow_one, Real.rpow_zero]; ring

lemma BddAX.e2_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => E2Fun τ) := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  exact BddAX.of_le_const (fun τ t hF _ _ _ => h τ (by linarith [hF.2]))

lemma BddAX.e4_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => E4Fun τ) :=
  BddAX.of_le_const (fun τ t hF _ _ _ => E4Fun_upper_half τ (by linarith [hF.2]))

lemma BddAX.e6_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => E6Fun τ) := by
  obtain ⟨C, hC, h⟩ := E6Fun_bound
  exact BddAX.of_le_const (fun τ t hF _ _ _ => h τ (by linarith [hF.2]))

lemma BddAX.e8_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => E8Fun τ) :=
  ((BddAX.mul (BddAX.e4_tau (H := H)) (BddAX.e4_tau (H := H))).congr_exp
      (by norm_num) (by norm_num)).congr (fun τ t => by
    show E4Fun τ * E4Fun τ = E8Fun τ
    rw [show E8Fun τ = E4Fun τ ^ 2 from rfl, pow_two])

lemma BddAX.e10_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => E10Fun τ) :=
  ((BddAX.mul (BddAX.e4_tau (H := H)) (BddAX.e6_tau (H := H))).congr_exp
      (by norm_num) (by norm_num)).congr (fun τ t => rfl)

lemma BddAX.e14_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => E14Fun τ) :=
  ((BddAX.mul (BddAX.e8_tau (H := H)) (BddAX.e6_tau (H := H))).congr_exp
      (by norm_num) (by norm_num)).congr (fun τ t => rfl)

lemma BddAX.delta_tau {H : ℝ} :
    BddAX H 0 (-(2*Real.pi)) (fun τ (_ : ℝ) => DeltaFun τ) := by
  refine BddAX.of_le_exp (C := 2) (by norm_num) (fun τ t hF hH h1 h2 => ?_)
  have h := DeltaFun_upper_sharp τ (by linarith [hF.2])
  calc ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) := h
    _ = 2 * Real.exp (0 * t + (-(2*Real.pi)) * τ.im) := by congr 1; ring

lemma BddAX.invdelta_tau {H : ℝ} :
    BddAX H 0 (2*Real.pi) (fun τ (_ : ℝ) => (DeltaFun τ)⁻¹) := by
  obtain ⟨c, hc, h⟩ := exists_Delta_Funnel_lower
  refine BddAX.of_le_exp (C := 1/c) (one_div_pos.mpr hc) (fun τ t hF hH h1 h2 => ?_)
  have hl := h τ hF
  have hpos : (0:ℝ) < c * Real.exp (-(2*Real.pi*τ.im)) := by positivity
  rw [norm_inv]
  have hinv : ‖DeltaFun τ‖⁻¹ ≤ (c * Real.exp (-(2*Real.pi*τ.im)))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos hl
  calc ‖DeltaFun τ‖⁻¹ ≤ (c * Real.exp (-(2*Real.pi*τ.im)))⁻¹ := hinv
    _ = (1/c) * Real.exp (2*Real.pi*τ.im) := by
        rw [mul_inv, Real.exp_neg, inv_inv, one_div]
    _ = (1/c) * Real.exp (0 * t + (2*Real.pi) * τ.im) := by congr 1; ring

lemma BddAX.j_tau {H : ℝ} :
    BddAX H 0 (2*Real.pi) (fun τ (_ : ℝ) => jInvariantFun τ) := by
  obtain ⟨C, hC, h⟩ := exists_jInvariantFun_Funnel_bound
  refine BddAX.of_le_exp (C := C) hC (fun τ t hF hH h1 h2 => ?_)
  calc ‖jInvariantFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := h τ hF
    _ = C * Real.exp (0 * t + (2*Real.pi) * τ.im) := by congr 1; ring

lemma BddAX.phi0_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => phi0 τ) := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  refine BddAX.of_le_poly (C := C + 3 / Real.pi) (N := 1) (M := 0)
    (add_pos hC (div_pos (by norm_num) Real.pi_pos)) (by norm_num) le_rfl ?_
  intro τ t hF hH h1 h2
  have hτ : 1 ≤ τ.im := by linarith [hF.2]
  have hE : ‖E2Fun τ‖ ≤ C := h τ hτ
  have hscale : ‖(τ : ℂ)‖ ≤ scale τ := by
    have hdef : scale τ = 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := rfl
    have hpos : 0 < (τ.im)⁻¹ := inv_pos.mpr τ.im_pos
    linarith [hdef, hpos]
  have hnum : ‖(τ : ℂ) * E2Fun τ‖ ≤ C * scale τ := by
    rw [norm_mul]
    calc ‖(τ : ℂ)‖ * ‖E2Fun τ‖ ≤ scale τ * C :=
          mul_le_mul hscale hE (norm_nonneg _) (scale_pos τ).le
      _ = C * scale τ := by ring
  have hconst : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hphi : phi0 τ = (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := rfl
  rw [hphi]
  calc ‖(τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(τ : ℂ) * E2Fun τ‖ + ‖3 * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ ≤ C * scale τ + 3 / Real.pi := add_le_add hnum (le_of_eq hconst)
    _ ≤ (C + 3 / Real.pi) * scale τ := by
        have hs1 : (1:ℝ) ≤ scale τ := one_le_scale τ
        have h3 : (0:ℝ) ≤ 3 / Real.pi := by positivity
        have := mul_le_mul_of_nonneg_left hs1 h3
        nlinarith [this]
    _ = (C + 3 / Real.pi) * scale τ ^ (1:ℝ) * (1 + t) ^ (0:ℝ) := by
        rw [Real.rpow_one, Real.rpow_zero]; ring

lemma BddAX.phi2_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => phi2 τ) := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  have hCnn : (0:ℝ) ≤ C := hC.le
  refine BddAX.of_le_poly (C := C^2 + 6 / Real.pi * C) (N := 2) (M := 0)
    (add_pos (pow_pos hC 2) (mul_pos (div_pos (by norm_num) Real.pi_pos) hC))
    (by norm_num) le_rfl ?_
  intro τ t hF hH h1 h2
  have hτ : 1 ≤ τ.im := by linarith [hF.2]
  have hE : ‖E2Fun τ‖ ≤ C := h τ hτ
  have hE2 : ‖E2Fun τ ^ 2‖ ≤ C ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE 2
  have hscale : ‖(τ : ℂ)‖ ≤ scale τ := by
    have hdef : scale τ = 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := rfl
    have hpos : 0 < (τ.im)⁻¹ := inv_pos.mpr τ.im_pos
    linarith [hdef, hpos]
  have hs1 : (1:ℝ) ≤ scale τ := one_le_scale τ
  have hnum : ‖(τ : ℂ) * E2Fun τ ^ 2‖ ≤ C^2 * scale τ ^ 2 := by
    rw [norm_mul]
    calc ‖(τ : ℂ)‖ * ‖E2Fun τ ^ 2‖ ≤ scale τ * C^2 :=
          mul_le_mul hscale hE2 (norm_nonneg _) (by positivity)
      _ = C^2 * scale τ := by ring
      _ ≤ C^2 * (scale τ * scale τ) := by
          have hle : scale τ ≤ scale τ * scale τ := by nlinarith [hs1]
          nlinarith [hle, sq_nonneg C]
      _ = C^2 * scale τ ^ 2 := by ring
  have hconst : ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖ ≤ (6 / Real.pi) * C := by
    rw [norm_mul]
    have hc6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
      rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hc6]
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have hphi : phi2 τ = (τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ := rfl
  rw [hphi]
  calc ‖(τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖
      ≤ ‖(τ : ℂ) * E2Fun τ ^ 2‖ + ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖ :=
        norm_sub_le _ _
    _ ≤ C^2 * scale τ ^ 2 + (6 / Real.pi) * C := add_le_add hnum hconst
    _ ≤ (C^2 + 6 / Real.pi * C) * scale τ ^ 2 := by
        have hone : (1:ℝ) ≤ scale τ ^ 2 := by
          have h := Real.one_le_rpow hs1 (by norm_num : (0:ℝ) ≤ (2:ℝ))
          rwa [Real.rpow_two] at h
        have h6 : (0:ℝ) ≤ 6 / Real.pi * C := by positivity
        have hml := mul_le_mul_of_nonneg_left hone h6
        rw [mul_one] at hml
        nlinarith [hml]
    _ = (C^2 + 6 / Real.pi * C) * scale τ ^ (2:ℝ) * (1 + t) ^ (0:ℝ) := by
        rw [Real.rpow_two, Real.rpow_zero]; ring

lemma BddAX.r0_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => (τ : ℂ) * E14Fun τ) :=
  (BddAX.mul (BddAX.self_tau (H := H)) (BddAX.e14_tau (H := H))).congr_exp (by ring) (by ring)

lemma BddAX.r1_tau {H : ℝ} :
    BddAX H 0 (-(2*Real.pi)) (fun τ (_ : ℝ) => phi0 τ * DeltaFun τ) :=
  (BddAX.mul (BddAX.phi0_tau (H := H)) (BddAX.delta_tau (H := H))).congr_exp (by ring) (by ring)

lemma BddAX.r2_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => phi2 τ * E10Fun τ) :=
  (BddAX.mul (BddAX.phi2_tau (H := H)) (BddAX.e10_tau (H := H))).congr_exp (by ring) (by ring)

lemma BddAX.R0_tau {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => phi0 τ * E4Fun τ ^ 3) :=
  ((BddAX.mul (BddAX.phi0_tau (H := H))
      (BddAX.mul (BddAX.e8_tau (H := H)) (BddAX.e4_tau (H := H)))).congr_exp
    (by norm_num) (by norm_num)).congr (fun τ t => by
      show phi0 τ * (E8Fun τ * E4Fun τ) = phi0 τ * E4Fun τ ^ 3
      rw [show E8Fun τ = E4Fun τ ^ 2 from rfl]; ring)

/-! ## The `z`-atoms -/

lemma BddAX.zsq_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => ((cti t : ℍ) : ℂ) ^ 2) := by
  refine BddAX.of_le_poly (C := 1) (N := 0) (M := 2) one_pos le_rfl (by norm_num) ?_
  intro τ t hF hH h1 h2
  have ht0 : 0 < t := by linarith
  have hnorm : ‖((cti t : ℍ) : ℂ)‖ = t := norm_cti_coe ht0
  have ht2 : t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith [ht0]
  calc ‖((cti t : ℍ) : ℂ) ^ 2‖ = t ^ 2 := by rw [norm_pow, hnorm]
    _ ≤ (1 + t) ^ 2 := ht2
    _ = 1 * scale τ ^ (0:ℝ) * (1 + t) ^ (2:ℝ) := by
        rw [Real.rpow_zero, Real.rpow_two]; ring

lemma BddAX.E2S_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => E2S (cti t)) := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  refine BddAX.of_le_const (c := C + 6 / Real.pi) (fun τ t hF hH h1 h2 => ?_)
  have ht0 : 0 < t := by linarith
  have hz : 1 ≤ (cti t).im := by rw [cti_im ht0]; linarith
  have hE : ‖E2Fun (cti t)‖ ≤ C := h _ hz
  have hnorm : ‖((cti t : ℍ) : ℂ)‖ = t := norm_cti_coe ht0
  have hratio : ‖(6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (cti t : ℂ))‖ ≤ 6 / Real.pi := by
    rw [norm_div]
    have hnum : ‖(6 : ℂ) * Complex.I‖ = 6 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    rw [hnum]
    have hden : ‖(Real.pi : ℂ) * (cti t : ℂ)‖ = Real.pi * t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, hnorm]
    rw [hden]
    refine div_le_div_of_nonneg_left (by norm_num) Real.pi_pos ?_
    nlinarith [Real.pi_pos, h1]
  rw [Work.Kernels.TildeFacts.E2S_eq]
  calc ‖E2Fun (cti t) - 6 * Complex.I / ((Real.pi : ℂ) * (cti t : ℂ))‖
      ≤ ‖E2Fun (cti t)‖ + ‖6 * Complex.I / ((Real.pi : ℂ) * (cti t : ℂ))‖ := norm_sub_le _ _
    _ ≤ C + 6 / Real.pi := add_le_add hE hratio

lemma BddAX.phit0_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => phitVec (cti t) 0) :=
  (BddAX.zsq_z (H := H)).congr (fun τ t => rfl)

lemma BddAX.phit1_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => phitVec (cti t) 1) :=
  ((BddAX.mul (BddAX.zsq_z (H := H)) (BddAX.E2S_z (H := H))).congr_exp
    (by norm_num) (by norm_num)).congr (fun τ t => rfl)

lemma BddAX.phit2_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => phitVec (cti t) 2) :=
  ((BddAX.mul (BddAX.phit1_z (H := H)) (BddAX.E2S_z (H := H))).congr_exp
    (by norm_num) (by norm_num)).congr (fun τ t => by
      show phitVec (cti t) 1 * E2S (cti t) = phitVec (cti t) 2
      rw [show phitVec (cti t) 1 = ((cti t : ℍ) : ℂ) ^ 2 * E2S (cti t) from rfl,
        show phitVec (cti t) 2 = ((cti t : ℍ) : ℂ) ^ 2 * (E2S (cti t)) ^ 2 from rfl]
      ring_nf)

lemma BddAX.e4_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => E4Fun (cti t)) :=
  BddAX.of_le_const (fun τ t hF hH h1 h2 => by
    have ht0 : 0 < t := by linarith
    have hz : 1 ≤ (cti t).im := by rw [cti_im ht0]; linarith
    exact E4Fun_upper_half _ hz)

lemma BddAX.e6_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => E6Fun (cti t)) := by
  obtain ⟨C, hC, h⟩ := E6Fun_bound
  exact BddAX.of_le_const (fun τ t hF hH h1 h2 => by
    have ht0 : 0 < t := by linarith
    have hz : 1 ≤ (cti t).im := by rw [cti_im ht0]; linarith
    exact h _ hz)

lemma BddAX.e8_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => E8Fun (cti t)) :=
  ((BddAX.mul (BddAX.e4_z (H := H)) (BddAX.e4_z (H := H))).congr_exp
      (by norm_num) (by norm_num)).congr (fun τ t => by
    show E4Fun (cti t) * E4Fun (cti t) = E8Fun (cti t)
    rw [show E8Fun (cti t) = E4Fun (cti t) ^ 2 from rfl, pow_two])

lemma BddAX.e10_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => E10Fun (cti t)) :=
  ((BddAX.mul (BddAX.e4_z (H := H)) (BddAX.e6_z (H := H))).congr_exp
      (by norm_num) (by norm_num)).congr (fun τ t => rfl)

lemma BddAX.e14_z {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => E14Fun (cti t)) :=
  ((BddAX.mul (BddAX.e8_z (H := H)) (BddAX.e6_z (H := H))).congr_exp
      (by norm_num) (by norm_num)).congr (fun τ t => rfl)

lemma BddAX.delta_z {H : ℝ} : BddAX H (-(2*Real.pi)) 0 (fun (_ : ℍ) t => DeltaFun (cti t)) := by
  refine BddAX.of_le_exp (C := 2) (by norm_num) (fun τ t hF hH h1 h2 => ?_)
  have ht0 : 0 < t := by linarith
  have hz : 1 ≤ (cti t).im := by rw [cti_im ht0]; linarith
  have h := DeltaFun_upper_sharp (cti t) hz
  rw [cti_im ht0] at h
  calc ‖DeltaFun (cti t)‖ ≤ 2 * Real.exp (-(2 * Real.pi * t)) := h
    _ = 2 * Real.exp ((-(2*Real.pi)) * t + 0 * τ.im) := by congr 1; ring

lemma BddAX.invdelta_z {H : ℝ} :
    BddAX H (2*Real.pi) 0 (fun (_ : ℍ) t => (DeltaFun (cti t))⁻¹) := by
  refine BddAX.of_le_exp (C := 2) (by norm_num) (fun τ t hF hH h1 h2 => ?_)
  have ht0 : 0 < t := by linarith
  have hl := DeltaFun_imagAxis_lower_sharp t ht0 (by linarith : 1 ≤ t)
  rw [cti_eq_imagAxis ht0, norm_inv]
  have hpos : (0:ℝ) < (1/2:ℝ) * Real.exp (-(2*Real.pi*t)) := by positivity
  have hinv : ‖DeltaFun (imagAxis t ht0)‖⁻¹
      ≤ ((1/2:ℝ) * Real.exp (-(2*Real.pi*t)))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos hl
  calc ‖DeltaFun (imagAxis t ht0)‖⁻¹ ≤ ((1/2:ℝ) * Real.exp (-(2*Real.pi*t)))⁻¹ := hinv
    _ = 2 * Real.exp (2*Real.pi*t) := by
        rw [mul_inv, Real.exp_neg, inv_inv]; norm_num
    _ = 2 * Real.exp ((2*Real.pi) * t + 0 * τ.im) := by congr 1; ring

/-! ## The `d = 8` bound on the axis in the regime `Im τ ≥ H`

The template for the whole file: expand `K_+^{(8)}` with `KPlus_eight_decomposition`, write the
result as a sum of products of the atoms above, and let the closure lemmas produce
`BddAX H 0 0 (fun τ t => K_+(8)(τ, it))`.  Each summand is first *normalized* with
`BddAX.norm_b` (for `b ≤ 0` the exponent `a t + b Im τ` is replaced by `(a+b) t`) before the
summands are added: adding `(-2π, 0)` and `(0, -2π)` *before* multiplying by the prefactor
`(2π, 0)` would lose the decay coming from `Δ(τ)` and from the divisor. -/

/-- `c₈ = (36π⁻²i)⁻¹`. -/
def c8 : ℂ := ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- The `τ`-part `τE₆(τ) - 2φ₀(τ)E₄(τ)` of the `d = 8` bracket. -/
def P8a (τ : ℍ) (_ : ℝ) : ℂ := (τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ

/-- First summand of the numerator of the `d = 8` bracket (with the prefactor cleared). -/
def P8n1 (τ : ℍ) (t : ℝ) : ℂ :=
  ((phi2 τ * E14Fun τ) * DeltaFun (cti t)) * phitVec (cti t) 0

/-- Second summand of the numerator of the `d = 8` bracket (with the prefactor cleared). -/
def P8n2 (τ : ℍ) (t : ℝ) : ℂ :=
  DeltaFun τ * ((((τ : ℂ) * E6Fun τ) * E8Fun (cti t)) * phitVec (cti t) 2
    - (2 : ℂ) * (((phi0 τ * E4Fun τ) * E10Fun (cti t)) * phitVec (cti t) 1))

/-- The reciprocal of the prefactor `Δ(τ)Δ(it)(j(τ) - j(it))`. -/
def P8pre (τ : ℍ) (t : ℝ) : ℂ :=
  (DeltaFun τ)⁻¹ * (DeltaFun (cti t))⁻¹ * (jInvariantFun τ - jInvariantFun (cti t))⁻¹

lemma BddAX.P8a_bdd {H : ℝ} : BddAX H 0 0 (fun τ t => P8a τ t) := by
  have h1 : BddAX H 0 0 (fun τ (_ : ℝ) => (τ : ℂ) * E6Fun τ) :=
    (BddAX.mul (BddAX.self_tau (H := H)) (BddAX.e6_tau (H := H))).congr_exp (by ring) (by ring)
  have h2 : BddAX H 0 0 (fun τ (_ : ℝ) => phi0 τ * E4Fun τ) :=
    (BddAX.mul (BddAX.phi0_tau (H := H)) (BddAX.e4_tau (H := H))).congr_exp
      (by ring) (by ring)
  have h3 : BddAX H 0 0 (fun τ (_ : ℝ) => (2 : ℂ) * (phi0 τ * E4Fun τ)) :=
    BddAX.const_mul 2 h2
  have h4 : BddAX H (max 0 0) (max 0 0)
      (fun τ (_ : ℝ) => (τ : ℂ) * E6Fun τ - 2 * (phi0 τ * E4Fun τ)) :=
    BddAX.sub h1 h3
  refine (h4.congr_exp (by simp) (by simp)).congr_region (fun τ t _ _ _ _ => ?_)
  show (τ : ℂ) * E6Fun τ - 2 * (phi0 τ * E4Fun τ) = P8a τ t
  rw [P8a]; ring

lemma BddAX.P8n1_bdd {H : ℝ} : BddAX H (-(2*Real.pi)) 0 (fun τ t => P8n1 τ t) := by
  have h1 : BddAX H 0 0 (fun τ (_ : ℝ) => phi2 τ * E14Fun τ) :=
    (BddAX.mul (BddAX.phi2_tau (H := H)) (BddAX.e14_tau (H := H))).congr_exp
      (by ring) (by ring)
  have h2 : BddAX H (-(2*Real.pi)) 0 (fun τ t => (phi2 τ * E14Fun τ) * DeltaFun (cti t)) :=
    ((BddAX.mul h1 (BddAX.delta_z (H := H))).congr_exp (by simp) (by simp)).congr_region
      (fun _ _ _ _ _ _ => rfl)
  have h3 : BddAX H (-(2*Real.pi)) 0
      (fun τ t => ((phi2 τ * E14Fun τ) * DeltaFun (cti t)) * phitVec (cti t) 0) :=
    ((BddAX.mul h2 (BddAX.phit0_z (H := H))).congr_exp (by ring) (by ring)).congr_region
      (fun _ _ _ _ _ _ => rfl)
  refine h3.congr_region (fun τ t _ _ _ _ => ?_)
  show ((phi2 τ * E14Fun τ) * DeltaFun (cti t)) * phitVec (cti t) 0 = P8n1 τ t
  rw [P8n1]

lemma BddAX.P8n2_bdd {H : ℝ} : BddAX H (-(2*Real.pi)) 0 (fun τ t => P8n2 τ t) := by
  have hA : BddAX H 0 0 (fun τ (_ : ℝ) => (τ : ℂ) * E6Fun τ) :=
    (BddAX.mul (BddAX.self_tau (H := H)) (BddAX.e6_tau (H := H))).congr_exp (by ring) (by ring)
  have h1 : BddAX H 0 0 (fun τ t => ((τ : ℂ) * E6Fun τ) * E8Fun (cti t)) :=
    ((BddAX.mul hA (BddAX.e8_z (H := H))).congr_exp (by ring) (by ring)).congr_region
      (fun _ _ _ _ _ _ => rfl)
  have h1b : BddAX H 0 0
      (fun τ t => (((τ : ℂ) * E6Fun τ) * E8Fun (cti t)) * phitVec (cti t) 2) :=
    ((BddAX.mul h1 (BddAX.phit2_z (H := H))).congr_exp (by ring) (by ring)).congr_region
      (fun _ _ _ _ _ _ => rfl)
  have hB : BddAX H 0 0 (fun τ (_ : ℝ) => phi0 τ * E4Fun τ) :=
    (BddAX.mul (BddAX.phi0_tau (H := H)) (BddAX.e4_tau (H := H))).congr_exp
      (by ring) (by ring)
  have h2 : BddAX H 0 0 (fun τ t => (phi0 τ * E4Fun τ) * E10Fun (cti t)) :=
    ((BddAX.mul hB (BddAX.e10_z (H := H))).congr_exp (by ring) (by ring)).congr_region
      (fun _ _ _ _ _ _ => rfl)
  have h2b : BddAX H 0 0
      (fun τ t => ((phi0 τ * E4Fun τ) * E10Fun (cti t)) * phitVec (cti t) 1) :=
    ((BddAX.mul h2 (BddAX.phit1_z (H := H))).congr_exp (by ring) (by ring)).congr_region
      (fun _ _ _ _ _ _ => rfl)
  have h2c : BddAX H 0 0
      (fun τ t => (2 : ℂ) * (((phi0 τ * E4Fun τ) * E10Fun (cti t)) * phitVec (cti t) 1)) :=
    BddAX.const_mul 2 h2b
  have h3 : BddAX H 0 0
      (fun τ t => (((τ : ℂ) * E6Fun τ) * E8Fun (cti t)) * phitVec (cti t) 2
        - (2 : ℂ) * (((phi0 τ * E4Fun τ) * E10Fun (cti t)) * phitVec (cti t) 1)) :=
    (BddAX.sub h1b h2c).congr_exp (by simp) (by simp)
  have h4 : BddAX H 0 (-(2*Real.pi))
      (fun τ t => DeltaFun τ * ((((τ : ℂ) * E6Fun τ) * E8Fun (cti t)) * phitVec (cti t) 2
        - (2 : ℂ) * (((phi0 τ * E4Fun τ) * E10Fun (cti t)) * phitVec (cti t) 1))) :=
    ((BddAX.mul (BddAX.delta_tau (H := H)) h3).congr_exp (by simp) (by simp)).congr_region
      (fun _ _ _ _ _ _ => rfl)
  have h5 : BddAX H (-(2*Real.pi)) 0
      (fun τ t => DeltaFun τ * ((((τ : ℂ) * E6Fun τ) * E8Fun (cti t)) * phitVec (cti t) 2
        - (2 : ℂ) * (((phi0 τ * E4Fun τ) * E10Fun (cti t)) * phitVec (cti t) 1))) :=
    (h4.norm_b (by linarith [Real.pi_pos] : -(2*Real.pi) ≤ 0)).congr_exp (by ring) (by ring)
  refine h5.congr_region (fun τ t _ _ _ _ => ?_)
  show DeltaFun τ * ((((τ : ℂ) * E6Fun τ) * E8Fun (cti t)) * phitVec (cti t) 2
        - (2 : ℂ) * (((phi0 τ * E4Fun τ) * E10Fun (cti t)) * phitVec (cti t) 1)) = P8n2 τ t
  rw [P8n2]

lemma BddAX.P8num_bdd {H : ℝ} :
    BddAX H (-(2*Real.pi)) 0 (fun τ t => P8n1 τ t + P8n2 τ t) :=
  ((BddAX.add (BddAX.P8n1_bdd (H := H)) (BddAX.P8n2_bdd (H := H))).congr_exp
    (by simp) (by simp)).congr_region (fun _ _ _ _ _ _ => rfl)

lemma BddAX.P8pre_bdd {H : ℝ} (hH : Hj ≤ H) : BddAX H (2*Real.pi) 0 (fun τ t => P8pre τ t) :=
  ((BddAX.mul (BddAX.mul (BddAX.invdelta_tau (H := H)) (BddAX.invdelta_z (H := H)))
      (BddAX.J_inv (H := H) hH)).congr_exp (by ring) (by ring)).congr_region
    (fun _ _ _ _ _ _ => rfl)

/-- `K_+^{(8)}(τ, it)` satisfies a `BddAX` bound with exponents `(0,0)` on the region
`Im τ ≥ Hj`. -/
lemma BddAX.KPlus8_bdd : BddAX Hj 0 0 (fun τ t => KPlus 8 τ (cti t)) := by
  have h1 : BddAX Hj 0 0 (fun τ t => phitVec (cti t) 0 * P8a τ t) :=
    ((BddAX.mul (BddAX.phit0_z (H := Hj)) (BddAX.P8a_bdd (H := Hj))).congr_exp
      (by ring) (by ring)).congr_region (fun _ _ _ _ _ _ => rfl)
  have h2 : BddAX Hj 0 0 (fun τ t => (P8n1 τ t + P8n2 τ t) * P8pre τ t) :=
    ((BddAX.mul (BddAX.P8num_bdd (H := Hj)) (BddAX.P8pre_bdd (H := Hj) le_rfl)).congr_exp
      (by ring) (by ring)).congr_region (fun _ _ _ _ _ _ => rfl)
  have h3 : BddAX Hj (max 0 0) (max 0 0)
      (fun τ t => phitVec (cti t) 0 * P8a τ t + (P8n1 τ t + P8n2 τ t) * P8pre τ t) :=
    BddAX.add h1 h2
  have h4 : BddAX Hj 0 0
      (fun τ t => phitVec (cti t) 0 * P8a τ t + (P8n1 τ t + P8n2 τ t) * P8pre τ t) :=
    h3.congr_exp (by simp) (by simp)
  have h5 : BddAX Hj 0 0 (fun τ t => c8 * (phitVec (cti t) 0 * P8a τ t
      + (P8n1 τ t + P8n2 τ t) * P8pre τ t)) :=
    (BddAX.const_mul c8 h4).congr_exp (by ring) (by ring)
  refine h5.congr_region ?_
  intro τ t hF hH h1 h2
  have ht0 : 0 < t := by linarith
  have hlow : (1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im)
      ≤ ‖jInvariantFun τ - jInvariantFun (cti t)‖ := by
    rw [cti_eq_imagAxis ht0]
    exact jDiff_lower_H τ t ht0 hH h1 h2
  have hJ : jInvariantFun τ - jInvariantFun (cti t) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlow
    have hpos : (0:ℝ) < (1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im) :=
      mul_pos Work.Residues.kpre_axis_const_pos (Real.exp_pos _)
    linarith
  rw [KPlus_eight_decomposition τ (cti t) (sub_ne_zero.mp hJ)]
  congr 1
  simp only [P8a, P8n1, P8n2, P8pre, div_eq_mul_inv, mul_inv]
  ring

/-- **The `d = 8` funnel bound on the axis.** -/
theorem KPlus8_axis_big : ∃ H C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ 0 ≤ H ∧
    ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖KPlus 8 τ (cti t)‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M := by
  refine ⟨Hj, ?_⟩
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := BddAX.KPlus8_bdd.to_target1
    (H := Hj) (a := 0) (b := 0) (f := fun τ t => KPlus 8 τ (cti t)) le_rfl (by norm_num)
  exact ⟨C, N, M, hC, hN, hM, Hj_nonneg, fun τ t hF hH h1 h2 => hb τ t hF hH h1 h2⟩

/-! ## The `d = 24` bound

`KPlus24_cusp_cti` is the exact algebraic decomposition of `K_+^{(24)}` on the contour: with
`r0 = τE₁₄(τ)`, `r1 = φ₀(τ)Δ(τ)`, `r2 = φ₂(τ)E₁₀(τ)`, `R0 = φ₀(τ)E₄(τ)³ = r1·j(τ)` (all
bounded on the funnel, `r1` even decaying like `e^{-2π Im τ}`),

  `(jτ - jz)·K_+^{(24)}(τ,it) = c₂₄·(it)²·( (jτ-jz)·P/Δ(z) + U/Δ(z) + V/Δ(z)² )`,

so that `K_+^{(24)} = c₂₄(it)²(P/Δ(z) + U/(Δ(z)(jτ-jz)) + V/(Δ(z)²(jτ-jz)))`.  Combining the
atom bounds with the reciprocal prefactor bound `(Δ(z)(jτ-jz))⁻¹ ↦ (2π, -2π)`, which
`BddAX.norm_b` normalizes to `(0,0)`, gives the required `e^{2πt}` growth. -/

def c24 : ℂ := ((36 : ℂ) * 1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- `r0(τ) = τE₁₄(τ)`. -/
def r0f (τ : ℍ) : ℂ := (τ : ℂ) * E14Fun τ
/-- `r1(τ) = φ₀(τ)Δ(τ)`. -/
def r1f (τ : ℍ) : ℂ := phi0 τ * DeltaFun τ
/-- `r2(τ) = φ₂(τ)E₁₀(τ)`. -/
def r2f (τ : ℍ) : ℂ := phi2 τ * E10Fun τ
/-- `R0(τ) = φ₀(τ)E₄(τ)³ = r1(τ)j(τ)`. -/
def R0f (τ : ℍ) : ℂ := phi0 τ * E4Fun τ ^ 3

lemma fkF0 : fk (0:ℤ) = (1 : ℍ → ℂ) := by funext τ; simp [fk]
lemma fkF2 : fk (2:ℤ) = E14Fun / DeltaFun := by funext τ; simp [fk]
lemma fkF4 : fk (4:ℤ) = E4Fun := by funext τ; simp [fk]
lemma fkF6 : fk (6:ℤ) = E6Fun := by funext τ; simp [fk]
lemma fkF8 : fk (8:ℤ) = E8Fun := by funext τ; simp [fk]
lemma fkF10 : fk (10:ℤ) = E10Fun := by funext τ; simp [fk]
lemma fkF12 : fk (12:ℤ) = DeltaFun := by funext τ; simp [fk]
lemma fkF14 : fk (14:ℤ) = E14Fun := by funext τ; simp [fk]

lemma r1f_mul_j (τ : ℍ) : r1f τ * jInvariantFun τ = R0f τ := by
  rw [r1f, R0f, mul_assoc, Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]

/-- The `τ`-part of the `d = 24` bracket, in the form in which it appears in `Υ_+^{(24)}`. -/
def P24j (τ : ℍ) (t : ℝ) : ℂ :=
  r0f τ * (6 * E4Fun (cti t) - 6 * (E2S (cti t)) ^ 2)
    + r1f τ * ((-12 * jInvariantFun τ + 8640) * E4Fun (cti t)
        + (12 * jInvariantFun τ - 12096) * (E2S (cti t)) ^ 2)
    + r2f τ * (6 * E4Fun (cti t) - 6 * (E2S (cti t)) ^ 2)

/-- The coefficient of `(Δ(z))⁻¹`. -/
def U24 (τ : ℍ) (t : ℝ) : ℂ :=
  1728 * r0f τ * (E2S (cti t)) ^ 2 + 1728 * r2f τ * E4Fun (cti t)

/-- The coefficient of `(Δ(z)²)⁻¹`. -/
def V24 (τ : ℍ) (t : ℝ) : ℂ := -3456 * r1f τ * E14Fun (cti t) * E2S (cti t)

/-- The `τ`-part of the `d = 24` bracket, with `r1·jτ` replaced by `R0` so that all factors
are bounded on the funnel. -/
def P24 (τ : ℍ) (t : ℝ) : ℂ :=
  (6 * (r0f τ + r2f τ) * (E4Fun (cti t) - (E2S (cti t)) ^ 2)
      + 8640 * r1f τ * E4Fun (cti t)) - 12096 * r1f τ * (E2S (cti t)) ^ 2
    - 12 * R0f τ * E4Fun (cti t) + 12 * R0f τ * (E2S (cti t)) ^ 2

lemma P24j_eq (τ : ℍ) (t : ℝ) : P24j τ t = P24 τ t := by
  have hj := r1f_mul_j τ
  simp only [P24j, P24]
  linear_combination (12 * (E2S (cti t)) ^ 2 - 12 * E4Fun (cti t)) * hj

/-- **The cusp identity for `K_+^{(24)}` on the contour.** -/
lemma KPlus24_cusp_cti (τ : ℍ) (t : ℝ) (hJ : jInvariantFun τ ≠ jInvariantFun (cti t)) :
    (jInvariantFun τ - jInvariantFun (cti t)) * KPlus 24 τ (cti t)
      = c24 * ((cti t : ℍ) : ℂ) ^ 2 *
        ((jInvariantFun τ - jInvariantFun (cti t)) * P24j τ t / DeltaFun (cti t)
          + U24 τ t / DeltaFun (cti t) + V24 τ t / DeltaFun (cti t) ^ 2) := by
  have hD : DeltaFun (cti t) ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hDt : DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hJ' : jInvariantFun τ - jInvariantFun (cti t) ≠ 0 := sub_ne_zero.mpr hJ
  have hJ2 : E4Fun τ ^ 3 * DeltaFun (cti t) - DeltaFun τ * E4Fun (cti t) ^ 3 ≠ 0 := by
    intro hh
    have h' : E4Fun τ ^ 3 * DeltaFun (cti t) - DeltaFun τ * E4Fun (cti t) ^ 3
        = (jInvariantFun τ - jInvariantFun (cti t)) * (DeltaFun (cti t) * DeltaFun τ) := by
      rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ,
        ← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun (cti t)]
      ring
    rw [h'] at hh
    rcases mul_eq_zero.mp hh with h1 | h2
    · exact hJ' h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hD h3
    · exact hDt h3
  simp only [KPlus, UpsilonPlus, if_neg (by norm_num : ¬ ((24 : ℕ) = 8)), if_true,
    PiMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    phiVec, phitVec, phiNeg2, phi0, phi2, c1728, E14Fun, E10Fun,
    P24j, U24, V24, r0f, r1f, r2f, c24,
    fkF4, fkF10, fkF12, fkF14, fkF2, fkF0,
    Pi.one_apply, mul_one, div_eq_mul_inv, mul_inv, pow_two, Pi.mul_apply, Pi.inv_apply]
  field_simp [hD, hJ', hI, hDt, hJ2]
  ring

/-- The cusp identity with `P24j` replaced by the bounded form `P24`. -/
lemma KPlus24_cusp_cti_P (τ : ℍ) (t : ℝ) (hJ : jInvariantFun τ ≠ jInvariantFun (cti t)) :
    (jInvariantFun τ - jInvariantFun (cti t)) * KPlus 24 τ (cti t)
      = c24 * ((cti t : ℍ) : ℂ) ^ 2 *
        ((jInvariantFun τ - jInvariantFun (cti t)) * P24 τ t / DeltaFun (cti t)
          + U24 τ t / DeltaFun (cti t) + V24 τ t / DeltaFun (cti t) ^ 2) := by
  rw [← P24j_eq τ t]
  exact KPlus24_cusp_cti τ t hJ

lemma BddAX.add_same {H a b : ℝ} {f g : ℍ → ℝ → ℂ} (hf : BddAX H a b f) (hg : BddAX H a b g) :
    BddAX H a b (fun τ t => f τ t + g τ t) := by
  have h := BddAX.add hf hg
  rwa [max_self, max_self] at h

lemma BddAX.sub_same {H a b : ℝ} {f g : ℍ → ℝ → ℂ} (hf : BddAX H a b f) (hg : BddAX H a b g) :
    BddAX H a b (fun τ t => f τ t - g τ t) := by
  have h := BddAX.sub hf hg
  rwa [max_self, max_self] at h

lemma BddAX.S2z_bdd {H : ℝ} : BddAX H 0 0 (fun (_ : ℍ) t => (E2S (cti t)) ^ 2) := by
  refine ((BddAX.mul (BddAX.E2S_z (H := H)) (BddAX.E2S_z (H := H))).congr_exp
    (by ring) (by ring)).congr_region (fun τ t _ _ _ _ => ?_)
  show E2S (cti t) * E2S (cti t) = (E2S (cti t)) ^ 2
  ring

lemma BddAX.ES_bdd {H : ℝ} :
    BddAX H 0 0 (fun (_ : ℍ) t => E4Fun (cti t) - (E2S (cti t)) ^ 2) :=
  BddAX.sub_same (BddAX.e4_z (H := H)) (BddAX.S2z_bdd (H := H))

lemma BddAX.r0f_bdd {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => r0f τ) :=
  ((BddAX.mul (BddAX.self_tau (H := H)) (BddAX.e14_tau (H := H))).congr_exp
    (by ring) (by ring)).congr_region (fun _ _ _ _ _ _ => rfl)

lemma BddAX.r1f_bdd {H : ℝ} : BddAX H 0 (-(2*Real.pi)) (fun τ (_ : ℝ) => r1f τ) :=
  ((BddAX.mul (BddAX.phi0_tau (H := H)) (BddAX.delta_tau (H := H))).congr_exp
    (by ring) (by ring)).congr_region (fun _ _ _ _ _ _ => rfl)

lemma BddAX.r2f_bdd {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => r2f τ) :=
  ((BddAX.mul (BddAX.phi2_tau (H := H)) (BddAX.e10_tau (H := H))).congr_exp
    (by ring) (by ring)).congr_region (fun _ _ _ _ _ _ => rfl)

lemma BddAX.R0f_bdd {H : ℝ} : BddAX H 0 0 (fun τ (_ : ℝ) => R0f τ) :=
  ((BddAX.mul (BddAX.phi0_tau (H := H))
    (BddAX.mul (BddAX.e8_tau (H := H)) (BddAX.e4_tau (H := H)))).congr_exp
    (by ring) (by ring)).congr_region (fun τ _ _ _ _ _ => by
      show phi0 τ * (E8Fun τ * E4Fun τ) = R0f τ
      rw [R0f, show E8Fun τ = E4Fun τ ^ 2 from rfl]; ring)

lemma BddAX.P24_bdd {H : ℝ} : BddAX H 0 0 (fun τ t => P24 τ t) := by
  have hr : BddAX H 0 0 (fun τ (_ : ℝ) => r0f τ + r2f τ) :=
    BddAX.add_same (BddAX.r0f_bdd (H := H)) (BddAX.r2f_bdd (H := H))
  have ht1 : BddAX H 0 0
      (fun τ t => (6 : ℂ) * (r0f τ + r2f τ) * (E4Fun (cti t) - (E2S (cti t)) ^ 2)) :=
    (BddAX.mul (BddAX.const_mul 6 hr) (BddAX.ES_bdd (H := H))).congr_exp
      (by ring) (by ring)
  have ht2 : BddAX H 0 (-(2*Real.pi)) (fun τ t => 8640 * r1f τ * E4Fun (cti t)) :=
    (BddAX.mul (BddAX.const_mul 8640 (BddAX.r1f_bdd (H := H)))
      (BddAX.e4_z (H := H))).congr_exp (by ring) (by ring)
  have ht2' : BddAX H 0 0 (fun τ t => 8640 * r1f τ * E4Fun (cti t)) :=
    ht2.mono le_rfl (by linarith [Real.pi_pos])
  have ht3₀ : BddAX H 0 (-(2*Real.pi)) (fun τ t => 12096 * r1f τ * (E2S (cti t)) ^ 2) :=
    (BddAX.mul (BddAX.const_mul 12096 (BddAX.r1f_bdd (H := H)))
      (BddAX.S2z_bdd (H := H))).congr_exp (by ring) (by ring)
  have ht3 : BddAX H 0 0 (fun τ t => 12096 * r1f τ * (E2S (cti t)) ^ 2) :=
    ht3₀.mono le_rfl (by linarith [Real.pi_pos])
  have ht4 : BddAX H 0 0 (fun τ t => 12 * R0f τ * E4Fun (cti t)) :=
    (BddAX.mul (BddAX.const_mul 12 (BddAX.R0f_bdd (H := H))) (BddAX.e4_z (H := H))).congr_exp
      (by ring) (by ring)
  have ht5 : BddAX H 0 0 (fun τ t => 12 * R0f τ * (E2S (cti t)) ^ 2) :=
    (BddAX.mul (BddAX.const_mul 12 (BddAX.R0f_bdd (H := H))) (BddAX.S2z_bdd (H := H))).congr_exp
      (by ring) (by ring)
  have h12 : BddAX H 0 0
      (fun τ t => (6 : ℂ) * (r0f τ + r2f τ) * (E4Fun (cti t) - (E2S (cti t)) ^ 2)
        + 8640 * r1f τ * E4Fun (cti t)) := BddAX.add_same ht1 ht2'
  have h123 : BddAX H 0 0
      (fun τ t => ((6 : ℂ) * (r0f τ + r2f τ) * (E4Fun (cti t) - (E2S (cti t)) ^ 2)
        + 8640 * r1f τ * E4Fun (cti t)) - 12096 * r1f τ * (E2S (cti t)) ^ 2) :=
    BddAX.sub_same h12 ht3
  have h1234 : BddAX H 0 0
      (fun τ t => (((6 : ℂ) * (r0f τ + r2f τ) * (E4Fun (cti t) - (E2S (cti t)) ^ 2)
        + 8640 * r1f τ * E4Fun (cti t)) - 12096 * r1f τ * (E2S (cti t)) ^ 2)
        - 12 * R0f τ * E4Fun (cti t)) := BddAX.sub_same h123 ht4
  have h12345 : BddAX H 0 0
      (fun τ t => ((((6 : ℂ) * (r0f τ + r2f τ) * (E4Fun (cti t) - (E2S (cti t)) ^ 2)
        + 8640 * r1f τ * E4Fun (cti t)) - 12096 * r1f τ * (E2S (cti t)) ^ 2)
        - 12 * R0f τ * E4Fun (cti t)) + 12 * R0f τ * (E2S (cti t)) ^ 2) :=
    BddAX.add_same h1234 ht5
  refine h12345.congr_region (fun τ t _ _ _ _ => ?_)
  show ((((6 : ℂ) * (r0f τ + r2f τ) * (E4Fun (cti t) - (E2S (cti t)) ^ 2)
        + 8640 * r1f τ * E4Fun (cti t)) - 12096 * r1f τ * (E2S (cti t)) ^ 2)
        - 12 * R0f τ * E4Fun (cti t)) + 12 * R0f τ * (E2S (cti t)) ^ 2 = P24 τ t
  rw [P24]

lemma BddAX.U24_bdd {H : ℝ} : BddAX H 0 0 (fun τ t => U24 τ t) := by
  have h1 : BddAX H 0 0 (fun τ t => 1728 * r0f τ * (E2S (cti t)) ^ 2) :=
    (BddAX.mul (BddAX.const_mul 1728 (BddAX.r0f_bdd (H := H)))
      (BddAX.S2z_bdd (H := H))).congr_exp (by ring) (by ring)
  have h2 : BddAX H 0 0 (fun τ t => 1728 * r2f τ * E4Fun (cti t)) :=
    (BddAX.mul (BddAX.const_mul 1728 (BddAX.r2f_bdd (H := H)))
      (BddAX.e4_z (H := H))).congr_exp (by ring) (by ring)
  refine (BddAX.add_same h1 h2).congr_region (fun τ t _ _ _ _ => ?_)
  show 1728 * r0f τ * (E2S (cti t)) ^ 2 + 1728 * r2f τ * E4Fun (cti t) = U24 τ t
  rw [U24]

lemma BddAX.V24_bdd {H : ℝ} : BddAX H (-(2*Real.pi)) 0 (fun τ t => V24 τ t) := by
  have h1 : BddAX H 0 (-(2*Real.pi))
      (fun τ t => 3456 * r1f τ * E14Fun (cti t) * E2S (cti t)) :=
    (BddAX.mul (BddAX.mul (BddAX.const_mul 3456 (BddAX.r1f_bdd (H := H)))
      (BddAX.e14_z (H := H))) (BddAX.E2S_z (H := H))).congr_exp (by ring) (by ring)
  have h2 : BddAX H 0 (-(2*Real.pi))
      (fun τ t => -3456 * r1f τ * E14Fun (cti t) * E2S (cti t)) :=
    ((BddAX.neg h1).congr_exp (by ring) (by ring)).congr_region
      (fun _ _ _ _ _ _ => by ring)
  refine ((h2.norm_b (by linarith [Real.pi_pos] : -(2*Real.pi) ≤ 0)).congr_exp
    (by ring) (by ring)).congr_region (fun τ t _ _ _ _ => ?_)
  show -3456 * r1f τ * E14Fun (cti t) * E2S (cti t) = V24 τ t
  rw [V24]

/-- The algebraic rearrangement moving the divisor `J = j(τ) - j(z)` into the denominators:
`J (p/D + u/(D J) + v/(D² J)) = J p/D + u/D + v/D²`. -/
lemma KPlus24_rearrange (p u v D J : ℂ) (hJ : J ≠ 0) :
    (J * p / D + u / D + v / D ^ 2)
      = J * (p * D⁻¹ + u * (D * J)⁻¹ + v * (D ^ 2 * J)⁻¹) := by
  have hJJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ
  simp only [div_eq_mul_inv, pow_two, mul_inv]
  rw [mul_add, mul_add]
  rw [show J * (u * (D⁻¹ * J⁻¹)) = u * D⁻¹ * (J * J⁻¹) from by ring,
    show J * (v * (D⁻¹ * D⁻¹ * J⁻¹)) = v * (D⁻¹ * D⁻¹) * (J * J⁻¹) from by ring]
  rw [hJJ]
  ring

/-- `K_+^{(24)}(τ, it)` in the decomposed form used for the estimates. -/
lemma KPlus24_decomp (τ : ℍ) (t : ℝ) (hJ : jInvariantFun τ ≠ jInvariantFun (cti t)) :
    KPlus 24 τ (cti t) = c24 * ((cti t : ℍ) : ℂ) ^ 2 *
      (P24 τ t * (DeltaFun (cti t))⁻¹
        + U24 τ t * (DeltaFun (cti t) * (jInvariantFun τ - jInvariantFun (cti t)))⁻¹
        + V24 τ t * ((DeltaFun (cti t)) ^ 2 * (jInvariantFun τ - jInvariantFun (cti t)))⁻¹) := by
  set J : ℂ := jInvariantFun τ - jInvariantFun (cti t) with hJdef
  set D : ℂ := DeltaFun (cti t) with hDdef
  have hD : D ≠ 0 := by
    rw [hDdef]; exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have hJn : J ≠ 0 := by rw [hJdef]; exact sub_ne_zero.mpr hJ
  have key := KPlus24_cusp_cti_P τ t hJ
  rw [show jInvariantFun τ - jInvariantFun (cti t) = J from hJdef.symm,
    show DeltaFun (cti t) = D from hDdef.symm] at key
  have hcancel : J * KPlus 24 τ (cti t)
      = J * (c24 * ((cti t : ℍ) : ℂ) ^ 2 *
          (P24 τ t * D⁻¹ + U24 τ t * (D * J)⁻¹ + V24 τ t * (D ^ 2 * J)⁻¹)) := by
    rw [key]
    rw [KPlus24_rearrange (P24 τ t) (U24 τ t) (V24 τ t) D J hJn]
    ring
  exact mul_left_cancel₀ hJn hcancel

lemma BddAX.KPlus24_bdd : BddAX Hj (2*Real.pi) 0 (fun τ t => KPlus 24 τ (cti t)) := by
  have hz2 : BddAX Hj 0 0 (fun (_ : ℍ) t => ((cti t : ℍ) : ℂ) ^ 2) := BddAX.zsq_z (H := Hj)
  have hP : BddAX Hj (2*Real.pi) 0 (fun τ t => P24 τ t * (DeltaFun (cti t))⁻¹) :=
    ((BddAX.mul (BddAX.P24_bdd (H := Hj)) (BddAX.invdelta_z (H := Hj))).congr_exp
      (by ring) (by ring)).congr_region (fun _ _ _ _ _ _ => rfl)
  have hU : BddAX Hj 0 0
      (fun τ t => U24 τ t * (DeltaFun (cti t))⁻¹
        * (jInvariantFun τ - jInvariantFun (cti t))⁻¹) := by
    have h1 : BddAX Hj (2*Real.pi) (-(2*Real.pi))
        (fun τ t => U24 τ t * (DeltaFun (cti t))⁻¹
          * (jInvariantFun τ - jInvariantFun (cti t))⁻¹) :=
      ((BddAX.mul (BddAX.mul (BddAX.U24_bdd (H := Hj)) (BddAX.invdelta_z (H := Hj)))
        (BddAX.J_inv (H := Hj) le_rfl)).congr_exp (by ring) (by ring)).congr_region
        (fun _ _ _ _ _ _ => rfl)
    exact (h1.norm_b (by linarith [Real.pi_pos] : -(2*Real.pi) ≤ 0)).congr_exp
      (by ring) (by ring)
  have hV : BddAX Hj 0 0
      (fun τ t => V24 τ t * (DeltaFun (cti t))⁻¹ * (DeltaFun (cti t))⁻¹
        * (jInvariantFun τ - jInvariantFun (cti t))⁻¹) := by
    have h1 : BddAX Hj (2*Real.pi) (-(2*Real.pi))
        (fun τ t => V24 τ t * (DeltaFun (cti t))⁻¹ * (DeltaFun (cti t))⁻¹
          * (jInvariantFun τ - jInvariantFun (cti t))⁻¹) :=
      ((BddAX.mul (BddAX.mul (BddAX.mul (BddAX.V24_bdd (H := Hj)) (BddAX.invdelta_z (H := Hj)))
        (BddAX.invdelta_z (H := Hj))) (BddAX.J_inv (H := Hj) le_rfl)).congr_exp
        (by ring) (by ring)).congr_region (fun _ _ _ _ _ _ => rfl)
    exact (h1.norm_b (by linarith [Real.pi_pos] : -(2*Real.pi) ≤ 0)).congr_exp
      (by ring) (by ring)
  have hU' : BddAX Hj (2*Real.pi) 0
      (fun τ t => U24 τ t * (DeltaFun (cti t))⁻¹
        * (jInvariantFun τ - jInvariantFun (cti t))⁻¹) :=
    hU.mono (by linarith [Real.pi_pos]) le_rfl
  have hV' : BddAX Hj (2*Real.pi) 0
      (fun τ t => V24 τ t * (DeltaFun (cti t))⁻¹ * (DeltaFun (cti t))⁻¹
        * (jInvariantFun τ - jInvariantFun (cti t))⁻¹) :=
    hV.mono (by linarith [Real.pi_pos]) le_rfl
  have hUV : BddAX Hj (2*Real.pi) 0
      (fun τ t => U24 τ t * (DeltaFun (cti t))⁻¹
          * (jInvariantFun τ - jInvariantFun (cti t))⁻¹
        + V24 τ t * (DeltaFun (cti t))⁻¹ * (DeltaFun (cti t))⁻¹
          * (jInvariantFun τ - jInvariantFun (cti t))⁻¹) := BddAX.add_same hU' hV'
  have hsum : BddAX Hj (2*Real.pi) 0
      (fun τ t => P24 τ t * (DeltaFun (cti t))⁻¹
        + (U24 τ t * (DeltaFun (cti t))⁻¹
            * (jInvariantFun τ - jInvariantFun (cti t))⁻¹
          + V24 τ t * (DeltaFun (cti t))⁻¹ * (DeltaFun (cti t))⁻¹
            * (jInvariantFun τ - jInvariantFun (cti t))⁻¹)) := BddAX.add_same hP hUV
  have hsum' : BddAX Hj (2*Real.pi) 0
      (fun τ t => P24 τ t * (DeltaFun (cti t))⁻¹
        + U24 τ t * (DeltaFun (cti t))⁻¹ * (jInvariantFun τ - jInvariantFun (cti t))⁻¹
        + V24 τ t * (DeltaFun (cti t))⁻¹ * (DeltaFun (cti t))⁻¹
          * (jInvariantFun τ - jInvariantFun (cti t))⁻¹) :=
    hsum.congr_region (fun _ _ _ _ _ _ => by ring)
  have hfin : BddAX Hj (2*Real.pi) 0
      (fun τ t => c24 * ((cti t : ℍ) : ℂ) ^ 2 *
        (P24 τ t * (DeltaFun (cti t))⁻¹
          + U24 τ t * (DeltaFun (cti t))⁻¹ * (jInvariantFun τ - jInvariantFun (cti t))⁻¹
          + V24 τ t * (DeltaFun (cti t))⁻¹ * (DeltaFun (cti t))⁻¹
            * (jInvariantFun τ - jInvariantFun (cti t))⁻¹)) :=
    ((BddAX.const_mul c24 (BddAX.mul hz2 hsum')).congr_exp (by ring) (by ring)).congr_region
      (fun _ _ _ _ _ _ => by ring)
  refine hfin.congr_region ?_
  intro τ t hF hH h1 h2
  have ht0 : 0 < t := by linarith
  have hlow : (1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im)
      ≤ ‖jInvariantFun τ - jInvariantFun (cti t)‖ := by
    rw [cti_eq_imagAxis ht0]
    exact jDiff_lower_H τ t ht0 hH h1 h2
  have hJne : jInvariantFun τ - jInvariantFun (cti t) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlow
    have hpos : (0:ℝ) < (1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im) :=
      mul_pos Work.Residues.kpre_axis_const_pos (Real.exp_pos _)
    linarith
  rw [KPlus24_decomp τ t (sub_ne_zero.mp hJne)]
  simp only [pow_two, mul_inv]
  ring_nf

/-- **The `d = 24` funnel bound on the axis.** -/
theorem KPlus24_axis_big : ∃ H C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ 0 ≤ H ∧
    ∀ (τ : ℍ) (t : ℝ), Funnel τ → H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖KPlus 24 τ (cti t)‖
        ≤ C * (scale τ) ^ N * (1 + t) ^ M * Real.exp (2 * Real.pi * t) := by
  refine ⟨Hj, ?_⟩
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := BddAX.KPlus24_bdd.to_target2
    (H := Hj) (a := 2*Real.pi) (b := 0) (f := fun τ t => KPlus 24 τ (cti t))
    le_rfl (by linarith [Real.pi_pos])
  exact ⟨C, N, M, hC, hN, hM, Hj_nonneg, fun τ t hF hH h1 h2 => hb τ t hF hH h1 h2⟩

end

end Work.Asymptotics
