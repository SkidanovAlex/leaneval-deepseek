import Mathlib
import Submission.Work.Asymptotics.Kaxis_expansion_vadd_one
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.LayerCont.SplitPoint
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.LayerCont.mdifferentiableOn_highPartAt

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold
open Work.Asymptotics.KevT2

/-! ## `(T-I)²`-annihilation of the CKMRV layer

The cusp model `Aexp (Gcusp ℓ d)` is annihilated by `(T-I)²` (`Work.Asymptotics.T2op_Aexp_kev`),
and so is the kernel along the contour (`Work.Asymptotics.Kaxis_Kfun_T2`).  It follows that every
piece of the paper's layer `F₂` -- the compact low piece, the cusp-subtracted tail and the
closed-form high part -- is annihilated as well, *for every real `r`*.  This is the analytic
content of the identity `F₂|(T-I)² = 0` for the *projective* layer; the corrected `F₂` differs from
it by the residue jump `sinSqC r · resCorr r` across `Re τ = 1`
(`Work.Residues.T2op_of_contourShift`), which is where the non-zero right-hand side of (5.6) comes
from. -/

/-- **Linearity of `(T-I)²` under Bochner integration.** -/
lemma T2op_integral_eq_zero {f : UpperHalfPlane → ℝ → ℂ} {s : Set ℝ} {τ : UpperHalfPlane}
    (h0 : IntegrableOn (fun t : ℝ => f τ t) s)
    (h1 : IntegrableOn (fun t : ℝ => f ((1 : ℝ) +ᵥ τ) t) s)
    (h2 : IntegrableOn (fun t : ℝ => f ((2 : ℝ) +ᵥ τ) t) s)
    (hpt : ∀ t : ℝ, f ((2 : ℝ) +ᵥ τ) t - 2 * f ((1 : ℝ) +ᵥ τ) t + f τ t = 0) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane => ∫ t in s, f σ t) τ = 0 := by
  have hA : IntegrableOn (fun t : ℝ => f ((2 : ℝ) +ᵥ τ) t - 2 * f ((1 : ℝ) +ᵥ τ) t) s :=
    h2.sub (h1.const_mul 2)
  have hsub : (∫ t in s, f ((2 : ℝ) +ᵥ τ) t) - 2 * (∫ t in s, f ((1 : ℝ) +ᵥ τ) t)
      = ∫ t in s, (f ((2 : ℝ) +ᵥ τ) t - 2 * f ((1 : ℝ) +ᵥ τ) t) := by
    rw [← MeasureTheory.integral_const_mul (2 : ℂ) (fun t : ℝ => f ((1 : ℝ) +ᵥ τ) t),
      ← MeasureTheory.integral_sub h2 (h1.const_mul 2)]
  have hadd : (∫ t in s, (f ((2 : ℝ) +ᵥ τ) t - 2 * f ((1 : ℝ) +ᵥ τ) t)) + (∫ t in s, f τ t)
      = ∫ t in s, (f ((2 : ℝ) +ᵥ τ) t - 2 * f ((1 : ℝ) +ᵥ τ) t + f τ t) :=
    (MeasureTheory.integral_add hA h0).symm
  have hz : (fun t : ℝ => f ((2 : ℝ) +ᵥ τ) t - 2 * f ((1 : ℝ) +ᵥ τ) t + f τ t)
      = fun _ : ℝ => (0 : ℂ) := funext fun t => by rw [hpt t]
  simp only [Work.Kernels.T2op]
  rw [hsub, hadd, hz]
  simp

/-- Scalar multiples of an annihilated function are annihilated. -/
lemma T2op_const_mul_eq (c : ℂ) {F : UpperHalfPlane → ℂ} (hF : Work.Kernels.T2op F = 0) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane => c * F σ) = 0 :=
  T2op_const_mul' c hF

/-- **`(T-I)²` annihilates the cusp model along the contour.** -/
lemma T2op_Aexp_Gcusp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (t : ℝ) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) = 0 :=
  T2op_Aexp_kev (fun i j => T2op_Gcusp_kev ℓ d hd i j) t

/-- **`(T-I)²` annihilates the kernel along the contour.** -/
lemma T2op_Kaxis_Gcusp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (t : ℝ) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) = 0 :=
  Work.Asymptotics.Kaxis_Kfun_T2 ℓ d hd t

/-- Boundedness of the kernel on `(0,p]` (given cleanliness there) makes the contour integrand
integrable. -/
lemma Kaxis_gauss_integrableOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {σ : UpperHalfPlane} {p : ℝ} (hp : 0 < p)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
      Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (r : ℝ) :
    IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
      * Work.Asymptotics.gaussWeight r t) (Set.Ioc (0 : ℝ) p) := by
  obtain ⟨C, hCnn, hCb⟩ := KaxisBoundedIocBall ℓ d hd σ hp hclean
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) p)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => C)
    (MeasureTheory.integrable_const C) ?_ ?_
  · exact ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd σ).mul
      (by unfold Work.Asymptotics.gaussWeight; fun_prop)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t‖
          * ‖Work.Asymptotics.gaussWeight r t‖
        ≤ C * 1 := mul_le_mul (hCb t ht) (norm_gaussWeight_le_one r t (le_of_lt ht.1))
          (norm_nonneg _) hCnn
      _ = C := mul_one _

/-- The `Aexp`-weight is continuous, hence integrable on any compact interval. -/
lemma Aexp_gauss_integrableOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (σ : UpperHalfPlane) (r : ℝ) (a b : ℝ) :
    IntegrableOn (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t
      * Work.Asymptotics.gaussWeight r t) (Set.Ioc a b) := by
  have hcont : Continuous (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t
      * Work.Asymptotics.gaussWeight r t) := by
    refine (continuous_Aexp_snd ℓ d hd σ).mul ?_
    unfold Work.Asymptotics.gaussWeight
    fun_prop
  exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

/-- The pointwise vanishing of the `(T-I)²`-defect of `Kaxis - Aexp`, multiplied by any `t`-weight
independent of `τ`. -/
lemma T2op_Kaxis_sub_Aexp_pointwise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (t : ℝ) :
    (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (((2 : ℝ) +ᵥ τ)) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (((2 : ℝ) +ᵥ τ)) t)
      - 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (((1 : ℝ) +ᵥ τ)) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (((1 : ℝ) +ᵥ τ)) t)
      + (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) = 0 := by
  have hK := congr_fun (T2op_Kaxis_Gcusp ℓ d hd t) τ
  have hA := congr_fun (T2op_Aexp_Gcusp ℓ d hd t) τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at hK hA
  linear_combination hK - hA

/-- The same, multiplied by the Gaussian weight. -/
lemma T2op_Kaxis_sub_Aexp_gauss (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {r : ℝ} (τ : UpperHalfPlane) (t : ℝ) :
    (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (((2 : ℝ) +ᵥ τ)) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (((2 : ℝ) +ᵥ τ)) t)
        * Work.Asymptotics.gaussWeight r t
      - 2 * ((Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (((1 : ℝ) +ᵥ τ)) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (((1 : ℝ) +ᵥ τ)) t)
        * Work.Asymptotics.gaussWeight r t)
      + (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Work.Asymptotics.gaussWeight r t = 0 := by
  linear_combination (Work.Asymptotics.gaussWeight r t)
    * (T2op_Kaxis_sub_Aexp_pointwise ℓ d hd τ t)

/-- The kernel-only pointwise version. -/
lemma T2op_Kaxis_gauss_pointwise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {r : ℝ} (τ : UpperHalfPlane) (t : ℝ) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (((2 : ℝ) +ᵥ τ)) t
        * Work.Asymptotics.gaussWeight r t
      - 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (((1 : ℝ) +ᵥ τ)) t
        * Work.Asymptotics.gaussWeight r t)
      + Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t = 0 := by
  have hK := congr_fun (T2op_Kaxis_Gcusp ℓ d hd t) τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at hK
  linear_combination (Work.Asymptotics.gaussWeight r t) * hK

/-- The `Aexp`-only pointwise version. -/
lemma T2op_Aexp_gauss_pointwise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {r : ℝ} (τ : UpperHalfPlane) (t : ℝ) :
    Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (((2 : ℝ) +ᵥ τ)) t
        * Work.Asymptotics.gaussWeight r t
      - 2 * (Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (((1 : ℝ) +ᵥ τ)) t
        * Work.Asymptotics.gaussWeight r t)
      + Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t = 0 := by
  have hA := congr_fun (T2op_Aexp_Gcusp ℓ d hd t) τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at hA
  linear_combination (Work.Asymptotics.gaussWeight r t) * hA

/-- **The high part is annihilated**: it is a `τ`-linear combination with `τ`-constant
coefficients of the four annihilated functions `Gcusp ℓ d i j`. -/
theorem T2op_highPart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) σ r) = 0 := by
  ext τ
  have h00 := congr_fun (T2op_Gcusp_kev ℓ d hd 0 0) τ
  have h01 := congr_fun (T2op_Gcusp_kev ℓ d hd 0 1) τ
  have h10 := congr_fun (T2op_Gcusp_kev ℓ d hd 1 0) τ
  have h11 := congr_fun (T2op_Gcusp_kev ℓ d hd 1 1) τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h00 h01 h10 h11
  simp only [Work.Kernels.T2op, Work.Asymptotics.highPart, Pi.zero_apply]
  linear_combination
    (((Real.pi * r ^ 2 : ℝ) : ℂ) * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ)
        * Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ)))) * h00
      + (Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ)
        * ((((Real.pi * r ^ 2 : ℝ) : ℂ)) + 1)
        * Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ)))) * h01
      + ((((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ))
        * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
        * Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)))) * h10
      + (Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
        * ((((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) + 1)
        * Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)))) * h11

/-- **The low piece is annihilated** (`r` unrestricted). -/
theorem T2op_layerLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {r : ℝ} {τ : UpperHalfPlane}
    (hclean : ∀ (σ : UpperHalfPlane), σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane) →
      ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 →
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d σ r) τ = 0 := by
  have hT : Work.Kernels.T2op (fun σ : UpperHalfPlane => ∫ t in Set.Ioc (0 : ℝ) 1,
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t * Work.Asymptotics.gaussWeight r t) τ = 0 := by
    refine T2op_integral_eq_zero (s := Set.Ioc (0 : ℝ) 1) ?_ ?_ ?_ ?_
    · exact Kaxis_gauss_integrableOn ℓ d hd (p := 1) one_pos
        (fun t ht htI => hclean τ (by simp) t ht htI) r
    · exact Kaxis_gauss_integrableOn ℓ d hd (p := 1) one_pos
        (fun t ht htI => hclean ((1 : ℝ) +ᵥ τ) (by simp) t ht htI) r
    · exact Kaxis_gauss_integrableOn ℓ d hd (p := 1) one_pos
        (fun t ht htI => hclean ((2 : ℝ) +ᵥ τ) (by simp) t ht htI) r
    · intro t
      exact T2op_Kaxis_gauss_pointwise ℓ d hd τ t
  have hfun : (fun σ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d σ r)
      = fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r * ∫ t in Set.Ioc (0 : ℝ) 1,
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t * Work.Asymptotics.gaussWeight r t := by
    funext σ
    rw [Work.Asymptotics.layerLow, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [Work.Asymptotics.gaussWeight]
  rw [hfun]
  have hsplit : Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r
      * ∫ t in Set.Ioc (0 : ℝ) 1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        * Work.Asymptotics.gaussWeight r t) τ
      = Work.Asymptotics.sinSq r * Work.Kernels.T2op (fun σ : UpperHalfPlane =>
          ∫ t in Set.Ioc (0 : ℝ) 1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            * Work.Asymptotics.gaussWeight r t) τ := by
    simp only [Work.Kernels.T2op]
    ring
  rw [hsplit, hT, mul_zero]

/-- **The free-split low piece is annihilated** (`r` unrestricted). -/
theorem T2op_layerLowAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {p r : ℝ} (hp : 0 ≤ p) {τ : UpperHalfPlane}
    (hclean : ∀ (σ : UpperHalfPlane), σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane) →
      ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane => layerLowAt ℓ d p r σ) τ = 0 := by
  rcases eq_or_lt_of_le hp with hp0 | hp'
  · -- `p = 0`: the interval integral vanishes
    have hz : (fun σ : UpperHalfPlane => layerLowAt ℓ d p r σ)
        = fun _ : UpperHalfPlane => (0 : ℂ) := by
      funext σ
      rw [layerLowAt, ← hp0, intervalIntegral.integral_same, mul_zero]
    rw [hz]
    simp only [Work.Kernels.T2op, Pi.zero_apply]
    ring
  · have hT : Work.Kernels.T2op (fun σ : UpperHalfPlane => ∫ t in Set.Ioc (0 : ℝ) p,
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t * Work.Asymptotics.gaussWeight r t) τ = 0 := by
      refine T2op_integral_eq_zero (s := Set.Ioc (0 : ℝ) p) ?_ ?_ ?_ ?_
      · exact Kaxis_gauss_integrableOn ℓ d hd hp' (fun t ht htI => hclean τ (by simp) t ht htI) r
      · exact Kaxis_gauss_integrableOn ℓ d hd hp'
          (fun t ht htI => hclean ((1 : ℝ) +ᵥ τ) (by simp) t ht htI) r
      · exact Kaxis_gauss_integrableOn ℓ d hd hp'
          (fun t ht htI => hclean ((2 : ℝ) +ᵥ τ) (by simp) t ht htI) r
      · intro t
        exact T2op_Kaxis_gauss_pointwise ℓ d hd τ t
    have hfun : (fun σ : UpperHalfPlane => layerLowAt ℓ d p r σ)
        = fun σ : UpperHalfPlane => Work.Asymptotics.sinSqC r * ∫ t in Set.Ioc (0 : ℝ) p,
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t * Work.Asymptotics.gaussWeight r t := by
      funext σ
      rw [layerLowAt, intervalIntegral.integral_of_le hp]
    rw [hfun]
    have hsplit : Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Asymptotics.sinSqC r
        * ∫ t in Set.Ioc (0 : ℝ) p, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          * Work.Asymptotics.gaussWeight r t) τ
        = Work.Asymptotics.sinSqC r * Work.Kernels.T2op (fun σ : UpperHalfPlane =>
            ∫ t in Set.Ioc (0 : ℝ) p, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
              * Work.Asymptotics.gaussWeight r t) τ := by
      simp only [Work.Kernels.T2op]
      ring
    rw [hsplit, hT, mul_zero]

/-- **The cusp-subtracted tail is annihilated** (`r` unrestricted, given the integrability of the
three shifted integrands, which holds whenever the contour is clean above the split point). -/
theorem T2op_layerTruncAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {p r : ℝ} {τ : UpperHalfPlane}
    (hInt : ∀ σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane),
      IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici p)) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r σ) τ = 0 := by
  have hT : Work.Kernels.T2op (fun σ : UpperHalfPlane => ∫ t in Set.Ici p,
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) τ = 0 := by
    refine T2op_integral_eq_zero (s := Set.Ici p) ?_ ?_ ?_ ?_
    · exact hInt τ (by simp)
    · exact hInt ((1 : ℝ) +ᵥ τ) (by simp)
    · exact hInt ((2 : ℝ) +ᵥ τ) (by simp)
    · intro t
      exact T2op_Kaxis_sub_Aexp_gauss ℓ d hd τ t
  have hfun : (fun σ : UpperHalfPlane => layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r σ)
      = fun σ : UpperHalfPlane => Work.Asymptotics.sinSqC r * ∫ t in Set.Ici p,
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
            * Work.Asymptotics.gaussWeight r t := by
    funext σ
    rw [layerTruncAt]
  rw [hfun]
  have hsplit : Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Asymptotics.sinSqC r
      * ∫ t in Set.Ici p, (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) τ
      = Work.Asymptotics.sinSqC r * Work.Kernels.T2op (fun σ : UpperHalfPlane =>
          ∫ t in Set.Ici p, (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
            * Work.Asymptotics.gaussWeight r t) τ := by
    simp only [Work.Kernels.T2op]
    ring
  rw [hsplit, hT, mul_zero]

/-- **The tail piece `[1,∞)` of the paper's layer is annihilated** (the `p = 1` case). -/
theorem T2op_layerTrunc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {r : ℝ} {τ : UpperHalfPlane}
    (hInt : ∀ σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane),
      IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ))) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r) τ = 0 := by
  have hfun : (fun σ : UpperHalfPlane =>
      Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r)
      = fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r * ∫ t in Set.Ici (1 : ℝ),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
            * Work.Asymptotics.gaussWeight r t := by
    funext σ
    rw [Work.Asymptotics.layerTrunc]
    simp only [Work.Asymptotics.gaussWeight]
  rw [hfun]
  have hT : Work.Kernels.T2op (fun σ : UpperHalfPlane => ∫ t in Set.Ici (1 : ℝ),
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) τ = 0 := by
    refine T2op_integral_eq_zero (s := Set.Ici (1 : ℝ)) ?_ ?_ ?_ ?_
    · exact hInt τ (by simp)
    · exact hInt ((1 : ℝ) +ᵥ τ) (by simp)
    · exact hInt ((2 : ℝ) +ᵥ τ) (by simp)
    · intro t
      exact T2op_Kaxis_sub_Aexp_gauss ℓ d hd τ t
  have hsplit : Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r
      * ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) τ
      = Work.Asymptotics.sinSq r * Work.Kernels.T2op (fun σ : UpperHalfPlane =>
          ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
            * Work.Asymptotics.gaussWeight r t) τ := by
    simp only [Work.Kernels.T2op]
    ring
  rw [hsplit, hT, mul_zero]

/-- **The `Aexp`-interval integral of `highPartAt` is annihilated.** -/
theorem T2op_Aexp_interval (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (p r : ℝ) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane => ∫ t in (1 : ℝ)..p,
      Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t
        * Work.Asymptotics.gaussWeight r t) = 0 := by
  have hF : Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      ∫ t in Set.Ioo (min (1 : ℝ) p) (max (1 : ℝ) p),
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t
          * Work.Asymptotics.gaussWeight r t) = 0 := by
    ext τ
    refine T2op_integral_eq_zero (s := Set.Ioo (min (1 : ℝ) p) (max (1 : ℝ) p)) ?_ ?_ ?_ ?_
    · exact (Aexp_gauss_integrableOn ℓ d hd τ r _ _).mono_set (fun x hx => ⟨hx.1, hx.2.le⟩)
    · exact (Aexp_gauss_integrableOn ℓ d hd ((1 : ℝ) +ᵥ τ) r _ _).mono_set
        (fun x hx => ⟨hx.1, hx.2.le⟩)
    · exact (Aexp_gauss_integrableOn ℓ d hd ((2 : ℝ) +ᵥ τ) r _ _).mono_set
        (fun x hx => ⟨hx.1, hx.2.le⟩)
    · intro t
      exact T2op_Aexp_gauss_pointwise ℓ d hd τ t
  have key : (fun σ : UpperHalfPlane => ∫ t in (1 : ℝ)..p,
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t
          * Work.Asymptotics.gaussWeight r t)
      = fun σ : UpperHalfPlane => (if (1 : ℝ) ≤ p then (1 : ℂ) else -1)
        * ∫ t in Set.Ioo (min (1 : ℝ) p) (max (1 : ℝ) p),
            Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t
              * Work.Asymptotics.gaussWeight r t := by
    funext σ
    exact intervalIntegral_eq_smul_integral_Ioo _ 1 p
  rw [key]
  exact T2op_const_mul' _ hF

/-- **The closed-form high part with a free split point is annihilated.** -/
theorem T2op_highPartAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (p r : ℝ) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      highPartAt (Work.Asymptotics.Gcusp ℓ d) p r σ) = 0 := by
  have hhp := T2op_highPart ℓ d hd r
  have hInt : Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Asymptotics.sinSqC r
      * ∫ t in (1 : ℝ)..p, Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t
        * Work.Asymptotics.gaussWeight r t) = 0 :=
    T2op_const_mul' _ (T2op_Aexp_interval ℓ d hd p r)
  refine T2op_of_eq' (F := fun σ : UpperHalfPlane =>
    highPartAt (Work.Asymptotics.Gcusp ℓ d) p r σ)
    (G := (fun σ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) σ r)
      - (fun σ : UpperHalfPlane => Work.Asymptotics.sinSqC r * ∫ t in (1 : ℝ)..p,
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t
          * Work.Asymptotics.gaussWeight r t))
    (fun σ => by simp only [highPartAt, Pi.sub_apply])
    (T2op_sub' hhp hInt)

/-- **The paper's layer is annihilated by `(T-I)²`, for every real `r`.** -/
theorem T2op_paperLayer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {r : ℝ} {τ : UpperHalfPlane}
    (hclean : ∀ (σ : UpperHalfPlane), σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane) →
      ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 →
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hInt : ∀ σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane),
      IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ))) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r) τ = 0 := by
  have h1 : Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d σ r) τ = 0 :=
    T2op_layerLow ℓ d hd (r := r) hclean
  have h2 : Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r) τ = 0 :=
    T2op_layerTrunc ℓ d hd (r := r) hInt
  have h3 : Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) σ r) τ = 0 :=
    congr_fun (T2op_highPart ℓ d hd r) τ
  have hfun : (fun σ : UpperHalfPlane =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r)
      = fun σ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d σ r
        + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r
        + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) σ r := rfl
  rw [hfun]
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 h2 h3
  simp only [Work.Kernels.T2op, Pi.add_apply, Pi.zero_apply]
  linear_combination h1 + h2 + h3

/-- **The free-split layer `layerAt p` is annihilated by `(T-I)²`, for every real `r`.** -/
theorem T2op_layerAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {p r : ℝ} (hp : 0 ≤ p) {τ : UpperHalfPlane}
    (hclean : ∀ (σ : UpperHalfPlane), σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane) →
      ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hInt : ∀ σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane),
      IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici p)) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r σ) τ = 0 := by
  have h1 : Work.Kernels.T2op (fun σ : UpperHalfPlane => layerLowAt ℓ d p r σ) τ = 0 :=
    T2op_layerLowAt ℓ d hd (p := p) (r := r) hp hclean
  have h2 : Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r σ) τ = 0 :=
    T2op_layerTruncAt ℓ d hd (p := p) (r := r) hInt
  have h3 : Work.Kernels.T2op (fun σ : UpperHalfPlane =>
      highPartAt (Work.Asymptotics.Gcusp ℓ d) p r σ) τ = 0 :=
    congr_fun (T2op_highPartAt ℓ d hd p r) τ
  have hfun : (fun σ : UpperHalfPlane => layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r σ)
      = fun σ : UpperHalfPlane => layerLowAt ℓ d p r σ
        + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r σ
        + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r σ := rfl
  rw [hfun]
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 h2 h3
  simp only [Work.Kernels.T2op, Pi.add_apply, Pi.zero_apply]
  linear_combination h1 + h2 + h3

end Work.LayerCont
