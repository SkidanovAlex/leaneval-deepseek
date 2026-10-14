import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.Nonlinear.N4Fields.AngSmoothIntHelpers
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.LWP.VorticityAPI
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.NauxAux.zSliceNormLeHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.NauxAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

variable {α : ℝ} {f : ℝ → ℝ → ℝ}

/-! ## Elementary facts about the weight `w` -/




/-- `ENNReal.ofReal` of the integral of an a.e. nonnegative function is at most the lintegral of
`ENNReal.ofReal` of that function. -/
theorem ofReal_integral_le_lintegral {μ : Measure ℝ} {g : ℝ → ℝ} (hg : 0 ≤ᵐ[μ] g) :
    ENNReal.ofReal (∫ x, g x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  by_cases h : Integrable g μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h hg]
  · rw [MeasureTheory.integral_undef h]
    simp

/-! ## The `θ`-derivative of the `θ`-slice -/


/-! ## The pointwise-in-`z` slice bound -/


/-! ## The main theorem -/


end Work.FTS.StrongEps.E4R3.NauxAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # Multiplication by the bounded angular profile `c₂(θ) = cos 2θ - sin²θ`

The target `c2m_mul_HkSq_le` says that multiplication by the bounded angular profile
`Work.Construction.c2m` does not raise the weighted `ℋ³`-order: for `g` of class `C^∞` on the
open quadrant with `HkMem α 3 g`,

`HkMem α 3 (c₂ · g)` and `HkSq α 3 (c₂ · g) ≤ C · HkSq α 3 g`

with a constant `C` universal in `α ∈ (0,1]`.

The proof goes through the *general* angular-multiplication estimate `ang_mul_HkSq_le` below:
for an arbitrary profile `a : ℝ → ℝ` which is `C^∞` on `Q₀`, bounded by `B` on `Iθ` and whose
`D_θ`-iterates decay like `B · sin 2θ`, multiplication by `a` is honest and costs `C · B ^ 2`.

* The pointwise estimate on the open quadrant is the already-proved unit-profile inequality
  `Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int` (constant `1` on the profile);
  the general profile is reached by the rescaling `a = B · (a / B)` (`HkIntegrand_const_mul`
  contributes the factor `B ^ 2`) combined with `LopIter_const_mul` for the `D_θ`-iterates.
* It is extended to the closed quadrant by `Work.FTS.Nonlinear.N4Fields.closed_of_interior`.
* Integration is `Work.FTS.Nonlinear.N4Fields.HkSq_le_of_integrand_le` (`HkSq`) together with
  `Work.FTS.LocData.HkMem_of_majorant` (`HkMem`), the continuity hypothesis being supplied by
  `Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul_On`.

The profile `c₂` is then fed in with `B = 1000`: `|c₂| ≤ 2` on `Iθ`
(`Work.FTS.Nonlinear.Pieces.abs_c2m_le_two`) and `|D_θ^i c₂| ≤ 1000 · sin(2θ)² ≤ 1000 · sin 2θ`
(`Work.FTS.Nonlinear.Pieces.DthIter_c2m_le`). -/

/-- **Angular multiplication in `ℋ^k`.**  There is a universal constant `C` such that for every
`α ∈ (0,1]`, every profile `a : ℝ → ℝ` which is `C^∞` on the open quadrant, bounded by
`B > 0` on `Iθ` with `D_θ`-iterates bounded by `B · sin 2θ`, and every `g` of class `C^∞` on the
open quadrant with `HkMem α k g`, the product `a · g` is honest and

`HkSq α k (a · g) ≤ C · B ^ 2 · HkSq α k g`.

(`HkIntegrand α k (a · g) ≤ C · B ^ 2 · HkIntegrand α k g` pointwise on the closed quadrant, in
fact.) -/
theorem ang_mul_HkSq_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℝ → ℝ) (B : ℝ), 0 < B →
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B) →
      (∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B * Real.sin (2 * θ)) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α k f →
      Work.Spaces.HkMem α k (fun z θ => a θ * f z θ) ∧
      Work.Spaces.HkSq α k (fun z θ => a θ * f z θ) ≤ C * B ^ 2 * Work.Spaces.HkSq α k f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int k
  refine ⟨C₁, hC₁pos, ?_⟩
  intro α hα0 hα1 a B hBpos hSO haB haIt f hf hmem
  have hCD : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 := hSO
  have hBne : B ≠ 0 := hBpos.ne'
  -- the rescaled profile
  set a' : ℝ → ℝ := fun θ => a θ / B with ha'def
  have hCD' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a' p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h := hCD.div_const B
    simpa only [ha'def] using h
  have ha'1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a' θ| ≤ 1 := by
    intro θ hθ
    have h1 := haB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h2 : |a' θ| = |a θ| / B := by rw [ha'def, abs_div, abs_of_pos hBpos]
    rw [h2]
    exact (div_le_one hBpos).mpr h1
  have ha'It : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a' θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
    intro m hm1 hmk θ hθ
    have hlin : ∀ θ' : ℝ, Work.FTS.EllipticEst.LopIter m a' θ'
        = B⁻¹ * Work.FTS.EllipticEst.LopIter m a θ' := by
      have h1 : a' = fun θ => B⁻¹ * a θ := by
        funext θ'; rw [ha'def]; field_simp
      intro θ'
      rw [h1, congrFun (Work.FTS.EllipticEst.Blocks.LopIter_const_mul B⁻¹ m a) θ']
    have hbound : |Work.FTS.EllipticEst.LopIter m a θ| ≤ B * Real.sin (2 * θ) := by
      have h2 : Work.FTS.EllipticEst.LopIter m a θ
          = Work.Spaces.DthIter m (fun _ (θ' : ℝ) => a θ') 0 θ := by
        rw [Work.Spaces.DthIter_eq_iterate_Lop]
        rfl
      rw [h2]
      exact haIt m hm1 hmk θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq : (Work.FTS.EllipticEst.LopIter m a θ) ^ 2
        ≤ (B * Real.sin (2 * θ)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
    rw [hlin θ]
    calc (B⁻¹ * Work.FTS.EllipticEst.LopIter m a θ) ^ 2
        = B⁻¹ ^ 2 * (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 := by ring
      _ ≤ B⁻¹ ^ 2 * (B * Real.sin (2 * θ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (Real.sin (2 * θ)) ^ 2 := by
          have hBB : B⁻¹ ^ 2 * B ^ 2 = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hBne, one_pow]
          rw [mul_pow, ← mul_assoc, hBB, one_mul]
  -- the pointwise bound on the closed quadrant
  have hclosed := Work.FTS.Nonlinear.N4Fields.closed_of_interior (k := k) (a := a') (C := C₁)
    (fun α' f' hα' hα'1 hf' => hC₁ a' ha'1 hCD' ha'It α' f' hα' hα'1 hf') α f hα0 hα1 hf
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
        ≤ (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz θ hθ
    have hrew : (fun z θ => a θ * f z θ) = fun z θ => B * (a' θ * f z θ) := by
      funext z' θ'
      have hBmul : B * (a θ' / B) = a θ' := by
        rw [mul_comm]; exact div_mul_cancel₀ (a θ') hBne
      rw [ha'def]
      calc a θ' * f z' θ' = (B * (a θ' / B)) * f z' θ' := by rw [hBmul]
        _ = B * (a θ' / B * f z' θ') := by ring
    have hconst : Work.Spaces.HkIntegrand α k (fun z θ => B * (a' θ * f z θ)) z θ
        = B ^ 2 * Work.Spaces.HkIntegrand α k (fun z θ => a' θ * f z θ) z θ :=
      Work.FTS.LocData.HkIntegrand_const_mul α k B (fun z θ => a' θ * f z θ) z θ
    rw [hrew, hconst]
    calc B ^ 2 * Work.Spaces.HkIntegrand α k (fun z θ => a' θ * f z θ) z θ
        ≤ B ^ 2 * (C₁ * Work.Spaces.HkIntegrand α k f z θ) :=
          mul_le_mul_of_nonneg_left (hclosed z hz θ hθ) (sq_nonneg B)
      _ = (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α k f z θ := by ring
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul_On hCD hf).continuousOn_HkIntegrand α k
  have hmem' : Work.Spaces.HkMem α k (fun z θ => a θ * f z θ) := by
    refine Work.FTS.LocData.HkMem_of_majorant α k hcont ?_ ?_ hpt
    · intro z hz
      exact (hmem.1 z hz).const_mul (B ^ 2 * C₁)
    · have h2 := hmem.2.const_mul (B ^ 2 * C₁)
      have heq : (fun z => ∫ θ in Work.Spaces.Iθ,
            (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α k f z θ)
          = fun z => (B ^ 2 * C₁) * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [heq]
      exact h2
  refine ⟨hmem', ?_⟩
  have hsq := Work.FTS.Nonlinear.N4Fields.HkSq_le_of_integrand_le α k (B ^ 2 * C₁) hmem hpt
  calc Work.Spaces.HkSq α k (fun z θ => a θ * f z θ)
      ≤ (B ^ 2 * C₁) * Work.Spaces.HkSq α k f := hsq
    _ = C₁ * B ^ 2 * Work.Spaces.HkSq α k f := by ring

/-! ## The profile hypotheses for `c₂` -/

/-- `c₂` is `C^∞` on the open quadrant (as a constant-in-`z` profile). -/
private theorem contDiffOn_c2m_snd :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiff ℝ ⊤ (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub
      ((Real.contDiff_sin).pow 2)
  have h2 : ContDiff ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) := h1.of_le le_top
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) Set.univ := h2.contDiffOn
  have h4 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    h3.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
  have hfun : (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2)
      = fun p : ℝ × ℝ => Work.Construction.c2m p.2 := by
    funext p
    rw [Work.Construction.c2m_eq]
  rwa [hfun] at h4

/-- `|c₂| ≤ 1000` on `Iθ`. -/
private theorem c2m_abs_le (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.c2m θ| ≤ 1000 := by
  have h := Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ
  linarith

/-- `|D_θ^i c₂| ≤ 1000 · sin 2θ` on `Iθ`, for `1 ≤ i ≤ 3`. -/
private theorem c2m_dthIter_le (i : ℕ) (hi : 1 ≤ i) (hi3 : i ≤ 3) (θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) := by
  have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi (by omega) θ
  rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ (2 : ℕ) from
    Real.rpow_natCast _ 2] at h
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
  calc |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) ^ 2 := h
    _ ≤ 1000 * Real.sin (2 * θ) := by linarith

/-! ## The target -/

theorem c2m_mul_HkSq_le : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkMem α 3 (fun z θ => Work.Construction.c2m θ * g z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.c2m θ * g z θ)
        ≤ C * Work.Spaces.HkSq α 3 g := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := ang_mul_HkSq_le 3
  refine ⟨C₁ * 1000 ^ 2, by positivity, ?_⟩
  intro α hα g hg hmem
  have hSOc : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    contDiffOn_c2m_snd
  obtain ⟨hmem', hsq⟩ := hC₁ α hα.1 hα.2 (fun θ => Work.Construction.c2m θ) 1000
    (by norm_num) hSOc c2m_abs_le c2m_dthIter_le g hg hmem
  exact ⟨hmem', hsq⟩

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.sliceIbpCanonW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice-by-slice radial integration by parts against the canonical weight

For a fixed `θ ∈ (0, π/2)` the canonical weight `canonW q · θ` is (a constant times) the
radial weight `w(z)² = (1+z)⁴/z⁴`, which satisfies the exact identity

  `z · (w²)'(z) = -4 · w(z)²/(1+z)`,  hence  `(z w²)'(z) = ((z-3)/(1+z)) · w(z)²`.

Consequently, if `|h| ≤ M` and `|z h'| ≤ M`, then

  `(d/dz) (z · canonW q z θ · h z) = canonW q z θ · (z h' + ((z-3)/(1+z)) h)`,

so the absolute value of this derivative is dominated by `4 M canonW q · θ`.  Integrating by
parts against `Y²` on `(0,∞)` — the boundary terms vanish by the two limit hypotheses —
turns `∫ canonW q · θ · h · (z Y') · Y` into `-(1/2) ∫ (z canonW h)' Y²`, which is exactly
the loss of a factor `2M` in the estimate.

## Main statement

`Work.FTS.StrongPersist.N6Trans.SixAux.sliceIbpCanonW`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The derivative of `z ↦ z · canonW q z θ · h z` -/

/-- For `θ` fixed, the function `z ↦ z · canonW q z θ · h z` has the derivative
`canonW q z θ · (z h' + ((z-3)/(1+z)) h)` on `(0,∞)`.  The point is the identity
`(z w²)' = ((z-3)/(1+z)) w²` for the radial weight `w(z) = (1+z)²/z²`, which combines with the
product rule and the extra factor `z`. -/
theorem hasDerivAt_zCanonW_mul {q : ℝ} {h : ℝ → ℝ} {θ : ℝ}
    (hh : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h z) z) :
    ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => z * canonW q z θ * h z)
      (canonW q x θ * (x * deriv h x + ((x - 3) / (1 + x)) * h x)) x := by
  intro x hx
  have h0 := (Work.RPFresh.hasDerivAt_w2z_mul (f := h) hx (hh x hx)).mul_const
    ((Real.sin (2 * θ)) ^ (-q))
  have hfun : (fun z => z * canonW q z θ * h z)
      = (fun z => (Work.Spaces.w z) ^ 2 * z * h z * (Real.sin (2 * θ)) ^ (-q)) := by
    funext z
    simp only [canonW]
    ring
  have hder : canonW q x θ * (x * deriv h x + ((x - 3) / (1 + x)) * h x)
      = (Work.Spaces.w x) ^ 2 * (x * deriv h x + (x - 3) / (1 + x) * h x)
        * (Real.sin (2 * θ)) ^ (-q) := by
    simp only [canonW]
    ring
  rw [hfun, hder]
  exact h0

/-- The `deriv` form of `hasDerivAt_zCanonW_mul`. -/
theorem deriv_zCanonW_mul {q : ℝ} {h : ℝ → ℝ} {θ : ℝ}
    (hh : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h z) z) :
    ∀ x ∈ Set.Ioi (0 : ℝ), deriv (fun z => z * canonW q z θ * h z) x
      = canonW q x θ * (x * deriv h x + ((x - 3) / (1 + x)) * h x) :=
  fun x hx => (hasDerivAt_zCanonW_mul (q := q) hh x hx).deriv

/-- The pointwise domination of the derivative: `|(z canonW h)'| ≤ 4 M canonW` on `(0,∞)`,
using `|h| ≤ M`, `|z h'| ≤ M` and `|(z-3)/(1+z)| ≤ 3`. -/
theorem abs_deriv_zCanonW_mul_le {q M : ℝ} {h : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hh : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h z) z)
    (hhn : ∀ z ∈ Set.Ioi (0 : ℝ), |h z| ≤ M)
    (hDhn : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv h z| ≤ M) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      |deriv (fun z => z * canonW q z θ * h z) x| ≤ 4 * M * canonW q x θ := by
  intro x hx
  have hx0 : 0 < x := hx
  have hθ' : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hCnn : 0 ≤ canonW q x θ := canonW_nonneg hθ'
  rw [deriv_zCanonW_mul (q := q) hh x hx]
  have h1 : |x * deriv h x + ((x - 3) / (1 + x)) * h x| ≤ M + 3 * M := by
    have hA : |x * deriv h x| ≤ M := hDhn x hx
    have hB : |((x - 3) / (1 + x)) * h x| ≤ 3 * M := by
      rw [abs_mul]
      have h1x : (0 : ℝ) < 1 + x := by linarith
      have h2 : |(x - 3) / (1 + x)| ≤ 3 := by
        rw [abs_div, abs_of_pos h1x, div_le_iff₀ h1x]
        have h3 : |x - 3| ≤ x + 3 := by
          rw [abs_le]
          constructor <;> linarith
        linarith
      exact mul_le_mul h2 (hhn x hx) (abs_nonneg _) (by linarith)
    calc |x * deriv h x + ((x - 3) / (1 + x)) * h x|
        ≤ |x * deriv h x| + |((x - 3) / (1 + x)) * h x| := abs_add_le _ _
      _ ≤ M + 3 * M := add_le_add hA hB
  calc |canonW q x θ * (x * deriv h x + ((x - 3) / (1 + x)) * h x)|
      = canonW q x θ * |x * deriv h x + ((x - 3) / (1 + x)) * h x| := by
        rw [abs_mul, abs_of_nonneg hCnn]
    _ ≤ canonW q x θ * (M + 3 * M) := mul_le_mul_of_nonneg_left h1 hCnn
    _ = 4 * M * canonW q x θ := by ring

/-! ## The integration by parts -/

theorem sliceIbpCanonW {q M : ℝ} (hM : 0 ≤ M) {h Y : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hh : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h z) z)
    (hY : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Y (deriv Y z) z)
    (hhn : ∀ z ∈ Set.Ioi (0 : ℝ), |h z| ≤ M)
    (hDhn : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv h z| ≤ M)
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z) ^ 2) (Set.Ioi (0 : ℝ)))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ * h z * (z * deriv Y z) * Y z)
      (Set.Ioi (0 : ℝ)))
    (hlim0 : Filter.Tendsto
      (fun z => z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z * (Y z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlimT : Filter.Tendsto
      (fun z => z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z * (Y z) ^ 2)
      Filter.atTop (nhds 0)) :
    |∫ z in Set.Ioi (0 : ℝ),
        Work.FTS.TransportS.SlotT2.canonW q z θ * h z * (z * deriv Y z) * Y z|
      ≤ 2 * M * ∫ z in Set.Ioi (0 : ℝ),
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z) ^ 2 := by
  -- ### the majorant `4 M · canonW q · θ · Y²`
  have hmaj : MeasureTheory.Integrable
      (fun z : ℝ => 4 * M * (canonW q z θ * (Y z) ^ 2))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hint1.const_mul (4 * M)
  -- ### integrability of `(z canonW h) · (Y²)'`
  have huv' : MeasureTheory.IntegrableOn
      (fun z : ℝ => (z * canonW q z θ * h z) * (2 * Y z * deriv Y z)) (Set.Ioi (0 : ℝ)) := by
    refine IntegrableOn.congr_fun (hint2.const_mul (2 : ℝ)) (fun z _ => ?_) measurableSet_Ioi
    ring
  -- ### the two `HasDerivAt` inputs of the integration by parts
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => z * canonW q z θ * h z)
      (deriv (fun z => z * canonW q z θ * h z) x) x :=
    fun x hx => (hasDerivAt_zCanonW_mul (q := q) hh x hx).differentiableAt.hasDerivAt
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => (Y z) ^ 2) (2 * Y x * deriv Y x) x := by
    intro x hx
    have h0 := (hY x hx).mul (hY x hx)
    have h : HasDerivAt (fun z : ℝ => Y z * Y z) (2 * Y x * deriv Y x) x :=
      h0.congr_deriv (by ring)
    have heq : (fun z : ℝ => Y z ^ 2) = (fun z : ℝ => Y z * Y z) := by
      funext z
      ring
    rw [heq]
    exact h
  -- ### the pointwise bound for the derivative
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      |deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
        ≤ 4 * M * (canonW q z θ * (Y z) ^ 2) := by
    intro z hz
    have hle := abs_deriv_zCanonW_mul_le (q := q) (M := M) hθ hh hhn hDhn z hz
    calc |deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
        = |deriv (fun z => z * canonW q z θ * h z) z| * (Y z) ^ 2 := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Y z))]
      _ ≤ (4 * M * canonW q z θ) * (Y z) ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = 4 * M * (canonW q z θ * (Y z) ^ 2) := by ring
  -- ### integrability of `(z canonW h)' · Y²`
  have hu'v : MeasureTheory.IntegrableOn
      (fun z : ℝ => deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have hY2 : AEStronglyMeasurable (fun z : ℝ => (Y z) ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hcont : ContinuousOn Y (Set.Ioi (0 : ℝ)) :=
        fun z hz => (hY z hz).continuousAt.continuousWithinAt
      have h1 : AEStronglyMeasurable Y (volume.restrict (Set.Ioi (0 : ℝ))) :=
        ContinuousOn.aestronglyMeasurable (μ := volume) hcont measurableSet_Ioi
      have h2 : AEStronglyMeasurable (fun z : ℝ => Y z * Y z)
          (volume.restrict (Set.Ioi (0 : ℝ))) := h1.mul h1
      simpa only [sq] using h2
    have hd : AEStronglyMeasurable
        (fun z : ℝ => deriv (fun z => z * canonW q z θ * h z) z)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (aestronglyMeasurable_deriv (fun z => z * canonW q z θ * h z) volume).mono_measure
        Measure.restrict_le_self
    refine hmaj.mono' (hd.mul hY2) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs]
    exact hpt z hz
  have hu'abs : MeasureTheory.Integrable
      (fun z : ℝ => |deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h := MeasureTheory.Integrable.abs hu'v
    simpa only [Real.norm_eq_abs] using h
  -- ### the integration by parts
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ))
    (u := fun z => z * canonW q z θ * h z)
    (u' := fun z => deriv (fun z => z * canonW q z θ * h z) z)
    (v := fun z => (Y z) ^ 2)
    (v' := fun z => 2 * Y z * deriv Y z)
    (a' := (0 : ℝ)) (b' := (0 : ℝ)) hu hv huv' hu'v hlim0 hlimT
  have hL : (∫ z in Set.Ioi (0 : ℝ), (z * canonW q z θ * h z) * (2 * Y z * deriv Y z))
      = 2 * (∫ z in Set.Ioi (0 : ℝ), canonW q z θ * h z * (z * deriv Y z) * Y z) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
  have h2A : 2 * (∫ z in Set.Ioi (0 : ℝ), canonW q z θ * h z * (z * deriv Y z) * Y z)
      = -(∫ z in Set.Ioi (0 : ℝ),
          deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2) := by
    rw [← hL]
    simpa using hIBP
  have hAeq : (∫ z in Set.Ioi (0 : ℝ), canonW q z θ * h z * (z * deriv Y z) * Y z)
      = -(1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
          deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2) := by
    linarith [h2A]
  -- ### the bound on the derivative term
  have hBnd : |∫ z in Set.Ioi (0 : ℝ),
        deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
      ≤ 4 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2 := by
    have hconst : (∫ z in Set.Ioi (0 : ℝ), 4 * M * (canonW q z θ * (Y z) ^ 2))
        = 4 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2 :=
      MeasureTheory.integral_const_mul (4 * M) _
    calc |∫ z in Set.Ioi (0 : ℝ), deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
        ≤ ∫ z in Set.Ioi (0 : ℝ),
            |deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Set.Ioi (0 : ℝ), 4 * M * (canonW q z θ * (Y z) ^ 2) :=
          MeasureTheory.integral_mono_ae hu'abs hmaj
            (ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hpt z hz))
      _ = 4 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2 := hconst
  -- ### conclusion
  rw [hAeq, abs_mul]
  have habs : |-(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [habs]
  calc (1 / 2) * |∫ z in Set.Ioi (0 : ℝ),
          deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
      ≤ (1 / 2) * (4 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2) :=
        mul_le_mul_of_nonneg_left hBnd (by norm_num)
    _ = 2 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2 := by ring

end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## The `D_θ`-identities -/

/-- `D_θ`-iteration against a leading `D_θ`: `DthIter n (D_θ f) = DthIter (n+1) f`. -/
theorem DthIter_Dth (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter n (Work.Spaces.Dth f) = Work.Spaces.DthIter (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show Work.Spaces.Dth (Work.Spaces.DthIter n (Work.Spaces.Dth f))
        = Work.Spaces.Dth (Work.Spaces.DthIter (n + 1) f)
      rw [ih]

/-- `mixed b a (D_θ f) = mixed b (a+1) f`, by definition. -/
theorem mixed_Dth (b a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed b a (Work.Spaces.Dth f) = Work.Spaces.mixed b (a + 1) f := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_Dth]

/-- **`D_θ` commutes with `mixed b a` on the open quadrant**: for `g` of class `C^∞` on the
open quadrant, `D_θ (D_z^bD_θ^a g) = D_z^bD_θ^{a+1} g = mixed b (a+1) g` there. -/
theorem Dth_mixed_eq {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (b a : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ = Work.Spaces.mixed b (a + 1) g z θ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DthIter a g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (hg.DthIter a).forall n
  have h := Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hsm b 1 hz hθ
  have h1 : Work.Spaces.DthIter 1 (Work.Spaces.DzIter b (Work.Spaces.DthIter a g))
      = Work.Spaces.Dth (Work.Spaces.mixed b a g) := rfl
  have h2 : Work.Spaces.DzIter b (Work.Spaces.DthIter 1 (Work.Spaces.DthIter a g))
      = Work.Spaces.mixed b (a + 1) g := by
    rw [show Work.Spaces.DthIter 1 (Work.Spaces.DthIter a g)
      = Work.Spaces.DthIter (a + 1) g from rfl, Work.Spaces.mixed]
  rw [← h1, ← h2]
  exact h

/-! ## Nonnegativity of the slot weight -/

/-- The slot weight `slotW α a` is nonnegative everywhere. -/
theorem slotW_nonneg (α : ℝ) (a : ℕ) (z θ : ℝ) : 0 ≤ Work.FTS.TransportS.slotW α a z θ := by
  rw [Work.FTS.TransportS.slotW]
  split_ifs <;> exact sq_nonneg _

/-- The binomial coefficient is bounded by `6` for `a ≤ 4`. -/
theorem choose_le_six {a i : ℕ} (ha : a ≤ 4) : a.choose i ≤ 6 := by
  rcases lt_or_ge i (a + 1) with h | h
  · interval_cases a <;> interval_cases i <;> decide
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    norm_num

/-- The product of two binomial coefficients is bounded by `36` for `a, b ≤ 4`. -/
theorem choose_mul_le {a i b j : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) :
    a.choose i * b.choose j ≤ 36 := by
  have h1 := choose_le_six (a := a) (i := i) ha
  have h2 := choose_le_six (a := b) (i := j) hb
  nlinarith

/-! ## The per-slot easy majorant -/

/-- **The easy Leibniz majorant of a single slot.**  For the slot `(a,b)` of the flat
`ℋ⁴`-pairing (`a` angular, `b` radial) and the Leibniz splits `(a1,b1) ≠ (0,0)` of
`mixed b a (f·D_θg)`, this is the sum of the absolute values of the Leibniz summands with the
slot weight `slotW α a` of the corresponding slot of `HkIntegrand α 4` (and without the
binomial coefficients of the Leibniz rule).

It is the single-slot part of the majorant `EasyLeib` of `LeibMajor.lean`. -/
def slotEasySum (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then 0 else
        Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
          * |Work.Spaces.mixed b a g z θ|)

theorem slotEasySum_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    0 ≤ slotEasySum α f g a b z θ := by
  rw [slotEasySum]
  refine Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => ?_
  by_cases h : a1 = 0 ∧ b1 = 0
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (mul_nonneg (mul_nonneg (slotW_nonneg α a z θ) (abs_nonneg _))
      (abs_nonneg _)) (abs_nonneg _)

/-- **The single-slot easy majorant is dominated by `EasyLeib`.**  For a slot with `a + b ≤ 4`,
the summand `slotEasySum α f g a b` is one of the summands of the global majorant `EasyLeib`. -/
theorem slotEasySum_le_EasyLeib {α : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} (hab : a + b ≤ 4)
    (z θ : ℝ) :
    slotEasySum α f g a b z θ ≤ Work.FTS.StrongPersist.N6Trans.EasyLeib α f g z θ := by
  have hFnn : ∀ a' b' : ℕ, 0 ≤ slotEasySum α f g a' b' z θ :=
    fun a' b' => slotEasySum_nonneg α f g a' b' z θ
  rw [Work.FTS.StrongPersist.N6Trans.EasyLeib]
  have hinner : ∀ a' b' : ℕ, 0 ≤ (if a' + b' ≤ 4 then slotEasySum α f g a' b' z θ else 0) := by
    intro a' b'
    by_cases h : a' + b' ≤ 4
    · rw [if_pos h]; exact hFnn a' b'
    · rw [if_neg h]
  have h1 : slotEasySum α f g a b z θ
      ≤ ∑ b' ∈ Finset.range 5, (if a + b' ≤ 4 then slotEasySum α f g a b' z θ else 0) := by
    have hmem : b ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
    have h := Finset.single_le_sum (s := Finset.range 5)
      (f := fun b' => (if a + b' ≤ 4 then slotEasySum α f g a b' z θ else 0))
      (fun b' _ => hinner a b') hmem
    simpa only [if_pos hab] using h
  have hmem2 : a ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have h2 := Finset.single_le_sum (s := Finset.range 5)
    (f := fun a' => ∑ b' ∈ Finset.range 5,
      (if a' + b' ≤ 4 then slotEasySum α f g a' b' z θ else 0))
    (fun a' _ => Finset.sum_nonneg fun b' _ => hinner a' b') hmem2
  exact le_trans h1 h2

/-! ## A.e. slice integrability out of product integrability -/


end

end Work.FTS.StrongPersist.N6Trans.T1Hon
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

set_option maxHeartbeats 1200000

theorem hardSlotSliceSixZero : ∃ C : ℝ, 0 < C ∧ ∀ (q Kf z : ℝ) (f Y : ℝ → ℝ → ℝ),
    0 ≤ q → q ≤ 2 → 0 ≤ Kf → z ∈ Work.Spaces.Iz →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen Y →
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → |f z θ| ≤ Kf) →
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → |Work.Spaces.Dth f z θ| ≤ Kf) →
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z θ) ^ 2) Work.Spaces.Iθ →
    |∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dth Y z θ * Y z θ|
      ≤ C * Kf * ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z θ) ^ 2 := by
  refine ⟨3 / 2, by norm_num, ?_⟩
  intro q Kf z f Y hq0 hq2 hKf0 hz hSf hSY hfb hdb hVint
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate radius `z = 0`, where the radial weight vanishes
    subst hz0
    have hL : (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q 0 θ * f 0 θ
        * Work.Spaces.Dth Y 0 θ * Y 0 θ) = fun _ => (0 : ℝ) := by
      funext θ
      simp only [Work.FTS.TransportS.SlotT2.canonW, Work.Spaces.w]
      norm_num
    have hR : (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q 0 θ * (Y 0 θ) ^ 2)
        = fun _ => (0 : ℝ) := by
      funext θ
      simp only [Work.FTS.TransportS.SlotT2.canonW, Work.Spaces.w]
      norm_num
    rw [hL, hR, MeasureTheory.integral_zero, abs_zero, mul_zero]
  · -- the open quadrant
    obtain ⟨chi, B, hB, hsm, hnn, hle, hone, hz0l, hz0r, hd0l, hd0r, hbd, hten⟩ :=
      Work.H2.T1Q.Cutoff
    have hIθ : MeasurableSet Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    have hFcd : ContDiffOn ℝ 1 (fun θ : ℝ => f z θ) (Set.Ioo 0 (π / 2)) :=
      (hSf.curry_θ hzpos).of_le (m := (1 : ℕ∞)) (by simp)
    have hVcd : ContDiffOn ℝ 1 (fun θ : ℝ => Y z θ) (Set.Ioo 0 (π / 2)) :=
      (hSY.curry_θ hzpos).of_le (m := (1 : ℕ∞)) (by simp)
    have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have h1 : Work.Spaces.w z ≠ 0 := by
        rw [Work.Spaces.w]
        exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hzpos))
      exact pow_ne_zero 2 h1
    -- the `q`-weighted slice energy is integrable
    have hVintq : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ := by
      have h2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Spaces.w z) ^ 2
            * ((Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))) Work.Spaces.Iθ :=
        hVint.congr_fun (fun θ _ => by
          simp only [Work.FTS.TransportS.SlotT2.canonW]; ring) hIθ
      exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp h2
    -- the pointwise bounds
    have hFb : ∀ θ : ℝ, 0 < θ → θ < π / 2 → |f z θ| ≤ Kf :=
      fun θ hθ hθ2 => hfb θ hθ hθ2
    have hFdb : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
        |Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ| ≤ Kf := by
      intro θ hθ hθ2
      have h := hdb θ hθ hθ2
      simpa only [Work.Spaces.Dth, Work.Spaces.pth] using h
    have hWq : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
        |(1 / 2) * (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
          + (1 - q) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf := by
      intro θ hθ hθ2
      refine Work.H2.T1Q.Wq_bound hKf0 (hFdb θ hθ hθ2) (hFb θ hθ hθ2) ?_
      rw [abs_le]; constructor <;> linarith
    -- the cut-off parameters tend to `0`
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 4)) atTop (𝓝 0) := by
      have hshift : Filter.Tendsto (fun n : ℕ => n + 3) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n 3) Filter.tendsto_id
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
      refine h.congr (fun n => ?_)
      simp only [Function.comp_apply]
      push_cast
      ring_nf
    have hlimeq : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 4))) atTop (𝓝 0) := by
      have h2 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 4)))
          Filter.atTop (𝓝 0) := by
        simpa using hbase.const_mul (1 / 2 : ℝ)
      refine h2.congr' ?_
      filter_upwards with n
      have hx : (4 + (n : ℝ)) ≠ 0 := by positivity
      field_simp
    have hlimpos : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 4))) atTop
        (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hlimeq, ?_⟩
      filter_upwards with n
      exact Set.mem_Ioi.mpr (by positivity)
    -- the cut-off converges to `1`
    have hchi_lim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Tendsto (fun n : ℕ => chi (1 / (2 * ((n : ℝ) + 4))) θ) atTop (𝓝 1) := by
      filter_upwards [Work.H2.T1Q.ae_Iθ_mem_Ioo] with θ hθ
      exact (hten θ hθ.1 hθ.2).comp hlimpos
    have hchi_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => chi (1 / (2 * ((n : ℝ) + 4))) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      fun n => (hsm (1 / (2 * ((n : ℝ) + 4)))).continuous.aestronglyMeasurable
    have hchi_le : ∀ (n : ℕ) (θ : ℝ), |chi (1 / (2 * ((n : ℝ) + 4))) θ| ≤ 1 := by
      intro n θ
      rw [abs_of_nonneg (hnn _ θ)]
      exact hle _ θ
    -- the per-`n` bound of the localised integral
    have hbd_seq : ∀ n : ℕ,
        |∫ θ in Work.Spaces.Iθ, chi (1 / (2 * ((n : ℝ) + 4))) θ
            * ((Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ)|
          ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ,
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)),
                  (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
              + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2),
                  (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
      intro n
      have hζn : 0 < (1 : ℝ) / (2 * ((n : ℝ) + 4)) := by positivity
      have hζn4 : (1 : ℝ) / (2 * ((n : ℝ) + 4)) ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity)]
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have h := SixZeroAux.singleSlotCutBoundMine (q := q) (Kf := Kf) (B := B) (z := z) (f := f)
        (Y := Y) (chi := chi) (ζ := 1 / (2 * ((n : ℝ) + 4)))
        hq0 hKf0 hB.le hzpos hsm hnn hle hone hz0l hz0r hd0l hd0r hbd
        hFcd hVcd hFb hWq hVintq hζn hζn4
      have h2ζ : 2 * (1 / (2 * ((n : ℝ) + 4))) = 1 / ((n : ℝ) + 4) := by
        have hx : ((n : ℝ) + 4) ≠ 0 := by positivity
        field_simp
      rw [h2ζ] at h
      exact h
    -- the shrinking boundary contributions vanish
    have herr : Tendsto (fun n : ℕ => (Kf * B / 2) *
        ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)),
            (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2),
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))) atTop (𝓝 0) := by
      have h := Work.H2.T1Q.ShrinkInt hVintq
      simpa using h.const_mul (Kf * B / 2)
    by_cases hint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
          * Work.Spaces.Dth Y z θ * Y z θ) Work.Spaces.Iθ
    · -- the integrable case: pass to the limit `n → ∞` in the cut-off bound
      have hφint : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ)
          Work.Spaces.Iθ := by
        have h2 : MeasureTheory.IntegrableOn
            (fun θ : ℝ => (Work.Spaces.w z) ^ 2
              * ((Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ))
            Work.Spaces.Iθ :=
          hint.congr_fun (fun θ _ => by
            simp only [Work.FTS.TransportS.SlotT2.canonW]; ring) hIθ
        exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp h2
      have hS := Work.H2.T1Q.SliceLimit
        (M := (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ,
            (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
        (φ := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ)
        (chi := fun n θ => chi (1 / (2 * ((n : ℝ) + 4))) θ)
        (err := fun n : ℕ => (Kf * B / 2) *
          ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)),
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2),
                (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
        herr hφint hchi_meas hchi_le hchi_lim hbd_seq
      have hAeq : (∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
            * Work.Spaces.Dth Y z θ * Y z θ)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
        simp only [Work.FTS.TransportS.SlotT2.canonW]
        ring
      have hBstep : (∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z θ) ^ 2)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
        simp only [Work.FTS.TransportS.SlotT2.canonW]
        ring
      rw [hAeq, abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
      refine le_trans (mul_le_mul_of_nonneg_left hS (sq_nonneg (Work.Spaces.w z))) ?_
      rw [hBstep]
      exact le_of_eq (by ring)
    · -- the non-integrable case: the integral is `0` by definition
      rw [MeasureTheory.integral_undef hint, abs_zero]
      refine mul_nonneg (mul_nonneg (by norm_num) hKf0)
        (MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem hIθ (fun θ hθ => ?_)))
      have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.bt_sin_nonneg hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)) (sq_nonneg _)

end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.GenSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2

/-- **The pure `D_z`-slot at an arbitrary order.**  For `0 < q ≤ η`, `j ≤ k` and
`θ ∈ Iθ`, `canonW q · (D_z^j g)² ≤ HkIntegrand α k g`. -/
theorem canonW_mul_z_le_gen (α : ℝ) (g : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q) (k : ℕ)
    (hq : q ≤ Work.Spaces.eta) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j : ℕ) (hj : j ≤ k) :
    canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hw : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθ]
    exact canonW_mono hq0 hq hθ
  calc canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj

/-- **The mixed slot at an arbitrary order.**  For `0 < q ≤ γ`, `1 ≤ i`, `i + j ≤ k` and
`θ ∈ Iθ`, `canonW q · (mixed j i g)² ≤ HkIntegrand α k g`. -/
theorem canonW_mul_mixed_le_gen (α : ℝ) (g : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q) (k : ℕ)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hw : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθ]
    exact canonW_mono hq0 hqγ hθ
  calc canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i j hi hij

/-- `canonW 0 ≤ canonW q` for `0 ≤ q` on the open angular interval. -/
theorem canonW_zero_le {q : ℝ} (hq : 0 ≤ q) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW 0 z θ ≤ canonW q z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
    simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
  have h2 : canonW q z θ = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-q) := rfl
  rw [h1, h2]
  exact le_mul_of_one_le_right (sq_nonneg _) (one_le_rpow_neg hq hθ)

/-- **The pure `D_z`-slot at an arbitrary order, for `0 ≤ q ≤ η`.** -/
theorem canonW_z_slot_le_gen {α : ℝ} (k : ℕ) {q : ℝ} (hqnn : 0 ≤ q) (hq : q ≤ Work.Spaces.eta)
    (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (j : ℕ) (hj : j ≤ k) :
    canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · subst h0
    exact le_trans (mul_le_mul_of_nonneg_right (canonW_zero_le Work.Spaces.eta_pos.le hθ)
      (sq_nonneg _)) (canonW_mul_z_le_gen α g Work.Spaces.eta_pos k le_rfl hθI j hj)
  · exact canonW_mul_z_le_gen α g hpos k hq hθI j hj

/-- **The mixed slot at an arbitrary order, for `0 ≤ q ≤ γ`.** -/
theorem canonW_mixed_slot_le_gen {α : ℝ} (hα : 0 < α) (k : ℕ) {q : ℝ} (hqnn : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · subst h0
    have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α := by
      rw [Work.Spaces.gam]
      have : Work.Spaces.eta = 99 / 100 := rfl
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right (canonW_zero_le Work.Spaces.eta_pos.le hθ)
      (sq_nonneg _)) (canonW_mul_mixed_le_gen α g Work.Spaces.eta_pos k hηγ hθI j i hi hij)
  · exact canonW_mul_mixed_le_gen α g hpos k hqγ hθI j i hi hij

end Work.FTS.TransportS.T2Sup
end
end
