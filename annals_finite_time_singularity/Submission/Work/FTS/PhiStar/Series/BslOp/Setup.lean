import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The majorant `(m+1)^{-3/2}` and the radial mode solution -/

/-- The majorant sequence `majPow m = (m+1)^{-3/2}` used for the differentiated mode series. -/
def majPow (m : ℕ) : ℝ := (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹

/-- The mode-`m` radial Green function of the source `𝒜φ = phiA α`. -/
abbrev gammaFun (α : ℝ) (m : ℕ) : ℝ → ℝ := fun z => Radial.radGreen α m (VocabO.phiA α) z

/-! ## Differentiability of the mode solutions -/

/-- `gammaFun α m = radGreen α m (phiA α)` is differentiable on `(0,∞)`, with derivative `rgiD1`,
and the derivative is differentiable too. -/
theorem hasDerivAt_gammaFun {α : ℝ} (hα : 0 < α) (m : ℕ)
    (hc : ContinuousOn (VocabO.phiA α) (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t => VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn
      (fun t => VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    (∀ z, 0 < z → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) z) z) ∧
    (∀ z, 0 < z →
      HasDerivAt (deriv (gammaFun α m)) (deriv (rgiD1 α m (VocabO.phiA α)) z) z) := by
  constructor
  · intro z hz
    have h := hasDerivAt_radGreenI (α := α) (m := m) (c := VocabO.phiA α) hc h0 hinf z hz
    exact h
  · intro z hz
    have heq : deriv (gammaFun α m) =ᶠ[𝓝 z] rgiD1 α m (VocabO.phiA α) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      have h := hasDerivAt_radGreenI (α := α) (m := m) (c := VocabO.phiA α) hc h0 hinf y hy
      exact h.deriv
    have hd : HasDerivAt (rgiD1 α m (VocabO.phiA α)) (deriv (rgiD1 α m (VocabO.phiA α)) z) z :=
      (rgiD1_differentiableAt (α := α) (m := m) (c := VocabO.phiA α) hc h0 hinf z hz).hasDerivAt
    exact (heq.hasDerivAt_iff).mpr hd

/-- The `z`-derivative of the mode coefficient `acoeff α m (RemSource α ψ)`. -/
theorem deriv_acoeff {α : ℝ} {ψ : ℝ → ℝ} (m : ℕ)
    (hA : ∀ z, 0 < z → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) z) z)
    (z : ℝ) (hz : 0 < z) :
    deriv (acoeff α m (RemSource α ψ)) z
      = α ^ 2 * bmode m ψ * rgiD1 α m (VocabO.phiA α) z := by
  have hfun : acoeff α m (RemSource α ψ) = fun t => (α ^ 2 * bmode m ψ) * gammaFun α m t := by
    funext t
    rw [acoeff_RemSource]
  rw [hfun, deriv_const_mul _ ((hA z hz).differentiableAt), (hA z hz).deriv]

/-- The second `z`-derivative of the mode coefficient. -/
theorem deriv_deriv_acoeff {α : ℝ} {ψ : ℝ → ℝ} (m : ℕ)
    (hA : ∀ z, 0 < z → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) z) z)
    (hA' : ∀ z, 0 < z →
      HasDerivAt (deriv (gammaFun α m)) (deriv (rgiD1 α m (VocabO.phiA α)) z) z)
    (z : ℝ) (hz : 0 < z) :
    deriv (deriv (acoeff α m (RemSource α ψ))) z
      = α ^ 2 * bmode m ψ * deriv (rgiD1 α m (VocabO.phiA α)) z := by
  have heq : deriv (acoeff α m (RemSource α ψ))
      =ᶠ[𝓝 z] fun t => (α ^ 2 * bmode m ψ) * deriv (gammaFun α m) t := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    rw [deriv_acoeff m hA t ht, (hA t ht).deriv]
  rw [heq.deriv_eq, deriv_const_mul _ ((hA' z hz).differentiableAt), (hA' z hz).deriv]

/-- HasDerivAt form of the mode coefficient and of its derivative, for the termwise
differentiation of the series. -/
theorem hasDerivAt_acoeff {α : ℝ} {ψ : ℝ → ℝ} (m : ℕ)
    (hA : ∀ z, 0 < z → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) z) z)
    (hA' : ∀ z, 0 < z →
      HasDerivAt (deriv (gammaFun α m)) (deriv (rgiD1 α m (VocabO.phiA α)) z) z) :
    (∀ z, 0 < z → HasDerivAt (acoeff α m (RemSource α ψ))
        (α ^ 2 * bmode m ψ * rgiD1 α m (VocabO.phiA α) z) z) ∧
    (∀ z, 0 < z → HasDerivAt (deriv (acoeff α m (RemSource α ψ)))
        (α ^ 2 * bmode m ψ * deriv (rgiD1 α m (VocabO.phiA α)) z) z) := by
  constructor
  · intro z hz
    have h1 : HasDerivAt (fun y => (α ^ 2 * bmode m ψ) * gammaFun α m y)
        ((α ^ 2 * bmode m ψ) * rgiD1 α m (VocabO.phiA α) z) z :=
      (hA z hz).const_mul _
    have heq : (fun y => (α ^ 2 * bmode m ψ) * gammaFun α m y)
        =ᶠ[𝓝 z] acoeff α m (RemSource α ψ) := by
      filter_upwards with y
      rw [acoeff_RemSource]
    exact (heq.hasDerivAt_iff).mp h1
  · intro z hz
    have h1 : HasDerivAt (fun y => (α ^ 2 * bmode m ψ) * deriv (gammaFun α m) y)
        ((α ^ 2 * bmode m ψ) * deriv (rgiD1 α m (VocabO.phiA α)) z) z :=
      (hA' z hz).const_mul _
    have heq : (fun y => (α ^ 2 * bmode m ψ) * deriv (gammaFun α m) y)
        =ᶠ[𝓝 z] deriv (acoeff α m (RemSource α ψ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      rw [deriv_acoeff m hA y hy, (hA y hy).deriv]
    exact (heq.hasDerivAt_iff).mp h1

/-! ## Elementary arithmetic helpers -/

/-- Multiplication of the two decay estimates. -/
theorem bound_mul {Cdec CBz lamv sq b g : ℝ} (hCdec : 0 ≤ Cdec) (hCBz : 0 ≤ CBz)
    (hlam : 0 < lamv) (hsq : 0 < sq)
    (hb : |b| ≤ Cdec / (lamv * sq)) (hg : |g| ≤ CBz / lamv) :
    |b| * |g| ≤ Cdec * CBz / (lamv ^ 2 * sq) := by
  calc |b| * |g| ≤ (Cdec / (lamv * sq)) * (CBz / lamv) := by
        exact mul_le_mul hb hg (abs_nonneg _) (by positivity)
    _ = Cdec * CBz / (lamv ^ 2 * sq) := by
        field_simp

/-- The angular factor `3(m+1)` dominating `√((2m+2)(2m+3))`. -/
theorem sqrt_mu_le {m : ℕ} (hm : 1 ≤ m) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ≤ 3 * ((m : ℝ) + 1) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [hm1]

/-- `μ ≤ 9(m+1)²` for `μ = (2m+2)(2m+3)`. -/
theorem mu_le {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) ≤ 9 * ((m : ℝ) + 1) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith [hm1]

/-- `μ√μ ≤ 27(m+1)³`. -/
theorem mu_mul_sqrt_mu_le {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)
        * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
      ≤ 27 * ((m : ℝ) + 1) ^ 3 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 := mu_le hm
  have h2 := sqrt_mu_le hm
  have h3 : ((m : ℝ) + 1) ^ 3 = ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) := by ring
  calc (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)
        * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
      ≤ (9 * ((m : ℝ) + 1) ^ 2) * (3 * ((m : ℝ) + 1)) := by
        exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = 27 * ((m : ℝ) + 1) ^ 3 := by ring

/-- `lam m = 2m(2m+5) ≥ 4m²`. -/
theorem four_mul_sq_le_lam {m : ℕ} (hm : 1 ≤ m) :
    4 * (m : ℝ) ^ 2 ≤ Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]
  nlinarith [hm1]

/-- `0 < lam m` for `m ≥ 1`. -/
theorem lam_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]
  nlinarith [hm1]

/-- `√(2m+1) > 0`. -/
theorem sqrt_two_m_pos (m : ℕ) : 0 < Real.sqrt (2 * (m : ℝ) + 1) :=
  Real.sqrt_pos_of_pos (by positivity)

/-- The majorant is positive. -/
theorem majPow_pos (m : ℕ) : 0 < majPow m := by
  rw [majPow]
  exact inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)

/-- The majorant is nonnegative. -/
theorem majPow_nonneg (m : ℕ) : 0 ≤ majPow m := le_of_lt (majPow_pos m)

/-- Addition of two convergent series. -/
theorem tsum_add' {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) :
    (∑' i, f i) + (∑' i, g i) = ∑' i, (f i + g i) :=
  (hf.tsum_add hg).symm

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
theorem iteratedDeriv_two_apply (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 2 f x = deriv (deriv f) x := by
  have h2 : iteratedDeriv 2 f = deriv (iteratedDeriv 1 f) :=
    iteratedDeriv_succ (n := 1) (f := f)
  have h1 : iteratedDeriv 1 f = deriv f := by
    have h := iteratedDeriv_succ (n := 0) (f := f)
    simpa using h
  rw [h2, h1]


/-- Linearity of `tsum` over five summable families with constant coefficients. -/
theorem tsum_lincomb5 (c1 c2 c3 c4 c5 : ℝ) (f1 f2 f3 f4 f5 : ℕ → ℝ)
    (h1 : Summable f1) (h2 : Summable f2) (h3 : Summable f3) (h4 : Summable f4)
    (h5 : Summable f5) :
    c1 * (∑' m, f1 m) + c2 * (∑' m, f2 m)
        + (c3 * (∑' m, f3 m) + c4 * (∑' m, f4 m) + c5 * (∑' m, f5 m))
      = ∑' m, (c1 * f1 m + c2 * f2 m + (c3 * f3 m + c4 * f4 m + c5 * f5 m)) := by
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    tsum_add' (h1.mul_left c1) (h2.mul_left c2),
    tsum_add' (h3.mul_left c3) (h4.mul_left c4),
    tsum_add' ((h3.mul_left c3).add (h4.mul_left c4)) (h5.mul_left c5),
    tsum_add' ((h1.mul_left c1).add (h2.mul_left c2))
      (((h3.mul_left c3).add (h4.mul_left c4)).add (h5.mul_left c5))]

/-- The Dirichlet eigen-relation in the derivative form needed for the final combination. -/
theorem eFam_lzero_deriv (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) (z : ℝ) :
    -iteratedDeriv 2 (Gegenbauer.eFam m) θ
        + deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ
        - 6 * Gegenbauer.eFam m θ = Gegenbauer.lam m * Gegenbauer.eFam m θ := by
  have h := Gegenbauer.eFam_Lzero m hθ z
  rw [Elliptic.Lzero_eq_deriv] at h
  simpa only [iteratedDeriv_two_apply] using h

end Work.FTS.PhiStar.Series
