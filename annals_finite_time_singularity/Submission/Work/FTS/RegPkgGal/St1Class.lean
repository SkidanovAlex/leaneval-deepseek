import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.TimeDerivContinuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals

/-- **The weak second-order time-clause of the window bundle.**  The `∂ₜ`-slices
`t ↦ ∂ₜω(y,t)` of the spacetime vorticity `ω` are continuous in `t`, locally around every time of
the half-window `preWindow T`, uniformly in the point `y`.

This is the local form of continuity in `t`; it is implied by the Lipschitz clause
`TimeDerivLocallyLipschitz` (see `timeDerivLocallyContinuous_of_locallyLipschitz`) and it is what
the joint `C¹` statement actually needs (the Lipschitz clause is used in
`biotSavartSpacetimeC1_holds` only through the continuity of those slices). -/
def TimeDerivLocallyContinuous (ω : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧
    ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
      ContinuousAt (fun s : ℝ => FiniteTimeSingularity.timeDeriv ω y s) t


end Work.CoreResiduals
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.RadGreenDzuAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist.Honesty

set_option autoImplicit false

/-! ## Linearity of `Dzu` -/





/-! ## Differentiability of the iterates of `radPhi` and `radPsi` -/



/-! ## The pointwise formula for `Dzu i (radGreen α m c)` -/




end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.radPsi_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist.Honesty

/-- A function continuous on `(0,∞)` which is integrable on `(1,∞)` is integrable on `(t,∞)`
for every `t > 0`: split `(t,∞) = (t,m] ∪ (m,∞)` with `m = max 1 t` and use compactness of
`[t,m]` together with monotonicity of the integral. -/
lemma integrableOn_Ioi_of_integrableOn_Ioi_one {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0)) (h1 : IntegrableOn f (Set.Ioi 1)) {t : ℝ} (ht : 0 < t) :
    IntegrableOn f (Set.Ioi t) := by
  have hta : t ≤ max 1 t := le_max_right 1 t
  have hIoc : IntegrableOn f (Set.Ioc t (max 1 t)) := by
    have hcu : ContinuousOn f (Set.uIcc t (max 1 t)) := by
      rw [Set.uIcc_of_le hta]
      exact hcont.mono (fun x hx => lt_of_lt_of_le ht hx.1)
    have hint : IntervalIntegrable f volume t (max 1 t) := hcu.intervalIntegrable
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hta] at hint
  have hIoi : IntegrableOn f (Set.Ioi (max 1 t)) :=
    h1.mono_set (Set.Ioi_subset_Ioi (le_max_left 1 t))
  have hunion : IntegrableOn f (Set.Ioc t (max 1 t) ∪ Set.Ioi (max 1 t)) := hIoc.union hIoi
  rwa [Set.Ioc_union_Ioi_eq_Ioi hta] at hunion

-- `radPsi α m c = fun z => ∫ u in Set.Ioi 1, c (z*u) * u^(-p-1)` with `p = radP α m = 2m/α ≥ 8`
-- (`Submission/Work/FTS/PhiStar/RadialWAux/Defs.lean`).  Claim: for `z > 0`,
--   `Ψ'(z) = (radP α m * Ψ(z) - c z) / z`, i.e. `z Ψ' = p Ψ - c`.
-- ROUTE: `Work.FTS.PhiStar.RadialWAux.integral_Ioi_one_rpow` (proved, in
-- `radGreen_eq_rescaled.lean`) gives `Ψ z = z^p * ∫ t in Set.Ioi z, c t * t^{-p-1}` (for any `c`,
-- `z > 0`).  Put `g t = c t * t^{-p-1}`, continuous on `(0,∞)` by `hc`.  For a fixed `z₀ > 0`
-- choose `a = max 1 (2*z₀)`; for `y < a`,
-- `∫ t in Ioi y, g t = ∫ t in Ioi a, g t + ∫ t in y..a, g t`
-- (split `Ioi y = Ioc y a ∪ Ioi a`; `IntegrableOn g (Ioi y)` follows from `hinf` on `Ioi 1`
-- together with continuity on `(y,1)`, via `IntegrableOn.union`).  The derivative at `y = z₀` of
-- `y ↦ ∫ t in y..a, g t` is `-g z₀` (`intervalIntegral.integral_hasDerivAt_left`), and the
-- displayed equality holds eventually near `z₀`, so `HasDerivAt (fun y => ∫ t in Ioi y, g t) (-g z₀) z₀`.
-- Finish with the product rule for `z ↦ z^p * A z` and the identity `z₀^p * g z₀ = c z₀ / z₀`
-- (`Real.rpow_add`, `z₀ > 0`).

theorem radPsi_hasDerivAt {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : MeasureTheory.IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (Work.FTS.PhiStar.RadialWAux.radPsi α m c)
        ((Work.FTS.PhiStar.RadialWAux.radP α m
            * Work.FTS.PhiStar.RadialWAux.radPsi α m c z - c z) / z) z := by
  intro z hz
  set p : ℝ := Work.FTS.PhiStar.RadialWAux.radP α m with hp
  set g : ℝ → ℝ := fun t => c t * t ^ (-p - 1) with hg
  have hpval : p = 2 * (m : ℝ) / α := by rw [hp]; rfl
  -- `g` is continuous on `(0,∞)`
  have hgcont : ContinuousOn g (Set.Ioi 0) := by
    rw [hg]
    exact hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  -- and integrable on `(1,∞)`, by comparison with the hypothesis `hinf`
  have hintegr : IntegrableOn g (Set.Ioi 1) := by
    have habs : IntegrableOn (fun t => |g t|) (Set.Ioi 1) := by
      refine hinf.congr_fun ?_ measurableSet_Ioi
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      simp only [hg, hpval]
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    have hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioi 1)) :=
      (hgcont.mono (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))).aestronglyMeasurable
        measurableSet_Ioi
    exact (integrable_norm_iff hmeas).mp
      (by simpa [Real.norm_eq_abs, IntegrableOn] using habs)
  -- the substitution identity `Ψ y = y^p · ∫_{Ioi y} g`
  have hsub : ∀ y : ℝ, 0 < y →
      Work.FTS.PhiStar.RadialWAux.radPsi α m c y = y ^ p * ∫ t in Set.Ioi y, g t := by
    intro y hy
    have h := Work.FTS.PhiStar.RadialWAux.integral_Ioi_one_rpow c
      (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1) hy
    show (∫ u in Set.Ioi (1 : ℝ),
        c (y * u) * u ^ (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1))
      = y ^ p * ∫ t in Set.Ioi y, g t
    rw [h, show -(-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1 + 1) = p from by rw [hp]; ring]
  -- the threshold `a = max 1 (2z)` and the splitting identity
  have h1a : (1 : ℝ) ≤ max 1 (2 * z) := le_max_left 1 (2 * z)
  have hza : z < max 1 (2 * z) := by
    have h2 : z < 2 * z := by linarith
    exact lt_of_lt_of_le h2 (le_max_right 1 (2 * z))
  have hza' : z ≤ max 1 (2 * z) := le_of_lt hza
  have hIa : IntegrableOn g (Set.Ioi (max 1 (2 * z))) :=
    hintegr.mono_set (Set.Ioi_subset_Ioi h1a)
  have hsplit : ∀ y : ℝ, 0 < y → y ≤ max 1 (2 * z) →
      (∫ t in Set.Ioi y, g t)
        = (∫ t in Set.Ioi (max 1 (2 * z)), g t) + ∫ t in y..(max 1 (2 * z)), g t := by
    intro y hy hya
    have hy' : IntegrableOn g (Set.Ioi y) :=
      integrableOn_Ioi_of_integrableOn_Ioi_one hgcont hintegr hy
    have h := intervalIntegral.integral_Ioi_sub_Ioi hy' hya
    rwa [sub_eq_iff_eq_add'] at h
  have hev : (fun y : ℝ => ∫ t in Set.Ioi y, g t)
      =ᶠ[𝓝 z] (fun y : ℝ => (∫ t in Set.Ioi (max 1 (2 * z)), g t)
        + ∫ t in y..(max 1 (2 * z)), g t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz, Iio_mem_nhds hza] with y hy hya
    exact hsplit y hy (le_of_lt hya)
  -- the derivative of `y ↦ ∫_{Ioi y} g` is `-g z`
  have hII : IntervalIntegrable g volume z (max 1 (2 * z)) := by
    have hcu : ContinuousOn g (Set.uIcc z (max 1 (2 * z))) := by
      rw [Set.uIcc_of_le hza']
      exact hgcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)
    exact hcu.intervalIntegrable
  have hmeas_z : StronglyMeasurableAtFilter g (𝓝 z) volume :=
    ContinuousOn.stronglyMeasurableAtFilter (f := g) (s := Set.Ioi 0) (μ := volume)
      isOpen_Ioi hgcont z hz
  have hcont_z : ContinuousAt g z := hgcont.continuousAt (isOpen_Ioi.mem_nhds hz)
  have hleft : HasDerivAt (fun y : ℝ => ∫ t in y..(max 1 (2 * z)), g t) (-(g z)) z :=
    intervalIntegral.integral_hasDerivAt_left hII hmeas_z hcont_z
  have hfull : HasDerivAt
      (fun y : ℝ => (∫ t in Set.Ioi (max 1 (2 * z)), g t)
        + ∫ t in y..(max 1 (2 * z)), g t) (-(g z)) z :=
    hleft.const_add (∫ t in Set.Ioi (max 1 (2 * z)), g t)
  have hA : HasDerivAt (fun y : ℝ => ∫ t in Set.Ioi y, g t) (-(g z)) z :=
    hfull.congr_of_eventuallyEq hev
  -- product rule for `y ↦ y^p · ∫_{Ioi y} g`
  have hpow : HasDerivAt (fun y : ℝ => y ^ p) (p * z ^ (p - 1)) z :=
    Real.hasDerivAt_rpow_const (x := z) (p := p) (Or.inl (ne_of_gt hz))
  have hprod : HasDerivAt (fun y : ℝ => y ^ p * ∫ t in Set.Ioi y, g t)
      (p * z ^ (p - 1) * (∫ t in Set.Ioi z, g t) + z ^ p * (-(g z))) z := hpow.mul hA
  -- the value of that derivative, rewritten in terms of `Ψ`
  have hval : p * z ^ (p - 1) * (∫ t in Set.Ioi z, g t) + z ^ p * (-(g z))
      = (Work.FTS.PhiStar.RadialWAux.radP α m
          * Work.FTS.PhiStar.RadialWAux.radPsi α m c z - c z) / z := by
    rw [hsub z hz]
    have hgz : g z = c z * z ^ (-p - 1) := by simp only [hg]
    have h1 : z ^ (p - 1) = z ^ p * z⁻¹ := by
      rw [show p - 1 = p + (-1) from by ring, Real.rpow_add hz, Real.rpow_neg_one]
    have h2 : z ^ p * z ^ (-p - 1) = z⁻¹ := by
      rw [← Real.rpow_add hz, show p + (-p - 1) = -1 from by ring, Real.rpow_neg_one]
    have h4 : z ^ p * (-(c z * z ^ (-p - 1))) = -(c z) * (z ^ p * z ^ (-p - 1)) := by ring
    rw [hgz, h1, h4, h2, div_eq_mul_inv, hp]
    ring
  rw [hval] at hprod
  exact hprod.congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact hsub y hy)

end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.Rows45 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary consequences of the envelope -/

/-- `|g|²_{ℋ⁴} ≤ Env α g` for `0 < α ≤ 1` (the weight `α^{-3/2}` of the `Env`-definition is
`≥ 1`). -/
theorem Xn_sq_le_Env (g : Fn) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (Work.FTS.Nonlin.Xn α g) ^ 2 ≤ Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have h1 : (1 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1
      (show (-(3 / 2 : ℝ)) ≤ 0 by norm_num)
    simpa using h
  have h2 : (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg _) h1
  rw [Env]
  have h3 : 0 ≤ α ^ 2 := sq_nonneg α
  have h4 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.sqrt_nonneg α) hX
  linarith

/-- `α·|g|_{ℋ⁴} ≤ Env α g` for `0 < α ≤ 1`. -/
theorem alpha_mul_Xn_le_Env {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have h1 : α ≤ Real.sqrt α := by
    have hα2 : α ^ 2 ≤ α := by nlinarith [hα.le, hα1]
    calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
      _ ≤ Real.sqrt α := Real.sqrt_le_sqrt hα2
  have h2 : Real.sqrt α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
    rw [Env]
    have h3 : 0 ≤ α ^ 2 := sq_nonneg α
    have h4 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  exact (mul_le_mul_of_nonneg_right h1 hX).trans h2

/-- `α²·|g|_{ℋ⁴} ≤ Env α g` for `0 < α ≤ 1`. -/
theorem alpha_sq_mul_Xn_le_Env {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have h1 : α ^ 2 ≤ α := by nlinarith [hα.le, hα1]
  exact (mul_le_mul_of_nonneg_right h1 hX).trans (alpha_mul_Xn_le_Env (g := g) hα hα1)

/-! ## The weight comparison `r⁻² ≤ w r` and its consequence for slot energies -/

/-- `|K θ| ≤ 3` on the open angular interval. -/
theorem K_abs_le_three' {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.K θ| ≤ 3 := by
  rw [abs_le]
  exact ⟨by
      have h := Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.K_nonneg_of_mem_Iθ
        (show θ ∈ Work.Spaces.Iθ from ⟨hθ.1.le, hθ.2.le⟩)
      linarith,
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.K_le_three θ⟩

theorem inv_sq_le_w {r : ℝ} (hr : 0 < r) : (r⁻¹) ^ 2 ≤ Work.Spaces.w r := by
  have h1 : (r⁻¹) ^ 2 = 1 / r ^ 2 := by rw [inv_pow, one_div]
  rw [Work.Spaces.w, h1, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < r ^ 2)]
  nlinarith [sq_nonneg (1 + r)]

/-- **The `r⁻²`-weighted slot energy.**  If `Φ ≥ 0` is measurable and `w·Φ` is integrable with
`∫ w Φ ≤ Xs`, then `r⁻²Φ` is integrable with `∫ r⁻²Φ ≤ Xs` (because `r⁻² ≤ w` on `r > 0`). -/
theorem invSq_mul_integrable_le {Φ : ℝ → ℝ} {Xs : ℝ}
    (hΦnn : ∀ r, 0 ≤ Φ r)
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦintw : MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Φ r) (Set.Ioi (0 : ℝ)))
    (hΦlew : (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ r) ≤ Xs) :
    MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r) ≤ Xs := by
  have hle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (r⁻¹) ^ 2 * Φ r ≤ Work.Spaces.w r * Φ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_of_nonneg_right (inv_sq_le_w hr) (hΦnn r)
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun r => (r⁻¹) ^ 2 * Φ r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : Measurable (fun r : ℝ => (r⁻¹) ^ 2) := by fun_prop
    exact (h1.aemeasurable.mul hΦmeas).aestronglyMeasurable
  have hint : MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)) :=
    hΦintw.mono' hmeas (hle.mono fun r hr => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hΦnn r))]
      exact hr)
  refine ⟨hint, ?_⟩
  exact (MeasureTheory.integral_mono_ae hint hΦintw hle).trans hΦlew

/-- The `B`-slot energy as a `θ`-lintegral: if `Φ r = ∫_θ (B r θ)²` and the slice is
integrable, then `∫⁻_θ ofReal (B r θ²) = ofReal (Φ r)`. -/
theorem slot_lintegral_eq {B : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ} {r : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => (B r θ) ^ 2) Work.Spaces.Iθ)
    (hΦ : Φ r = ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2)) = ENNReal.ofReal (Φ r) := by
  rw [hΦ]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun θ => sq_nonneg (B r θ))).symm

/-! ## The angular moment `FK g` and its pointwise bound -/

/-- `(FK g r)² ≤ 16·Φ0 g r`, i.e. `|FK g r| ≤ 4√(Φ0 g r)` (`FK_g_pt`). -/
theorem FK_sq_le {g : Fn} {r : ℝ} (hr : 0 < r)
    (hint : MeasureTheory.IntegrableOn (fun θ => (g r θ) ^ 2) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => g r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (Work.Construction.FK g r) ^ 2
      ≤ 16 * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
  have h := FK_g_pt (g := g) hr hint hmeas
  have hΦ0 : (0 : ℝ) ≤ Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg (g r θ))
  have hsq : |Work.Construction.FK g r| ^ 2
      ≤ (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)) ^ 2 := by
    have h2 := mul_self_le_mul_self (abs_nonneg _) h
    rw [pow_two, pow_two]
    exact h2
  rw [mul_pow, Real.sq_sqrt hΦ0, sq_abs] at hsq
  linarith [hsq]

/-- The profile data of `c r = d·r/(1+r)²`: `r⁻¹c r = d/(1+r)²` on `r > 0`, so its square is
integrable with square-integral `≤ 2d²` (because `(1+r)^{-4} ≤ (1+r)^{-2}`). -/
theorem profile_data_sq {d : ℝ} (hd : 0 ≤ d) :
    AEMeasurable (fun r : ℝ => r⁻¹ * (d * r / (1 + r) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2) ≤ d ^ 2 * 2 ∧
      Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
        ≤ d * Real.sqrt 2 := by
  have hkey : ∀ r : ℝ, 0 < r → r⁻¹ * (d * r / (1 + r) ^ 2) = d / (1 + r) ^ 2 := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hmeas : AEMeasurable (fun r : ℝ => r⁻¹ * (d * r / (1 + r) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hbase : AEMeasurable (fun r : ℝ => d * ((1 + r) ^ 2)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_const.mul ((measurable_const.add measurable_id).pow_const 2).inv).aemeasurable
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    rw [hkey r hr]
    rfl
  have hbaseint : MeasureTheory.IntegrableOn
      (fun r : ℝ => d ^ 2 * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_inv_one_add_sq'.1).const_mul _
  -- on `r > 0`, the square is `d²/(1+r)⁴`, which is dominated by `d²/(1+r)²`
  have hval : ∀ r : ℝ, 0 < r → (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2 = d ^ 2 / (1 + r) ^ 4 := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    rw [hkey r hr, div_pow, ← pow_mul]
  have hbaseval : ∀ r : ℝ, d ^ 2 * (1 / (1 + r)) ^ 2 = d ^ 2 / (1 + r) ^ 2 := by
    intro r
    rw [div_pow, one_pow]
    ring
  have hdom : ∀ r ∈ Set.Ioi (0 : ℝ),
      (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2 ≤ d ^ 2 * (1 / (1 + r)) ^ 2 := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    have h1r : (0 : ℝ) < 1 + r := by linarith
    rw [hval r hr', hbaseval r]
    refine div_le_div_of_nonneg_left (sq_nonneg d) (pow_pos h1r 2) ?_
    nlinarith [sq_nonneg r, hr'.le]
  have hsm : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hmeas.pow_const 2).aestronglyMeasurable
  have hint : MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    hbaseint.mono' hsm (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hdom r hr)
  have hle : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2) ≤ d ^ 2 * 2 := by
    refine (MeasureTheory.integral_mono_ae hint hbaseint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hdom)).trans ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left integrableOn_inv_one_add_sq'.2 (sq_nonneg _)
  refine ⟨hmeas, hint, hle, ?_⟩
  calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
      ≤ Real.sqrt (d ^ 2 * 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (d ^ 2) * Real.sqrt 2 := Real.sqrt_mul (sq_nonneg _) 2
    _ = d * Real.sqrt 2 := by rw [Real.sqrt_sq hd]

/-! ## The six rows -/

/-- **Rows `N₄^{gg}`, `N₅^{gg}`** (`FK g` against `D_θg` resp. `g`). -/
theorem ggRows45 : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g : Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g →
    Fa (Work.FTS.Nonlin.N4gg α g) ≤ ENNReal.ofReal (K * Env α g) ∧
    Fa (Work.FTS.Nonlin.N5gg g) ≤ ENNReal.ofReal (K * Env α g) := by
  refine ⟨12 * Real.sqrt (Real.pi / 2) + 1, by positivity, ?_⟩
  intro α g hα hα1 hgal
  have hreg : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hsq : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have haxis : ∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 := fun θ hθ => (hgal.axis θ hθ).1
  have s0 := slot0 (α := α) (g := g) hsq hmem
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_of_axis haxis)
  have s1 := slot1 (α := α) (g := g) hα.le hsq hmem
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_Dth_of_axis haxis)
  have hXs : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  have hΦ1w := invSq_mul_integrable_le (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g)
    (Xs := Work.Spaces.HkSq α 4 g) s1.nonneg s1.meas s1.intw s1.lew
  have hΦ0w := invSq_mul_integrable_le (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
    (Xs := Work.Spaces.HkSq α 4 g) s0.nonneg s0.meas s0.intw s0.lew
  have hEnvn : 0 ≤ Env α g := Env_nonneg g hα.le
  have hX2 := Xn_sq_le_Env g hα hα1
  have hfinal : ∀ {N : Fn}, Fa N ≤ ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
      * (Work.FTS.Nonlin.Xn α g) ^ 2) →
      Fa N ≤ ENNReal.ofReal ((12 * Real.sqrt (Real.pi / 2) + 1) * Env α g) := by
    intro N hN
    refine hN.trans (ENNReal.ofReal_le_ofReal ?_)
    have h12 : 0 ≤ 12 * Real.sqrt (Real.pi / 2) := by positivity
    calc 12 * Real.sqrt (Real.pi / 2) * (Work.FTS.Nonlin.Xn α g) ^ 2
        ≤ 12 * Real.sqrt (Real.pi / 2) * Env α g := mul_le_mul_of_nonneg_left hX2 h12
      _ ≤ (12 * Real.sqrt (Real.pi / 2) + 1) * Env α g := by
          nlinarith [hEnvn, Real.sqrt_nonneg (Real.pi / 2)]
  constructor
  · -- `N₄^{gg} = -(1/2)·FK g·D_θ g`
    have hmain := Fa_le_coef_slot (N := Work.FTS.Nonlin.N4gg α g)
      (A := fun r _ => 3 * Work.Construction.FK g r) (B := Work.Spaces.Dth g)
      (C := 144) (Ys := Work.Spaces.HkSq α 4 g) (Zs := Work.Spaces.HkSq α 4 g)
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
      (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g)
      (by norm_num) hXs hXs s0.nonneg s0.meas s0.int s0.le
      s1.nonneg s1.meas hΦ1w.1 hΦ1w.2
      (fun r _ => aestronglyMeasurable_const)
      (fun r hr => s1.aesm r hr)
      (fun r hr => s1.sqint r hr)
      (fun r hr => Filter.Eventually.of_forall fun θ => by
        have h := FK_sq_le (g := g) hr (s0.sqint r hr) (s0.aesm r hr)
        have h9 : (3 * Work.Construction.FK g r) ^ 2 = 9 * (Work.Construction.FK g r) ^ 2 := by
          ring
        rw [h9]
        linarith [h])
      (fun r hr => (slot_lintegral_eq (s1.sqint r hr) rfl).le)
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g r θ|
            = |Work.Spaces.K θ| * (1 / 2) * |Work.Construction.FK g r|
              * |Work.Spaces.Dth g r θ| := by
          rw [Work.FTS.Nonlin.N4gg]
          simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
          ring
        have h2 : |Work.Spaces.K θ| * (1 / 2) * |Work.Construction.FK g r|
              * |Work.Spaces.Dth g r θ|
            ≤ 3 * (1 / 2) * |Work.Construction.FK g r| * |Work.Spaces.Dth g r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hK (by norm_num)
        have h3 : 3 * (1 / 2) * |Work.Construction.FK g r| * |Work.Spaces.Dth g r θ|
            ≤ |3 * Work.Construction.FK g r| * |Work.Spaces.Dth g r θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
          nlinarith [abs_nonneg (Work.Construction.FK g r),
            abs_nonneg (Work.Spaces.Dth g r θ)]
        exact (le_of_eq h1).trans (h2.trans h3))
    have hsimp : ENNReal.ofReal (Real.sqrt 144 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.Spaces.HkSq α 4 g) * Real.sqrt (Work.Spaces.HkSq α 4 g))
        = ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
          * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
      have hK : Real.sqrt (144 : ℝ) = 12 := by
        rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hX : Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g := rfl
      rw [hK, hX]
      congr 1
      ring
    rw [hsimp] at hmain
    exact hfinal hmain
  · -- `N₅^{gg} = -sin²θ·FK g·g`
    have hmain := Fa_le_coef_slot (N := Work.FTS.Nonlin.N5gg g)
      (A := fun r _ => 3 * Work.Construction.FK g r) (B := g)
      (C := 144) (Ys := Work.Spaces.HkSq α 4 g) (Zs := Work.Spaces.HkSq α 4 g)
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
      (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
      (by norm_num) hXs hXs s0.nonneg s0.meas s0.int s0.le
      s0.nonneg s0.meas hΦ0w.1 hΦ0w.2
      (fun r _ => aestronglyMeasurable_const)
      (fun r hr => s0.aesm r hr)
      (fun r hr => s0.sqint r hr)
      (fun r hr => Filter.Eventually.of_forall fun θ => by
        have h := FK_sq_le (g := g) hr (s0.sqint r hr) (s0.aesm r hr)
        have h9 : (3 * Work.Construction.FK g r) ^ 2 = 9 * (Work.Construction.FK g r) ^ 2 := by
          ring
        rw [h9]
        linarith [h])
      (fun r hr => (slot_lintegral_eq (s0.sqint r hr) rfl).le)
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have hs : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g r θ|
            = |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
              * |g r θ| := by
          rw [Work.FTS.Nonlin.N5gg]
          simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        have h2 : |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
              * |g r θ|
            ≤ 3 * 1 * |Work.Construction.FK g r| * |g r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul hK hs (sq_nonneg _) (by norm_num)
        have h3 : 3 * 1 * |Work.Construction.FK g r| * |g r θ|
            ≤ |3 * Work.Construction.FK g r| * |g r θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), mul_one]
        exact (le_of_eq h1).trans (h2.trans h3))
    have hsimp : ENNReal.ofReal (Real.sqrt 144 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.Spaces.HkSq α 4 g) * Real.sqrt (Work.Spaces.HkSq α 4 g))
        = ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
          * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
      have hK : Real.sqrt (144 : ℝ) = 12 := by
        rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hX : Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g := rfl
      rw [hK, hX]
      congr 1
      ring
    rw [hsimp] at hmain
    exact hfinal hmain

/-- **Rows `N₄^{gs}`, `N₅^{gs}`** (`FK g` against the explicit profiles `D_θF_*` resp. `F_*`). -/
theorem gsRows45 {Ce : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φg : Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
    Fa (Work.FTS.Nonlin.N4gs α g) ≤ ENNReal.ofReal (K * Env α g) ∧
    Fa (Work.FTS.Nonlin.N5gs α g) ≤ ENNReal.ofReal (K * Env α g) := by
  refine ⟨80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1, by positivity, ?_⟩
  intro α g Φg hα hα1 hgal hell
  have hreg : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hsq : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have haxis : ∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 := fun θ hθ => (hgal.axis θ hθ).1
  have s0 := slot0 (α := α) (g := g) hsq hmem
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_of_axis haxis)
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hEnvn : 0 ≤ Env α g := Env_nonneg g hα.le
  have hsqrtX : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
      Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) ≤ Work.FTS.Nonlin.Xn α g :=
    Real.sqrt_le_sqrt s0.le
  have hX2 := Xn_sq_le_Env g hα hα1
  have hα2X := alpha_sq_mul_Xn_le_Env (g := g) hα hα1
  have hαX := alpha_mul_Xn_le_Env (g := g) hα hα1
  have hrad2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  constructor
  · -- `N₄^{gs} = -(1/2)·sin2θ·FK g·∂_θF_*`
    have hp := profile_data_sq (d := 40 * α ^ 2) (by positivity)
    have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N4gs α g)
      (c := fun r => 40 * α ^ 2 * r / (1 + r) ^ 2)
      (M := fun r => 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (C := 16)
      (by norm_num)
      (fun r hr => by positivity)
      (fun r => by positivity)
      s0.nonneg s0.meas s0.int hp.1 hp.2.1
      (fun r hr => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (s0.nonneg r)]
        norm_num))
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have hd := DthFstar_pt (α := α) hα hα1 hr hθ.1 hθ.2
        have hFKabs : |Work.Construction.FK g r|
            ≤ 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) := by
          have hFK := Real.abs_le_sqrt (FK_sq_le (g := g) hr (s0.sqint r hr) (s0.aesm r hr))
          rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
            show Real.sqrt (16 : ℝ) = 4 from by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hFK
        have hDth : |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|
            ≤ (80 / 3) * α ^ 2 * (r / (1 + r) ^ 2) := hd
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
            = |Work.Spaces.K θ| * (1 / 2)
              * |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|
              * |Work.Construction.FK g r| := by
          rw [Work.FTS.Nonlin.N4gs]
          simp only [Work.Construction.s2, Work.Spaces.Dth, abs_mul, abs_neg,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
          ring
        have hb : (0 : ℝ) ≤ (80 / 3) * α ^ 2 * (r / (1 + r) ^ 2) := by positivity
        have h4 : (0 : ℝ) ≤ 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) :=
          by positivity
        have hstep : |Work.Spaces.K θ| * (1 / 2)
              * |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|
              * |Work.Construction.FK g r|
            ≤ 3 * (1 / 2) * ((80 / 3) * α ^ 2 * (r / (1 + r) ^ 2))
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)) := by
          refine mul_le_mul ?_ hFKabs (abs_nonneg _) (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_right hK (by norm_num)) hDth (abs_nonneg _)
            (by norm_num)
        have heq : 3 * (1 / 2) * ((80 / 3) * α ^ 2 * (r / (1 + r) ^ 2))
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
            = (40 * α ^ 2 * r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)) := by ring
        exact (le_of_eq h1).trans (hstep.trans (le_of_eq heq)))
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show Real.sqrt (16 : ℝ) = 4 from by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have hsq := (profile_data_sq (d := 40 * α ^ 2) (by positivity)).2.2.2
    have h40 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2) ≤ 40 * α ^ 2 * 2 :=
      hsq.trans (by nlinarith [Real.sqrt_nonneg 2, hrad2, sq_nonneg α])
    have hstep : Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2))
        ≤ Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (40 * α ^ 2 * 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrtX (by norm_num)) h40
        (Real.sqrt_nonneg _) (by positivity)
    refine hstep.trans ?_
    have hEnv : Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (40 * α ^ 2 * 2))
        ≤ (80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1) * Env α g := by
      have h1 : Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (40 * α ^ 2 * 2))
          = (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
      rw [h1]
      have h2 : (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α g)
          ≤ (160 * Real.pi) * Env α g :=
        mul_le_mul_of_nonneg_left hα2X (by positivity)
      have h3 : (160 : ℝ) * Real.pi
          ≤ 80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1 := by
        have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]
          norm_num
        nlinarith [Real.pi_pos, hs2]
      calc (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α g)
          ≤ (160 * Real.pi) * Env α g := h2
        _ ≤ (80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1) * Env α g :=
            mul_le_mul_of_nonneg_right h3 hEnvn
    exact hEnv
  · -- `N₅^{gs} = -sin²θ·FK g·F_*`
    have hp := profile_data_sq (d := 60 * α) (by positivity)
    have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N5gs α g)
      (c := fun r => 60 * α * r / (1 + r) ^ 2)
      (M := fun r => 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (C := 16)
      (by norm_num)
      (fun r hr => by positivity)
      (fun r => by positivity)
      s0.nonneg s0.meas s0.int hp.1 hp.2.1
      (fun r hr => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (s0.nonneg r)]
        norm_num))
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have hs : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
        have hF : |Work.Construction.Fstar α r θ|
            ≤ 20 * α * (r / (1 + r) ^ 2) := by
          have h := Fstar_pt (α := α) hα hα1 hr ⟨hθ.1.le, hθ.2.le⟩
          rwa [mul_div_assoc] at h
        have hFKabs : |Work.Construction.FK g r|
            ≤ 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) := by
          have hFK := Real.abs_le_sqrt (FK_sq_le (g := g) hr (s0.sqint r hr) (s0.aesm r hr))
          rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
            show Real.sqrt (16 : ℝ) = 4 from by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hFK
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
            = |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
              * |Work.Construction.Fstar α r θ| := by
          rw [Work.FTS.Nonlin.N5gs]
          simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        have hstep : |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
              * |Work.Construction.Fstar α r θ|
            ≤ 3 * 1 * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
              * (20 * α * (r / (1 + r) ^ 2)) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hK hs (sq_nonneg _) (by norm_num))
            hFKabs (abs_nonneg _) (by positivity)) hF (abs_nonneg _) (by positivity)
        have heq : 3 * 1 * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
              * (20 * α * (r / (1 + r) ^ 2))
            = (60 * α * r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)) := by ring
        exact (le_of_eq h1).trans (hstep.trans (le_of_eq heq)))
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show Real.sqrt (16 : ℝ) = 4 from by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have hsq := (profile_data_sq (d := 60 * α) (by positivity)).2.2.2
    have h60 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2) ≤ 60 * α * 2 :=
      hsq.trans (by nlinarith [Real.sqrt_nonneg 2, hrad2, hα.le])
    have hstep : Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2))
        ≤ Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (60 * α * 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrtX (by norm_num)) h60
        (Real.sqrt_nonneg _) (by positivity)
    refine hstep.trans ?_
    have h1 : Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (60 * α * 2))
        = (240 * Real.pi) * (α * Work.FTS.Nonlin.Xn α g) := by ring
    rw [h1]
    have h3 : (240 : ℝ) * Real.pi
        ≤ 80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1 := by
      have hs2 : ((6 : ℝ) / 5) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      nlinarith [Real.pi_pos, hs2]
    calc (240 * Real.pi) * (α * Work.FTS.Nonlin.Xn α g)
        ≤ (240 * Real.pi) * Env α g := mul_le_mul_of_nonneg_left hαX (by positivity)
      _ ≤ (80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1) * Env α g :=
          mul_le_mul_of_nonneg_right h3 hEnvn

/-- The `Fa`-functional only sees the product `A·B` up to the association of the three
factors `K θ·A·B` (the engine `PsgAux.rl1_slot_le` groups them as `(K θ·A)·B`). -/
theorem Fa_mul_eq (A B : Fn) :
    Fa (fun r θ => A r θ * B r θ)
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|)) := by
  rw [Fa]
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  refine MeasureTheory.lintegral_congr fun θ => ?_
  rw [mul_assoc]

/-- **Rows `N₄^{sg}`, `N₅^{sg}`** (`FK (F_*) = α·2r/(1+r)²` against `D_θg` resp. `g`). -/
theorem sgRows45 {Cs : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs : Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.StarPkgo α Cs Φs →
    Fa (Work.FTS.Nonlin.N4sg α g) ≤ ENNReal.ofReal (K * Env α g) ∧
    Fa (Work.FTS.Nonlin.N5sg α g) ≤ ENNReal.ofReal (K * Env α g) := by
  refine ⟨6 * Real.sqrt (Real.pi / 2) + 1, by positivity, ?_⟩
  intro α g Φs hα hα1 hgal hs
  have hreg : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hsq : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hEnvn : 0 ≤ Env α g := Env_nonneg g hα.le
  have hαX := alpha_mul_Xn_le_Env (g := g) hα hα1
  have hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.contOn_of_smoothQuad hsq
  have hcontD : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.contOn_of_smoothQuad
      (Work.FTS.LocData.SmoothQuad.DthIter hsq 1)
  have hFKF : ∀ r : ℝ, 0 < r → |Work.Construction.FK (Work.Construction.Fstar α) r|
      ≤ α / 2 := by
    intro r hr
    rw [FK_Fstar_pt hα hα1]
    have h1 : (0 : ℝ) ≤ 2 * r / (1 + r) ^ 2 := div_nonneg (by linarith) (by positivity)
    rw [abs_mul, abs_of_nonneg hα.le, abs_of_nonneg h1]
    have h2 : 2 * r / (1 + r) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (1 - r)]
    nlinarith [h2, hα.le]
  constructor
  · -- `N₄^{sg} = -(1/2)·FK (F_*)·D_θ g`
    have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
      (α := α) (C := 3 * α) (g := g)
      (A := fun z _ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
      (B := Work.Spaces.Dth g)
      (by positivity) hmem
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have h1 : |Work.Spaces.K θ * (-(1 / 2)
              * Work.Construction.FK (Work.Construction.Fstar α) r)| 
            = |Work.Spaces.K θ| * (1 / 2)
              * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
          simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
          ring
        rw [h1]
        have h3 : |Work.Spaces.K θ| * (1 / 2)
            * |Work.Construction.FK (Work.Construction.Fstar α) r| ≤ 3 * (1 / 2) * (α / 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hK (by norm_num)) (hFKF r hr)
            (abs_nonneg _) (by positivity)
        refine h3.trans ?_
        nlinarith [hα.le])
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hcontD hr)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hcontD)
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ =>
        Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dth hα hr hθ g)
    have hid : Work.FTS.Nonlin.N4sg α g
        = fun r θ => (-(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) r)
            * Work.Spaces.Dth g r θ := by
      funext r θ
      simp only [Work.FTS.Nonlin.N4sg]
    rw [hid, Fa_mul_eq (A := fun z _ =>
        -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
      (B := Work.Spaces.Dth g)]
    refine hmain.trans ?_
    · exact ENNReal.ofReal_le_ofReal (by
        have h1 : (3 * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
            = (3 * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g) := by ring
        rw [h1]
        have h2 : (3 * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g)
            ≤ (3 * Real.sqrt (Real.pi / 2)) * Env α g :=
          mul_le_mul_of_nonneg_left hαX (by positivity)
        have h3 : (3 * Real.sqrt (Real.pi / 2))
            ≤ (6 * Real.sqrt (Real.pi / 2) + 1) := by
          nlinarith [Real.sqrt_nonneg (Real.pi / 2)]
        exact h2.trans (mul_le_mul_of_nonneg_right h3 hEnvn))
  · -- `N₅^{sg} = -sin²θ·FK (F_*)·g`
    have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
      (α := α) (C := 6 * α) (g := g)
      (A := fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z)
      (B := g)
      (by positivity) hmem
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
        have h1 : |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
              * Work.Construction.FK (Work.Construction.Fstar α) r)|
            = |Work.Spaces.K θ| * (Real.sin θ) ^ 2
              * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
          simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        rw [h1]
        have h3 : |Work.Spaces.K θ| * (Real.sin θ) ^ 2
            * |Work.Construction.FK (Work.Construction.Fstar α) r|
            ≤ 3 * 1 * (α / 2) := by
          refine mul_le_mul (mul_le_mul hK hsin (sq_nonneg _) (by norm_num)) (hFKF r hr)
            (abs_nonneg _) (by positivity)
        exact h3.trans (by nlinarith [hα.le]))
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hcont hr)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hcont)
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ =>
        Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_g hα hr hθ g)
    have hid : Work.FTS.Nonlin.N5sg α g
        = fun r θ => (-(Real.sin θ) ^ 2
            * Work.Construction.FK (Work.Construction.Fstar α) r) * g r θ := by
      funext r θ
      simp only [Work.FTS.Nonlin.N5sg]
    rw [hid, Fa_mul_eq (A := fun z θ =>
        -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) (B := g)]
    refine hmain.trans ?_
    · exact ENNReal.ofReal_le_ofReal (by
        have h1 : (6 * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
            = (6 * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g) := by ring
        rw [h1]
        have h2 : (6 * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g)
            ≤ (6 * Real.sqrt (Real.pi / 2)) * Env α g :=
          mul_le_mul_of_nonneg_left hαX (by positivity)
        exact h2.trans (mul_le_mul_of_nonneg_right (by
          nlinarith [Real.sqrt_nonneg (Real.pi / 2)]) hEnvn))

end Work.FTS.NonlinRows.Rl1
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.gsRow2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-- Row `N₂^{gs} = -2𝒰(Φ̃_g)·∂_θF_*` of the primed `gs`-block (namespace
`Work.FTS.NonlinRows.Rl1`).  With the `r`-dependent coefficient majorant
`M₂ r = √(CA/(γ-1) · ∫_θ HkIntegrand α 4 (𝒰/sin 2θ) r θ)` (`hang` is the angular sup bound of
`Work.FTS.NonlinRows.Rl1.angSup_le`, instantiated at the `HQo`-coefficient `𝒰/sin2θ` of
`hell.U`) and the pointwise profile bound `|K θ · ∂_θF_*| ≤ 80α²·r/(1+r)²`
(`Work.FTS.NonlinRows.Rl1.K_pthFstar_pt`), the `L₁₂`-density functional satisfies
`Fa (N2gs) ≤ ofReal (2000·√(10CA)·max Ce 0·α^{1/2}·|g|_{ℋ⁴})`.  Route: write
`𝒰 = sin2θ·(𝒰/sin2θ)` (valid on `Ioo 0 (π/2)`, and the endpoints are null), then
`Work.FTS.NonlinRows.Rl1.Fa_le_of_profile` with profile `c r = 160α²·r/(1+r)`, using
`Work.FTS.NonlinRows.Rl1.profile_data` for the profile and `HkSlot_data`/`hell.U.2` for the
coefficient energy.  Template: `row1gs` in
`Submission/Work/FTS/NonlinRows/Rl1/gsBounds.lean` (proved). -/
theorem gsRow2 {CA α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn} (hCA : 0 < CA)
    (hang : ∀ (A : Work.FTS.Galerkin.Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.Spaces.HkMem α 4 A →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ')
    (hα : 0 < α) (hα1 : α ≤ 1) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2gs α g Φg)
      ≤ ENNReal.ofReal (2000 * Real.sqrt (10 * CA) * max Ce 0
          * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  have hC : 0 ≤ CA / (Work.Spaces.gam α - 1) := div_nonneg hCA.le hγ.le
  -- the `HQo`-coefficient `𝒰/sin 2θ` of `hell.U`, and its angular slot
  set A : Work.FTS.Galerkin.Fn := fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ with hA
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A := hell.U.1.1
  have hAmem : Work.Spaces.HkMem α 4 A := hell.U.1.2
  have hAxn : Work.FTS.Nonlin.Xn α A ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.U.2
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ with hΨ
  set M : ℝ → ℝ := fun r => Real.sqrt (CA / (Work.Spaces.gam α - 1) * Ψ r) with hM
  set cc : ℝ → ℝ := fun r => 160 * α ^ 2 * r / (1 + r) with hcc
  have hccnn : ∀ r, 0 < r → 0 ≤ cc r := by
    intro r hr
    have h : cc r = 160 * α ^ 2 * r / (1 + r) := rfl
    rw [h]; positivity
  have hMnn : ∀ r, 0 ≤ M r := fun r => Real.sqrt_nonneg _
  have hΨnn : ∀ r, 0 ≤ Ψ r := by
    intro r
    exact MeasureTheory.setIntegral_nonneg
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 A r θ)
  have hMle : ∀ r, 0 < r → (M r) ^ 2 ≤ CA / (Work.Spaces.gam α - 1) * Ψ r := by
    intro r _
    exact (Real.sq_sqrt (mul_nonneg hC (hΨnn r))).le
  obtain ⟨hΨmeas, hΨint, hΨle⟩ := HkSlot_data hAmem
  have hccmeas : AEMeasurable (fun r => r⁻¹ * cc r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (profile_data (d := 160 * α ^ 2) (by positivity)).1
  have hccint : MeasureTheory.IntegrableOn (fun r => (r⁻¹ * cc r) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (profile_data (d := 160 * α ^ 2) (by positivity)).2.1
  -- ### the pointwise (angular) step: `𝒰 = sin 2θ · (𝒰/sin 2θ)`
  have hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2gs α g Φg r θ| ≤ cc r * M r := by
    intro r hr θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hs2pos : 0 < Work.Construction.s2 θ := by
      rw [Work.Construction.s2_eq]
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs2le : Work.Construction.s2 θ ≤ 1 := by
      rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
    have hUfac : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
        = Work.Construction.s2 θ * A r θ := by
      have hA' : A r θ = Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
          / Work.Construction.s2 θ := rfl
      rw [hA', mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hs2pos)]
    have hAabs : |A r θ| ≤ M r := by
      have h2 := hang A hAsm hAmem r θ hr hθ0 hθ1
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq_eq_abs] at h3
    have hK := K_pthFstar_pt hα hα1 hr hθ0 hθ1
    have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt hs2pos
    have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N2gs α g Φg r θ|
        = 2 * (Work.Construction.s2 θ * |A r θ|)
            * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ| := by
      have hval : Work.Spaces.K θ * Work.FTS.Nonlin.N2gs α g Φg r θ
          = -2 * (Work.Construction.s2 θ * A r θ)
              * (Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ) := by
        simp only [Work.FTS.Nonlin.N2gs]
        rw [hUfac]
        ring
      rw [hval]
      simp only [abs_mul, abs_neg, abs_of_nonneg hs2nn,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    have h2le : Work.Construction.s2 θ * |A r θ| ≤ 1 * M r :=
      mul_le_mul hs2le hAabs (abs_nonneg _) zero_le_one
    have h1 : 2 * (Work.Construction.s2 θ * |A r θ|) ≤ 2 * (1 * M r) :=
      mul_le_mul_of_nonneg_left h2le (by norm_num)
    have hmid : 2 * (Work.Construction.s2 θ * |A r θ|)
        * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|
        ≤ 2 * (1 * M r) * (80 * α ^ 2 * (r / (1 + r) ^ 2)) :=
      mul_le_mul h1 hK (abs_nonneg _) (by positivity)
    refine hmid.trans ?_
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have hstepp : 160 * α ^ 2 * (r / (1 + r) ^ 2) ≤ 160 * α ^ 2 * (r / (1 + r)) := by
      have hle : r / (1 + r) ^ 2 ≤ r / (1 + r) := by
        rw [div_le_div_iff₀ (by positivity) h1r]
        nlinarith [hr.le, h1r.le, sq_nonneg r, mul_nonneg hr.le h1r.le]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    calc 2 * (1 * M r) * (80 * α ^ 2 * (r / (1 + r) ^ 2))
        = 160 * α ^ 2 * (r / (1 + r) ^ 2) * M r := by ring
      _ ≤ 160 * α ^ 2 * (r / (1 + r)) * M r := mul_le_mul_of_nonneg_right hstepp (hMnn r)
      _ = cc r * M r := by
          have hcc' : cc r = 160 * α ^ 2 * r / (1 + r) := rfl
          rw [hcc']
          ring
  -- ### the Cauchy–Schwarz step
  have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N2gs α g Φg) (c := cc) (M := M)
    (Ψ := Ψ) (C := CA / (Work.Spaces.gam α - 1)) hC hccnn hMnn hΨnn hΨmeas hΨint
    hccmeas hccint hMle hpt
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCa0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  have hs10 : 0 ≤ Real.sqrt (10 * CA) := Real.sqrt_nonneg _
  have hα12 : 0 ≤ α ^ (1 / 2 : ℝ) := Real.rpow_nonneg hα.le _
  have hΨbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
      ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g := by
    have h1 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Work.FTS.Nonlin.Xn α A :=
      Real.sqrt_le_sqrt hΨle
    calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Work.FTS.Nonlin.Xn α A := h1
      _ ≤ Ce * Work.FTS.Nonlin.Xn α g := hAxn
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) hX0
  have hcbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
      ≤ 160 * α ^ 2 * Real.sqrt 2 :=
    (profile_data (d := 160 * α ^ 2) (by positivity)).2.2.2
  have hkey : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
      ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
          * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
    have h1 : Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        ≤ Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (max Ce 0 * Work.FTS.Nonlin.Xn α g)
            * (160 * α ^ 2 * Real.sqrt 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hΨbd (Real.sqrt_nonneg _)) hcbd
        (Real.sqrt_nonneg _) ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCa0 hX0)
    have h2 : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * (max Ce 0 * Work.FTS.Nonlin.Xn α g) * (160 * α ^ 2 * Real.sqrt 2))
        = Real.pi / 2 * Real.sqrt 2 * 160
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
            * max Ce 0 * Work.FTS.Nonlin.Xn α g := by ring
    have h3 : Real.pi / 2 * Real.sqrt 2 * 160
          * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
          * max Ce 0 * Work.FTS.Nonlin.Xn α g
        ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
            * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
      rw [sqrt_coef_mul_alpha_sq hCA.le hα]
      have h3232 : α ^ (3 / 2 : ℝ) ≤ α ^ (1 / 2 : ℝ) := rpow_three_halves_le' hα hα1
      have hα32 : 0 ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα.le _
      have hconst : Real.pi / 2 * Real.sqrt 2 * 160 ≤ 2000 := by
        have h2 : Real.sqrt 2 ≤ 2 := by
          have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
          have h2' := Real.sqrt_nonneg 2
          nlinarith
        have hp : Real.pi / 2 ≤ 2 := by
          have h := Real.pi_lt_four
          have h2' := Real.pi_pos
          linarith
        nlinarith [Real.sqrt_nonneg 2, Real.pi_pos]
      have hR : 0 ≤ Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
        mul_nonneg (mul_nonneg hs10 hCa0) hX0
      have hR32 : 0 ≤ Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0
          * Work.FTS.Nonlin.Xn α g :=
        mul_nonneg (mul_nonneg (mul_nonneg hs10 hα32) hCa0) hX0
      have hstep : Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0 * Work.FTS.Nonlin.Xn α g
          ≤ Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
        calc Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0 * Work.FTS.Nonlin.Xn α g
            = (Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
                * α ^ (3 / 2 : ℝ) := by ring
          _ ≤ (Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
                * α ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left h3232 hR
          _ = Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0
                * Work.FTS.Nonlin.Xn α g := by ring
      calc Real.pi / 2 * Real.sqrt 2 * 160 * (Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ))
            * max Ce 0 * Work.FTS.Nonlin.Xn α g
          = (Real.pi / 2 * Real.sqrt 2 * 160)
              * (Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0
                * Work.FTS.Nonlin.Xn α g) := by ring
        _ ≤ 2000 * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0
              * Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul hconst hstep hR32 (by norm_num)
        _ = 2000 * Real.sqrt (10 * CA) * max Ce 0
              * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by ring
    calc Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
        ≤ Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
            * (max Ce 0 * Work.FTS.Nonlin.Xn α g) * (160 * α ^ 2 * Real.sqrt 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi / 2 * Real.sqrt 2 * 160
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
            * max Ce 0 * Work.FTS.Nonlin.Xn α g := h2
      _ ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
            * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := h3
  exact hmain.trans (ENNReal.ofReal_le_ofReal hkey)

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.gsRow3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-- Row `N₃^{gs} = -2α𝒱(Φ̃_g)·D_zF_*` of the primed `gs`-block (namespace
`Work.FTS.NonlinRows.Rl1`).  With the `r`-dependent coefficient majorant
`M₃ r = √(CA/(γ-1) · ∫_θ HkIntegrand α 4 (𝒱(Φ̃_g)) r θ)` (`hang` is the angular sup bound of
`Work.FTS.NonlinRows.Rl1.angSup_le`, instantiated at the `HQo`-coefficient `hell.V`) and the
pointwise profile bound `|K θ · D_zF_*| ≤ 60α·r/(1+r)²`
(`Work.FTS.NonlinRows.Rl1.K_DzFstar_pt`), the `L₁₂`-density functional satisfies
`Fa (N3gs) ≤ ofReal (2000·√(10CA)·max Ce 0·α^{1/2}·|g|_{ℋ⁴})`.  Route: `Fa_le_of_profile`
with profile `c r = 120α²·r/(1+r)`, using `Work.FTS.NonlinRows.Rl1.profile_data` for the
profile and `HkSlot_data`/`hell.V.2` for the coefficient energy; the extra factor `2α` of the
piece gives `2α·60α = 120α²`, and `√(CA/(γ-1))·α² = √(10CA)·α^{3/2} ≤ √(10CA)·α^{1/2}` by
`sqrt_coef_mul_alpha_sq`/`rpow_three_halves_le'`.  Template: `row1gs` in
`Submission/Work/FTS/NonlinRows/Rl1/gsBounds.lean` (proved). -/
theorem gsRow3 {CA α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn} (hCA : 0 < CA)
    (hang : ∀ (A : Work.FTS.Galerkin.Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.Spaces.HkMem α 4 A →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ')
    (hα : 0 < α) (hα1 : α ≤ 1) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3gs α g Φg)
      ≤ ENNReal.ofReal (2000 * Real.sqrt (10 * CA) * max Ce 0
          * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  have hC : 0 ≤ CA / (Work.Spaces.gam α - 1) := div_nonneg hCA.le hγ.le
  -- the `HQo`-coefficient `𝒱(Φ̃_g)` of `hell.V`, and its angular slot
  set A : Work.FTS.Galerkin.Fn :=
    Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) with hA
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A := hell.V.1.1
  have hAmem : Work.Spaces.HkMem α 4 A := hell.V.1.2
  have hAxn : Work.FTS.Nonlin.Xn α A ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.V.2
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ with hΨ
  set M : ℝ → ℝ := fun r => Real.sqrt (CA / (Work.Spaces.gam α - 1) * Ψ r) with hM
  set cc : ℝ → ℝ := fun r => 120 * α ^ 2 * r / (1 + r) with hcc
  have hccnn : ∀ r, 0 < r → 0 ≤ cc r := by
    intro r hr
    rw [hcc]
    positivity
  have hMnn : ∀ r, 0 ≤ M r := fun r => Real.sqrt_nonneg _
  have hΨnn : ∀ r, 0 ≤ Ψ r := by
    intro r
    exact MeasureTheory.setIntegral_nonneg
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 A r θ)
  have hMle : ∀ r, 0 < r → (M r) ^ 2 ≤ CA / (Work.Spaces.gam α - 1) * Ψ r := by
    intro r _
    exact (Real.sq_sqrt (mul_nonneg hC (hΨnn r))).le
  obtain ⟨hΨmeas, hΨint, hΨle⟩ := HkSlot_data hAmem
  have hccmeas : AEMeasurable (fun r => r⁻¹ * cc r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (profile_data (d := 120 * α ^ 2) (by positivity)).1
  have hccint : MeasureTheory.IntegrableOn (fun r => (r⁻¹ * cc r) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (profile_data (d := 120 * α ^ 2) (by positivity)).2.1
  -- ### the pointwise (angular) step
  have hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N3gs α g Φg r θ| ≤ cc r * M r := by
    intro r hr θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hAabs : |A r θ| ≤ M r := by
      have h2 := hang A hAsm hAmem r θ hr hθ0 hθ1
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq_eq_abs] at h3
    have hK := K_DzFstar_pt hα hα1 hr hθI
    have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N3gs α g Φg r θ|
        = 2 * α * |A r θ|
          * |Work.Spaces.K θ * Work.Spaces.Dz (Work.Construction.Fstar α) r θ| := by
      have hval : Work.Spaces.K θ * Work.FTS.Nonlin.N3gs α g Φg r θ
          = -2 * α * A r θ
            * (Work.Spaces.K θ * Work.Spaces.Dz (Work.Construction.Fstar α) r θ) := by
        simp only [Work.FTS.Nonlin.N3gs, hA]
        ring
      rw [hval, abs_mul, abs_mul,
        show |(-2 : ℝ) * α| = 2 * α by
          rw [show (-2 : ℝ) * α = -(2 * α) by ring, abs_neg,
            abs_of_nonneg (by positivity)]]
    rw [habs]
    have h1 : 2 * α * |A r θ| ≤ 2 * α * M r :=
      mul_le_mul_of_nonneg_left hAabs (by positivity)
    have hmid : 2 * α * |A r θ|
          * |Work.Spaces.K θ * Work.Spaces.Dz (Work.Construction.Fstar α) r θ|
        ≤ 2 * α * M r * (60 * α * (r / (1 + r) ^ 2)) :=
      mul_le_mul h1 hK (abs_nonneg _) (by positivity)
    refine hmid.trans ?_
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have hstepp : 120 * α ^ 2 * (r / (1 + r) ^ 2) ≤ 120 * α ^ 2 * (r / (1 + r)) := by
      have hle : r / (1 + r) ^ 2 ≤ r / (1 + r) := by
        rw [div_le_div_iff₀ (by positivity) h1r]
        nlinarith [hr.le, h1r.le, sq_nonneg r, mul_nonneg hr.le h1r.le]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    calc 2 * α * M r * (60 * α * (r / (1 + r) ^ 2))
        = 120 * α ^ 2 * (r / (1 + r) ^ 2) * M r := by ring
      _ ≤ 120 * α ^ 2 * (r / (1 + r)) * M r := mul_le_mul_of_nonneg_right hstepp (hMnn r)
      _ = cc r * M r := by
          rw [hcc]
          ring
  -- ### the Cauchy–Schwarz step
  have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N3gs α g Φg) (c := cc) (M := M)
    (Ψ := Ψ) (C := CA / (Work.Spaces.gam α - 1)) hC hccnn hMnn hΨnn hΨmeas hΨint
    hccmeas hccint hMle hpt
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCa0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  have hs10 : 0 ≤ Real.sqrt (10 * CA) := Real.sqrt_nonneg _
  have hα12 : 0 ≤ α ^ (1 / 2 : ℝ) := Real.rpow_nonneg hα.le _
  have hΨbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
      ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g := by
    have h1 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Work.FTS.Nonlin.Xn α A :=
      Real.sqrt_le_sqrt hΨle
    calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Work.FTS.Nonlin.Xn α A := h1
      _ ≤ Ce * Work.FTS.Nonlin.Xn α g := hAxn
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) hX0
  have hcbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
      ≤ 120 * α ^ 2 * Real.sqrt 2 :=
    (profile_data (d := 120 * α ^ 2) (by positivity)).2.2.2
  have hkey : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
      ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
          * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
    have h1 : Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        ≤ Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (max Ce 0 * Work.FTS.Nonlin.Xn α g)
            * (120 * α ^ 2 * Real.sqrt 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hΨbd (Real.sqrt_nonneg _)) hcbd
        (Real.sqrt_nonneg _) ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCa0 hX0)
    have h2 : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * (max Ce 0 * Work.FTS.Nonlin.Xn α g) * (120 * α ^ 2 * Real.sqrt 2))
        = Real.pi / 2 * Real.sqrt 2 * 120
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
            * max Ce 0 * Work.FTS.Nonlin.Xn α g := by ring
    have h3 : Real.pi / 2 * Real.sqrt 2 * 120
          * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
          * max Ce 0 * Work.FTS.Nonlin.Xn α g
        ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
            * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
      rw [sqrt_coef_mul_alpha_sq hCA.le hα]
      have h3232 : α ^ (3 / 2 : ℝ) ≤ α ^ (1 / 2 : ℝ) := rpow_three_halves_le' hα hα1
      have hα32 : 0 ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα.le _
      have hR : 0 ≤ Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
        mul_nonneg (mul_nonneg hs10 hCa0) hX0
      have hR32 : 0 ≤ Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0
          * Work.FTS.Nonlin.Xn α g :=
        mul_nonneg (mul_nonneg (mul_nonneg hs10 hα32) hCa0) hX0
      have hstep : Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0
            * Work.FTS.Nonlin.Xn α g
          ≤ Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0
            * Work.FTS.Nonlin.Xn α g := by
        calc Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0 * Work.FTS.Nonlin.Xn α g
            = (Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
                * α ^ (3 / 2 : ℝ) := by ring
          _ ≤ (Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
                * α ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left h3232 hR
          _ = Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0
                * Work.FTS.Nonlin.Xn α g := by ring
      calc Real.pi / 2 * Real.sqrt 2 * 120 * (Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ))
            * max Ce 0 * Work.FTS.Nonlin.Xn α g
          = (Real.pi / 2 * Real.sqrt 2 * 120)
              * (Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0
                * Work.FTS.Nonlin.Xn α g) := by ring
        _ ≤ 2000 * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0
              * Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul pi_div_two_mul_sqrt_two_mul hstep hR32 (by norm_num)
        _ = 2000 * Real.sqrt (10 * CA) * max Ce 0
              * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by ring
    calc Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
        ≤ Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
            * (max Ce 0 * Work.FTS.Nonlin.Xn α g) * (120 * α ^ 2 * Real.sqrt 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi / 2 * Real.sqrt 2 * 120
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
            * max Ce 0 * Work.FTS.Nonlin.Xn α g := h2
      _ ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
            * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := h3
  exact hmain.trans (ENNReal.ofReal_le_ofReal hkey)

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.PhiAjDivFlat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open Set

/-! ## The constant -/

/-- The constant of the flat bound for the divided `𝒜`-iterates: an `α`-free, `j`-free envelope
of the coefficient bounds `cit (2j) (2j+1) k · nb j`, `j ≤ 9`, `k ≤ 7`. -/
noncomputable def DivA : ℝ := 1 + ∑ j ∈ Finset.range 10, ∑ k ∈ Finset.range 8,
    Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j

lemma DivA_pos : 0 < DivA := by
  rw [DivA]
  have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range 10, ∑ k ∈ Finset.range 8,
      Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (Unif.cit_nonneg (2 * j) (2 * j + 1) k) (Unif.nb_nonneg j)
  linarith

lemma term_le_DivA {j k : ℕ} (hj : j ≤ 9) (hk : k ≤ 7) :
    Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j ≤ DivA := by
  have hj10 : j ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have hk8 : k ∈ Finset.range 8 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ j' ∈ Finset.range 10, 0 ≤ ∑ k' ∈ Finset.range 8,
      Unif.cit (2 * j') (2 * j' + 1) k' * Unif.nb j' := fun j' _ =>
    Finset.sum_nonneg fun k' _ =>
      mul_nonneg (Unif.cit_nonneg (2 * j') (2 * j' + 1) k') (Unif.nb_nonneg j')
  have h1 : Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j
      ≤ ∑ k' ∈ Finset.range 8, Unif.cit (2 * j) (2 * j + 1) k' * Unif.nb j :=
    Finset.single_le_sum (fun k' _ =>
      mul_nonneg (Unif.cit_nonneg (2 * j) (2 * j + 1) k') (Unif.nb_nonneg j)) hk8
  have h2 : (∑ k' ∈ Finset.range 8, Unif.cit (2 * j) (2 * j + 1) k' * Unif.nb j)
      ≤ ∑ j' ∈ Finset.range 10, ∑ k' ∈ Finset.range 8,
          Unif.cit (2 * j') (2 * j' + 1) k' * Unif.nb j' :=
    Finset.single_le_sum hinner hj10
  rw [DivA]
  linarith

/-! ## The target -/

theorem PhiAjDivFlat : ∃ A : ℝ, 0 < A ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (j : ℕ), j ≤ 9 → ∀ (k : ℕ), k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Work.FTS.PhiStar.phiAj j α z') z| ≤ A := by
  refine ⟨DivA, DivA_pos, ?_⟩
  intro α hα hα5 j hj k hk z hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hQ : (phiAjNumDiv α j).natDegree ≤ 2 * j := phiAjNumDiv_natDegree_le α j
  have hN : (numIter (2 * j + 1) (phiAjNumDiv α j) k).natDegree ≤ 2 * j :=
    (numIter_natDegree_le (2 * j + 1) (phiAjNumDiv α j) k).trans hQ
  -- the divided profile is the rational function `Q/(1+z)^(2j+1)` on `(0,∞)`
  have hfun : Set.EqOn (fun z' : ℝ => (z' + 1) / z' * phiAj j α z')
      (fun z' : ℝ => (phiAjNumDiv α j).eval z' / (1 + z') ^ (2 * j + 1)) (Set.Ioi 0) := by
    intro z' hz'
    show (z' + 1) / z' * phiAj j α z' = (phiAjNumDiv α j).eval z' / (1 + z') ^ (2 * j + 1)
    have hd : phiAj j α z' / z' = (phiAjNumDiv α j).eval z' / (1 + z') ^ (2 * j + 2) :=
      phiAj_div_eqOn_num α j hz'
    have hne : (1 + z' : ℝ) ≠ 0 := by
      have : (0 : ℝ) < z' := hz'
      linarith
    have hne0 : z' ≠ 0 := ne_of_gt hz'
    have hmul : (z' + 1) / z' * phiAj j α z' = (z' + 1) * (phiAj j α z' / z') := by
      field_simp
    rw [hmul, hd]
    rw [show (2 * j + 2 : ℕ) = (2 * j + 1) + 1 from by omega, pow_succ]
    field_simp
    ring
  -- the iterated derivative against the numerator polynomial
  have heq : iteratedDeriv k (fun z' : ℝ => (z' + 1) / z' * phiAj j α z') z
      = (numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z / (1 + z) ^ (2 * j + 1 + k) := by
    rw [iteratedDeriv_congr_of_eqOn_isOpen isOpen_Ioi hfun k hz]
    exact iteratedDeriv_rat (phiAjNumDiv α j) (2 * j + 1) (by omega) k hz1
  -- the `(z+1)^k` factor cancels one power of `1+z`
  have hne1 : (1 + z : ℝ) ≠ 0 := by linarith
  have hstep : (z + 1) ^ k * ((numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z
        / (1 + z) ^ (2 * j + 1 + k))
      = (numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z / (1 + z) ^ (2 * j + 1) := by
    rw [← mul_div_assoc, show (2 * j + 1 + k : ℕ) = k + (2 * j + 1) from by omega, pow_add]
    field_simp
    ring
  have hcl : (∑ i ∈ Finset.range (2 * j + 1),
        |(numIter (2 * j + 1) (phiAjNumDiv α j) k).coeff i|)
      = Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) :=
    Unif.sum_range_coeff_eq_cl1 hN
  have hpe := poly_eval_bound (numIter (2 * j + 1) (phiAjNumDiv α j) k) hN hz.le
  rw [hcl] at hpe
  -- the `α`-uniform coefficient bound
  have hCN : Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k)
      ≤ Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j := by
    have h1 := Unif.cl1_numIter_le (2 * j + 1) (2 * j) k hQ
    have h2 : Unif.cl1 (phiAjNumDiv α j) ≤ Unif.nb j :=
      (Unif.cl1_divX_le (phiAjNum α j)).trans (Unif.cl1_phiAjNum_le α hα hα5 j)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Unif.cit_nonneg (2 * j) (2 * j + 1) k))
  have hCnn : 0 ≤ Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) := Unif.cl1_nonneg _
  have hfin : |(numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z / (1 + z) ^ (2 * j + 1)|
      ≤ Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ (2 * j + 1))]
    have hpos : (0 : ℝ) < (1 + z) ^ (2 * j + 1) := by positivity
    calc |(numIter (2 * j + 1) (phiAjNumDiv α j) k).eval z| / (1 + z) ^ (2 * j + 1)
        ≤ Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) * (1 + z) ^ (2 * j)
            / (1 + z) ^ (2 * j + 1) := by
          apply div_le_div_of_nonneg_right hpe hpos.le
      _ = Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) / (1 + z) := by
          rw [pow_succ]
          field_simp
      _ ≤ Unif.cl1 (numIter (2 * j + 1) (phiAjNumDiv α j) k) :=
          div_le_self hCnn (by linarith)
      _ ≤ Unif.cit (2 * j) (2 * j + 1) k * Unif.nb j := hCN
  rw [heq, hstep]
  exact hfin.trans (term_le_DivA hj hk)

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_mul_deriv_atTop_zero_meas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The definitional identity `radGreen = rgK (rgG1 + rgG2)`. -/
private lemma radGreen_eq_rgK_mul (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = Work.FTS.EllExist.rgK α m
        * (Work.FTS.EllExist.rgG1 α m c z + Work.FTS.EllExist.rgG2 α m c z) := by
  rw [Work.FTS.EllExist.radGreen_eq]
  simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.LinvFlat.LinvLopOde =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The first-order equation satisfied by `Linv h` -/

lemma LI_lop_Linv_eq {h : ℝ → ℝ}
    (hcd : ContDiffOn ℝ 9 h (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    Set.EqOn (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
      (fun θ : ℝ => -(h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  obtain ⟨-, hderiv⟩ :=
    Linv_contDiffOn_hasDerivAt (h := h) (n := 9) (by norm_num) hcd hint
  intro θ hθ
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hcoef : 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2) = LI_L2fun θ := by
    rw [LI_L2fun_eq]
  show Real.sin (2 * θ) * deriv (Work.FTS.PhiStar.Linv h) θ
    = -(h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)
  rw [(hderiv θ hθ).deriv, hcoef]
  field_simp [hsin]

/-- Expansion of `Lop^[k]` applied to the source function `-(h + L₂ Linv h)`. -/
lemma LI_lop_iter_Xfun_eqOn {h : ℝ → ℝ}
    (hcd9 : ContDiffOn ℝ 9 h (Set.Ioo 0 (Real.pi / 2)))
    (hg9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)))
    {k : ℕ} (hk : k ≤ 8) :
    Set.EqOn
      (Work.Spaces.Lop^[k]
        (fun θ : ℝ => -(h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)))
      (fun θ : ℝ => -(Work.Spaces.Lop^[k] h θ)
        - ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) *
            ((Work.Spaces.Lop^[a]) LI_L2fun θ * (Work.Spaces.Lop^[k - a])
              (Work.FTS.PhiStar.Linv h) θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hh : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) h (Set.Ioo 0 (Real.pi / 2)) :=
    hcd9.of_le (by exact_mod_cast (by omega : k ≤ 9))
  have hg : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (Work.FTS.PhiStar.Linv h)
      (Set.Ioo 0 (Real.pi / 2)) := hg9.of_le (by exact_mod_cast (by omega : k ≤ 9))
  have hL2 : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) LI_L2fun (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_LI_L2fun k
  have hA0 : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω)
      (fun θ : ℝ => h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)
      (Set.Ioo 0 (Real.pi / 2)) := hh.add (hL2.mul hg)
  have hB : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω)
      (LI_L2fun * Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)) := hL2.mul hg
  have hneg := LI_Lop_iter_neg_eqOn hU k
    (A := (fun θ : ℝ => h θ + LI_L2fun θ * Work.FTS.PhiStar.Linv h θ)) hA0
  have hadd := LI_Lop_iter_add_eqOn hU k hh hB
  have hleib := LI_Lop_iter_mul_eqOn_9 hU (contDiffOn_LI_L2fun 9) hg9 k hk
  refine hneg.trans ?_
  have hmid : Set.EqOn
      (fun θ : ℝ => -(Work.Spaces.Lop^[k]
        (fun θ' : ℝ => h θ' + LI_L2fun θ' * Work.FTS.PhiStar.Linv h θ') θ))
      (fun θ : ℝ => -(Work.Spaces.Lop^[k] h θ
        + Work.Spaces.Lop^[k] (LI_L2fun * Work.FTS.PhiStar.Linv h) θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ hθ
    exact congrArg Neg.neg (hadd hθ)
  refine hmid.trans ?_
  intro θ hθ
  show -(Work.Spaces.Lop^[k] h θ + Work.Spaces.Lop^[k] (LI_L2fun * Work.FTS.PhiStar.Linv h) θ)
    = -(Work.Spaces.Lop^[k] h θ)
      - ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) *
          ((Work.Spaces.Lop^[a]) LI_L2fun θ
            * (Work.Spaces.Lop^[k - a]) (Work.FTS.PhiStar.Linv h) θ)
  rw [hleib hθ]
  ring

/-! ## The growth sequence -/

/-- `LI_Cfun M n = 4 (10⁶ (M+1))ⁿ`. -/
def LI_Cfun (M : ℝ) (n : ℕ) : ℝ := 4 * (1000000 * (M + 1)) ^ n

lemma LI_Cfun_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : 0 ≤ LI_Cfun M n := by
  show 0 ≤ 4 * (1000000 * (M + 1)) ^ n
  have h : (0 : ℝ) ≤ 1000000 * (M + 1) := by nlinarith
  exact mul_nonneg (by norm_num) (pow_nonneg h n)

lemma LI_Cfun_one_le {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : (1 : ℝ) ≤ LI_Cfun M n := by
  show (1 : ℝ) ≤ 4 * (1000000 * (M + 1)) ^ n
  have hR : (1 : ℝ) ≤ 1000000 * (M + 1) := by nlinarith
  have h2 : (1 : ℝ) ≤ (1000000 * (M + 1)) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; nlinarith [ih, hR]
  nlinarith

lemma LI_Cfun_mono {M : ℝ} (hM : 0 ≤ M) {m n : ℕ} (hmn : m ≤ n) :
    LI_Cfun M m ≤ LI_Cfun M n := by
  show 4 * (1000000 * (M + 1)) ^ m ≤ 4 * (1000000 * (M + 1)) ^ n
  have hR : (1 : ℝ) ≤ 1000000 * (M + 1) := by nlinarith
  have hpow : ∀ k : ℕ, (1 : ℝ) ≤ (1000000 * (M + 1)) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; nlinarith [ih, hR]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  have h2 : (0 : ℝ) ≤ (1000000 * (M + 1)) ^ m := pow_nonneg (by linarith) m
  nlinarith [hpow k, h2]


end Work.FTS.PhiStar.LinvFlat
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.Aux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RadialWAux.Aux2` — differentiation under the integral sign for the `Φ`-kernel, and the tail
tools

* `hasDerivAt_radPhiKernel_aux`, `radPhi_iteratedDeriv_hasDerivAt`: the `HasDerivAt` facts for the
  iterated derivatives of `Φ = radPhi α m c` (the parametric differentiation over the fixed
  interval `(0,1)`).
* `continuousOn_iteratedDeriv_of`, `integrableOn_Ioi_of_le_rpow`: two tools for the tail.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false



set_option autoImplicit false

/-! ### A. Differentiation under the integral sign for the `Φ`-kernel -/







/-! ### B. Tools for the tail -/

/-- `iteratedDeriv j c` is continuous on `(0,∞)` for `j ≤ n`, from `ContDiffOn ℝ n c (Ioi 0)`. -/
lemma continuousOn_iteratedDeriv_of {c : ℝ → ℝ} {n j : ℕ} (hc : ContDiffOn ℝ n c (Set.Ioi 0))
    (hj : j ≤ n) : ContinuousOn (iteratedDeriv j c) (Set.Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin j c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Ioi 0)
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- A continuous function on `(1,∞)` dominated by `C·u^t` with `t < -1` is integrable there. -/
lemma integrableOn_Ioi_of_le_rpow {g : ℝ → ℝ} {C t : ℝ} (ht : t < -1) (hC : 0 ≤ C)
    (hg : ContinuousOn g (Set.Ioi 1)) (hle : ∀ u ∈ Set.Ioi 1, |g u| ≤ C * u ^ t) :
    IntegrableOn g (Set.Ioi 1) := by
  have hdom : IntegrableOn (fun u : ℝ => C * u ^ t) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ht zero_lt_one).const_mul C
  refine Integrable.mono' hdom (hg.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs]
  exact hle u hu

end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.phiKernel_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `phiKernel_hasDerivAt` — differentiation under the integral sign for the `Φ`-kernel

The `Φ`-piece of the rescaled radial Green function is the parametric integral

  `Φ z = ∫ u in (0)..1, c (z * u) * u ^ (Q - 1)`

over the *fixed* interval `(0,1)` (exponent `Q > 0`).  For a source `c` of class `C^14` on
`(0,∞)` whose first `14` derivatives are bounded by `K`, the `k`-th `z`-derivative of the kernel

  `phiKernelAux Q c k z = ∫ u in (0)..1, c^{(k)} (z * u) * u ^ (k + Q - 1)`

is obtained by differentiating under the integral sign, and passing from the `k`-th to the
`(k+1)`-st kernel is precisely the statement proved here:

`HasDerivAt (fun x => ∫ u in (0)..1, c^{(k)}(x*u) * u^(k+Q-1))
  (∫ u in (0)..1, c^{(k+1)}(z*u) * u^(k+1+Q-1)) z`   for `z > 0`, `k + 1 ≤ 14`.

The ingredients are (i) differentiability of `iteratedDeriv k c` on `(0,∞)` with derivative
`iteratedDeriv (k+1) c` (from `ContDiffOn ℝ 14 c (Ioi 0)`), and (ii) domination of the
differentiated integrand by `K u^{k+Q-1}` on `(0,1]` (integrable because `k + Q > 0`), followed
by `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

This is the general-`Q` analogue of the private helper `hasDerivAt_PhiKernel` of
`RadialWAux/PhiPsiGeneralQ.lean`, restated for an arbitrary source `h` and exponent `Q`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-- The `k`-th differentiated kernel of the `Φ`-piece with general exponent `Q > 0`, i.e. the
parametric integral `z ↦ ∫ u in (0)..1, c^{(k)}(z * u) * u^{k + Q - 1}`. -/
private def phiKernelAux (Q : ℝ) (c : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + Q - 1)

/-- On `Ioi 0`, where `c` is `C^14`, the `k`-th iterated derivative of `c` is differentiable as
soon as `k < 14`. -/
private lemma phiAux_differentiableAt_iteratedDeriv {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 14 c (Set.Ioi 0)) {k : ℕ} (hk : k < 14) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (iteratedDeriv k c) y := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_of_lt hk))
      ht).symm
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)

/-- The `Φ`-kernel integrand `u ↦ c^{(k)}(x u) u^{k + Q - 1}` is a.e. strongly measurable on
`(0,1]` for `x > 0`, `k ≤ 14`.  (Measurability only fails at the single point `u = 0`, where `c`
is only known to be `C^14` on `(0,∞)` and where `u^{k+Q-1}` may blow up.) -/
private lemma phiAux_aestronglyMeasurable_kernel {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 14 c (Set.Ioi 0)) {Q : ℝ} {k : ℕ} (hk : k ≤ 14) {x : ℝ} (hx : 0 < x) :
    AEStronglyMeasurable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
  have hw : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  have hmaps : Set.MapsTo (fun u : ℝ => x * u) (Set.Ioo 0 1) (Set.Ioi 0) :=
    fun u hu => mul_pos hx hu.1
  have h1 : ContinuousOn (fun u : ℝ => iteratedDerivWithin k c (Set.Ioi 0) (x * u))
      (Set.Ioo 0 1) :=
    hw.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have h2 : Set.EqOn (fun u : ℝ => iteratedDeriv k c (x * u))
      (fun u : ℝ => iteratedDerivWithin k c (Set.Ioi 0) (x * u)) (Set.Ioo 0 1) := by
    intro u hu
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds (hmaps hu))).of_le (by exact_mod_cast hk))
      (hmaps hu)).symm
  have h3 : ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ioo 0 1) := h1.congr h2
  have h4 : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) + Q - 1)) (Set.Ioo 0 1) :=
    ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl (ne_of_gt hu.1))
  have h5 : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (h3.mul h4).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rwa [show (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
        = (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) from
    (Measure.restrict_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Ioc).symm]

/-- The `Φ`-kernel integrand is integrable on `(0,1]`, dominated by `K u^{k+Q-1}`. -/
private lemma phiAux_integrableOn_kernel {c : ℝ → ℝ} {K Q : ℝ} (hK : 0 ≤ K) (hQ : 0 < Q)
    (hb : Work.FTS.PhiStar.BddDeriv 14 c K) {k : ℕ} (hk : k ≤ 14) {x : ℝ} (hx : 0 < x)
    (hmeas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.Ioc 0 1))) :
    IntegrableOn (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (Set.Ioc 0 1) volume := by
  have hr : (-1 : ℝ) < (k : ℝ) + Q - 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
    linarith
  have hg : Integrable (fun u : ℝ => K * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
    have h1 : IntervalIntegrable (fun u : ℝ => u ^ ((k : ℝ) + Q - 1)) volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' hr
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] at h1
    exact h1.const_mul K
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)]
  exact mul_le_mul_of_nonneg_right (hb k hk (x * u) (mul_pos hx hu0))
    (Real.rpow_nonneg (le_of_lt hu0) _)

/-- Differentiation under the integral sign for the kernel of the `Φ`-piece: passing from the
`k`-th to the `(k+1)`-st kernel multiplies the `u`-weight by `u`. -/
private lemma hasDerivAt_phiKernelAux {Q : ℝ} (hQ : 0 < Q) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 14 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 14 c K) {k : ℕ} (hk : k + 1 ≤ 14) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (phiKernelAux Q c k) (phiKernelAux Q c (k + 1) z) z := by
  have hkle : k ≤ 14 := by omega
  have hklt : k < 14 := by omega
  have hr : (-1 : ℝ) < ((k + 1 : ℕ) : ℝ) + Q - 1 := by
    have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + Q - 1)) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact phiAux_aestronglyMeasurable_kernel hc hkle hx
  have hF_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + Q - 1))
      volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact phiAux_integrableOn_kernel hK hQ hb hkle hz
      (phiAux_aestronglyMeasurable_kernel hc hkle hz)
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (k + 1) c (z * u)
        * u ^ (((k + 1 : ℕ) : ℝ) + Q - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact phiAux_aestronglyMeasurable_kernel hc hk hz
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + Q - 1)‖
        ≤ K * t ^ (((k + 1 : ℕ) : ℝ) + Q - 1) := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) hk (x * t) (mul_pos hx ht0))
      (Real.rpow_nonneg (le_of_lt ht0) _)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t) * t ^ ((k : ℝ) + Q - 1))
        (iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + Q - 1)) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have hxt : 0 < x * t := mul_pos hx ht0
    have hgd : HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c (x * t)) (x * t) := by
      simpa only [iteratedDeriv_succ] using
        (phiAux_differentiableAt_iteratedDeriv hc hklt hxt).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t))
        (iteratedDeriv (k + 1) c (x * t) * t) x := by
      simpa only [Function.comp_def] using hgd.comp x hlin
    have hmul := hcomp.mul_const (t ^ ((k : ℝ) + Q - 1))
    have hexp : (((k + 1 : ℕ) : ℝ) + Q - 1) = ((k : ℝ) + Q - 1) + 1 := by
      push_cast; ring
    rw [hexp]
    refine hmul.congr_deriv ?_
    rw [Real.rpow_add ht0, Real.rpow_one]
    ring
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + Q - 1))
    (F' := fun x u => iteratedDeriv (k + 1) c (x * u)
      * u ^ (((k + 1 : ℕ) : ℝ) + Q - 1))
    (x₀ := z) (s := Set.Ioi 0) (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
    (bound := fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + Q - 1))
    hs hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  exact hmain

theorem phiKernel_hasDerivAt {Q B : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 14 h (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv 14 h B)
    {j : ℕ} (hj : j + 1 ≤ 14) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..1,
        iteratedDeriv j h (x * u) * u ^ ((j : ℝ) + Q - 1))
      (∫ u in (0 : ℝ)..1,
        iteratedDeriv (j + 1) h (z * u) * u ^ (((j + 1 : ℕ) : ℝ) + Q - 1)) z :=
  hasDerivAt_phiKernelAux hQ hB hh hb hj hz

end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.psiKernel_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `psiKernel_hasDerivAt` — differentiation under the integral sign for the outer rescaled kernel

The function considered here is the kernel of the outer rescaled Green piece
`PsiP P c = fun z => ∫_{u > 1} c (z u) u^{-P-1} du` at a derivative level `j`:

  `z ↦ ∫_{u > 1} c^{(j)}(z u) u^{j-P-1} du`.

For `c` of class `C^14` on `(0,∞)` with the first `14` derivatives bounded by `B`, `j + 1 ≤ 14`
and `j + 1 < P` this function is differentiable at every `z > 0` and its derivative is the same
integral one order higher:

  `(d/dz) ∫_{u>1} c^{(j)}(zu) u^{j-P-1} du = ∫_{u>1} c^{(j+1)}(zu) u^{j+1-P-1} du`.

This is the level `j` form of `PsiP_iteratedDeriv` (equivalently of
`radPsiAux_kernel_hasDerivAt`, which is stated at order `22`); the proof is the standard
dominated-convergence argument, with dominating function `B u^{j-P}` on `(Ioi 1)` — integrable
because `j - P < -1`, i.e. precisely the hypothesis `(j : ℝ) + 1 < P`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

/-- On `(0,∞)` a function of class `C^14` has continuous `k`-th iterated derivative for `k ≤ 14`. -/
private lemma contOn_iteratedDeriv_fourteen {c : ℝ → ℝ} (hc : ContDiffOn ℝ 14 c (Set.Ioi 0))
    {k : ℕ} (hk : k ≤ 14) : ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- The `(k+1)`-st iterated derivative is the derivative of the `k`-th one, for a function of
class `C^14`. -/
private lemma hasDerivAt_iteratedDeriv_fourteen {c : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (hc : ContDiffAt ℝ 14 c x) (hk : k < 14) :
    HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k c) x := by
    have h' := hc.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin (m := k)
      (show ((k : ℕ) : WithTop ℕ∞) < ((14 : ℕ) : WithTop ℕ∞) by exact_mod_cast hk)
      (show UniqueDiffOn ℝ (insert x (Set.univ : Set ℝ)) from by
        simpa using (uniqueDiffOn_univ (𝕜 := ℝ) (E := ℝ)))
    rw [differentiableWithinAt_univ] at h'
    simpa using h'
  have h1 : HasDerivAt (iteratedDeriv k c) (deriv (iteratedDeriv k c) x) x := hd.hasDerivAt
  simpa [iteratedDeriv_succ] using h1

theorem psiKernel_hasDerivAt {P B : ℝ} (hB : 0 ≤ B) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 14 h (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv 14 h B)
    {j : ℕ} (hj : j + 1 ≤ 14) (hjP : (j : ℝ) + 1 < P) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x : ℝ => ∫ u in Set.Ioi 1,
        iteratedDeriv j h (x * u) * u ^ ((j : ℝ) - P - 1))
      (∫ u in Set.Ioi 1,
        iteratedDeriv (j + 1) h (z * u) * u ^ (((j + 1 : ℕ) : ℝ) - P - 1)) z := by
  have hkle : j ≤ 14 := by omega
  have hlt : (j : ℝ) - P < -1 := by linarith
  have hlt' : (j : ℝ) - P - 1 < -1 := by linarith
  have hcont_j : ContinuousOn (iteratedDeriv j h) (Set.Ioi 0) :=
    contOn_iteratedDeriv_fourteen hh hkle
  have hcont_j1 : ContinuousOn (iteratedDeriv (j + 1) h) (Set.Ioi 0) :=
    contOn_iteratedDeriv_fourteen hh hj
  have hne : ∀ u ∈ Set.Ioi (1 : ℝ), u ≠ 0 := fun u hu => ne_of_gt (lt_trans zero_lt_one hu)
  have hrpow : ContinuousOn (fun u : ℝ => u ^ ((j : ℝ) - P - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hrpow1 : ContinuousOn (fun u : ℝ => u ^ (((j + 1 : ℕ) : ℝ) - P - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hcomp : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv j h (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_j.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hcomp1 : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv (j + 1) h (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_j1.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 1)) (s := Set.Ioi (0 : ℝ)) (x₀ := z)
    (F := fun x u : ℝ => iteratedDeriv j h (x * u) * u ^ ((j : ℝ) - P - 1))
    (F' := fun x u : ℝ => iteratedDeriv (j + 1) h (x * u)
      * u ^ (((j + 1 : ℕ) : ℝ) - P - 1))
    (bound := fun u : ℝ => B * u ^ ((j : ℝ) - P))
    (isOpen_Ioi.mem_nhds hz)
    (by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ((hcomp x hx).mul hrpow).aestronglyMeasurable measurableSet_Ioi)
    (by
      refine MeasureTheory.Integrable.mono'
        ((integrableOn_Ioi_rpow_of_lt hlt' zero_lt_one).const_mul B)
        (((hcomp z hz).mul hrpow).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : 0 < u := lt_trans zero_lt_one hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu' _)]
      exact mul_le_mul_of_nonneg_right (hb j hkle (z * u) (mul_pos hz hu'))
        (le_of_lt (Real.rpow_pos_of_pos hu' _)))
    (by exact ((hcomp1 z hz).mul hrpow1).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha' _),
        show (((j + 1 : ℕ) : ℝ) - P - 1) = (j : ℝ) - P from by push_cast; ring]
      exact mul_le_mul_of_nonneg_right (hb (j + 1) hj (x * a) (mul_pos hx ha'))
        (le_of_lt (Real.rpow_pos_of_pos ha' _)))
    (by exact (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul B)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      have hid : HasDerivAt (fun y : ℝ => y * a) a x := by
        simpa using (hasDerivAt_id x).mul_const a
      have hca : ContDiffAt ℝ 14 h (x * a) :=
        hh.contDiffAt (isOpen_Ioi.mem_nhds (mul_pos hx ha'))
      have hd := hasDerivAt_iteratedDeriv_fourteen hca (by omega : j < 14)
      have hcomp' := hd.comp x hid
      have hfun : (iteratedDeriv j h ∘ fun y : ℝ => y * a) =
          fun y : ℝ => iteratedDeriv j h (y * a) := rfl
      rw [hfun] at hcomp'
      have hres := hcomp'.mul_const (a ^ ((j : ℝ) - P - 1))
      have hval : ((iteratedDeriv (j + 1) h (x * a) * a) * a ^ ((j : ℝ) - P - 1))
          = iteratedDeriv (j + 1) h (x * a) * a ^ (((j + 1 : ℕ) : ℝ) - P - 1) := by
        rw [show (((j + 1 : ℕ) : ℝ) - P - 1) = 1 + ((j : ℝ) - P - 1) from by push_cast; ring,
          Real.rpow_add ha', Real.rpow_one]
        ring
      rw [hval] at hres
      exact hres)
  exact hmain.2

end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.SmoothAux.Deleg.radPhi_general =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `radPhi_general` — the `z`-derivatives of `radPhi` at an arbitrary order bound

`radPhi α m c = fun z => ∫ u in (0)..1, c (z * u) * u ^ (radQ α m - 1)`.  The sibling module
`RadialWAux/radPhi_iteratedDeriv.lean` proves, for a source `c` that is `C^22` on `(0,∞)` with
`|c^{(j)}| ≤ K` up to order `22`, that

  `(d/dz)^k (radPhi α m c) z = ∫ u in (0)..1, c^{(k)}(z u) u^{k + radQ α m - 1}`  (`k ≤ 22`),

together with the accompanying bound `≤ K/(k + radQ α m)`.

Here the numerical restriction `22` is replaced by an arbitrary order bound `N`, and in addition
the operator identity — that the derivative of the `k`-th iterated derivative of `radPhi` is the
kernel of order `k + 1` — is recorded whenever `k + 1 ≤ N`.

The proof is the verbatim adaptation of the order-`22` argument: differentiability of the `k`-th
iterated derivative of `c` on `(0,∞)` for `k < N` (from `ContDiffOn ℝ N c`), the chain rule and
`iteratedDeriv_succ` for the pointwise `z`-derivative of the integrand, domination of the
differentiated integrand by `K u^{k+1+radQ-1}` (integrable on `(0,1]` since `k + radQ > 0`), and
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.SmoothAux.Deleg

set_option autoImplicit false

/-- The `k`-th differentiated kernel of `radPhi α m c`, i.e. the parametric integral
`z ↦ ∫ u in (0)..1, c^{(k)}(z * u) * u^{k + q - 1}` (`q = radQ α m`).  `radPhi` itself is the
case `k = 0`. -/
private def radPhiKernel (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, iteratedDeriv k c (z * u)
    * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)

/-- On `Ioi 0`, where `c` is `C^N`, the `k`-th iterated derivative of `c` is differentiable as
soon as `k < N`. -/
private lemma differentiableAt_iteratedDeriv {N : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0)) {k : ℕ} (hk : k < N) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (iteratedDeriv k c) y := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_of_lt hk))
      ht).symm
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)

/-- The kernel integrand `u ↦ c^{(k)}(x u) u^{k + q - 1}` is a.e. strongly measurable on `(0,1]`
for `x > 0`, `k ≤ N`.  (Measurability only fails at the single point `u = 0`, where `c` is only
known to be `C^N` on `(0,∞)` and where `u^{k+q-1}` may blow up.) -/
private lemma aestronglyMeasurable_kernel {N : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0)) {q : ℝ} {k : ℕ} (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    AEStronglyMeasurable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
  have hw : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  have hmaps : Set.MapsTo (fun u : ℝ => x * u) (Set.Ioo 0 1) (Set.Ioi 0) :=
    fun u hu => mul_pos hx hu.1
  have h1 : ContinuousOn (fun u : ℝ => iteratedDerivWithin k c (Set.Ioi 0) (x * u))
      (Set.Ioo 0 1) :=
    hw.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have h2 : Set.EqOn (fun u : ℝ => iteratedDeriv k c (x * u))
      (fun u : ℝ => iteratedDerivWithin k c (Set.Ioi 0) (x * u)) (Set.Ioo 0 1) := by
    intro u hu
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds (hmaps hu))).of_le (by exact_mod_cast hk))
      (hmaps hu)).symm
  have h3 : ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ioo 0 1) := h1.congr h2
  have h4 : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) + q - 1)) (Set.Ioo 0 1) :=
    ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl (ne_of_gt hu.1))
  have h5 : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (h3.mul h4).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rwa [show (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
        = (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) from
    (Measure.restrict_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Ioc).symm]

/-- The kernel integrand is integrable on `(0,1]`, dominated by `K u^{k+q-1}`. -/
private lemma integrableOn_kernel {N : ℕ} {c : ℝ → ℝ} {K q : ℝ} (hK : 0 ≤ K) (hq : 0 < q)
    (hb : Work.FTS.PhiStar.BddDeriv N c K) {k : ℕ} (hk : k ≤ N) {x : ℝ} (hx : 0 < x)
    (hmeas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1))) :
    IntegrableOn (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (Set.Ioc 0 1) volume := by
  have hr : (-1 : ℝ) < (k : ℝ) + q - 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
    linarith
  have hg : Integrable (fun u : ℝ => K * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
    have h1 : IntervalIntegrable (fun u : ℝ => u ^ ((k : ℝ) + q - 1)) volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' hr
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] at h1
    exact h1.const_mul K
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)]
  exact mul_le_mul_of_nonneg_right (hb k hk (x * u) (mul_pos hx hu0))
    (Real.rpow_nonneg (le_of_lt hu0) _)

/-- Differentiation under the integral sign for the kernel of `radPhi`: passing from the `k`-th to
the `(k+1)`-st kernel multiplies the `u`-weight by `u`. -/
private lemma hasDerivAt_radPhiKernel {α : ℝ} (hα : 0 < α) (m : ℕ) {N : ℕ} {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) {k : ℕ} (hk : k + 1 ≤ N) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (radPhiKernel α m c k) (radPhiKernel α m c (k + 1) z) z := by
  have hq : 0 < Work.FTS.PhiStar.RadialWAux.radQ α m :=
    Work.FTS.PhiStar.RadialWAux.radQ_pos hα m
  have hkle : k ≤ N := by omega
  have hklt : k < N := by omega
  have hr : (-1 : ℝ) < ((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1 := by
    have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u)
        * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact aestronglyMeasurable_kernel hc hkle hx
  have hF_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u)
        * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact integrableOn_kernel hK hq hb hkle hz (aestronglyMeasurable_kernel hc hkle hz)
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (k + 1) c (z * u)
        * u ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact aestronglyMeasurable_kernel hc hk hz
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖iteratedDeriv (k + 1) c (x * t)
          * t ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)‖
        ≤ K * t ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) hk (x * t) (mul_pos hx ht0))
      (Real.rpow_nonneg (le_of_lt ht0) _)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t)
          * t ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
        (iteratedDeriv (k + 1) c (x * t)
          * t ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have hxt : 0 < x * t := mul_pos hx ht0
    have hgd : HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c (x * t)) (x * t) := by
      simpa only [iteratedDeriv_succ] using
        (differentiableAt_iteratedDeriv hc hklt hxt).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t))
        (iteratedDeriv (k + 1) c (x * t) * t) x := by
      simpa only [Function.comp_def] using hgd.comp x hlin
    have hmul := hcomp.mul_const (t ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
    have hexp : (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
        = ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) + 1 := by
      push_cast; ring
    rw [hexp]
    refine hmul.congr_deriv ?_
    rw [Real.rpow_add ht0, Real.rpow_one]
    ring
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => iteratedDeriv k c (x * u)
      * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
    (F' := fun x u => iteratedDeriv (k + 1) c (x * u)
      * u ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
    (x₀ := z) (s := Set.Ioi 0) (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
    (bound := fun u : ℝ =>
      K * u ^ (((k + 1 : ℕ) : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
    hs hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  exact hmain

/-- `iteratedDeriv k (radPhi α m c)` is the `k`-th kernel, for every `k ≤ N`. -/
private lemma iteratedDeriv_radPhi_eq_kernel {α : ℝ} (hα : 0 < α) (m : ℕ) {N : ℕ} {c : ℝ → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) :
    ∀ k : ℕ, k ≤ N → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z = radPhiKernel α m c k z := by
  intro k
  induction k with
  | zero =>
    intro _ z _
    simp only [radPhiKernel, Work.FTS.PhiStar.RadialWAux.radPhi, iteratedDeriv_zero,
      Nat.cast_zero, zero_add]
  | succ n ih =>
    intro hn z hz
    have hnle : n ≤ N := by omega
    have h1 : deriv (iteratedDeriv n (Work.FTS.PhiStar.RadialWAux.radPhi α m c)) z
        = deriv (radPhiKernel α m c n) z := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih hnle y hy
    have h2 : deriv (radPhiKernel α m c n) z = radPhiKernel α m c (n + 1) z :=
      (hasDerivAt_radPhiKernel hα m hK hc hb hn hz).deriv
    rw [iteratedDeriv_succ, h1, h2]

theorem radPhi_general {α : ℝ} (hα : 0 < α) (m : ℕ) (N : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) :
    ∀ k : ℕ, k ≤ N → ∀ z : ℝ, 0 < z →
      (iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z
          = ∫ u in (0 : ℝ)..1, iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      ∧ |iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z|
          ≤ K / ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m)
      ∧ (k + 1 ≤ N → HasDerivAt (iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c))
          (∫ u in (0 : ℝ)..1, iteratedDeriv (k + 1) c (z * u)
              * u ^ ((k : ℝ) + 1 + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) z) := by
  have hq : 0 < Work.FTS.PhiStar.RadialWAux.radQ α m :=
    Work.FTS.PhiStar.RadialWAux.radQ_pos hα m
  intro k hk z hz
  refine ⟨?_, ?_, ?_⟩
  · rw [iteratedDeriv_radPhi_eq_kernel hα m hK hc hb k hk z hz]
    rfl
  · -- the bound `K / (k + q)`
    have hkq : 0 < (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m := by
      have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
      linarith
    have hr : (-1 : ℝ) < (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1 := by linarith
    have hab : (0 : ℝ) ≤ 1 := by norm_num
    have hg_int : IntervalIntegrable
        (fun u : ℝ => iteratedDeriv k c (z * u)
          * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
        volume (0 : ℝ) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      exact integrableOn_kernel hK hq hb hk hz (aestronglyMeasurable_kernel hc hk hz)
    have hK_int : IntervalIntegrable
        (fun u : ℝ => K * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
        volume (0 : ℝ) 1 :=
      (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
    have hae : ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        |iteratedDeriv k c (z * u)
            * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|
          ≤ K * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) := by
      rw [show (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
          = (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) from
        (Measure.restrict_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Icc).symm]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hu0 : 0 < u := hu.1
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      exact mul_le_mul_of_nonneg_right (hb k hk (z * u) (mul_pos hz hu0))
        (Real.rpow_nonneg hu0.le _)
    have h1 : |iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z|
        ≤ ∫ u in (0 : ℝ)..1,
            |iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)| := by
      rw [iteratedDeriv_radPhi_eq_kernel hα m hK hc hb k hk z hz]
      exact intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ u in (0 : ℝ)..1,
          |iteratedDeriv k c (z * u)
            * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|)
        ≤ ∫ u in (0 : ℝ)..1, K * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) :=
      intervalIntegral.integral_mono_ae_restrict hab hg_int.abs hK_int hae
    have h3 : (∫ u in (0 : ℝ)..1, K * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
        = K / ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr), Real.one_rpow,
        Real.zero_rpow (by linarith : (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1 + 1 ≠ 0),
        sub_zero,
        show (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1 + 1
          = (k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m from by ring]
      ring
    linarith
  · -- the derivative identity
    intro hk1
    have hder : HasDerivAt (radPhiKernel α m c k) (radPhiKernel α m c (k + 1) z) z :=
      hasDerivAt_radPhiKernel hα m hK hc hb hk1 hz
    have hev : (iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c))
        =ᶠ[𝓝 z] radPhiKernel α m c k := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact iteratedDeriv_radPhi_eq_kernel hα m hK hc hb k (by omega) y hy
    have hfin := hder.congr_of_eventuallyEq hev
    simpa only [radPhiKernel, Nat.cast_add, Nat.cast_one] using hfin

end Work.FTS.PhiStar.Series.SmoothAux.Deleg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.SmoothAux.remSource_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `remSource_facts` — the `hInt` hypothesis bundle of the mode-series differentiation

The termwise differentiation of the mode series `psiSeries α (RemSource α ψ)` needs the
bundle `hInt`:

* `t ↦ cmode m (RemSource α ψ) t` continuous on `Ioi 0`;
* `t ↦ cmode m (RemSource α ψ) t · t^((2m+5)/α − 1)` integrable on `Ioo 0 1`;
* `t ↦ cmode m (RemSource α ψ) t · t^(−2m/α − 1)` integrable on `Ioi 1`;

together with the same three statements for the radial profile `𝒜φ = VocabO.phiA α`.

`RemSource α ψ z θ = α²·(𝒜φ)(z)·ψ(θ)` is separable in `z`, and `Series/RemSetup.lean` gives

  `cmode m (RemSource α ψ) t = α²·(𝒜φ)(t)·bmode m ψ`   (`cmode_RemSource`),

so each `cmode`-conjunct is a scalar multiple of the corresponding `phiA`-conjunct and all the
content is in the three analytic facts about `𝒜φ`, proved in
`Series/Deleg/psiSeriesIntegrability.lean` from the explicit form
`𝒜φ(z) = 4αz²(z−2)/(1+z)⁴ + 2(5+α)z(1−z)/(1+z)³` (`z ≠ −1`):

* `𝒜φ` is rational with its only pole at `z = −1`, hence continuous on `Ioi 0`;
* `|𝒜φ(t)| ≤ (10α+10)·t` on `(0,1)` and `|𝒜φ(t)| ≤ (14α+10)/t` on `(1,∞)`, so the integrands
  are dominated by `(10α+10)·t^{(2m+5)/α}` and `(14α+10)·t^{−2m/α−2}`, integrable because
  `(2m+5)/α > −1` and `−2m/α − 2 < −1` (here `α > 0`, `m ≥ 0`).
-/

namespace Work.FTS.PhiStar.Series.SmoothAux


end Work.FTS.PhiStar.Series.SmoothAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.linv23_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar


end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.C1JetFstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false

namespace Work.FTS.RegPkgGal.Der

open Work.FTS.Regularity

/-! ## The `z`-derivative of the static profile slice -/

/-- The `z`-derivative of the slice `z' ↦ F_*(z',θ)` of the static profile: the profile factors as
`(p·(Γ(θ)/c(p)))·F_*(z')` with a `z`-independent coefficient, so its `z`-derivative is the
coefficient times `deriv F_*`. -/
theorem pz_Fstar_eq (p z θ : ℝ) :
    Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * deriv Work.FM.Fstar z := by
  change deriv (fun z' => Work.Construction.Fstar p z' θ) z = _
  have hfun : (fun z' => Work.Construction.Fstar p z' θ)
      = fun z' => (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * Work.FM.Fstar z' := by
    funext z'; simp only [Work.Construction.Fstar]
  rw [hfun, deriv_const_mul_field]

/-- The uniform `z`-derivative box of the static profile: `|∂_zF_*(z,θ)| ≤ 20·pExp α` for
`z ≥ 0` and `θ ∈ Iθ` (this is `Work.FTS.Regularity.fstarDz_abs_le`, transported across the
definitional unfolding of `pz`). -/
theorem pz_Fstar_pExp_abs_le {α z θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ| ≤ 20 * pExp α := by
  rw [pz_Fstar_eq]
  exact Work.FTS.Regularity.fstarDz_abs_le hα hα13 hz hθ

/-! ## The target -/

theorem C1JetFstar {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have hN : 0 ≤ 100 + 20 * pExp α := by linarith
  refine ⟨⟨hN, ?_, ?_⟩, ?_⟩
  · -- the uniform (`C⁰`) bound: `|F_*| ≤ 20Γ ≤ 20`
    intro z θ τ hz hθ _hτ
    calc |Work.Construction.Fstar (pExp α) z θ|
        ≤ 20 * Work.FTS.Regularity.Gamma α θ :=
          Work.FTS.Regularity.fstar_abs_le_gamma hα hα13 hz hθ
      _ ≤ 20 * 1 :=
          mul_le_mul_of_nonneg_left (Work.ConstructionInstance.Gamma_le_one hα.le hθ)
            (by norm_num)
      _ ≤ 100 + 20 * pExp α := by linarith
  · -- the joint `α`-Hölder modulus for the metric `|Δz| + |Δθ| + |Δτ|`
    intro z z' θ θ' τ τ' hz hz' hθ hθ' _hτ _hτ'
    have hD : 0 ≤ |z - z'| + |θ - θ'| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hD' : 0 ≤ |z - z'| + |θ - θ'| + |τ - τ'| :=
      add_nonneg hD (abs_nonneg _)
    have hmono : (|z - z'| + |θ - θ'|) ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow hD (le_add_of_nonneg_right (abs_nonneg _)) hα.le
    calc |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ'|
        ≤ 100 * (|z - z'| + |θ - θ'|) ^ α :=
          Work.FTS.Regularity.fstar_joint_modulus hα hα13 hz hz' hθ hθ'
      _ ≤ 100 * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ ≤ (100 + 20 * pExp α) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hD' α)
  · -- the `z`-derivative box on `z > 0`
    intro τ _hτ θ hθ z hz
    have hz0 : 0 < z := hz
    refine ⟨Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ,
      Work.ConstructionInstance.hasDerivAt_Fstar_z (p := pExp α) z θ (by linarith), ?_⟩
    calc |Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ| ≤ 20 * pExp α :=
          pz_Fstar_pExp_abs_le hα hα13 hz0.le hθ
      _ ≤ 100 + 20 * pExp α := by linarith

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.jet_L12f =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## The assembly -/

theorem jet_L12f {α S : ℝ} {F : ℝ → ℝ → ℝ → ℝ} {N Kl Lf Nt : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |F z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → F z θ τ = 0)
    (htau : 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ici (0:ℝ), |F z θ τ - F z θ τ'| ≤ Nt * z * |τ - τ'| ^ α) :
    ∃ N' : ℝ, Work.FTS.Regularity.Jet α S N'
      (fun z θ τ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z) := by
  have hN0 : 0 ≤ N := hJ.1
  have hKl0 : 0 ≤ Kl := hlin.1
  have hLfpos : 0 < Lf := hsupp.1
  have hNt0 : 0 ≤ Nt := htau.1
  let v : ℝ → ℝ → ℝ :=
    fun τ s => Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s
  obtain ⟨hDensLe, hDensZero⟩ :=
    L12fDensBound (α := α) (S := S) (N := N) (Kl := Kl) (Lf := Lf) hJ hlin hsupp
  have hDensDif : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ s : ℝ, 0 < s →
      |v τ s - v τ' s| ≤ 6 * Nt * |τ - τ'| ^ α :=
    L12fDensDiff (α := α) (S := S) (N := N) (Nt := Nt) hα hJ htau
  have hInt0 : ∀ τ ∈ Set.Icc 0 S, MeasureTheory.IntegrableOn (v τ) (Set.Ioi 0) :=
    fun τ hτ => (L12fDensContInt (α := α) (S := S) (N := N) (Kl := Kl) (Lf := Lf)
      hα hJ hlin hsupp τ hτ).2
  have hCden0 : 0 ≤ 6 * max Kl N := by
    have h1 : (0:ℝ) ≤ max Kl N := le_trans hN0 (le_max_right Kl N)
    linarith
  have hM0 : 0 ≤ (6 * max Kl N) * Lf := mul_nonneg hCden0 hLfpos.le
  have hCt0 : 0 ≤ (6 * Nt) * Lf := mul_nonneg (by linarith) hLfpos.le
  -- the tail integral is supported in `(z, Lf]`
  have htail : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        = ∫ s in Set.Ioc z Lf, v τ s := by
    intro τ hτ z
    have h1 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        = ∫ s in Set.Ioi z, v τ s := rfl
    rw [h1]
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self (fun x hx => ?_)
    have hxgt : Lf < x := by
      by_contra hcon
      exact hx.2 ⟨hx.1, le_of_not_gt hcon⟩
    exact hDensZero τ hτ x hxgt.le
  -- the `z`-Lipschitz bound (monotone case)
  have hzlip_le : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → z ≤ z' →
      |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'|
      ≤ (6 * max Kl N) * |z' - z| := by
    intro τ hτ z z' hz hzz
    have hI1 : MeasureTheory.IntegrableOn (v τ) (Set.Ioi z') :=
      (hInt0 τ hτ).mono_set (Set.Ioi_subset_Ioi (le_trans hz hzz))
    have hI2 : MeasureTheory.IntegrableOn (v τ) (Set.Ioc z z') :=
      (hInt0 τ hτ).mono_set (fun x hx => lt_of_le_of_lt hz hx.1)
    have hU : Set.Ioi z = Set.Ioi z' ∪ Set.Ioc z z' := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        rcases lt_or_ge z' x with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | h)
        · exact lt_of_le_of_lt hzz h
        · exact h.1
    have hsplit : (∫ s in Set.Ioi z, v τ s)
        = (∫ s in Set.Ioi z', v τ s) + ∫ s in Set.Ioc z z', v τ s := by
      rw [hU]
      exact MeasureTheory.setIntegral_union
        (Set.disjoint_left.mpr (fun a ha ha' => absurd ha (not_lt.mpr ha'.2)))
        measurableSet_Ioc hI1 hI2
    have hdiff : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'
        = ∫ s in Set.Ioc z z', v τ s := by
      have e1 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          = ∫ s in Set.Ioi z, v τ s := rfl
      have e2 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'
          = ∫ s in Set.Ioi z', v τ s := rfl
      rw [e1, e2, hsplit]
      ring
    rw [hdiff]
    have hb : |∫ s in Set.Ioc z z', v τ s| ≤ (6 * max Kl N) * |z' - z| := by
      rw [show (∫ s in Set.Ioc z z', v τ s) = ∫ s in z..z', v τ s from
        (intervalIntegral.integral_of_le hzz).symm]
      exact intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s : ℝ => v τ s)
        (a := z) (b := z') (C := 6 * max Kl N) (by
          intro x hx
          rw [uIoc_of_le hzz] at hx
          have hxpos : 0 < x := lt_of_le_of_lt hz hx.1
          exact hDensLe τ hτ x hxpos)
    exact hb
  -- the `z`-Lipschitz bound (general case)
  have hzlip : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'|
      ≤ (6 * max Kl N) * |z - z'| := by
    intro τ hτ z z' hz hz'
    rcases le_total z z' with h | h
    · have hthis := hzlip_le τ hτ z z' hz h
      rw [abs_sub_comm z' z] at hthis
      exact hthis
    · have hthis := hzlip_le τ hτ z' z hz' h
      rw [abs_sub_comm (Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z')
        (Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z)] at hthis
      exact hthis
  -- the `τ`-Hölder bound
  have hthold : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z|
      ≤ (6 * Nt * Lf) * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ' z hz
    have h1 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z
        = ∫ s in Set.Ioi z, (v τ s - v τ' s) := by
      have e1 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          = ∫ s in Set.Ioi z, v τ s := rfl
      have e2 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z
          = ∫ s in Set.Ioi z, v τ' s := rfl
      rw [e1, e2]
      exact (MeasureTheory.integral_sub
        ((hInt0 τ hτ).mono_set (Set.Ioi_subset_Ioi hz))
        ((hInt0 τ' hτ').mono_set (Set.Ioi_subset_Ioi hz))).symm
    rw [h1]
    have h2 : (∫ s in Set.Ioi z, (v τ s - v τ' s))
        = ∫ s in Set.Ioc z Lf, (v τ s - v τ' s) := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Set.Ioc_subset_Ioi_self (fun x hx => ?_)
      have hxgt : Lf < x := by
        by_contra hcon
        exact hx.2 ⟨hx.1, le_of_not_gt hcon⟩
      have e1 : v τ x = 0 := hDensZero τ hτ x hxgt.le
      have e2 : v τ' x = 0 := hDensZero τ' hτ' x hxgt.le
      rw [e1, e2, sub_zero]
    rw [h2]
    have hb : |∫ s in Set.Ioc z Lf, (v τ s - v τ' s)|
        ≤ (6 * Nt * |τ - τ'| ^ α) * MeasureTheory.volume.real (Set.Ioc z Lf) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (s := Set.Ioc z Lf) (f := fun s : ℝ => v τ s - v τ' s)
        (C := 6 * Nt * |τ - τ'| ^ α)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        (fun x hx => by
          have hxpos : 0 < x := lt_of_le_of_lt hz hx.1
          exact hDensDif τ hτ τ' hτ' x hxpos)
    have hLfm : MeasureTheory.volume.real (Set.Ioc z Lf) ≤ Lf := by
      rw [Real.volume_real_Ioc]
      exact max_le (by linarith) hLfpos.le
    have hnn : (0:ℝ) ≤ 6 * Nt * |τ - τ'| ^ α :=
      mul_nonneg (mul_nonneg (by norm_num) hNt0) (Real.rpow_nonneg (abs_nonneg _) α)
    calc |∫ s in Set.Ioc z Lf, (v τ s - v τ' s)|
        ≤ (6 * Nt * |τ - τ'| ^ α) * MeasureTheory.volume.real (Set.Ioc z Lf) := hb
      _ ≤ (6 * Nt * |τ - τ'| ^ α) * Lf := mul_le_mul_of_nonneg_left hLfm hnn
      _ = (6 * Nt * Lf) * |τ - τ'| ^ α := by ring
  -- the pointwise bound
  have hbound : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z| ≤ (6 * max Kl N) * Lf := by
    intro τ hτ z hz
    rw [htail τ hτ z]
    have hb : |∫ s in Set.Ioc z Lf, v τ s|
        ≤ (6 * max Kl N) * MeasureTheory.volume.real (Set.Ioc z Lf) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (s := Set.Ioc z Lf) (f := fun s : ℝ => v τ s) (C := 6 * max Kl N)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        (fun x hx => by
          have hxpos : 0 < x := lt_of_le_of_lt hz hx.1
          exact hDensLe τ hτ x hxpos)
    have hLfm : MeasureTheory.volume.real (Set.Ioc z Lf) ≤ Lf := by
      rw [Real.volume_real_Ioc]
      exact max_le (by linarith) hLfpos.le
    calc |∫ s in Set.Ioc z Lf, v τ s|
        ≤ (6 * max Kl N) * MeasureTheory.volume.real (Set.Ioc z Lf) := hb
      _ ≤ (6 * max Kl N) * Lf := mul_le_mul_of_nonneg_left hLfm hCden0
  refine ⟨max 0 (max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) + (6 * Nt * Lf)), ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · intro z θ τ hz hθ hτ
    have h1 : (6 * max Kl N) * Lf ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) :=
      le_trans (le_mul_of_one_le_left hM0 (by norm_num)) (le_max_right _ _)
    have h2 : max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf))
        ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) + (6 * Nt * Lf) :=
      le_add_of_nonneg_right hCt0
    refine le_trans (hbound τ hτ z hz) ?_
    refine le_trans h1 ?_
    refine le_trans h2 ?_
    exact le_max_right _ _
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    set D := |z - z'| + |θ - θ'| + |τ - τ'| with hDdef
    have hD0 : 0 ≤ D := by rw [hDdef]; positivity
    have hzD : |z - z'| ^ α ≤ D ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by rw [hDdef]; linarith [abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]) hα.le
    have htD : |τ - τ'| ^ α ≤ D ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by rw [hDdef]; linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ')]) hα.le
    have h1 : |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'|
        ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * |z - z'| ^ α :=
      Lib.holder_of_lipschitz_of_bounded hα hα1 hCden0 hM0 (hzlip τ hτ) (hbound τ hτ) z z' hz hz'
    have h2 : |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z'|
        ≤ (6 * Nt * Lf) * |τ - τ'| ^ α := hthold τ hτ τ' hτ' z' hz'
    have hsplit : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z'
        = (Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
            - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z')
          + (Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'
            - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z') := by ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add h1 h2) ?_
    have hA0 : 0 ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) :=
      le_trans hCden0 (le_max_left _ _)
    have hsum : max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * |z - z'| ^ α
          + (6 * Nt * Lf) * |τ - τ'| ^ α
        ≤ (max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) + (6 * Nt * Lf)) * D ^ α := by
      have h3 : max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * |z - z'| ^ α
          ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * D ^ α :=
        mul_le_mul_of_nonneg_left hzD hA0
      have h4 : (6 * Nt * Lf) * |τ - τ'| ^ α ≤ (6 * Nt * Lf) * D ^ α :=
        mul_le_mul_of_nonneg_left htD hCt0
      have h5 : (max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) + (6 * Nt * Lf)) * D ^ α
          = max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * D ^ α
            + (6 * Nt * Lf) * D ^ α := by ring
      linarith [h3, h4, h5]
    refine le_trans hsum ?_
    refine mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hD0 α)

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.rhs_zderiv_of_parts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

set_option maxHeartbeats 1600000

theorem rhs_zderiv_of_parts {α S : ℝ} {g Φ : Work.FTS.RegPkgGal.Fam} {N₁ N₂ N₃ N₄ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hL : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => -(Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z' θ)) d z ∧ |d| ≤ N₁)
    (hN₀ : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ N₂)
    (hN : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z' θ) d z ∧ |d| ≤ N₃)
    (hNs : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ N₄)
    (hmb : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |Work.Construction.mubar
        (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice g τ))
        (Work.Construction.N (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ))| ≤ M) :
    ∃ Nc : ℝ, 0 ≤ Nc ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z' θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z' θ) d z ∧ |d| ≤ Nc := by
  obtain ⟨M, hM0, hM⟩ := hmb
  have ha : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have ha1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  refine ⟨|N₁| + |N₂| + |N₃| + |N₄| + 20 * M, by positivity, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d₁, hd₁, hb₁⟩ := hL τ hτ θ hθ z hz
  obtain ⟨d₂, hd₂, hb₂⟩ := hN₀ τ hτ θ hθ z hz
  obtain ⟨d₃, hd₃, hb₃⟩ := hN τ hτ θ hθ z hz
  obtain ⟨d₄, hd₄, hb₄⟩ := hNs τ hτ θ hθ z hz
  obtain ⟨dA, hdA, hbA⟩ := ak_hasDerivAt_bound ha ha1 hθ hz
  set c : ℝ := Work.Construction.mubar
      (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ))
      (Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) with hcdef
  have hcM : |c| ≤ M := by rw [hcdef]; exact hM τ hτ
  have hslice : Work.FTS.Galerkin.slice g τ = Work.FTS.Regularity.gSlice g τ := rfl
  have hdec : ∀ z' : ℝ, Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z' θ
      = (-c) * Work.Construction.AK (Work.FTS.Regularity.pExp α) z' θ
        + Work.Construction.N0 (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
            (Work.FTS.Regularity.gSlice g τ) z' θ
        + Work.Construction.N (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
            (Work.FTS.Regularity.gSlice Φ τ) z' θ
        + Work.Construction.Nstar (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
            (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
            (Work.FTS.Regularity.gSlice g τ) z' θ := by
    intro z'
    rw [hcdef]
    rfl
  refine ⟨d₁ + ((-c) * dA + d₂ + d₃ + d₄), ?_, ?_⟩
  · have e2 : HasDerivAt (fun z' => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d₂ z := hd₂
    have e3 : HasDerivAt (fun z' => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z' θ) d₃ z := hd₃
    have e4 : HasDerivAt (fun z' => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d₄ z := hd₄
    have e5 : HasDerivAt (fun z' => (-c) * Work.Construction.AK (Work.FTS.Regularity.pExp α) z' θ)
        ((-c) * dA) z := hdA.const_mul (-c)
    have hall := hd₁.add (((e5.add e2).add e3).add e4)
    convert hall using 1
    · funext z'
      simp only [Pi.add_apply, Work.FTS.Galerkin.dynLin, hslice, hdec z']
  · have h1 : |d₁| ≤ |N₁| := le_trans hb₁ (le_abs_self N₁)
    have h2 : |d₂| ≤ |N₂| := le_trans hb₂ (le_abs_self N₂)
    have h3 : |d₃| ≤ |N₃| := le_trans hb₃ (le_abs_self N₃)
    have h4 : |d₄| ≤ |N₄| := le_trans hb₄ (le_abs_self N₄)
    have hmul : |(-c) * dA| ≤ 20 * M := by
      rw [abs_mul, abs_neg]
      calc |c| * |dA| ≤ M * 20 := mul_le_mul hcM hbA (abs_nonneg _) hM0
        _ = 20 * M := by ring
    have ht1 := abs_add_le ((-c) * dA) d₂
    have ht2 := abs_add_le (((-c) * dA) + d₂) d₃
    have ht3 := abs_add_le ((((-c) * dA) + d₂) + d₃) d₄
    have ht0 := abs_add_le d₁ (((((-c) * dA) + d₂) + d₃) + d₄)
    linarith [abs_nonneg d₁, abs_nonneg d₂, abs_nonneg d₃, abs_nonneg d₄,
      abs_nonneg ((-c) * dA), ht0, ht1, ht2, ht3, h1, h2, h3, h4, hmul]

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.sup2_extG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The support, the calculus and the pointwise trade-off -/

/-- **Congruence of `∂_z²` between the extension slice and the slice of `g`.**  For `τ ≥ 0` the
two functions `z' ↦ extG g z' θ τ` and `z' ↦ g z' θ τ` agree on the open half line `Ioi 0`
(`extG_of_pos`), and `pz` is a local operator, so their second `z`-derivatives agree at every
`z > 0`. -/
private lemma pz_pz_extG_eq {g : Work.FTS.RegPkgGal.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z) :
    Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hagree : EqOn (Function.uncurry (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
      (Function.uncurry (fun z θ => g z θ τ)) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rintro ⟨z', θ'⟩ ⟨hz', -⟩
    exact Work.FTS.RegPkgGal.extG_of_pos hz' hτ
  have h1 : EqOn (Function.uncurry (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)))
      (Function.uncurry (Work.Spaces.pz (fun z θ => g z θ τ)))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    intro y hy
    exact Work.Spaces.pz_congr_of_isOpen hV hagree hy
  exact Work.Spaces.pz_congr_of_isOpen hV h1 ⟨hz, trivial⟩

/-- **The bridge `D_z² = D_z + z²∂_z²`.**  If the `z`-slice of `pz F` is differentiable at `z`,
then `D_z²F = D_zF + z²∂_z²F` at `(z,θ)`.  (This is the `n = 2` case of the expansion of
`D_z = z∂_z` in terms of `z^k∂_z^k`, with Stirling coefficients `S(2,1) = S(2,2) = 1`; only the
product rule is needed, so no smoothness of higher order is required.) -/
private lemma DzIter_two_eq_add (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z) :
    Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
  have hdmul : deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
    have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id' z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz F z' θ)
        (Work.Spaces.pz (Work.Spaces.pz F) z θ) z := hd.hasDerivAt
    have h3 : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz F z' θ)
        (1 * Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ) z :=
      (h1.mul h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext z'; rfl))
    simpa only [one_mul] using h3.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = z * Work.Spaces.pz F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ
  rw [hdmul]
  ring



/-! ## The target -/


end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.sup_extG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R1b.extG_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.R1b.extG_cont`

The joint `C¹`-gluing of the extension `g̃ = extG g` across `z = 0` and across `τ = 0`,
under *uniform* (joint in `(z,τ)`) hypotheses on `g` near `z = 0`.

The hypotheses ask for the limits as `(z,τ) → (0,τ₀)` **within `z > 0`**, i.e. they are uniform
in `τ`; that uniformity is exactly what makes the corner `(z,τ) = (0,0)` of the piecewise
definition tame.  (The earlier `R1` version of the statement, with only ray-wise limits, is
false — see `Submission/Work/FTS/RegPkgGal/R1/NOTES_extG_cont_FALSE.md`.)

## Proof outline

For fixed `θ` let `baseFn g θ (z,τ) = g z θ τ`, `tauDer g θ z = deriv (fun s => g z θ s) 0`
and `jetFn g θ (z,τ) = g z θ 0 + τ * tauDer g θ z` (the `τ < 0` branch of `extG`).  Then
`extG g z θ τ` is `0` for `z ≤ 0`, `jetFn` for `z > 0, τ < 0` and `baseFn` for `z > 0, τ ≥ 0`.
Both branches are `C¹` on `z > 0`, and the candidate derivative `extDeriv g θ` is the nested
piecewise combination of their partial derivatives.  The two joins are:

* `τ = 0`, `z > 0`: `jetFn` and `baseFn` have the *same* Fréchet derivative there, since at
  `τ = 0` the jet is the first-order Taylor expansion of `baseFn` in `τ`
  (`fderiv_jetFn_eq_fderiv_baseFn`, `jetBranch_eq_baseBranch_at_zero`);
* `z = 0`: the joint limits `g = o(z)`, `∂_zg → 0`, `∂_τg → 0`, `∂_τg(·,0) = o(z)` and
  `∂_z(∂_τg(·,0)) → 0` identify the derivative as `0` there, and give the continuity of
  `extDeriv` at `(0,τ₀)`.

The gluing itself is `hasFDerivAt_of_union`, and everything is assembled with
`contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn`.

## Layout

The supporting material lives in the sibling modules of this directory:
`General` (elementary analysis helpers), `Locals` (the local objects and their basic
rewriting lemmas) and `C1Facts` (smoothness of the two branches, their Fréchet derivatives,
the `τ = 0` join and the continuity of the branch functions).
-/

namespace Work.FTS.RegPkgGal.R1b

open Set Filter Topology MeasureTheory
open scoped Topology Real ContDiff

set_option autoImplicit false

theorem extG_cont {S : ℝ} (hS : 0 < S) {g : ℝ → ℝ → ℝ → ℝ}
    (hbase : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1))))
    (hj0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ioo (-1) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => g p.1 θ p.2)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hjz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ioo (-1) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * g p.1 θ p.2)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hjdz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ioo (-1) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => g z θ p.2) p.1)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hjdt : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ioo (-1) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => g p.1 θ s) p.2)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hd1 : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => deriv (fun s => g q.1 θ s) 0)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1))))
    (hd1z : ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => g z θ s) 0) p.1)
        (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hd1z2 : ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
        (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (ht0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun τ => deriv (fun s => g z θ s) τ)
        (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => g z θ s) 0))) :
    ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
      (Set.prod (Set.Ioi (-1)) (Set.Ioo (-1) (S + 1))) := by
  intro θ hθ
  change ContDiffOn ℝ 1 (extFun g θ) (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1))
  have hUopen : IsOpen (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)) := isOpen_Ioi.prod isOpen_Ioo
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hbaseV : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := hbase θ hθ
  have hddV : ContDiffOn ℝ 1 (tauDerFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := hd1 θ hθ
  have hjetV : ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    jetFn_contDiffOn hbaseV hddV
  have hτV : ContDiffOn ℝ 1 (tauDer g θ) (Ioi (0:ℝ)) := tauDer_contDiffOn hddV
  have hbaseAt : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)),
      HasFDerivAt (baseFn g θ) (fderiv ℝ (baseFn g θ) x) x :=
    fun x hx => hasFDerivAt_of_contDiffOn_one hVopen hbaseV hx
  have hjetAt : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)),
      HasFDerivAt (jetFn g θ) (fderiv ℝ (jetFn g θ) x) x :=
    fun x hx => hasFDerivAt_of_contDiffOn_one hVopen hjetV hx
  have hbasediff : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)), DifferentiableAt ℝ (baseFn g θ) x :=
    fun x hx => (hbaseAt x hx).differentiableAt
  have hjetdiff : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)), DifferentiableAt ℝ (jetFn g θ) x :=
    fun x hx => (hjetAt x hx).differentiableAt
  have hτdiff : ∀ z ∈ Ioi (0:ℝ), DifferentiableAt ℝ (tauDer g θ) z :=
    fun z hz => (hτV.differentiableOn one_ne_zero z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hz0diff : ∀ z ∈ Ioi (0:ℝ), DifferentiableAt ℝ (fun z' => g z' θ 0) z := by
    intro z hz
    have hzc : DifferentiableAt ℝ (fun z' : ℝ => (z', (0:ℝ))) z := by fun_prop
    have hbd : DifferentiableAt ℝ (baseFn g θ) (z, (0:ℝ)) := hbasediff (z, 0) ⟨hz, by norm_num⟩
    have hcomp := hbd.comp z hzc
    simpa [Function.comp_def, baseFn] using hcomp
  have hAcont : ContinuousOn (jetBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    continuousOn_jetBranch hjetV
  have hBcont : ContinuousOn (baseBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    continuousOn_baseBranch hbaseV
  have h0mem : (0:ℝ) ∈ Ioo (-1:ℝ) (S + 1) := ⟨by norm_num, by linarith⟩
  -- ## Step 1: differentiability with derivative `extDeriv`
  have hderiv : ∀ x ∈ (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)),
      HasFDerivAt (extFun g θ) (extDeriv g θ x) x := by
    rintro ⟨z, τ⟩ hxU
    have hτU : τ ∈ Ioo (-1:ℝ) (S + 1) := hxU.2
    rcases lt_trichotomy z 0 with hz | hz | hz
    · -- `z < 0`: the extension vanishes identically nearby
      have hxd : extDeriv g θ (z, τ) = 0 := extDeriv_of_nonpos g θ (le_of_lt hz) τ
      rw [hxd]
      refine (hasFDerivAt_const (c := (0:ℝ)) (x := ((z, τ) : ℝ × ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds hz] with y hy
      exact extFun_of_nonpos g θ (le_of_lt hy)
    · -- `z = 0`: the corner; everything is `o(z)`
      subst hz
      have hxd : extDeriv g θ ((0:ℝ), τ) = 0 := extDeriv_of_nonpos g θ le_rfl τ
      rw [hxd]
      refine (hasFDerivAt_iff_isLittleO).2 ?_
      have hsub : (fun y : ℝ × ℝ =>
            extFun g θ y - extFun g θ ((0:ℝ), τ)
              - (0 : (ℝ × ℝ) →L[ℝ] ℝ) (y - ((0:ℝ), τ)))
          = fun y : ℝ × ℝ => extFun g θ y := by
        funext y
        rw [extFun_of_nonpos g θ le_rfl]
        simp
      rw [hsub]
      refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
      set η : ℝ := c / (2 * (|τ| + 2)) with hηdef
      have hηpos : 0 < η := by rw [hηdef]; positivity
      have hηK : η * (|τ| + 2) = c / 2 := by rw [hηdef]; field_simp
      have hηc : η ≤ c := by
        rw [hηdef]
        have h2 : (1:ℝ) ≤ 2 * (|τ| + 2) := by nlinarith [abs_nonneg τ]
        calc c / (2 * (|τ| + 2)) ≤ c / 1 := div_le_div_of_nonneg_left (le_of_lt hc) one_pos h2
          _ = c := by ring
      obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := slice_bound_of_tendsto hηpos (hjz θ hθ 0 h0mem)
      obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := slice_bound_of_tendsto hηpos (hd1z2 θ hθ)
      have hev₂ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |y.1⁻¹ * g y.1 θ 0| < η := by
        filter_upwards [eventually_box τ δ₂ hδ₂pos] with y hy hy1
        exact hδ₂ y.1 hy1 (hy hy1).1
      have hev₃ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |y.1⁻¹ * tauDer g θ y.1| < η := by
        filter_upwards [eventually_box τ δ₃ hδ₃pos] with y hy hy1
        exact hδ₃ y.1 hy1 (hy hy1).1
      have hev₁ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ), 0 < y.1 → y.1 < 1 := by
        filter_upwards [eventually_box τ 1 one_pos] with y hy hy1
        exact (hy hy1).1
      have hevτ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ), 0 < y.1 → |y.2 - τ| < 1 := by
        filter_upwards [eventually_box τ 1 one_pos] with y hy hy1
        exact (hy hy1).2
      filter_upwards [eventually_of_tendsto_box hηpos (hjz θ hθ τ hτU), hev₂, hev₃, hev₁, hevτ]
        with y hyA hy₂ hy₃ hy₁ hyτ
      rw [Real.norm_eq_abs]
      by_cases hy1 : 0 < y.1
      · have hgr : |g y.1 θ y.2| < η * y.1 := abs_lt_mul_of_abs_inv_mul_lt hy1 (hyA hy1)
        have hg0 : |g y.1 θ 0| < η * y.1 := abs_lt_mul_of_abs_inv_mul_lt hy1 (hy₂ hy1)
        have hdd : |tauDer g θ y.1| < η * y.1 := abs_lt_mul_of_abs_inv_mul_lt hy1 (hy₃ hy1)
        have hyt : |y.2| ≤ |τ| + 1 := by
          have habs : |y.2 - τ| < 1 := hyτ hy1
          calc |y.2| = |(y.2 - τ) + τ| := by ring_nf
            _ ≤ |y.2 - τ| + |τ| := abs_add_le _ _
            _ ≤ |τ| + 1 := by linarith [habs]
        have hnorm : y.1 ≤ ‖y - ((0:ℝ), τ)‖ := by
          have hle : y.1 ≤ max |y.1| |y.2 - τ| := by
            rw [abs_of_pos hy1]; exact le_max_left _ _
          calc y.1 ≤ max |y.1| |y.2 - τ| := hle
            _ = ‖y - ((0:ℝ), τ)‖ := by
                rw [Prod.norm_def]
                simp [Real.norm_eq_abs]
        rcases lt_or_ge y.2 0 with hy2 | hy2
        · -- jet branch
          have he : extFun g θ y = jetFn g θ y := by
            obtain ⟨y1, y2⟩ := y
            exact extFun_of_pos_of_neg g θ hy1 hy2
          rw [he, jetFn_apply]
          have hb : |g y.1 θ 0 + y.2 * tauDer g θ y.1| ≤ η * y.1 * (|τ| + 2) := by
            have h1 : |y.2 * tauDer g θ y.1| = |y.2| * |tauDer g θ y.1| := abs_mul _ _
            have h2 : |y.2| * |tauDer g θ y.1| ≤ (|τ| + 1) * (η * y.1) :=
              mul_le_mul hyt (le_of_lt hdd) (abs_nonneg _) (by positivity)
            have h3 : |g y.1 θ 0 + y.2 * tauDer g θ y.1|
                ≤ |g y.1 θ 0| + |y.2| * |tauDer g θ y.1| := by
              calc |g y.1 θ 0 + y.2 * tauDer g θ y.1|
                  ≤ |g y.1 θ 0| + |y.2 * tauDer g θ y.1| := abs_add_le _ _
                _ = |g y.1 θ 0| + |y.2| * |tauDer g θ y.1| := by rw [h1]
            have h4 : |g y.1 θ 0| + |y.2| * |tauDer g θ y.1|
                ≤ η * y.1 + (|τ| + 1) * (η * y.1) := add_le_add (le_of_lt hg0) h2
            calc |g y.1 θ 0 + y.2 * tauDer g θ y.1|
                ≤ η * y.1 + (|τ| + 1) * (η * y.1) := le_trans h3 h4
              _ = η * y.1 * (|τ| + 2) := by ring
          calc |g y.1 θ 0 + y.2 * tauDer g θ y.1| ≤ η * y.1 * (|τ| + 2) := hb
            _ = (c / 2) * y.1 := by rw [← hηK]; ring
            _ ≤ (c / 2) * ‖y - ((0:ℝ), τ)‖ := mul_le_mul_of_nonneg_left hnorm (by positivity)
            _ ≤ c * ‖y - ((0:ℝ), τ)‖ :=
                mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        · -- family branch
          have he : extFun g θ y = baseFn g θ y := by
            obtain ⟨y1, y2⟩ := y
            exact extFun_of_pos_of_nonneg g θ hy1 hy2
          rw [he, baseFn_apply]
          calc |g y.1 θ y.2| ≤ η * y.1 := le_of_lt hgr
            _ ≤ η * ‖y - ((0:ℝ), τ)‖ := mul_le_mul_of_nonneg_left hnorm (le_of_lt hηpos)
            _ ≤ c * ‖y - ((0:ℝ), τ)‖ := mul_le_mul_of_nonneg_right hηc (norm_nonneg _)
      · -- `y.1 ≤ 0`: the extension vanishes
        obtain ⟨y1, y2⟩ := y
        rw [extFun_of_nonpos g θ (le_of_not_gt hy1)]
        simp only [abs_zero]
        exact mul_nonneg (le_of_lt hc) (by positivity)
    · -- `z > 0`
      have hxV : (z, τ) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, hτU.1⟩
      by_cases hτn : τ < 0
      · -- the jet branch
        have hxd : extDeriv g θ (z, τ) = fderiv ℝ (jetFn g θ) (z, τ) :=
          extDeriv_eq_fderiv_jetFn g θ hz hτn (hjetdiff (z, τ) hxV)
        rw [hxd]
        refine (hjetAt (z, τ) hxV).congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
          (isOpen_Iio.preimage continuous_snd).mem_nhds hτn] with y hy1 hy2
        exact extFun_of_pos_of_neg g θ hy1 hy2
      · rcases lt_or_eq_of_le (le_of_not_gt hτn) with hτp | hτ0
        · -- the family branch
          have hxd : extDeriv g θ (z, τ) = fderiv ℝ (baseFn g θ) (z, τ) :=
            extDeriv_eq_fderiv_baseFn g θ hz (le_of_lt hτp) (hbasediff (z, τ) hxV)
          rw [hxd]
          refine (hbaseAt (z, τ) hxV).congr_of_eventuallyEq ?_
          filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
            (isOpen_Ioi.preimage continuous_snd).mem_nhds hτp] with y hy1 hy2
          exact extFun_of_pos_of_nonneg g θ hy1 (le_of_lt hy2)
        · -- the `τ = 0` join
          subst hτ0
          exact hasFDerivAt_extFun_join hz hbaseV hjetV
  -- ## Step 2: continuity of the candidate derivative
  have hcont : ContinuousOn (extDeriv g θ) (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)) := by
    rintro ⟨z, τ⟩ hxU
    have hτU : τ ∈ Ioo (-1:ℝ) (S + 1) := hxU.2
    rcases lt_trichotomy z 0 with hz | hz | hz
    · -- `z < 0`
      have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] (fun _ => (0 : (ℝ × ℝ) →L[ℝ] ℝ)) := by
        filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds hz] with y hy
        exact extDeriv_of_nonpos g θ (le_of_lt hy) y.2
      exact (continuousAt_const.congr_of_eventuallyEq hev).continuousWithinAt
    · -- `z = 0`
      subst hz
      have hxd : extDeriv g θ ((0:ℝ), τ) = 0 := extDeriv_of_nonpos g θ le_rfl τ
      refine ContinuousAt.continuousWithinAt ?_
      rw [ContinuousAt, hxd, Metric.tendsto_nhds]
      simp_rw [dist_zero_right]
      intro ε hε
      set η : ℝ := ε / (2 * (|τ| + 3)) with hηdef
      have hηpos : 0 < η := by rw [hηdef]; positivity
      have hηK : η * (|τ| + 3) = ε / 2 := by rw [hηdef]; field_simp
      have hηε : η ≤ ε := by
        rw [hηdef]
        have h2 : (1:ℝ) ≤ 2 * (|τ| + 3) := by nlinarith [abs_nonneg τ]
        calc ε / (2 * (|τ| + 3)) ≤ ε / 1 := div_le_div_of_nonneg_left (le_of_lt hε) one_pos h2
          _ = ε := by ring
      have hslice₀ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |deriv (fun z => g z θ 0) y.1| < η := by
        obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos (hjdz θ hθ 0 h0mem)
        filter_upwards [eventually_box τ δ hδ] with y hy hy1
        exact H y.1 hy1 (hy hy1).1
      have hslice₁ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |deriv (fun z => deriv (fun s => g z θ s) 0) y.1| < η := by
        obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos (hd1z θ hθ)
        filter_upwards [eventually_box τ δ hδ] with y hy hy1
        exact H y.1 hy1 (hy hy1).1
      have hslice₂ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |tauDer g θ y.1| < η * y.1 := by
        obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos (hd1z2 θ hθ)
        filter_upwards [eventually_box τ δ hδ] with y hy hy1
        exact abs_lt_mul_of_abs_inv_mul_lt hy1 (H y.1 hy1 (hy hy1).1)
      have hslice₃ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ), 0 < y.1 → y.1 < 1 := by
        filter_upwards [eventually_box τ 1 one_pos] with y hy hy1
        exact (hy hy1).1
      have hslice₄ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ), 0 < y.1 → |y.2 - τ| < 1 := by
        filter_upwards [eventually_box τ 1 one_pos] with y hy hy1
        exact (hy hy1).2
      filter_upwards [eventually_of_tendsto_box hηpos (hjdz θ hθ τ hτU),
        eventually_of_tendsto_box hηpos (hjdt θ hθ τ hτU),
        hslice₀, hslice₁, hslice₂, hslice₃, hslice₄]
        with y hdz hdt h₀ h₁ h₂ h₃ h₄
      by_cases hy1 : 0 < y.1
      · rcases lt_or_ge y.2 0 with hy2 | hy2
        · -- jet branch
          have hye : extDeriv g θ y = jetBranch g θ y := by
            obtain ⟨y1, y2⟩ := y
            exact extDeriv_of_pos_of_neg' g θ hy1 hy2
          rw [hye]
          have hsplit : ‖jetBranch g θ y‖
              ≤ |deriv (fun z' => jetFn g θ (z', y.2)) y.1|
                + |deriv (fun t => jetFn g θ (y.1, t)) y.2| := by
            simp only [jetBranch]
            exact norm_smul_fst_add_smul_snd_le _ _
          have hzf : deriv (fun z' => jetFn g θ (z', y.2)) y.1
              = deriv (fun z' => g z' θ 0) y.1
                + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1 :=
            deriv_jetFn_fst g θ (hz0diff y.1 hy1) (hτdiff y.1 hy1)
          have htf : deriv (fun t => jetFn g θ (y.1, t)) y.2 = tauDer g θ y.1 :=
            deriv_jetFn_snd g θ y.1 y.2
          rw [hzf, htf] at hsplit
          have hyt : |y.2| ≤ |τ| + 1 := by
            have habs : |y.2 - τ| < 1 := h₄ hy1
            calc |y.2| = |(y.2 - τ) + τ| := by ring_nf
              _ ≤ |y.2 - τ| + |τ| := abs_add_le _ _
              _ ≤ |τ| + 1 := by linarith [habs]
          have hb : |deriv (fun z' => g z' θ 0) y.1
                + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
              + |tauDer g θ y.1| < ε := by
            have hI : |deriv (fun z' => g z' θ 0) y.1
                + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
                ≤ η + (|τ| + 1) * η := by
              calc |deriv (fun z' => g z' θ 0) y.1
                    + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
                  ≤ |deriv (fun z' => g z' θ 0) y.1|
                    + |y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1| := abs_add_le _ _
                _ = |deriv (fun z' => g z' θ 0) y.1|
                    + |y.2| * |deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1| := by
                      rw [abs_mul]
                _ ≤ η + (|τ| + 1) * η :=
                      add_le_add (le_of_lt (h₀ hy1))
                        (mul_le_mul hyt (le_of_lt (h₁ hy1)) (abs_nonneg _) (by positivity))
            have hII : |tauDer g θ y.1| ≤ η :=
              le_of_lt (lt_of_lt_of_le (h₂ hy1) (by nlinarith [h₃ hy1]))
            have hIII : η + (|τ| + 1) * η + η ≤ ε := by
              have heq : η + (|τ| + 1) * η + η = η * (|τ| + 3) := by ring
              rw [heq, hηK]
              linarith
            linarith [hI, hII, hIII]
          exact lt_of_le_of_lt hsplit hb
        · -- family branch
          have hye : extDeriv g θ y = baseBranch g θ y := by
            obtain ⟨y1, y2⟩ := y
            exact extDeriv_of_pos_of_nonneg' g θ hy1 hy2
          rw [hye]
          have hsplit : ‖baseBranch g θ y‖
              ≤ |deriv (fun z' => baseFn g θ (z', y.2)) y.1|
                + |deriv (fun t => baseFn g θ (y.1, t)) y.2| := by
            simp only [baseBranch]
            exact norm_smul_fst_add_smul_snd_le _ _
          have hb : |deriv (fun z' => baseFn g θ (z', y.2)) y.1|
              + |deriv (fun t => baseFn g θ (y.1, t)) y.2| < ε := by
            have h1 : |deriv (fun z' => baseFn g θ (z', y.2)) y.1| < η := by
              simpa [baseFn] using hdz hy1
            have h2 : |deriv (fun t => baseFn g θ (y.1, t)) y.2| < η := by
              simpa [baseFn] using hdt hy1
            have hηhalf : η ≤ ε / 2 := by
              rw [hηdef]
              have h2 : (2:ℝ) ≤ 2 * (|τ| + 3) := by linarith [abs_nonneg τ]
              exact div_le_div_of_nonneg_left (le_of_lt hε) (by norm_num) h2
            linarith [h1, h2, hηhalf]
          exact lt_of_le_of_lt hsplit hb
      · -- `y.1 ≤ 0`
        have hye : extDeriv g θ y = 0 := by
          obtain ⟨y1, y2⟩ := y
          exact extDeriv_of_nonpos g θ (le_of_not_gt hy1) y2
        rw [hye]
        simpa using hε
    · -- `z > 0`
      have hxV : (z, τ) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, hτU.1⟩
      by_cases hτn : τ < 0
      · -- the jet branch
        have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] jetBranch g θ := by
          filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
            (isOpen_Iio.preimage continuous_snd).mem_nhds hτn] with y hy1 hy2
          exact extDeriv_of_pos_of_neg' g θ hy1 hy2
        exact ((hAcont.continuousAt (hVopen.mem_nhds hxV)).congr_of_eventuallyEq hev).continuousWithinAt
      · rcases lt_or_eq_of_le (le_of_not_gt hτn) with hτp | hτ0
        · -- the family branch
          have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] baseBranch g θ := by
            filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
              (isOpen_Ioi.preimage continuous_snd).mem_nhds hτp] with y hy1 hy2
            exact extDeriv_of_pos_of_nonneg' g θ hy1 (le_of_lt hy2)
          exact ((hBcont.continuousAt (hVopen.mem_nhds hxV)).congr_of_eventuallyEq hev).continuousWithinAt
        · -- the `τ = 0` join: the two branches agree there
          subst hτ0
          have hxV0 : (z, (0:ℝ)) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, by norm_num⟩
          have hAca : ContinuousAt (jetBranch g θ) (z, 0) :=
            hAcont.continuousAt (hVopen.mem_nhds hxV0)
          have hBca : ContinuousAt (baseBranch g θ) (z, 0) :=
            hBcont.continuousAt (hVopen.mem_nhds hxV0)
          have hAB : jetBranch g θ (z, 0) = baseBranch g θ (z, 0) :=
            jetBranch_eq_baseBranch_at_zero g θ z
          have hxe : extDeriv g θ (z, 0) = jetBranch g θ (z, 0) := by
            rw [extDeriv_of_pos_of_nonneg' g θ hz le_rfl]
            exact hAB.symm
          refine ContinuousAt.continuousWithinAt ?_
          rw [ContinuousAt, hxe, Metric.tendsto_nhds]
          intro ε hε
          have hAev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ),
              dist (jetBranch g θ y) (jetBranch g θ (z, 0)) < ε :=
            (Metric.tendsto_nhds.mp hAca) ε hε
          have hBev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ),
              dist (baseBranch g θ y) (baseBranch g θ (z, 0)) < ε :=
            (Metric.tendsto_nhds.mp hBca) ε hε
          have hVev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ), 0 < y.1 :=
            (isOpen_Ioi.preimage continuous_fst).mem_nhds hz
          filter_upwards [hAev, hBev, hVev] with y hyA hyB hy1
          by_cases hy : y.2 < 0
          · have hye : extDeriv g θ y = jetBranch g θ y := by
              obtain ⟨y1, y2⟩ := y
              exact extDeriv_of_pos_of_neg' g θ hy1 hy
            rw [hye]
            exact hyA
          · have hye : extDeriv g θ y = baseBranch g θ y := by
              obtain ⟨y1, y2⟩ := y
              exact extDeriv_of_pos_of_nonneg' g θ hy1 (le_of_not_gt hy)
            rw [hye, hAB]
            exact hyB
  -- ## Assembly
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl]
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUopen.uniqueDiffOn).2 ?_
  refine ⟨?_, extDeriv g θ, ?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · exact contDiffOn_zero.mpr hcont
  · intro x hx
    exact (hderiv x hx).hasFDerivWithinAt
end Work.FTS.RegPkgGal.R1b
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R4c.van_zsq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R4c

open Work.FTS.RegPkgGal.R4b

set_option autoImplicit false

/-- The analytic core of `van_global`: the angular FTC bound with the `z ^ 2` factor kept, valid
for **every** `z ≥ 0` (not only `z ≤ 2`).  This is `Work.FTS.RegPkgGal.R4b.van_of_dthvan` with the
`z ≤ 2` restriction removed: the proof there in fact produces
`|g z θ τ| ≤ Cθ * z^2 * max (M / (α * c₁)) (N / (2 * α * c₂)) * Γ(θ)` for all `z ≥ 0` (the `4` in
its final constant is only `z^2 ≤ 4`), so the same argument with `z ^ 2` in place of `4` at the one
step which uses `z ≤ 2` gives this. -/
theorem van_zsq {α S Cθ : ℝ} (hα : 0 < α) (hS : 0 < S) (hCθ : 0 ≤ Cθ)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (-1 : ℝ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨M, hM0, hM⟩ := primBoundLeft hα
  obtain ⟨N, hN0, hN⟩ := primBoundRight hα
  set c1 : ℝ := (1 / Real.pi) ^ α with hc1
  set c2 : ℝ := ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α with hc2
  have hc1pos : 0 < c1 := by rw [hc1]; exact Real.rpow_pos_of_pos (by positivity) _
  have hc2pos : 0 < c2 := by rw [hc2]; exact Real.rpow_pos_of_pos (by positivity) _
  have hzsq : ∀ z : ℝ, 0 ≤ z ^ 2 := fun z => sq_nonneg z
  refine ⟨Cθ * max (M / (α * c1)) (N / (2 * α * c2)), ?_, ?_⟩
  · exact mul_nonneg hCθ (le_trans (div_nonneg hM0 (by positivity)) (le_max_left _ _))
  · intro τ hτ z θ hz hθ
    have hzmem : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
    rcases le_or_gt θ (Real.pi / 4) with hθle | hθgt
    · -- ## the left half: integrate from `0` up to `θ ≤ π/4`
      have hθ0 : 0 ≤ θ := hθ.1
      have hsub : Set.Icc (0:ℝ) θ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
      have hmaj_int : IntervalIntegrable (fun x : ℝ => Cθ * z ^ 2 * M * x ^ (α - 1)) volume 0 θ :=
        (intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < α - 1 by linarith)).const_mul _
      have hmaj : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0:ℝ) θ)),
          ‖deriv (fun θ' => g z θ' τ) x‖ ≤ Cθ * z ^ 2 * M * x ^ (α - 1) := by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
        have hxle : x ≤ Real.pi / 4 := le_trans hx.2 hθle
        have h := pth_le_majorant hCθ (hd τ hτ) hM hz hx.1 hxle
        simpa [Work.Spaces.pth, Work.FTS.Regularity.gSlice, Real.norm_eq_abs] using h
      have hftc := slice_ftc_abs_le isOpen_Ioi isOpen_Ioo (hsm τ hτ) hzmem hθ0 hsub hmaj_int hmaj
      have hval : ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1)
          = Cθ * z ^ 2 * M * (θ ^ α / α) := by
        rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (show (-1:ℝ) < α - 1 by linarith)),
            show α - 1 + 1 = α by ring, Real.zero_rpow (ne_of_gt hα), sub_zero]
      have hGam : c1 * θ ^ α ≤ Work.FTS.Regularity.Gamma α θ := by
        rw [hc1]; exact Gamma_left_lb hα hθ0 hθle
      have hAc1 : θ ^ α * c1 ≤ Work.FTS.Regularity.Gamma α θ := by
        linarith [hGam, mul_comm c1 (θ ^ α)]
      have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
      have hquot : θ ^ α / α ≤ Work.FTS.Regularity.Gamma α θ / (α * c1) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < α),
            show Work.FTS.Regularity.Gamma α θ / (α * c1) * α
              = Work.FTS.Regularity.Gamma α θ * α / (α * c1) by ring,
            le_div_iff₀ (by positivity : (0:ℝ) < α * c1)]
        nlinarith [hAc1, hα, hc1pos]
      have hstep2 : M * (θ ^ α / α) ≤ (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ := by
        have h1 := mul_le_mul_of_nonneg_left hquot hM0
        rwa [show M * (Work.FTS.Regularity.Gamma α θ / (α * c1))
              = (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
      have hstep3 : (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ
          ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hΓ0
      calc |g z θ τ| = |g z θ τ - g z 0 τ| := by
              rw [show g z 0 τ = 0 from (hvt τ hτ).1 z, sub_zero]
        _ ≤ ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1) := hftc
        _ = Cθ * z ^ 2 * M * (θ ^ α / α) := hval
        _ = Cθ * z ^ 2 * (M * (θ ^ α / α)) := by ring
        _ ≤ Cθ * z ^ 2 * ((M / (α * c1)) * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCθ (hzsq z))
        _ ≤ Cθ * z ^ 2 * (max (M / (α * c1)) (N / (2 * α * c2))
              * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCθ (hzsq z))
        _ = (Cθ * max (M / (α * c1)) (N / (2 * α * c2))) * z ^ 2
              * Work.FTS.Regularity.Gamma α θ := by ring
    · -- ## the right half: integrate from `θ > π/4` up to `π/2`
      have hθpi2 : θ ≤ Real.pi / 2 := hθ.2
      have hsub : Set.Icc θ (Real.pi / 2) ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
        intro x hx
        exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
      have hbase : IntervalIntegrable (fun x : ℝ => x ^ (2 * α - 1)) volume 0 (Real.pi / 2 - θ) :=
        intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < 2 * α - 1 by linarith)
      have hcomp : IntervalIntegrable (fun x : ℝ => (Real.pi / 2 - x) ^ (2 * α - 1))
          volume (Real.pi / 2) θ := by
        have h' := hbase.comp_sub_left (Real.pi / 2)
        rw [sub_zero, show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h'
        exact h'
      have hmaj_int : IntervalIntegrable
          (fun x : ℝ => Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)) volume θ (Real.pi / 2) :=
        (hcomp.symm).const_mul _
      have hmaj : ∀ᵐ x ∂(volume.restrict (Set.Ioc θ (Real.pi / 2))),
          ‖deriv (fun θ' => g z θ' τ) x‖ ≤ Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
          rw [MeasureTheory.ae_iff]
          simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
          exact MeasureTheory.measure_singleton _
        filter_upwards [hae] with x hx hxmem
        have hx1 : Real.pi / 4 ≤ x := le_trans (le_of_lt hθgt) hxmem.1.le
        have hx2 : x < Real.pi / 2 := lt_of_le_of_ne hxmem.2 hx
        have h := pth_le_majorant_right hCθ (hd τ hτ) hN hz hx1 hx2
        simpa [Work.Spaces.pth, Work.FTS.Regularity.gSlice, Real.norm_eq_abs] using h
      have hftc := slice_ftc_abs_le isOpen_Ioi isOpen_Ioo (hsm τ hτ) hzmem hθpi2 hsub hmaj_int hmaj
      have hval : ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)
          = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ (2 * α - 1)) (Real.pi / 2),
            show Real.pi / 2 - Real.pi / 2 = 0 by ring,
            integral_rpow (Or.inl (show (-1:ℝ) < 2 * α - 1 by linarith)),
            show 2 * α - 1 + 1 = 2 * α by ring,
            Real.zero_rpow (by linarith : 2 * α ≠ 0), sub_zero]
      have hσ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθpi2]
      have hσle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith [hθgt]
      have hGam : c2 * (Real.pi / 2 - θ) ^ (2 * α) ≤ Work.FTS.Regularity.Gamma α θ := by
        have h := Gamma_right_lb hα hσ0 hσle
        rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h
      have hAc2 : (Real.pi / 2 - θ) ^ (2 * α) * c2 ≤ Work.FTS.Regularity.Gamma α θ := by
        linarith [hGam, mul_comm c2 ((Real.pi / 2 - θ) ^ (2 * α))]
      have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
      have hquot : (Real.pi / 2 - θ) ^ (2 * α) / (2 * α)
          ≤ Work.FTS.Regularity.Gamma α θ / (2 * α * c2) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * α),
            show Work.FTS.Regularity.Gamma α θ / (2 * α * c2) * (2 * α)
              = Work.FTS.Regularity.Gamma α θ * (2 * α) / (2 * α * c2) by ring,
            le_div_iff₀ (by positivity : (0:ℝ) < 2 * α * c2)]
        nlinarith [hAc2, hα, hc2pos]
      have hstep2 : N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))
          ≤ (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ := by
        have h1 := mul_le_mul_of_nonneg_left hquot hN0
        rwa [show N * (Work.FTS.Regularity.Gamma α θ / (2 * α * c2))
              = (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
      have hstep3 : (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ
          ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hΓ0
      calc |g z θ τ| = |g z (Real.pi / 2) τ - g z θ τ| := by
              rw [show g z (Real.pi / 2) τ = 0 from (hvt τ hτ).2 z, zero_sub, abs_neg]
        _ ≤ ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := hftc
        _ = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := hval
        _ = Cθ * z ^ 2 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))) := by ring
        _ ≤ Cθ * z ^ 2 * ((N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCθ (hzsq z))
        _ ≤ Cθ * z ^ 2 * (max (M / (α * c1)) (N / (2 * α * c2))
              * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCθ (hzsq z))
        _ = (Cθ * max (M / (α * c1)) (N / (2 * α * c2))) * z ^ 2
              * Work.FTS.Regularity.Gamma α θ := by ring

end Work.FTS.RegPkgGal.R4c
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R5f.jet_dtg_of_rhs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.R5f.jet_dtg_of_rhs` — the fake-time jet `∂_τg̃` from the a-priori
# regularity of the right-hand side

`R5.dtg_eq_rhs` identifies the fake-time derivative of the extension `g̃ = extG g` with the
right-hand side `dynLin α g τ + dynRHS α Φ g τ` **on the open quadrant** `Qd = (0,∞) × (0,π/2)`.
This file turns that identification into the `Jet` of the derivative on the **closed** domain
`z ≥ 0`, `θ ∈ Iθ = [0,π/2]`, `τ ∈ [0,S]`, given the a-priori regularity of the right-hand side
itself:

* `hRHS` — the right-hand side is a `Jet α S N0` (bounded and jointly `α`-Hölder on the closed
  domain);
* `hRz0`, `hRθ0`, `hRθπ` — it vanishes at `z = 0` and on the two angular boundary lines.

The point is that the *closed* domain is `Qd ∪ {z = 0} ∪ {θ = 0} ∪ {θ = π/2}`, so only the three
boundary pieces have to be added to the identification:

* **`z = 0`**: `g̃ 0 θ τ = 0` for *every* `τ` (the `z ≤ 0` branch of `extG` wins), so the
  derivative is `0`, which is the value of the right-hand side by `hRz0`;
* **`θ = 0` or `θ = π/2`, `z > 0`**: `RegPkgMin.vanish` makes the slice `s ↦ g z θ s` vanish on
  the whole half-line `s ≥ 0`; consequently both branches of `extG g z θ ·` vanish —
  the value branch by `vanish`, the Taylor branch because `g z θ 0 = 0` *and*
  `deriv (fun s => g z θ s) 0 = 0` (`deriv_eq_zero_of_eq_zero_on_Ici`: a function which vanishes
  on `[0,∞)` has zero derivative at `0`, either because its two-sided derivative, if it exists,
  must agree with its (vanishing) right derivative, or because it is not differentiable at `0`
  at all, in which case `deriv` is `0` by convention).  Hence the derivative is `0` there too,
  the value given by `hRθ0`/`hRθπ`.

Everything else is a verbatim re-run of `R5.dtg_eq_rhs`, with the elliptic law dropped
(`dtg_eq_rhs_of_isDynEqOn` below needs only the one-sided equation `IsDynEqOn`, not the packaged
`IsDynGSolWith`), and then the `Jet` of the derivative is the `Jet` of the right-hand side by
pointwise rewriting.
-/

namespace Work.FTS.RegPkgGal.R5f

open Set Filter Topology
open scoped Real Topology

/-- **A function which vanishes on `[0,∞)` has zero derivative at `0`.**

If `f` is differentiable at `0`, its two-sided derivative must agree with its right derivative,
which is `0` (compute `derivWithin f (Ici 0) 0` from the vanishing of `f` on `Ici 0` and from the
`HasDerivWithinAt` form of `f`'s derivative); if it is not differentiable, `deriv` is `0` by
convention (`deriv_zero_of_not_differentiableAt`). -/
theorem deriv_eq_zero_of_eq_zero_on_Ici {f : ℝ → ℝ}
    (hf : ∀ s : ℝ, 0 ≤ s → f s = 0) : deriv f 0 = 0 := by
  by_cases h : DifferentiableAt ℝ f 0
  · have h1 : derivWithin f (Set.Ici 0) 0 = deriv f 0 :=
      h.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
    have h2 : derivWithin f (Set.Ici 0) 0 = 0 :=
      ((hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) (0 : ℝ)).congr
        (fun y hy => hf y hy) (hf 0 le_rfl)).derivWithin (uniqueDiffWithinAt_Ici 0)
    rw [h1] at h2
    exact h2
  · exact deriv_zero_of_not_differentiableAt h

/-- **The extension vanishes identically at the angular endpoints.**  If the slice
`s ↦ g z θ s` vanishes on the whole half-line `s ≥ 0` (which is what `RegPkgMin.vanish` gives at
`θ = 0` and `θ = π/2`) and `z > 0`, then `s ↦ g̃ z θ s = extG g z θ s` vanishes identically: the
value branch by hypothesis, and the Taylor branch because `g z θ 0 = 0` and
`deriv (fun s => g z θ s) 0 = 0` (`deriv_eq_zero_of_eq_zero_on_Ici`). -/
theorem extG_eq_zero_of_eq_zero_on_Ici {g : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hg : ∀ s : ℝ, 0 ≤ s → g z θ s = 0) : ∀ s : ℝ, extG g z θ s = 0 := by
  have hd : deriv (fun s => g z θ s) 0 = 0 := deriv_eq_zero_of_eq_zero_on_Ici hg
  intro s
  rcases lt_or_ge s 0 with hs | hs
  · rw [extG_of_neg hz hs, hg 0 le_rfl, hd]
    ring
  · rw [extG_of_pos hz hs, hg s hs]

/-- **The identification `∂_τg̃ = dynLin + dynRHS` on the open quadrant, from the one-sided
equation alone.**  This is `R5.dtg_eq_rhs` with the elliptic-law component of the packaged
predicate dropped: only `hsol` (the half-line equation) and the two-sided `τ = 0` identity `h0`
carry the derivative, exactly as in the sibling lemma, which it re-uses verbatim through
`R5.hasDerivAt_extG_of_zero` and `R5.hasDerivAt_extG_of_pos`. -/
theorem dtg_eq_rhs_of_isDynEqOn {α S : ℝ}
    {g Φ : ℝ → ℝ → ℝ → ℝ}
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0) :
    ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      deriv (fun s => extG g z θ s) τ
        = Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ := by
  intro τ hτ z θ hz hQd
  have hLeq : HasDerivWithinAt (fun s => g z θ s)
      (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ) (Set.Ici 0) τ :=
    hsol z θ τ hτ.1 hQd
  rcases eq_or_lt_of_le hτ.1 with hzero | hpos
  · subst hzero
    exact (Work.FTS.RegPkgGal.R5.hasDerivAt_extG_of_zero hz (h0 z θ hz hQd)).deriv
  · exact (Work.FTS.RegPkgGal.R5.hasDerivAt_extG_of_pos hz hpos
      (hLeq.hasDerivAt (Ici_mem_nhds hpos))).deriv

/-- **The pointwise identification of `∂_τg̃` with the right-hand side on the closed domain.**

On the open quadrant this is `dtg_eq_rhs_of_isDynEqOn`; on the three boundary pieces (`z = 0` and
the two angular lines) the derivative is `0` — because `g̃` vanishes identically there as a
function of `τ` — and the right-hand side is `0` by `hRz0`/`hRθ0`/`hRθπ`. -/
theorem deriv_extG_eq_rhs_of_jet {α S : ℝ} {g Φ : ℝ → ℝ → ℝ → ℝ}
    (hmin : Work.FTS.RegPkgGal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0)
    (hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ 0 θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ 0 θ = 0)
    (hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z 0
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z 0 = 0)
    (hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z (Real.pi / 2)
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z (Real.pi / 2) = 0) :
    ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => extG g z θ s) τ
        = Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ := by
  intro z θ τ hz hθ hτ
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: the extension is identically `0` in `τ`
    subst hz0
    have hzero : (fun s => extG g 0 θ s) = fun _ => (0 : ℝ) :=
      funext (fun s => extG_of_nonpos (le_refl (0 : ℝ)))
    rw [hzero, deriv_const]
    exact (hRz0 τ hτ θ hθ).symm
  · rcases eq_or_ne θ 0 with hθ0 | hθ0
    · -- `θ = 0`: `vanish` makes the slice vanish on `[0,∞)`, hence the extension identically
      subst hθ0
      have hgg : ∀ s : ℝ, 0 ≤ s → g z 0 s = 0 := fun s hs => (hmin.vanish s hs z hzpos.le).1
      rw [funext (extG_eq_zero_of_eq_zero_on_Ici hzpos hgg), deriv_const]
      exact (hRθ0 τ hτ z).symm
    · rcases eq_or_ne θ (Real.pi / 2) with hθπ | hθπ
      · -- `θ = π/2`: same
        subst hθπ
        have hgg : ∀ s : ℝ, 0 ≤ s → g z (Real.pi / 2) s = 0 :=
          fun s hs => (hmin.vanish s hs z hzpos.le).2
        rw [funext (extG_eq_zero_of_eq_zero_on_Ici hzpos hgg), deriv_const]
        exact (hRθπ τ hτ z).symm
      · -- interior point of the quadrant: the identification of `R5`
        have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
        have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 hθπ
        exact dtg_eq_rhs_of_isDynEqOn hsol h0 τ hτ z θ hzpos ⟨hzpos, hθpos, hθlt⟩

theorem jet_dtg_of_rhs {α S N0 : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {g Φ : ℝ → ℝ → ℝ → ℝ}
    (hmin : Work.FTS.RegPkgGal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0)
    (hRHS : Work.FTS.Regularity.Jet α S N0
      (fun z θ τ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ))
    (hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ 0 θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ 0 θ = 0)
    (hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z 0
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z 0 = 0)
    (hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z (Real.pi / 2)
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z (Real.pi / 2) = 0) :
    ∃ Nd : ℝ, Work.FTS.Regularity.Jet α S Nd
      (fun z θ τ => deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ) := by
  -- the derivative is the right-hand side pointwise on the closed domain, so it inherits the
  -- whole `Jet` of `hRHS`
  refine ⟨N0, hRHS.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    show |deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ| ≤ N0
    rw [deriv_extG_eq_rhs_of_jet hmin hsol h0 hRz0 hRθ0 hRθπ z θ τ hz hθ hτ]
    exact hRHS.2.1 z θ τ hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    show |deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ
        - deriv (fun s => Work.FTS.RegPkgGal.extG g z' θ' s) τ'|
      ≤ N0 * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
    rw [deriv_extG_eq_rhs_of_jet hmin hsol h0 hRz0 hRθ0 hRθπ z θ τ hz hθ hτ,
      deriv_extG_eq_rhs_of_jet hmin hsol h0 hRz0 hRθ0 hRθπ z' θ' τ' hz' hθ' hτ']
    exact hRHS.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'

end Work.FTS.RegPkgGal.R5f
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.St1Class =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- **THE `St1`-CLASS EXPORT.**  The class data of the perturbation `g̃` which the paper's
construction provides and which the physical bridge consumes (see the module docstring). -/
structure St1Class (α S : ℝ) (g : Fam) : Prop where
  /-- the `Γ`-vanishing of the angular derivative together with the Taylor data at `z = 0` -/
  hSt : StData α S (extG g)
  /-- the second-order `z`-bound at the origin -/
  hSt2 : StData2 α S (extG g)
  /-- the `θ`-modulus of `g̃` (`α`-Hölder, uniform in `(z,τ)`) -/
  hhθ : ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
    ∀ θ' ∈ Work.Spaces.Iθ, |extG g z θ τ - extG g z θ' τ| ≤ Lθ * |θ - θ'| ^ α
  /-- the `θ`-modulus of `∂_zg̃` (`α`-Hölder, uniform in `(z,τ)`) -/
  hhθp : ∃ Nθ : ℝ, 0 ≤ Nθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
    ∀ θ' ∈ Work.Spaces.Iθ,
    |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => extG g z θ τ) z θ'| ≤ Nθ * |θ - θ'| ^ α



/-- The `Γ`-vanishing clause of the class, in the shape the derivations consume. -/
theorem St1Class.dthvan {α S : ℝ} {g : Fam} (H : St1Class α S g) :
    ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (gSlice (extG g) τ) z θ| ≤ Cθ * z ^ 2 * Gamma α θ := H.hSt.dthvan

/-- The Taylor clause at `z = 0` of the class, in the shape the derivations consume. -/
theorem St1Class.quad {α S : ℝ} {g : Fam} (H : St1Class α S g) :
    ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |extG g z θ τ| ≤ K * z ^ 2) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |Work.Spaces.pz (gSlice (extG g) τ) z θ| ≤ Q * z) := H.hSt.quad

/-- The second-order clause of the class, in the shape the derivations consume. -/
theorem St1Class.quad2 {α S : ℝ} {g : Fam} (H : St1Class α S g) :
    ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → z ≤ 2 →
      |Work.Spaces.pz (Work.Spaces.pz (gSlice (extG g) τ)) z θ| ≤ Q₂ := H.hSt2.quad2

end Work.FTS.RegPkgGal
end
end
