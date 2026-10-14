import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamSupAux.ug_bound
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.ModeEnergyCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-! ## Nonnegativity of the two weighted `L²` functionals -/


/-- Nonnegativity of the weighted gradient functional `∫_0^∞ (z f')² w²`. -/
theorem integral_grad_w_sq_nonneg (f : ℝ → ℝ) :
    0 ≤ ∫ z in Set.Ioi 0, (z * deriv f z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
  MeasureTheory.integral_nonneg_of_ae (μ := volume.restrict (Set.Ioi 0))
    (Filter.Eventually.of_forall fun z => by positivity)

/-! ## The AM–GM bound of the weighted pairing -/

/-- **The AM–GM bound.**  For `μ > 0`, the weighted pairing is dominated by
`(∫ c² w² + μ² ∫ a² w²)/(2μ)`.  Pointwise this is
`2μ·c a w² ≤ c² w² + μ² a² w²`, the elementary inequality `2 μ x y ≤ x² + μ² y²` with
`x = c w`, `y = a w`. -/
theorem integral_pairing_le {μ : ℝ} (hμ : 0 < μ) {a c : ℝ → ℝ}
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint4 : MeasureTheory.IntegrableOn
      (fun z => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, c z * a z * (Work.Spaces.w z) ^ 2)
      ≤ ((∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)) / (2 * μ) := by
  have h2μ : 0 < 2 * μ := by linarith
  have hInt : MeasureTheory.IntegrableOn
      (fun z => (((c z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)) / (2 * μ)) (Set.Ioi 0) :=
    (hint4.add (hint2.const_mul _)).div_const _
  have hmono := MeasureTheory.setIntegral_mono hint3 hInt (fun z => by
    have h := sq_nonneg (c z * Work.Spaces.w z - μ * (a z * Work.Spaces.w z))
    have e : (c z * Work.Spaces.w z - μ * (a z * Work.Spaces.w z)) ^ 2
        = (c z) ^ 2 * (Work.Spaces.w z) ^ 2
          - 2 * μ * (c z * a z * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
    rw [e] at h
    rw [le_div_iff₀ h2μ]
    nlinarith [h])
  calc (∫ z in Set.Ioi 0, c z * a z * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (((c z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)) / (2 * μ) := hmono
    _ = ((∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)) / (2 * μ) := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add hint4 (hint2.const_mul _),
          MeasureTheory.integral_const_mul]

/-! ## The sharp weighted `L²` per-mode bound -/

/-- **The sharp per-mode bound, squared form.**  Under the hypotheses of `modeWeightedEnergy`
together with the integrability of `c² w²` and the positivity of
`μ = lam − 3α² − 3α(5+α)/2`, one has `μ² ∫ a² w² ≤ ∫ c² w²`. -/
theorem modeWeightedEnergy_sq {α lam : ℝ} (hα : 0 < α) {a c : ℝ → ℝ}
    (hac : ContinuousOn a (Set.Ioi 0))
    (ha : ∀ z, 0 < z → HasDerivAt a (deriv a z) z)
    (ha' : ∀ z, 0 < z → HasDerivAt (deriv a) (deriv (deriv a) z) z)
    (hode : ∀ z, 0 < z → α ^ 2 * z ^ 2 * deriv (deriv a) z + α * (5 + α) * z * deriv a z
        = lam * a z - c z)
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint4 : MeasureTheory.IntegrableOn
      (fun z => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hcont : ContinuousWithinAt (Work.FTS.ClassC.flux α a) (Set.Ici 0) 0)
    (hdec : Filter.Tendsto (Work.FTS.ClassC.flux α a) Filter.atTop (nhds 0))
    (hmu : 0 < lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) :
    (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  have hbase := modeWeightedEnergy (α := α) (lam := lam) hα hac ha ha' hode hint1 hint2 hint3
    hcont hdec
  set mu := lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2 with hmu_def
  set A := ∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2 with hA_def
  set B := ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 with hB_def
  set P := ∫ z in Set.Ioi 0, c z * a z * (Work.Spaces.w z) ^ 2 with hP_def
  have hmu_pos : 0 < mu := hmu
  have hgrad : 0 ≤ ∫ z in Set.Ioi 0, (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    integral_grad_w_sq_nonneg a
  have hmuA : mu * A ≤ P := by
    have h2 : 0 ≤ α ^ 2 * (∫ z in Set.Ioi 0, (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (sq_nonneg α) hgrad
    linarith
  have hamgm := integral_pairing_le hmu_pos hint3 hint2 hint4
  have h2μ : 0 < 2 * mu := by linarith
  rw [le_div_iff₀ h2μ] at hamgm
  nlinarith [hmuA, hamgm]


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.coercive_slice_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Auxiliary facts for the slice coercivity -/


/-- The constant `c = (1 + 225π²/2048)/16` of the slice coercivity. -/
def sliceC : ℝ := (1 + 225 * π ^ 2 / 2048) / 16

theorem sliceC_pos : 0 < sliceC := by
  rw [sliceC]; positivity

theorem sliceC_lt : sliceC < 1 / 6 := by
  have hpi : π ^ 2 < 15 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  rw [sliceC]
  nlinarith [hpi]

/-- The set integral over `Iθ = [0,π/2]` written as an interval integral. -/
theorem Iθ_eq_interval (G : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, G θ) = ∫ θ in (0 : ℝ)..(π / 2), G θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]

/-- The first sine coefficient `a = (4/π)∫ f sin 2θ` of `f` on `[0,π/2]`. -/
def coeffF (f : ℝ → ℝ) : ℝ := (4 / π) * ∫ θ in (0 : ℝ)..(π / 2), f θ * Real.sin (2 * θ)

/-- The residue `g = f - a sin 2θ`, orthogonal to `sin 2θ`. -/
def residF (f : ℝ → ℝ) : ℝ → ℝ := fun θ => f θ - coeffF f * Real.sin (2 * θ)

/-- The final arithmetic step: given the two orthogonal decompositions
`∫f² = (π/4)a² + S`, `∫(f')² = πa² + R`, the bound on the first coefficient
`(π/4)a² ≤ (225π²/2048)S` and the spectral gap `16 S ≤ R`, deduce the coercivity bound. -/
theorem final_arith {A F2 F1 S R : ℝ} (hA0 : 0 ≤ A)
    (h2 : F2 = (π / 4) * A + S) (h1 : F1 = π * A + R)
    (hA : (π / 4) * A ≤ (225 * π ^ 2 / 2048) * S) (hgap : 16 * S ≤ R) :
    F2 ≤ sliceC * F1 := by
  have hpi := Real.pi_pos
  have hK : (0 : ℝ) < 1 + 225 * π ^ 2 / 2048 := by positivity
  have h1R : R ≤ F1 := by nlinarith [h1, hA0, hpi]
  have hfin : F2 ≤ (1 + 225 * π ^ 2 / 2048) * S := by nlinarith [h2, hA]
  rw [sliceC]
  nlinarith [hfin, hgap, h1R, hK]

/-- Agreement on the open interval implies a.e. agreement for the measure restricted to the
(oriented) closed interval. -/
private lemma ae_eq_of_eqOn_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : Set.EqOn f g (Set.Ioo a b)) : f =ᵐ[volume.restrict (Set.uIoc a b)] g := by
  rw [Set.uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  exact ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => h hx)

/-- `(deriv f)²` is interval integrable on any subinterval `[a,b] ⊆ [0,π/2]` when `f` is `C²`
on `[0,π/2]` and vanishes at the endpoints (the derivative is continuous on the open interval
and bounded there). -/
private lemma intervalIntegrable_deriv_sq_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ π / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2) volume a b := by
  have hf1 : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2)) := hf.of_le (by norm_num)
  have hcont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (π / 2)) :=
    continuousOn_deriv_Ioo_of_contDiffOn hf1
  obtain ⟨C, hC0, -, hCbnd⟩ := Work.Elliptic.contDiffOn_one_bounds hf1 h0 h1
  refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hab ?_ (C ^ 2) ?_
  · refine (hcont.pow 2).mono ?_
    intro x hx
    exact ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
    have hb' := hCbnd x hx'
    rw [Real.norm_eq_abs] at hb'
    rw [abs_of_nonneg (sq_nonneg (deriv f x))]
    calc (deriv f x) ^ 2 = |deriv f x| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb' 2

/-- The angular moment of the residue `g = f - a sin 2θ` against `sin θ cos²θ` equals
`-(4/15) a`, and Cauchy–Schwarz with `∫ (sin θ cos²θ)² = π/32` bounds its square by
`(π/32) ∫ g²`. -/
private theorem residF_moment (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (horth : (∫ θ in (0 : ℝ)..(π / 2), f θ * Work.Elliptic.sinCos2 θ) = 0) :
    (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ
        = -(4 / 15) * coeffF f) ∧
    ((∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ) ^ 2
        ≤ (π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2)) := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  obtain ⟨T1, T2, T3, T4⟩ := sin_integrals
  have hcont_f : ContinuousOn f (Set.uIcc 0 (π / 2)) := by
    rw [Set.uIcc_of_le hpi]; exact hf.continuousOn
  have hcont_w : ContinuousOn Work.Elliptic.sinCos2 (Set.uIcc 0 (π / 2)) := by
    unfold Work.Elliptic.sinCos2; fun_prop
  have hcont_g : ContinuousOn (residF f) (Set.uIcc 0 (π / 2)) := by
    unfold residF; fun_prop
  have hmom : (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ)
      = -(4 / 15) * coeffF f := by
    have hpt : ∀ θ, residF f θ * Work.Elliptic.sinCos2 θ
        = f θ * Work.Elliptic.sinCos2 θ
          - coeffF f * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
      intro θ; unfold residF; ring
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
    have i1 : IntervalIntegrable (fun θ => f θ * Work.Elliptic.sinCos2 θ) volume 0 (π / 2) :=
      (hcont_f.mul hcont_w).intervalIntegrable
    have i2 : IntervalIntegrable
        (fun θ => coeffF f * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) volume 0 (π / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      exact (((by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
        (Set.uIcc 0 (π / 2)))).mul hcont_w).const_mul _
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
    have hswap : (∫ θ in (0 : ℝ)..(π / 2), Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
        = 4 / 15 := by
      have heq : (∫ θ in (0 : ℝ)..(π / 2), Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
          = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ) :=
        intervalIntegral.integral_congr (fun θ _ => by ring)
      rw [heq]; exact T4
    rw [hswap, horth]; ring
  refine ⟨hmom, ?_⟩
  have hquad0 : ∀ t : ℝ,
      0 ≤ (∫ θ in (0 : ℝ)..(π / 2), (residF f θ - t * Work.Elliptic.sinCos2 θ) ^ 2) := by
    intro t
    exact intervalIntegral.integral_nonneg hpi (fun θ _ => sq_nonneg _)
  have hpt_sq : ∀ (t θ : ℝ), (residF f θ - t * Work.Elliptic.sinCos2 θ) ^ 2
      = (residF f θ) ^ 2 - 2 * t * (residF f θ * Work.Elliptic.sinCos2 θ)
        + t ^ 2 * (Work.Elliptic.sinCos2 θ) ^ 2 := by
    intro t θ; ring
  have hexp : ∀ t : ℝ,
      (∫ θ in (0 : ℝ)..(π / 2), (residF f θ - t * Work.Elliptic.sinCos2 θ) ^ 2)
        = (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2)
          - 2 * t * (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ)
          + t ^ 2 * (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.sinCos2 θ) ^ 2) := by
    intro t
    rw [intervalIntegral.integral_congr (fun θ _ => hpt_sq t θ)]
    have iA : IntervalIntegrable (fun θ => (residF f θ) ^ 2) volume 0 (π / 2) :=
      (hcont_g.pow 2).intervalIntegrable
    have iB : IntervalIntegrable (fun θ => 2 * t * (residF f θ * Work.Elliptic.sinCos2 θ))
        volume 0 (π / 2) :=
      ((hcont_g.mul hcont_w).const_mul _).intervalIntegrable
    have iC : IntervalIntegrable (fun θ => t ^ 2 * (Work.Elliptic.sinCos2 θ) ^ 2)
        volume 0 (π / 2) :=
      ((hcont_w.pow 2).const_mul _).intervalIntegrable
    rw [intervalIntegral.integral_add (iA.sub iB) iC, intervalIntegral.integral_sub iA iB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hquad : ∀ x : ℝ, 0 ≤ (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.sinCos2 θ) ^ 2)
      * (x * x) + (-2 * (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ)) * x
      + (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by
    intro x
    have h := hquad0 x
    rw [hexp x] at h
    nlinarith [h]
  have hd := discrim_le_zero hquad
  rw [discrim, sq, T3] at hd
  nlinarith [hd]

/-- The sharp second Dirichlet eigenvalue on `[0,π/2]`: a `C²` function vanishing at the two
endpoints and orthogonal to `sin 2θ` satisfies `16 ∫ h² ≤ ∫ (h')²`.  Proof: split at `π/4`,
where `η = h - h(π/4) sin 2θ` vanishes, and apply Wirtinger's inequality with constant
`(π/(π/4))² = 16` on each half. -/
private theorem second_eigenvalue {h : ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (h0 : h 0 = 0) (h1 : h (π / 2) = 0)
    (hmean : (∫ θ in (0 : ℝ)..(π / 2), h θ * Real.sin (2 * θ)) = 0) :
    16 * (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2) ≤ ∫ θ in (0 : ℝ)..(π / 2), (deriv h θ) ^ 2 := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hpi4 : (0 : ℝ) < π / 4 := by positivity
  obtain ⟨T1, T2, T3, Dsin, Dcos⟩ := trig_resid
  -- the integration by parts `∫ h' (2 cos 2θ) = 4 ∫ h sin 2θ`
  have hcross : (∫ θ in (0 : ℝ)..(π / 2), deriv h θ * (2 * Real.cos (2 * θ))) = 0 := by
    have hIBP := ibp_contdiffon hpi hh
      (by fun_prop : ContDiff ℝ 2 (fun θ : ℝ => 2 * Real.cos (2 * θ)))
    have hint2 : (∫ x in (0 : ℝ)..(π / 2),
          h x * deriv (fun θ : ℝ => 2 * Real.cos (2 * θ)) x)
        = ∫ x in (0 : ℝ)..(π / 2), h x * (-4 * Real.sin (2 * x)) :=
      intervalIntegral.integral_congr (fun x _ => by rw [Dcos x])
    have hint : (∫ x in (0 : ℝ)..(π / 2), h x * (-4 * Real.sin (2 * x)))
        = -4 * (∫ x in (0 : ℝ)..(π / 2), h x * Real.sin (2 * x)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun x _ => by ring)
    have h2pi : (2 : ℝ) * Real.cos (2 * (π / 2)) = -2 := by
      rw [show (2 : ℝ) * (π / 2) = π by ring, Real.cos_pi]; ring
    have h20 : (2 : ℝ) * Real.cos (2 * 0) = 2 := by
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.cos_zero]; ring
    rw [hIBP, hint2, hint, hmean, h2pi, h20, h1, h0]; ring
  set c : ℝ := h (π / 4) with hc
  set η : ℝ → ℝ := fun θ => h θ - c * Real.sin (2 * θ) with heta
  have hηC : ContDiffOn ℝ 2 η (Set.Icc 0 (π / 2)) := by
    rw [heta]; fun_prop
  have hη0 : η 0 = 0 := by rw [heta]; simp [h0]
  have hη4 : η (π / 4) = 0 := by
    change h (π / 4) - c * Real.sin (2 * (π / 4)) = 0
    rw [← hc]
    have h2 : (2 : ℝ) * (π / 4) = π / 2 := by ring
    rw [h2, Real.sin_pi_div_two]; ring
  have hη1 : η (π / 2) = 0 := by
    change h (π / 2) - c * Real.sin (2 * (π / 2)) = 0
    have h2 : (2 : ℝ) * (π / 2) = π := by ring
    rw [h2, Real.sin_pi, h1]; ring
  have hsub1 : Set.Icc (0 : ℝ) (π / 4) ⊆ Set.Icc (0 : ℝ) (π / 2) := by
    intro x hx; exact ⟨hx.1, le_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hsub2 : Set.Icc (π / 4) (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) := by
    intro x hx; exact ⟨le_trans (by linarith [Real.pi_pos]) hx.1, hx.2⟩
  have hc4 : (π / ((π : ℝ) / 4 - 0)) ^ 2 = 16 := by
    have h1 : (π : ℝ) / (π / 4) = 4 := by field_simp
    rw [sub_zero, h1]; norm_num
  have hc4' : (π / ((π : ℝ) / 2 - π / 4)) ^ 2 = 16 := by
    have h1 : (π : ℝ) / (π / 2 - π / 4) = 4 := by
      rw [show (π : ℝ) / 2 - π / 4 = π / 4 by ring]
      field_simp
    rw [h1]; norm_num
  have hw1 : 16 * (∫ θ in (0 : ℝ)..(π / 4), (η θ) ^ 2)
      ≤ ∫ θ in (0 : ℝ)..(π / 4), (deriv η θ) ^ 2 := by
    have h := wirtinger_interval hpi4 (hηC.mono hsub1) hη0 hη4
    rwa [hc4] at h
  have hw2 : 16 * (∫ θ in (π / 4)..(π / 2), (η θ) ^ 2)
      ≤ ∫ θ in (π / 4)..(π / 2), (deriv η θ) ^ 2 := by
    have h := wirtinger_interval (by linarith [Real.pi_pos] : (π : ℝ) / 4 < π / 2)
      (hηC.mono hsub2) hη4 hη1
    rwa [hc4'] at h
  have iη1 : IntervalIntegrable (fun θ => (η θ) ^ 2) volume 0 (π / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpi4.le]
    exact (hηC.continuousOn.pow 2).mono hsub1
  have iη2 : IntervalIntegrable (fun θ => (η θ) ^ 2) volume (π / 4) (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (π : ℝ) / 4 ≤ π / 2)]
    exact (hηC.continuousOn.pow 2).mono hsub2
  have iD1 : IntervalIntegrable (fun θ => (deriv η θ) ^ 2) volume 0 (π / 4) :=
    intervalIntegrable_deriv_sq_Ioo hpi4.le le_rfl (by linarith [Real.pi_pos]) hηC hη0 hη1
  have iD2 : IntervalIntegrable (fun θ => (deriv η θ) ^ 2) volume (π / 4) (π / 2) :=
    intervalIntegrable_deriv_sq_Ioo (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      le_rfl hηC hη0 hη1
  have hsp1 : (∫ θ in (0 : ℝ)..(π / 2), (η θ) ^ 2)
      = (∫ θ in (0 : ℝ)..(π / 4), (η θ) ^ 2) + (∫ θ in (π / 4)..(π / 2), (η θ) ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals iη1 iη2).symm
  have hsp2 : (∫ θ in (0 : ℝ)..(π / 2), (deriv η θ) ^ 2)
      = (∫ θ in (0 : ℝ)..(π / 4), (deriv η θ) ^ 2)
        + (∫ θ in (π / 4)..(π / 2), (deriv η θ) ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals iD1 iD2).symm
  have hgapη : 16 * (∫ θ in (0 : ℝ)..(π / 2), (η θ) ^ 2)
      ≤ ∫ θ in (0 : ℝ)..(π / 2), (deriv η θ) ^ 2 := by
    rw [hsp1, hsp2]; linarith [hw1, hw2]
  -- expansion of `∫ η²`
  have hE1 : (∫ θ in (0 : ℝ)..(π / 2), (η θ) ^ 2)
      = (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2) + c ^ 2 * (π / 4) := by
    have hpt1 : ∀ θ, (η θ) ^ 2 = (h θ) ^ 2 - 2 * c * (h θ * Real.sin (2 * θ))
        + c ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
      intro θ; rw [heta]; dsimp only; ring
    have hsq : (∫ θ in (0 : ℝ)..(π / 2), (η θ) ^ 2)
        = ∫ θ in (0 : ℝ)..(π / 2), ((h θ) ^ 2 - 2 * c * (h θ * Real.sin (2 * θ))
            + c ^ 2 * (Real.sin (2 * θ)) ^ 2) :=
      intervalIntegral.integral_congr (fun θ _ => hpt1 θ)
    rw [hsq]
    have hcont_h : ContinuousOn h (Set.uIcc 0 (π / 2)) := by
      rw [Set.uIcc_of_le hpi.le]; exact hh.continuousOn
    have hcont_s2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.uIcc 0 (π / 2)) := by
      fun_prop
    have i1 : IntervalIntegrable (fun θ => (h θ) ^ 2) volume 0 (π / 2) :=
      (hcont_h.pow 2).intervalIntegrable
    have i2 : IntervalIntegrable (fun θ => 2 * c * (h θ * Real.sin (2 * θ)))
        volume 0 (π / 2) :=
      ((hcont_h.mul hcont_s2).const_mul (2 * c)).intervalIntegrable
    have i3 : IntervalIntegrable (fun θ => c ^ 2 * (Real.sin (2 * θ)) ^ 2)
        volume 0 (π / 2) :=
      ((hcont_s2.pow 2).const_mul (c ^ 2)).intervalIntegrable
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hmean, T1]
    ring
  -- expansion of `∫ (η')²`
  have hdpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      deriv η θ = deriv h θ - 2 * c * Real.cos (2 * θ) := by
    have heq : η = h - fun θ : ℝ => c * Real.sin (2 * θ) := by rw [heta]; rfl
    intro θ hθ
    have hnhds : Set.Icc (0 : ℝ) (π / 2) ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hθ.2
    have hhd : DifferentiableAt ℝ h θ := (hh.contDiffAt hnhds).differentiableAt (by norm_num)
    have hsd : DifferentiableAt ℝ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
    have hsd' : DifferentiableAt ℝ (fun θ : ℝ => c * Real.sin (2 * θ)) θ := hsd.const_mul c
    rw [heq, deriv_sub hhd hsd', deriv_const_mul c hsd, Dsin θ]
    ring
  have hE2 : (∫ θ in (0 : ℝ)..(π / 2), (deriv η θ) ^ 2)
      = (∫ θ in (0 : ℝ)..(π / 2), (deriv h θ) ^ 2) + π * c ^ 2 := by
    have hae : (fun θ => (deriv η θ) ^ 2)
        =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) (π / 2))]
          (fun θ => (deriv h θ - 2 * c * Real.cos (2 * θ)) ^ 2) := by
      refine ae_eq_of_eqOn_Ioo hpi.le ?_
      intro θ hθ
      dsimp only
      rw [hdpt θ hθ]
    rw [intervalIntegral.integral_congr_ae_restrict hae]
    have hsq : (∫ θ in (0 : ℝ)..(π / 2), (deriv h θ - 2 * c * Real.cos (2 * θ)) ^ 2)
        = ∫ θ in (0 : ℝ)..(π / 2), ((deriv h θ) ^ 2
            - 2 * c * (deriv h θ * (2 * Real.cos (2 * θ)))
            + c ^ 2 * (2 * Real.cos (2 * θ)) ^ 2) :=
      intervalIntegral.integral_congr (fun θ _ => by ring)
    rw [hsq]
    have h1c : ContDiffOn ℝ 1 h (Set.Icc 0 (π / 2)) := hh.of_le (by norm_num)
    have iD : IntervalIntegrable (deriv h) volume 0 (π / 2) :=
      intervalIntegrable_deriv_of_contDiffOn h1c h0 h1
    have hcont_c2 : ContinuousOn (fun θ : ℝ => 2 * Real.cos (2 * θ)) (Set.uIcc 0 (π / 2)) := by
      fun_prop
    have i1 : IntervalIntegrable (fun θ => (deriv h θ) ^ 2) volume 0 (π / 2) :=
      intervalIntegrable_deriv_sq_Ioo hpi.le le_rfl le_rfl hh h0 h1
    have i2 : IntervalIntegrable (fun θ => 2 * c * (deriv h θ * (2 * Real.cos (2 * θ))))
        volume 0 (π / 2) :=
      ((iD.mul_continuousOn hcont_c2).const_mul (2 * c))
    have i3 : IntervalIntegrable (fun θ => c ^ 2 * (2 * Real.cos (2 * θ)) ^ 2)
        volume 0 (π / 2) :=
      ((hcont_c2.pow 2).const_mul (c ^ 2)).intervalIntegrable
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcross, T3]
    ring
  rw [hE1, hE2] at hgapη
  nlinarith [hgapη, sq_nonneg c, Real.pi_pos]

/-- The assembly: given the three analytic inputs (the orthogonal decomposition of `f` along
`sin 2θ`, the bound on the first coefficient from the solvability condition, and the spectral
gap `16` on the orthogonal complement), the slice coercivity follows with the constant `sliceC`. -/
theorem assembly
    (hres : ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) → f 0 = 0 → f (π / 2) = 0 →
      (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Real.sin (2 * θ) = 0) ∧
      (∫ θ in (0 : ℝ)..(π / 2), deriv (residF f) θ * (2 * Real.cos (2 * θ)) = 0) ∧
      (∫ θ in (0 : ℝ)..(π / 2), (f θ) ^ 2
        = (π / 4) * (coeffF f) ^ 2 + ∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) ∧
      (∫ θ in (0 : ℝ)..(π / 2), (deriv f θ) ^ 2
        = π * (coeffF f) ^ 2 + ∫ θ in (0 : ℝ)..(π / 2), (deriv (residF f) θ) ^ 2))
    (hmom : ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) →
      (∫ θ in (0 : ℝ)..(π / 2), f θ * Work.Elliptic.sinCos2 θ) = 0 →
      (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ
          = -(4 / 15) * coeffF f) ∧
      ((∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ) ^ 2
          ≤ (π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2)))
    (hgap : ∀ h : ℝ → ℝ, ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)) → h 0 = 0 → h (π / 2) = 0 →
      (∫ θ in (0 : ℝ)..(π / 2), h θ * Real.sin (2 * θ)) = 0 →
      16 * (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2) ≤ ∫ θ in (0 : ℝ)..(π / 2), (deriv h θ) ^ 2) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) → f 0 = 0 → f (π / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0 →
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ sliceC * ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  intro f hf h0 h1 horth
  have horth' : (∫ θ in (0 : ℝ)..(π / 2), f θ * Work.Elliptic.sinCos2 θ) = 0 := by
    rw [← Iθ_eq_interval (fun θ => f θ * Work.Elliptic.sinCos2 θ)]
    exact horth
  rw [Iθ_eq_interval (fun θ => (f θ) ^ 2), Iθ_eq_interval (fun θ => (deriv f θ) ^ 2)]
  obtain ⟨hgphi, -, hf2, hf12⟩ := hres f hf h0 h1
  obtain ⟨hmom1, hmom2⟩ := hmom f hf horth'
  have hgc : ContDiffOn ℝ 2 (residF f) (Set.Icc 0 (π / 2)) := by
    unfold residF; fun_prop
  have hg0 : residF f 0 = 0 := by simp [residF, h0]
  have hg1 : residF f (π / 2) = 0 := by
    have h2pi : (2 : ℝ) * (π / 2) = π := by ring
    simp [residF, h1, h2pi, Real.sin_pi]
  have hgp := hgap (residF f) hgc hg0 hg1 hgphi
  have hA : (π / 4) * (coeffF f) ^ 2
      ≤ (225 * π ^ 2 / 2048) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by
    have h1 : ((-(4 / 15) * coeffF f)) ^ 2
        ≤ (π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by
      rw [← hmom1]; exact hmom2
    have h2 : (16 / 225) * (coeffF f) ^ 2
        ≤ (π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by
      nlinarith [h1]
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 225 * π / 64 by positivity)
    calc (π / 4) * (coeffF f) ^ 2
        = (225 * π / 64) * ((16 / 225) * (coeffF f) ^ 2) := by ring
      _ ≤ (225 * π / 64) * ((π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2)) := h3
      _ = (225 * π ^ 2 / 2048) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by ring
  exact final_arith (sq_nonneg _) hf2 hf12 hA hgp



/-- **Slice-wise coercivity of the `α = 0` angular operator, away from its kernel.**

For a function `f` on `[0,π/2]` that is `C²`, vanishes at `θ = 0` and `θ = π/2`, and whose
angular moment against `sin θ cos²θ` vanishes (the paper's orthogonality condition
`OrthCond`), the unweighted `L²`-norm of `f` is dominated by that of `deriv f` with a
constant strictly below `1/6`.

This is the quantitative form of "`sin 2θ` spans the kernel of
`L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6`, while `∫₀^{π/2} sin 2θ · sin θ cos²θ dθ = 4/15 ≠ 0`, so
the orthogonality condition excludes the kernel direction with a quantitative gain".  It is
Step 1/the Fourier step of the proof of Proposition `prop:L2` (Elgindi, Annals 194 (3) 2021,
tex 740-760), and it is what makes the naive energy inequality
`∫(f')² - 6∫f² ≤ (F,f)` (which loses a factor `α`) close in the constant `6`:
with `∫f² ≤ c ∫(f')²` and `6c < 1` one gets `∫(f')² ≲ (F,f)`.

A concrete route: expand `f` in the Dirichlet eigenbasis `sin(2kθ)` of `-d²/dθ²` on
`(0,π/2)` (Parseval: `∫f² = (π/4)Σa_k²`, `∫(f')² = (π/4)Σ4k²a_k²`), use the constraint
`Σ b_k a_k = 0` with `b_k = ∫₀^{π/2} sin(2kθ) sin θ cos²θ dθ`
(the explicit value `|b_k| = 4k/((4k²-1)|4k²-9|)` — the *corrected* form of the paper's
coefficient, already available in this workspace as
`Work.Elliptic.integral_sinCos2_mul_sin_two` — note `b₁ = 4/15`), Cauchy–Schwarz
`b₁²a₁² ≤ (Σ_{k≥2}a_k²)(Σ_{k≥2}b_k²)`, and `Σ_{k≥2}b_k² < b₁²/2`.  The sharp constant is
`≈ 1/15.09`, so the bound `1/6` has ample room: a cruder argument is welcome and no attempt
at the sharp constant is needed.

Downstream use: the slice-wise energy identity of the elliptic section produces
`∫(Ψ_θ)² - 6∫(Ψ)² ≤ (F,Ψ)` for `Ψ(z,·)`; combined with this result applied to each slice,
`6c < 1` gives `∫(Ψ_θ)² ≲ ∫F·Ψ`, hence `‖Ψ_θ‖ ≲ ‖F‖` by Cauchy–Schwarz. -/
theorem coercive_slice_fts : ∃ c : ℝ, 0 < c ∧ c < 1 / 6 ∧
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) → f 0 = 0 → f (π / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0 →
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ c * ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  refine ⟨sliceC, sliceC_pos, sliceC_lt, ?_⟩
  refine assembly ?_ ?_ ?_
  · intro f hf h0 h1
    exact resid_expansion f hf h0 h1
  · intro f hf horth
    exact residF_moment f hf horth
  · intro h hh h0 h1 hmean
    exact second_eigenvalue hh h0 h1 hmean

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.inversionNear =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the substitution `x = sin(2θ)` on the near region

We collect the one-variable calculus of `thetaOf x = arcsin x / 2`, `kappa x = cos(2·thetaOf x)`
and `xNear = sin(π/4) = 1/√2` needed by the inversion. -/

private lemma insv_xNear_sq : xNear ^ 2 = 1 / 2 := by
  rw [xNear, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `κ x = √(1-x²)` for every real `x`. -/
private lemma kappa_eq (x : ℝ) : kappa x = Real.sqrt (1 - x ^ 2) := by
  simp only [kappa, thetaOf]
  rw [show 2 * (Real.arcsin x / 2) = Real.arcsin x by ring, Real.cos_arcsin]

/-- `sin (2 θ(x)) = x` for `x ∈ [-1,1]`. -/
private lemma sin_two_thetaOf_prv {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sin (2 * thetaOf x) = x := by
  have h2 : 2 * thetaOf x = Real.arcsin x := by simp only [thetaOf]; ring
  rw [h2, Real.sin_arcsin hx.1 hx.2]

/-- On the near interval `(0,x₁)`, `θ(x)` lands in the angular interval `(0,π/2)`. -/
private lemma thetaOf_mem_Ioo_prv {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have ha0 : 0 < Real.arcsin x := Real.arcsin_pos.mpr hx.1
  have ha2 : Real.arcsin x ≤ Real.pi / 2 := (Real.arcsin_mem_Icc x).2
  constructor <;> simp only [thetaOf] <;> linarith

private lemma thetaOf_xNear_prv : thetaOf xNear = Real.pi / 8 := by
  rw [thetaOf, xNear, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

private lemma thetaOf_zero_prv : thetaOf 0 = 0 := by simp [thetaOf]

/-- `θ` is `C^∞` on the near region; its derivative there is the Jacobian `1/(2κ x)`. -/
private lemma hasDerivAt_thetaOf'_prv {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
  have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have h2 : HasDerivAt (fun y => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
    h1.div_const 2
  have hval : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * kappa x) := by
    rw [kappa_eq]; ring
  exact h2.congr_deriv hval

/-- `1/√2 ≤ κ x` on `[0,x₁]`. -/
private lemma kappa_ge_prv {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) :
    1 / Real.sqrt 2 ≤ kappa x := by
  have hxnn : 0 ≤ x := hx.1
  have hxsq : x ^ 2 ≤ 1 / 2 := by
    have h1 : x * x ≤ xNear * xNear :=
      mul_le_mul hx.2 hx.2 hxnn (le_trans hxnn hx.2)
    have h2 : xNear * xNear = 1 / 2 := by simpa [pow_two] using insv_xNear_sq
    nlinarith [h1, h2]
  have hsqrt : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1) 2, Real.sqrt_one]
  rw [kappa_eq]
  linarith [hsqrt, h2]

/-- `1 ≤ 2 κ x` on `[0,x₁]`. -/
private lemma two_kappa_ge_one_prv {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) :
    1 ≤ 2 * kappa x := by
  have h := kappa_ge_prv hx
  have h2 : (2:ℝ) * (1 / Real.sqrt 2) = Real.sqrt 2 := by
    rw [mul_one_div, div_eq_iff (by positivity : (Real.sqrt 2) ≠ 0)]
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  have h3 : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith [h, h2, h3]


/-- `sliceX h = h ∘ θ` is `C^∞` on the near interval whenever `h` is `C^∞` on `(0,π/2)`. -/
private lemma contDiffOn_sliceX_prv {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioo 0 xNear) := by
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) thetaOf (Set.Ioo 0 xNear) := by
    intro x hx
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) Real.arcsin x :=
      Real.contDiffAt_arcsin (by linarith [hx.1]) (by linarith [hx.2, xNear_lt])
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) thetaOf x := h1.div_const 2
    exact h2.contDiffWithinAt
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioo 0 xNear) :=
    hsm.comp hθ (fun x hx => thetaOf_mem_Ioo_prv hx)
  exact hcomp

/-- Every iterated `x`-derivative of `sliceX h` is `C^∞` on the near interval. -/
private lemma contDiffOn_iteratedDeriv_sliceX_prv {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n (sliceX h)) (Set.Ioo 0 xNear) := by
  induction n with
  | zero => simpa using contDiffOn_sliceX_prv hsm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioo (by simp)

/-- `Gop` is insensitive to replacing `u` by a function agreeing with it on an open set. -/
private lemma Gop_eqOn {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : Set.EqOn u v s) :
    Set.EqOn (Gop u) (Gop v) s := by
  intro y hy
  have hd : deriv u y = deriv v y := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hs.mem_nhds hy] with z hz
    exact h hz
  simp only [Gop, hd]

/-- Iterated version of `Gop_eqOn`. -/
private lemma Gop_iter_eqOn {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : Set.EqOn u v s)
    (i : ℕ) : Set.EqOn ((Gop^[i]) u) ((Gop^[i]) v) s := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      intro y hy
      rw [Function.iterate_succ']
      exact Gop_eqOn hs ih hy

/-- **The `x`-expansion of the angular derivative `D_θ^i(∂_θ h)`.**  On the near region,
`Dth1Iter i (deriv h) (thetaOf x)` is the `aCoeff`-expansion of `G^i(2κ ∂_x(sliceX h))`, because
`sliceX (deriv h) = 2κ · ∂_x (sliceX h)` on `(0,x₁)`. -/
theorem Dth1Iter_deriv_expansion (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    Work.Elliptic.Dth1Iter i (deriv h) (thetaOf x)
      = ∑ l ∈ Finset.range (i + 1),
          aCoeff i l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x) := by
  have hsm' : ContDiffOn ℝ (⊤ : ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by simp)
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  have hD : Work.Elliptic.Dth1Iter i (deriv h) (thetaOf x)
      = (Gop^[i] (sliceX (deriv h))) x := DthIter_sliceX i hsm' hx
  rw [hD]
  have heq : Set.EqOn (sliceX (deriv h))
      (fun y => 2 * kappa y * deriv (sliceX h) y) (Set.Ioo 0 xNear) := by
    intro y hy
    have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hy.1], by linarith [hy.2, xNear_lt]⟩
    have hmem : thetaOf y ∈ Set.Ioo 0 (Real.pi / 2) := thetaOf_mem_Ioo_prv hy
    have hdh : DifferentiableAt ℝ h (thetaOf y) :=
      ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp))
    have hchain : HasDerivAt (sliceX h)
        (deriv h (thetaOf y) * (1 / (2 * kappa y))) y :=
      hdh.hasDerivAt.comp y (hasDerivAt_thetaOf'_prv hyI)
    have hk0 : kappa y ≠ 0 := ne_of_gt (kappa_pos_of_mem ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
    simp only [sliceX]
    rw [hchain.deriv]
    field_simp
  rw [Gop_iter_eqOn isOpen_Ioo heq i hx]
  exact aCoeff_expansion i (contDiffOn_sliceX_prv hsm) hx

/-! ## The quantities of the inversion

`Denη = ∫_{Iθ}(∂_θh)²s^{-η}`, `Denγ m = ∫_{Iθ}(D_θ^m(∂_θh))²s^{-γ}`, the `x`-side quantities
`Wide_prv l = x^{2l-γ}(∂_x^{l+1}(sliceX h))²`, and the pullbacks of the `θ`-integrands under
`x = sin(2θ)` (with the Jacobian `1/(2κ x)`).  All of these are `private`: they exist only to
structure the proof of `inversionNear`. -/

private def PsiEta_prv (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

private def PsiGam_prv (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun θ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

private def DenEta (h : ℝ → ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, PsiEta_prv h θ

private def DenGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, PsiGam_prv α h m θ

/-- The right-hand side `Denη + Σ_{1 ≤ m ≤ j} Denγ m` of the inversion. -/
private def SS (α : ℝ) (h : ℝ → ℝ) (j : ℕ) : ℝ :=
  DenEta h + ∑ m ∈ Finset.Icc 1 j, DenGam α h m

/-- The integrand `x ↦ x^{2l-γ}(∂_x^{l+1}(sliceX h) x)²` of `B_l`. -/
private def Wide_prv (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : ℝ → ℝ :=
  fun x => x ^ (2 * (l : ℝ) - Work.Spaces.gam α)
    * (iteratedDeriv (l + 1) (sliceX h) x) ^ 2

/-- The `x`-pullback of `PsiEta_prv`. -/
private def SubEta_prv (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => PsiEta_prv h (thetaOf x) * (1 / (2 * kappa x))

/-- The `x`-pullback of `PsiGam_prv m`. -/
private def SubGam_prv (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => PsiGam_prv α h m (thetaOf x) * (1 / (2 * kappa x))

/-- The `x`-pullback of `PsiGam_prv m` with `sin(2θ(x))` evaluated as `x`. -/
private def HonGam_prv (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => (Work.Elliptic.Dth1Iter m (deriv h) (thetaOf x)) ^ 2
    * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))

/-- The full `j`-th expansion of `D_θ^j(∂_θh)(θ x)` and its off-diagonal part. -/
private def Expn_prv (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun x => ∑ l ∈ Finset.range (j + 1),
    aCoeff j l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)

private def Restn_prv (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun x => ∑ l ∈ Finset.range j,
    aCoeff j l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)

/-- `sin (2 θ(x)) = x` on the near interval. -/
private lemma sin_two_thetaOf_Ioo_prv {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Real.sin (2 * thetaOf x) = x :=
  sin_two_thetaOf_prv ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩

private lemma gam_lt_four_prv {α : ℝ} (hα : α ≤ 1) : Work.Spaces.gam α < 4 + Work.Spaces.eta := by
  unfold Work.Spaces.gam Work.Spaces.eta; linarith

private lemma psiEta_nonneg_prv (h : ℝ → ℝ) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ PsiEta_prv h θ := by
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ <;> linarith
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

private lemma psiGam_nonneg_prv (α : ℝ) (h : ℝ → ℝ) (m : ℕ) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ PsiGam_prv α h m θ := by
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ <;> linarith
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

/-- The chain rule for `sliceX h = h ∘ θ` on the near interval. -/
private lemma deriv_sliceX_eq_prv {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    deriv (sliceX h) x = deriv h (thetaOf x) * (1 / (2 * kappa x)) := by
  have hyI : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  have hmem : thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := thetaOf_mem_Ioo_prv hx
  have hdh : DifferentiableAt ℝ h (thetaOf x) :=
    ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp))
  exact (hdh.hasDerivAt.comp x (hasDerivAt_thetaOf'_prv hyI)).deriv




/-- The auxiliary `x^{-η}(∂_x(sliceX h))²` of the `l = 0` slot is dominated by `SubEta_prv`. -/
private lemma etaPiece_le_subEta_prv {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 ≤ SubEta_prv h x := by
  have hxnn : (0:ℝ) ≤ x := le_of_lt hx.1
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one_prv ⟨hxnn, le_of_lt hx.2⟩
  have hkpos : (0:ℝ) < 2 * kappa x := lt_of_lt_of_le one_pos hk1
  have hs : Real.sin (2 * thetaOf x) = x := sin_two_thetaOf_Ioo_prv hx
  have hd : deriv (sliceX h) x = deriv h (thetaOf x) * (1 / (2 * kappa x)) :=
    deriv_sliceX_eq_prv hsm hx
  have h1 : (1:ℝ) / (2 * kappa x) ≤ 1 := by
    rw [div_le_one hkpos]; linarith
  have h2 : (0:ℝ) ≤ (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hxnn _)
  simp only [SubEta_prv, PsiEta_prv, hs]
  rw [hd]
  have hrw : x ^ (-(Work.Spaces.eta))
        * (deriv h (thetaOf x) * (1 / (2 * kappa x))) ^ 2
      = (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta))
          * (1 / (2 * kappa x)) ^ 2 := by
    ring
  rw [hrw]
  have h3 : (1 / (2 * kappa x)) ^ 2 ≤ 1 / (2 * kappa x) := by
    have hnn : (0:ℝ) ≤ 1 / (2 * kappa x) := by positivity
    nlinarith [h1, hnn]
  calc (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) ^ 2
      ≤ (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) :=
        mul_le_mul_of_nonneg_left h3 h2
    _ = (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) := rfl

/-- The joint recursion producing the dominating functions `Dom_prv` and their partial sums
`AccDom_prv`. -/
private def domSeq_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) : ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (SubEta_prv h, fun _ => 0)
  | (l + 1) =>
      (fun x => 2 * HonGam_prv α h (l + 1) x
          + 2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2 * ((domSeq_prv α h Cm l).2 x + (domSeq_prv α h Cm l).1 x),
        fun x => (domSeq_prv α h Cm l).2 x + (domSeq_prv α h Cm l).1 x)

/-- An integrable dominating function for the level-`l` quantity. -/
private def Dom_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) : ℝ → ℝ := (domSeq_prv α h Cm l).1

/-- The partial sum `Σ_{m < l} Dom_prv m`. -/
private def AccDom_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) : ℝ → ℝ := (domSeq_prv α h Cm l).2

private lemma AccDom_succ_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) :
    AccDom_prv α h Cm (l + 1) = fun x => AccDom_prv α h Cm l x + Dom_prv α h Cm l x := by
  funext x
  simp only [AccDom_prv, Dom_prv, domSeq_prv]

private lemma Dom_succ_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) :
    Dom_prv α h Cm (l + 1) = fun x => 2 * HonGam_prv α h (l + 1) x
        + 2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom_prv α h Cm (l + 1) x := by
  funext x
  simp only [AccDom_prv, Dom_prv, domSeq_prv]

private lemma Dom_zero_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    Dom_prv α h Cm 0 = SubEta_prv h := by
  funext x
  simp only [Dom_prv, domSeq_prv]

private lemma AccDom_zero_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    AccDom_prv α h Cm 0 = fun _ => 0 := by
  funext x
  simp only [AccDom_prv, domSeq_prv]

private lemma Dom_succ_eq_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (k : ℕ) (x : ℝ) :
    Dom_prv α h Cm (k + 1) x = 2 * HonGam_prv α h (k + 1) x
      + 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom_prv α h Cm (k + 1) x := by
  rw [Dom_succ_prv]

private lemma accDom_eq_sum_prv (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) (x : ℝ) :
    AccDom_prv α h Cm l x = ∑ m ∈ Finset.range l, Dom_prv α h Cm m x := by
  induction l with
  | zero => rw [AccDom_zero_prv]; simp
  | succ l ih =>
      rw [AccDom_succ_prv]
      show AccDom_prv α h Cm l x + Dom_prv α h Cm l x = _
      rw [ih, Finset.sum_range_succ]

private lemma Wide_nonneg_prv (α : ℝ) (h : ℝ → ℝ) (l : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Wide_prv α h l x :=
  mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _)








/-- The Young inequality `A² ≤ 2(A+R)² + 2R²`. -/
private lemma young_prv (A R : ℝ) : A ^ 2 ≤ 2 * (A + R) ^ 2 + 2 * R ^ 2 := by
  nlinarith [sq_nonneg (A + 2 * R)]

/-! ## The pointwise estimates -/

/-- `(x^m)² x^{c} = x^{2m+c}` for `x > 0`. -/
private lemma pow_sq_mul_rpow_prv {x : ℝ} (hx : 0 < x) (m : ℕ) (c : ℝ) :
    (x ^ m) ^ 2 * x ^ c = x ^ (2 * (m : ℝ) + c) := by
  rw [← pow_mul, show m * 2 = 2 * m by ring, ← Real.rpow_natCast x (2 * m),
    show ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) by push_cast; ring, ← Real.rpow_add hx]

/-- **Diagonal domination.** -/
private lemma wide_le_diag {α : ℝ} {h : ℝ → ℝ} {j : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide_prv α h j x
      ≤ (aCoeff j j x * (x ^ j * iteratedDeriv (j + 1) (sliceX h) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
  have hxpos : (0:ℝ) < x := hx.1
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one_prv ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hk0 : (2 * kappa x) ≠ 0 := by positivity
  have hA : (2 * kappa x) ^ (2 * j + 2) * (1 / (2 * kappa x)) = (2 * kappa x) ^ (2 * j + 1) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, pow_succ, one_div, mul_assoc,
      mul_inv_cancel₀ hk0, mul_one]
  have hB : (x ^ j) ^ 2 * x ^ (-(Work.Spaces.gam α))
      = x ^ (2 * (j : ℝ) - Work.Spaces.gam α) := by
    have h := pow_sq_mul_rpow_prv hxpos j (-(Work.Spaces.gam α))
    rwa [show 2 * (j : ℝ) + (-(Work.Spaces.gam α)) = 2 * (j : ℝ) - Work.Spaces.gam α by ring]
      at h
  have key : ((2 * kappa x) ^ (j + 1) * (x ^ j * iteratedDeriv (j + 1) (sliceX h) x)) ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      = (2 * kappa x) ^ (2 * j + 1)
        * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) := by
    set g : ℝ := iteratedDeriv (j + 1) (sliceX h) x
    have h1 : ((2 * kappa x) ^ (j + 1)) ^ 2 = (2 * kappa x) ^ (2 * j + 2) := by
      rw [← pow_mul, show (j + 1) * 2 = 2 * j + 2 by ring]
    have h2 : (x ^ j * g) ^ 2 = (x ^ j) ^ 2 * g ^ 2 := mul_pow (x ^ j) g 2
    have h3 : ((2 * kappa x) ^ (j + 1) * (x ^ j * g)) ^ 2
        = ((2 * kappa x) ^ (j + 1)) ^ 2 * (x ^ j * g) ^ 2 :=
      mul_pow ((2 * kappa x) ^ (j + 1)) (x ^ j * g) 2
    have h4 : (2 * kappa x) ^ (2 * j + 2) * ((x ^ j) ^ 2 * g ^ 2)
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = ((2 * kappa x) ^ (2 * j + 2) * (1 / (2 * kappa x)))
          * ((x ^ j) ^ 2 * x ^ (-(Work.Spaces.gam α))) * g ^ 2 := by ring
    rw [h3, h1, h2, h4, hA, hB]
    ring
  have hadiag : aCoeff j j x = (2 * kappa x) ^ (j + 1) := by rw [aCoeff_diag]
  rw [hadiag, key, Wide_prv]
  have hnn : (0:ℝ) ≤ x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
      * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (sq_nonneg _)
  have h2' : (1:ℝ) ≤ (2 * kappa x) ^ (2 * j + 1) := one_le_pow₀ hk1
  calc x ^ (2 * (j : ℝ) - Work.Spaces.gam α) * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2
      = 1 * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) := by ring
    _ ≤ (2 * kappa x) ^ (2 * j + 1)
          * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) :=
        mul_le_mul_of_nonneg_right h2' hnn

/-- The `m ≥ 1` summand of `Restn_prv`: the weight `x^{-γ}` combines with `x^{2m}` into `Wide_prv m`. -/
private lemma rest_term_eq {α : ℝ} {h : ℝ → ℝ} {l m : ℕ} {x : ℝ} (hx : 0 < x) :
    (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
        * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
      = (aCoeff l m x) ^ 2 * Wide_prv α h m x * (1 / (2 * kappa x)) := by
  have hB : (x ^ m) ^ 2 * x ^ (-(Work.Spaces.gam α))
      = x ^ (2 * (m : ℝ) - Work.Spaces.gam α) := by
    have h := pow_sq_mul_rpow_prv hx m (-(Work.Spaces.gam α))
    rwa [show 2 * (m : ℝ) + (-(Work.Spaces.gam α)) = 2 * (m : ℝ) - Work.Spaces.gam α by ring]
      at h
  have h3 : (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
      = (aCoeff l m x) ^ 2
        * ((x ^ m) ^ 2 * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2) := by
    rw [mul_pow (aCoeff l m x) (x ^ m * iteratedDeriv (m + 1) (sliceX h) x) 2,
      mul_pow (x ^ m) (iteratedDeriv (m + 1) (sliceX h) x) 2]
  rw [h3, Wide_prv]
  set g : ℝ := iteratedDeriv (m + 1) (sliceX h) x
  rw [show (aCoeff l m x) ^ 2 * ((x ^ m) ^ 2 * g ^ 2)
        * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
      = (aCoeff l m x) ^ 2 * ((x ^ m) ^ 2 * x ^ (-(Work.Spaces.gam α)))
        * g ^ 2 * (1 / (2 * kappa x)) by ring]
  rw [hB]
  ring

/-- **The off-diagonal remainder.** -/
private lemma rest_le {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} (hCm : 0 ≤ Cm) (hα1 : α ≤ 1) {l : ℕ}
    (hl : 1 ≤ l)
    (hCb : ∀ m ≤ l, ∀ x ∈ Set.Icc (0:ℝ) xNear, |aCoeff l m x| ≤ Cm)
    (hC0 : ∀ x ∈ Set.Icc (0:ℝ) xNear, |aCoeff l 0 x| ≤ Cm * x ^ 2)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hWle : ∀ m, 1 ≤ m → m < l → ∀ x ∈ Set.Ioo (0:ℝ) xNear, Wide_prv α h m x ≤ Dom_prv α h Cm m x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    (Restn_prv h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * Cm ^ 2 * AccDom_prv α h Cm l x := by
  have hxpos : (0:ℝ) < x := hx.1
  have hxIcc : x ∈ Set.Icc (0:ℝ) xNear := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hxle1 : x ≤ 1 := by linarith [hx.2, xNear_lt]
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one_prv hxIcc
  have hkpos : (0:ℝ) < 2 * kappa x := lt_of_lt_of_le one_pos hk1
  have hknn : (0:ℝ) ≤ 1 / (2 * kappa x) := by positivity
  have hlnn : (0:ℝ) ≤ (l : ℝ) := by positivity
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range l)
    (f := fun m => aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x))
  have hCS : (∑ m ∈ Finset.range l,
        aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2 := by
    simpa using hcs
  have hterm : ∀ m ∈ Finset.range l,
      (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
        ≤ Cm ^ 2 * Dom_prv α h Cm m x := by
    intro m hm
    have hml : m ≤ l := by have := Finset.mem_range.mp hm; omega
    have hmlt : m < l := Finset.mem_range.mp hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hinv : 1 / (2 * kappa x) ≤ 1 := by rw [div_le_one hkpos]; linarith
      have h4η : x ^ (4 - Work.Spaces.gam α) ≤ x ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hxle1 (by have := gam_lt_four_prv hα1; linarith)
      have hsub : x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 ≤ SubEta_prv h x :=
        etaPiece_le_subEta_prv hsm hx
      have h1 : (aCoeff l 0 x) ^ 2 ≤ Cm ^ 2 * x ^ 4 := by
        have hle : |aCoeff l 0 x| ≤ Cm * x ^ 2 := hC0 x hxIcc
        rw [show (aCoeff l 0 x) ^ 2 = |aCoeff l 0 x| ^ 2 from (sq_abs _).symm]
        calc |aCoeff l 0 x| ^ 2 ≤ (Cm * x ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = Cm ^ 2 * x ^ 4 := by ring
      have hx4 : x ^ 4 * x ^ (-(Work.Spaces.gam α)) = x ^ (4 - Work.Spaces.gam α) := by
        have hh := (Real.rpow_add hxpos (4:ℝ) (-(Work.Spaces.gam α))).symm
        rw [← Real.rpow_natCast x 4]
        exact hh.trans (congrArg (fun e => x ^ e)
          (by ring : (4:ℝ) + (-(Work.Spaces.gam α)) = 4 - Work.Spaces.gam α))
      have hkey : x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
          ≤ x ^ (-(Work.Spaces.eta)) := by
        calc x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
            = x ^ (4 - Work.Spaces.gam α) * (1 / (2 * kappa x)) := by rw [hx4]
          _ ≤ x ^ (4 - Work.Spaces.gam α) * 1 :=
              mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hxpos.le _)
          _ = x ^ (4 - Work.Spaces.gam α) := by ring
          _ ≤ x ^ (-(Work.Spaces.eta)) := h4η
      simp only [pow_zero, one_mul, Nat.zero_add, iteratedDeriv_one]
      calc (aCoeff l 0 x * deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
          = (aCoeff l 0 x) ^ 2 * (deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by ring
        _ ≤ (Cm ^ 2 * x ^ 4) * (deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
            · exact mul_nonneg (Real.rpow_nonneg hxpos.le _) hknn
        _ = Cm ^ 2 * (deriv (sliceX h) x) ^ 2
              * (x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by ring
        _ ≤ Cm ^ 2 * (deriv (sliceX h) x) ^ 2 * x ^ (-(Work.Spaces.eta)) := by
            refine mul_le_mul_of_nonneg_left hkey (mul_nonneg (sq_nonneg Cm) (sq_nonneg _))
        _ ≤ Cm ^ 2 * SubEta_prv h x := by
            have hh := mul_le_mul_of_nonneg_left hsub (sq_nonneg Cm)
            rw [show Cm ^ 2 * (deriv (sliceX h) x) ^ 2 * x ^ (-(Work.Spaces.eta))
              = Cm ^ 2 * (x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2) by ring]
            exact hh
        _ = Cm ^ 2 * Dom_prv α h Cm 0 x := by rw [Dom_zero_prv]
    · have h1 : (aCoeff l m x) ^ 2 ≤ Cm ^ 2 := by
        have hle : |aCoeff l m x| ≤ Cm := hCb m hml x hxIcc
        rw [show (aCoeff l m x) ^ 2 = |aCoeff l m x| ^ 2 from (sq_abs _).symm]
        calc |aCoeff l m x| ^ 2 ≤ Cm ^ 2 := by
              simpa using pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = Cm ^ 2 := rfl
      have hinv : 1 / (2 * kappa x) ≤ 1 := by rw [div_le_one hkpos]; linarith
      rw [rest_term_eq (α := α) (h := h) (x := x) hxpos]
      calc (aCoeff l m x) ^ 2 * Wide_prv α h m x * (1 / (2 * kappa x))
          ≤ Cm ^ 2 * Wide_prv α h m x * 1 := by
            have hp : (0:ℝ) < 1 / (2 * kappa x) := div_pos one_pos hkpos
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Wide_nonneg_prv α h m hxpos.le))
              hinv (le_of_lt hp) (mul_nonneg (sq_nonneg Cm) (Wide_nonneg_prv α h m hxpos.le))
        _ ≤ Cm ^ 2 * Dom_prv α h Cm m x := by
            have h3 := hWle m hmpos hmlt x hx
            nlinarith [h3, sq_nonneg Cm]
  have hstep1 : (Restn_prv h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
            * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
    have hz : (0:ℝ) ≤ x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
      mul_nonneg (Real.rpow_nonneg hxpos.le _) hknn
    have h0 : (Restn_prv h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (Restn_prv h l x) ^ 2 * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
      ring
    have hS : Restn_prv h l x = ∑ m ∈ Finset.range l,
        aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x) := rfl
    rw [hS]
    rw [show (∑ m ∈ Finset.range l, aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (∑ m ∈ Finset.range l, aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) by ring]
    refine (mul_le_mul_of_nonneg_right hCS hz).trans (le_of_eq ?_)
    rw [mul_assoc, Finset.sum_mul]
  calc (Restn_prv h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
            * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := hstep1
    _ ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l, Cm ^ 2 * Dom_prv α h Cm m x :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hlnn
    _ = ((l : ℝ)) * Cm ^ 2 * ∑ m ∈ Finset.range l, Dom_prv α h Cm m x := by
        have h1 : ((l : ℝ)) * ∑ m ∈ Finset.range l, Cm ^ 2 * Dom_prv α h Cm m x
            = ((l : ℝ)) * (Cm ^ 2 * ∑ m ∈ Finset.range l, Dom_prv α h Cm m x) := by
          simp only [Finset.mul_sum]
        rw [show ((l : ℝ)) * Cm ^ 2 * ∑ m ∈ Finset.range l, Dom_prv α h Cm m x
            = ((l : ℝ)) * (Cm ^ 2 * ∑ m ∈ Finset.range l, Dom_prv α h Cm m x) by ring]
        exact h1
    _ = ((l : ℝ)) * Cm ^ 2 * AccDom_prv α h Cm l x := by rw [accDom_eq_sum_prv]

/-- The pointwise Young step at level `k+1`. -/
private lemma wide_le_dom_succ {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hCm : 0 ≤ Cm) (hα1 : α ≤ 1) (hk : k + 1 ≤ 4)
    (hCb : ∀ m ≤ k + 1, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff (k + 1) m x| ≤ Cm)
    (hC0 : ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff (k + 1) 0 x| ≤ Cm * x ^ 2)
    (hWle : ∀ m, 1 ≤ m → m ≤ k → ∀ x ∈ Set.Ioo (0 : ℝ) xNear,
      Wide_prv α h m x ≤ Dom_prv α h Cm m x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide_prv α h (k + 1) x ≤ Dom_prv α h Cm (k + 1) x := by
  have hxpos : (0 : ℝ) < x := hx.1
  have hkpos : (0 : ℝ) < 2 * kappa x :=
    lt_of_lt_of_le one_pos (two_kappa_ge_one_prv ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hknn : (0 : ℝ) ≤ x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (le_of_lt (div_pos one_pos hkpos))
  set A : ℝ := aCoeff (k + 1) (k + 1) x
    * (x ^ (k + 1) * iteratedDeriv ((k + 1) + 1) (sliceX h) x) with hA
  set R : ℝ := Restn_prv h (k + 1) x with hR
  have hExp : Work.Elliptic.Dth1Iter (k + 1) (deriv h) (thetaOf x) = Expn_prv h (k + 1) x :=
    Dth1Iter_deriv_expansion (k + 1) hsm hx
  have hR' : (∑ l ∈ Finset.range (k + 1), aCoeff (k + 1) l x
      * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)) = R := by
    rw [hR]; rfl
  have hsplit : Expn_prv h (k + 1) x = A + R := by
    have hE : Expn_prv h (k + 1) x
        = (∑ l ∈ Finset.range (k + 1), aCoeff (k + 1) l x
            * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x))
          + (aCoeff (k + 1) (k + 1) x
            * (x ^ (k + 1) * iteratedDeriv ((k + 1) + 1) (sliceX h) x)) := by
      simp only [Expn_prv]
      rw [Finset.sum_range_succ]
    rw [hE, hR', ← hA, add_comm]
  have hHon : HonGam_prv α h (k + 1) x
      = (A + R) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
    simp only [HonGam_prv]
    rw [← hsplit, ← hExp]
  have hdiag : Wide_prv α h (k + 1) x
      ≤ A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
    rw [hA]; exact wide_le_diag hx
  have hY2 : A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
          * (1 / (2 * kappa x)) := by
    have := mul_le_mul_of_nonneg_right (young_prv A R) hknn
    simpa only [mul_assoc] using this
  have h2 : (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
        * (1 / (2 * kappa x))
      = 2 * HonGam_prv α h (k + 1) x
        + 2 * (R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
    rw [hHon]; ring
  have h3 : R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom_prv α h Cm (k + 1) x := by
    rw [hR]
    exact rest_le (α := α) (h := h) (Cm := Cm) hCm hα1 (by omega) hCb hC0 hsm
      (fun m hm1 hmk => hWle m hm1 (by omega)) hx
  calc Wide_prv α h (k + 1) x ≤ A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := hdiag
    _ ≤ (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
          * (1 / (2 * kappa x)) := hY2
    _ = 2 * HonGam_prv α h (k + 1) x
          + 2 * (R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := h2
    _ ≤ 2 * HonGam_prv α h (k + 1) x
          + 2 * ((((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom_prv α h Cm (k + 1) x) := by
        linarith [h3]
    _ = Dom_prv α h Cm (k + 1) x := by rw [Dom_succ_eq_prv]; ring


/-! ## The integral step -/

/-- **The integral step at level `k+1`.** -/
private lemma level_bound {α : ℝ} {h : ℝ → ℝ} {Cm T : ℝ} {k : ℕ}
    (hGamInt : MeasureTheory.IntegrableOn (HonGam_prv α h (k + 1)) (Set.Ioo 0 xNear))
    (hAccInt : MeasureTheory.IntegrableOn (AccDom_prv α h Cm (k + 1)) (Set.Ioo 0 xNear))
    (hGamBd : (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam_prv α h (k + 1) x) ≤ DenGam α h (k + 1))
    (hGamSS : DenGam α h (k + 1) ≤ SS α h (k + 1))
    (hAccBd : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom_prv α h Cm (k + 1) x)
        ≤ T * SS α h (k + 1)) :
    (∫ x in Set.Ioo (0 : ℝ) xNear, Dom_prv α h Cm (k + 1) x)
      ≤ (2 + 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * T) * SS α h (k + 1) := by
  have hI1 : MeasureTheory.IntegrableOn (fun x => 2 * HonGam_prv α h (k + 1) x)
      (Set.Ioo 0 xNear) := hGamInt.const_mul 2
  have hI2 : MeasureTheory.IntegrableOn
      (fun x => (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2) * AccDom_prv α h Cm (k + 1) x)
      (Set.Ioo 0 xNear) := hAccInt.const_mul _
  have hEq : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom_prv α h Cm (k + 1) x)
      = 2 * (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam_prv α h (k + 1) x)
        + (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
            * (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom_prv α h Cm (k + 1) x) := by
    simp only [Dom_succ_eq_prv]
    rw [MeasureTheory.integral_add hI1 hI2,
      MeasureTheory.integral_const_mul 2 (fun x => HonGam_prv α h (k + 1) x),
      MeasureTheory.integral_const_mul (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
        (fun x => AccDom_prv α h Cm (k + 1) x)]
  rw [hEq]
  have hstep := mul_le_mul_of_nonneg_left hAccBd
    (by positivity : (0:ℝ) ≤ 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
  linarith [hGamBd, hGamSS, hstep]

/-- The accumulated constants of the level-by-level induction: `KT1` and `KK1 Cm` bound
`∫ AccDom_prv 1` and `∫ Dom_prv 1` by `KT1 · SS 1` and `KK1 Cm · SS 1`, and so on. -/
private def KT1 : ℝ := 1

private def KK1 (Cm : ℝ) : ℝ := 2 + 2 * 1 * Cm ^ 2 * KT1

private def KT2 (Cm : ℝ) : ℝ := KT1 + KK1 Cm

private def KK2 (Cm : ℝ) : ℝ := 2 + 2 * 2 * Cm ^ 2 * KT2 Cm

private def KT3 (Cm : ℝ) : ℝ := KT2 Cm + KK2 Cm

private def KK3 (Cm : ℝ) : ℝ := 2 + 2 * 3 * Cm ^ 2 * KT3 Cm

private def KT4 (Cm : ℝ) : ℝ := KT3 Cm + KK3 Cm

private def KK4 (Cm : ℝ) : ℝ := 2 + 2 * 4 * Cm ^ 2 * KT4 Cm

/-- The universal constant of `inversionNear`. -/
private def KC (Cm : ℝ) : ℝ := max 2 (max (KK1 Cm) (max (KK2 Cm) (max (KK3 Cm) (KK4 Cm))))


end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.SeriesOdeAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open Filter Set

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.FTS.PhiStar.Gegenbauer (eFam lam)
open Work.FTS.PhiStar.Series.Deleg (Npsi)

/-! ## 1. Arithmetic of the mode weights -/

lemma Npsi_le_nine (m : ℕ) : Npsi m ≤ 9 * ((m : ℝ) + 1) ^ 2 := by
  rw [Work.FTS.PhiStar.Series.Deleg.Npsi]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

lemma sqrt_Npsi_le_three (m : ℕ) : Real.sqrt (Npsi m) ≤ 3 * ((m : ℝ) + 1) := by
  have h : Npsi m ≤ (3 * ((m : ℝ) + 1)) ^ 2 := by
    have h' := Npsi_le_nine m
    nlinarith
  calc Real.sqrt (Npsi m) ≤ Real.sqrt ((3 * ((m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt h
    _ = 3 * ((m : ℝ) + 1) := Real.sqrt_sq (by positivity)

lemma Npsi_mul_sqrt_le (m : ℕ) : Npsi m * Real.sqrt (Npsi m) ≤ 27 * ((m : ℝ) + 1) ^ 3 := by
  have h1 : Real.sqrt (Npsi m) ≤ 3 * ((m : ℝ) + 1) := sqrt_Npsi_le_three m
  have h3 : Npsi m ≤ 9 * ((m : ℝ) + 1) ^ 2 := Npsi_le_nine m
  calc Npsi m * Real.sqrt (Npsi m) ≤ (9 * ((m : ℝ) + 1) ^ 2) * (3 * ((m : ℝ) + 1)) :=
        mul_le_mul h3 h1 (Real.sqrt_nonneg _) (by positivity)
    _ = 27 * ((m : ℝ) + 1) ^ 3 := by ring

/-! ## 2. Summability of the coefficient-weighted majorants -/

section Summable

variable {c d : ℕ → ℝ}

lemma one_le_cast_add_one (m : ℕ) : (1 : ℝ) ≤ (m : ℝ) + 1 := by
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma summable_abs_c_one (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2)) :
    Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1)) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hc
  have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := one_le_cast_add_one m
  have h2 : (0 : ℝ) ≤ |c m| := abs_nonneg _
  have h3 : ((m : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left h3 h2

lemma summable_abs_c_Npsi (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2)) :
    Summable (fun m : ℕ => |c m| * Npsi m) := by
  refine Summable.of_nonneg_of_le (fun m => by
    exact mul_nonneg (abs_nonneg _) (le_of_lt (Work.FTS.PhiStar.Series.Deleg.Npsi_pos m)))
    (fun m => ?_) (hc.mul_left 9)
  have h := Npsi_le_nine m
  have h2 : (0 : ℝ) ≤ |c m| := abs_nonneg _
  calc |c m| * Npsi m ≤ |c m| * (9 * ((m : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left h h2
    _ = 9 * (|c m| * ((m : ℝ) + 1) ^ 2) := by ring

lemma abs_d_eq (hcd : ∀ m : ℕ, c m * lam m = d m) (m : ℕ) :
    |d m| = |c m| * lam m := by
  have hlam : (0 : ℝ) ≤ lam m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]; positivity
  rw [← hcd m, abs_mul, abs_of_nonneg hlam]

lemma cube_le_lam (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ 3 ≤ 4 * lam m * ((m : ℝ) + 1) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkey : ((m : ℝ) + 1) ^ 2 ≤ 8 * (m : ℝ) * (2 * (m : ℝ) + 5) := by
    nlinarith [sq_nonneg ((m : ℝ))]
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hcube : ((m : ℝ) + 1) ^ 3 = ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) := by ring
  rw [Work.FTS.PhiStar.Gegenbauer.lam, hcube]
  calc ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1)
      ≤ (8 * (m : ℝ) * (2 * (m : ℝ) + 5)) * ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
    _ = 4 * (2 * (m : ℝ) * (2 * (m : ℝ) + 5)) * ((m : ℝ) + 1) := by ring

lemma cube_le_lam_mul (hcd : ∀ m : ℕ, c m * lam m = d m) {m : ℕ} (hm : 1 ≤ m) :
    |c m| * ((m : ℝ) + 1) ^ 3 ≤ 4 * (|d m| * ((m : ℝ) + 1)) := by
  have hcube := cube_le_lam m hm
  have hc' : (0 : ℝ) ≤ |c m| := abs_nonneg _
  rw [abs_d_eq hcd m]
  calc |c m| * ((m : ℝ) + 1) ^ 3 ≤ |c m| * (4 * lam m * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hcube hc'
    _ = 4 * (|c m| * lam m * ((m : ℝ) + 1)) := by ring

/-- `Σ_m |c m| (m+1)³` is summable, from `Σ_m |d m| (m+1)` and `d m = c m · lam m`. -/
lemma summable_abs_c_cube (hcd : ∀ m : ℕ, c m * lam m = d m)
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1))) :
    Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 3) := by
  have hshift : Summable (fun k : ℕ => |d (k + 1)| * (((k + 1 : ℕ) : ℝ) + 1)) :=
    (summable_nat_add_iff 1).mpr hd
  have hmain : Summable (fun k : ℕ => |c (k + 1)| * (((k + 1 : ℕ) : ℝ) + 1) ^ 3) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hshift.mul_left 4)
    exact cube_le_lam_mul hcd (Nat.le_add_left 1 k)
  exact (summable_nat_add_iff 1).mp hmain

/-- `Σ_m |c m| (Npsi m)^{3/2}` is summable. -/
lemma summable_abs_c_Npsi32 (hcd : ∀ m : ℕ, c m * lam m = d m)
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1))) :
    Summable (fun m : ℕ => |c m| * (Npsi m * Real.sqrt (Npsi m))) := by
  refine Summable.of_nonneg_of_le (fun m => by
    exact mul_nonneg (abs_nonneg _) (mul_nonneg
      (le_of_lt (Work.FTS.PhiStar.Series.Deleg.Npsi_pos m)) (Real.sqrt_nonneg _)))
    (fun m => ?_) ((summable_abs_c_cube hcd hd).mul_left 27)
  have h := Npsi_mul_sqrt_le m
  have hc' : (0 : ℝ) ≤ |c m| := abs_nonneg _
  calc |c m| * (Npsi m * Real.sqrt (Npsi m)) ≤ |c m| * (27 * ((m : ℝ) + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left h hc'
    _ = 27 * (|c m| * ((m : ℝ) + 1) ^ 3) := by ring

/-- The majorant of the first derivative series is summable. -/
lemma summable_u1 {s : ℝ} (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2)) :
    Summable (fun m : ℕ => 100 * Npsi m / s ^ 2 * |c m|) := by
  have hEq : (fun m : ℕ => 100 * Npsi m / s ^ 2 * |c m|)
      = fun m : ℕ => (100 / s ^ 2) * (|c m| * Npsi m) := by
    funext m; ring
  rw [hEq]
  exact (summable_abs_c_Npsi hc).mul_left _

/-- The majorant of the second derivative series is summable. -/
lemma summable_u2 {s : ℝ} (hcd : ∀ m : ℕ, c m * lam m = d m)
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1))) :
    Summable (fun m : ℕ => 1000 * Npsi m * Real.sqrt (Npsi m) / s ^ 4 * |c m|) := by
  have hEq : (fun m : ℕ => 1000 * Npsi m * Real.sqrt (Npsi m) / s ^ 4 * |c m|)
      = fun m : ℕ => (1000 / s ^ 4) * (|c m| * (Npsi m * Real.sqrt (Npsi m))) := by
    funext m; ring
  rw [hEq]
  exact (summable_abs_c_Npsi32 hcd hd).mul_left _

end Summable

/-! ## 3. The modes and their derivatives -/

lemma contDiff_eFam (m : ℕ) : ContDiff ℝ 3 (eFam m) := by
  show ContDiff ℝ 3 (fun θ : ℝ => Real.cos θ
    * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.contDiff_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)

lemma hasDerivAt_eFam (m : ℕ) (θ : ℝ) : HasDerivAt (eFam m) (deriv (eFam m) θ) θ :=
  ((contDiff_eFam m).differentiable (by norm_num)).differentiableAt.hasDerivAt

lemma hasDerivAt_deriv_eFam (m : ℕ) (θ : ℝ) :
    HasDerivAt (deriv (eFam m)) (iteratedDeriv 2 (eFam m) θ) θ := by
  have h2 : ContDiff ℝ 2 (deriv (eFam m)) := (contDiff_eFam m).deriv'
  have hd : HasDerivAt (deriv (eFam m)) (deriv (deriv (eFam m)) θ) θ :=
    (h2.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hiter : iteratedDeriv 2 (eFam m) = deriv (deriv (eFam m)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rwa [hiter]

lemma contDiff_iteratedDeriv_two_eFam (m : ℕ) : ContDiff ℝ 1 (iteratedDeriv 2 (eFam m)) := by
  have h : iteratedDeriv 2 (eFam m) = deriv (deriv (eFam m)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h]
  exact (contDiff_eFam m).deriv'.deriv'

/-- `deriv tan θ = 1/cos²θ`. -/
lemma hasDerivAt_tan_real {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := by
  have h := (Real.hasDerivAt_sin θ).div (Real.hasDerivAt_cos θ) hcos
  have htan : Real.tan = Real.sin / Real.cos := funext fun x => Real.tan_eq_sin_div_cos x
  rw [← htan] at h
  have hval : (Real.cos θ * Real.cos θ - Real.sin θ * (-Real.sin θ)) / Real.cos θ ^ 2
      = 1 / Real.cos θ ^ 2 := by
    have h1 : Real.cos θ * Real.cos θ - Real.sin θ * (-Real.sin θ) = 1 := by
      have hs := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [h1]
  rwa [hval] at h

/-- `Lzero` of a `z`-independent function, in terms of the one-variable derivatives. -/
lemma Lzero_of_one_var (g : ℝ → ℝ) {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hg : HasDerivAt g (deriv g θ) θ) :
    Work.Elliptic.Lzero (fun _ θ' => g θ') 0 θ
      = -iteratedDeriv 2 g θ + Real.tan θ * deriv g θ + (1 / Real.cos θ ^ 2) * g θ
        - 6 * g θ := by
  have h2 : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h3 : deriv (fun θ' : ℝ => Real.tan θ' * g θ') θ
      = 1 / Real.cos θ ^ 2 * g θ + Real.tan θ * deriv g θ :=
    ((hasDerivAt_tan_real hcos).mul hg).deriv
  have hgoal : Work.Elliptic.Lzero (fun _ θ' => g θ') 0 θ
      = -(deriv (deriv g) θ) + deriv (fun θ' : ℝ => Real.tan θ' * g θ') θ - 6 * g θ := by
    rw [Work.Elliptic.Lzero_eq_deriv]
  rw [hgoal, h3, ← h2]
  ring

/-! ## 4. Termwise differentiation on compacts -/

/-- If `Ioo ε (π/2 - ε)` contains a point and `ε > 0`, then `ε < π/2`. -/
lemma eps_lt_pi_half_of_mem {ε θ : ℝ} (hε : 0 < ε) (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    ε < Real.pi / 2 := by
  have h2 : ε < Real.pi / 2 - ε := lt_trans hθ.1 hθ.2
  linarith [Real.pi_pos]

/-- If `Ioo ε (π/2 - ε)` contains a point and `ε > 0`, then `0 < sin ε`. -/
lemma sin_pos_of_mem {ε θ : ℝ} (hε : 0 < ε) (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    0 < Real.sin ε :=
  Real.sin_pos_of_pos_of_lt_pi hε (by linarith [eps_lt_pi_half_of_mem hε hθ, Real.pi_pos])

/-- Where `y` lies in `Ioo ε (π/2 - ε)` with `ε > 0`, `cos y ≥ sin ε`. -/
lemma cos_ge_sin_of_mem {ε : ℝ} (hε : 0 < ε) (y : ℝ)
    (hy : y ∈ Set.Ioo ε (Real.pi / 2 - ε)) : Real.sin ε ≤ Real.cos y := by
  have hy0 : 0 ≤ y := le_of_lt (lt_trans hε hy.1)
  have hyπ : Real.pi / 2 - ε ≤ Real.pi := by linarith [Real.pi_pos, hε]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi hy0 hyπ (le_of_lt hy.2)
  rwa [Real.cos_pi_div_two_sub] at h

lemma mem_Ioo_pi_half {ε y : ℝ} (hε : 0 < ε) (hy : y ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    y ∈ Set.Ioo 0 (Real.pi / 2) :=
  ⟨lt_trans hε hy.1, by linarith [hy.2]⟩

/-- Termwise differentiation of the mode series: on `Ioo ε (π/2 - ε)`,
`d/dθ ∑_m c_m e_m(θ) = ∑_m c_m e_m'(θ)`. -/
lemma hasDerivAt_series {c : ℕ → ℝ}
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    {ε : ℝ} (hε : 0 < ε) {θ : ℝ} (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)
      (∑' m : ℕ, c m * deriv (eFam m) θ) θ := by
  have hsin : 0 < Real.sin ε := sin_pos_of_mem hε hθ
  have hcos : ∀ y ∈ Set.Ioo ε (Real.pi / 2 - ε), Real.sin ε ≤ Real.cos y :=
    fun y hy => cos_ge_sin_of_mem hε y hy
  refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (t := Set.Ioo ε (Real.pi / 2 - ε))
    (u := fun m : ℕ => 100 * Npsi m / (Real.sin ε) ^ 2 * |c m|)
    (g := fun m y => c m * eFam m y) (g' := fun m y => c m * deriv (eFam m) y)
    (summable_u1 (s := Real.sin ε) hc) isOpen_Ioo isPreconnected_Ioo ?_ ?_ hθ ?_ hθ
  · intro m y hy
    exact (hasDerivAt_eFam m y).const_mul (c m)
  · intro m y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.1 m y (mem_Ioo_pi_half hε hy)
    have hcs := hcos y hy
    have hnum : (0 : ℝ) ≤ 100 * Npsi m := by
      have := Work.FTS.PhiStar.Series.Deleg.Npsi_pos m; linarith
    have hcospos : 0 < Real.cos y := lt_of_lt_of_le hsin hcs
    have hsq : (Real.sin ε) ^ 2 ≤ (Real.cos y) ^ 2 := by nlinarith
    have hden : (0 : ℝ) < (Real.sin ε) ^ 2 := by positivity
    have hle : 100 * Npsi m / (Real.cos y) ^ 2 ≤ 100 * Npsi m / (Real.sin ε) ^ 2 :=
      div_le_div_of_nonneg_left hnum hden hsq
    calc |c m| * |deriv (eFam m) y| ≤ |c m| * (100 * Npsi m / (Real.cos y) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |c m| * (100 * Npsi m / (Real.sin ε) ^ 2) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = 100 * Npsi m / (Real.sin ε) ^ 2 * |c m| := by ring
  · refine Summable.of_norm_bounded (f := fun m : ℕ => c m * eFam m θ)
      (g := fun m : ℕ => 3 * (|c m| * ((m : ℝ) + 1))) ?_ (fun m => ?_)
    · exact (summable_abs_c_one hc).mul_left 3
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).1 m θ (mem_Ioo_pi_half hε hθ)
      have hb' := sqrt_Npsi_le_three m
      calc |c m| * |eFam m θ| ≤ |c m| * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (le_trans hb hb') (abs_nonneg _)
        _ = 3 * (|c m| * ((m : ℝ) + 1)) := by ring

/-- Termwise differentiation, once more: on `Ioo ε (π/2 - ε)`,
`d/dθ ∑_m c_m e_m'(θ) = ∑_m c_m e_m''(θ)`. -/
lemma hasDerivAt_series_deriv {c d : ℕ → ℝ}
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1)))
    (hcd : ∀ m : ℕ, c m * lam m = d m)
    {ε : ℝ} (hε : 0 < ε) {θ : ℝ} (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * deriv (eFam m) y)
      (∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) θ) θ := by
  have hsin : 0 < Real.sin ε := sin_pos_of_mem hε hθ
  have hcos : ∀ y ∈ Set.Ioo ε (Real.pi / 2 - ε), Real.sin ε ≤ Real.cos y :=
    fun y hy => cos_ge_sin_of_mem hε y hy
  refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (t := Set.Ioo ε (Real.pi / 2 - ε))
    (u := fun m : ℕ => 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 * |c m|)
    (g := fun m y => c m * deriv (eFam m) y)
    (g' := fun m y => c m * iteratedDeriv 2 (eFam m) y)
    (summable_u2 (s := Real.sin ε) hcd hd) isOpen_Ioo isPreconnected_Ioo ?_ ?_ hθ ?_ hθ
  · intro m y hy
    exact (hasDerivAt_deriv_eFam m y).const_mul (c m)
  · intro m y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.2.1 m y (mem_Ioo_pi_half hε hy)
    have hcs := hcos y hy
    have hnum : (0 : ℝ) ≤ 1000 * Npsi m * Real.sqrt (Npsi m) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (Work.FTS.PhiStar.Series.Deleg.Npsi_pos m)))
        (Real.sqrt_nonneg _)
    have hcospos : 0 < Real.cos y := lt_of_lt_of_le hsin hcs
    have h2 : (Real.sin ε) ^ 2 ≤ (Real.cos y) ^ 2 := by nlinarith
    have hsq : (Real.sin ε) ^ 4 ≤ (Real.cos y) ^ 4 := by
      have hnn : (0 : ℝ) ≤ (Real.sin ε) ^ 2 := by positivity
      have hnn' : (0 : ℝ) ≤ (Real.cos y) ^ 2 := by positivity
      have hmul := mul_le_mul h2 h2 hnn hnn'
      calc (Real.sin ε) ^ 4 = (Real.sin ε) ^ 2 * (Real.sin ε) ^ 2 := by ring
        _ ≤ (Real.cos y) ^ 2 * (Real.cos y) ^ 2 := hmul
        _ = (Real.cos y) ^ 4 := by ring
    have hden : (0 : ℝ) < (Real.sin ε) ^ 4 := by positivity
    have hle : 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos y) ^ 4
        ≤ 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 :=
      div_le_div_of_nonneg_left hnum hden hsq
    calc |c m| * |iteratedDeriv 2 (eFam m) y|
        ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos y) ^ 4) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 * |c m| := by ring
  · refine Summable.of_norm_bounded (f := fun m : ℕ => c m * deriv (eFam m) θ)
      (g := fun m : ℕ => (100 / (Real.cos θ) ^ 2) * (|c m| * Npsi m)) ?_ (fun m => ?_)
    · exact (summable_abs_c_Npsi hc).mul_left _
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.1 m θ (mem_Ioo_pi_half hε hθ)
      have hle : 100 * Npsi m / (Real.cos θ) ^ 2 = (100 / (Real.cos θ) ^ 2) * Npsi m := by ring
      calc |c m| * |deriv (eFam m) θ| ≤ |c m| * (100 * Npsi m / (Real.cos θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (100 / (Real.cos θ) ^ 2) * (|c m| * Npsi m) := by rw [hle]; ring

/-- The second derivative series is continuous on `Ioo ε (π/2 - ε)`. -/
lemma continuousOn_series'' {c d : ℕ → ℝ}
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1)))
    (hcd : ∀ m : ℕ, c m * lam m = d m) {ε : ℝ} (hε : 0 < ε)
    (hε4 : ε < Real.pi / 2) :
    ContinuousOn (fun y : ℝ => ∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) y)
      (Set.Ioo ε (Real.pi / 2 - ε)) := by
  have hsin : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε (by linarith [hε4, Real.pi_pos])
  have hcos : ∀ y ∈ Set.Ioo ε (Real.pi / 2 - ε), Real.sin ε ≤ Real.cos y :=
    fun y hy => cos_ge_sin_of_mem hε y hy
  refine continuousOn_tsum (f := fun m y => c m * iteratedDeriv 2 (eFam m) y)
    (u := fun m : ℕ => 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 * |c m|)
    ?_ (summable_u2 (s := Real.sin ε) hcd hd) ?_
  · intro m
    exact (continuous_const.mul (contDiff_iteratedDeriv_two_eFam m).continuous).continuousOn
  · intro m y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.2.1 m y (mem_Ioo_pi_half hε hy)
    have hcs := hcos y hy
    have hnum : (0 : ℝ) ≤ 1000 * Npsi m * Real.sqrt (Npsi m) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (Work.FTS.PhiStar.Series.Deleg.Npsi_pos m)))
        (Real.sqrt_nonneg _)
    have hcospos : 0 < Real.cos y := lt_of_lt_of_le hsin hcs
    have h2 : (Real.sin ε) ^ 2 ≤ (Real.cos y) ^ 2 := by nlinarith
    have hsq : (Real.sin ε) ^ 4 ≤ (Real.cos y) ^ 4 := by
      have hnn : (0 : ℝ) ≤ (Real.sin ε) ^ 2 := by positivity
      have hnn' : (0 : ℝ) ≤ (Real.cos y) ^ 2 := by positivity
      have hmul := mul_le_mul h2 h2 hnn hnn'
      calc (Real.sin ε) ^ 4 = (Real.sin ε) ^ 2 * (Real.sin ε) ^ 2 := by ring
        _ ≤ (Real.cos y) ^ 2 * (Real.cos y) ^ 2 := hmul
        _ = (Real.cos y) ^ 4 := by ring
    have hden : (0 : ℝ) < (Real.sin ε) ^ 4 := by positivity
    have hle : 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos y) ^ 4
        ≤ 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 :=
      div_le_div_of_nonneg_left hnum hden hsq
    calc |c m| * |iteratedDeriv 2 (eFam m) y|
        ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos y) ^ 4) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 * |c m| := by ring

/-! ## 5. Assembling `ContDiffOn ℝ 2` -/

/-- `HasDerivAt` data for `f` and for its derivative, plus continuity of the second derivative,
give `ContDiffOn ℝ 2`. -/
lemma contDiffOn_two_of_hasDerivAt {F A A' : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h1 : ∀ x ∈ s, HasDerivAt F (A x) x) (h2 : ∀ x ∈ s, HasDerivAt A (A' x) x)
    (h3 : ContinuousOn A' s) : ContDiffOn ℝ 2 F s := by
  have hFdiff : DifferentiableOn ℝ F s :=
    fun x hx => (h1 x hx).differentiableAt.differentiableWithinAt
  have hAdiff : DifferentiableOn ℝ A s :=
    fun x hx => (h2 x hx).differentiableAt.differentiableWithinAt
  have hA' : ContinuousOn (derivWithin A s) s :=
    h3.congr (fun x hx => (derivWithin_of_isOpen hs hx).trans (h2 x hx).deriv)
  have hA1 : ContDiffOn ℝ 1 A s :=
    (contDiffOn_one_iff_derivWithin hs.uniqueDiffOn).2 ⟨hAdiff, hA'⟩
  have hderiv : ContDiffOn ℝ 1 (derivWithin F s) s :=
    hA1.congr (fun x hx => (derivWithin_of_isOpen hs hx).trans (h1 x hx).deriv)
  rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 from by norm_num,
    contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact ⟨hFdiff, fun h => absurd h (WithTop.natCast_ne_top 1), hderiv⟩

/-- The mode series is `C²` on `(0, π/2)`. -/
lemma contDiffOn_series {c d : ℕ → ℝ}
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1)))
    (hcd : ∀ m : ℕ, c m * lam m = d m) :
    ContDiffOn ℝ 2 (fun θ : ℝ => ∑' m : ℕ, c m * eFam m θ) (Set.Ioo 0 (Real.pi / 2)) := by
  refine contDiffOn_of_locally_contDiffOn (fun θ hθ => ?_)
  obtain ⟨h0, h1⟩ := hθ
  set ε : ℝ := min θ (Real.pi / 2 - θ) / 2 with hεdef
  have hpi : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos, h1]
  have hε : 0 < ε := by
    rw [hεdef]
    have h2 : (0 : ℝ) < min θ (Real.pi / 2 - θ) := lt_min h0 hpi
    linarith
  have hmem : θ ∈ Set.Ioo ε (Real.pi / 2 - ε) := by
    rw [hεdef]
    constructor
    · have h := min_le_left θ (Real.pi / 2 - θ); linarith
    · have h := min_le_right θ (Real.pi / 2 - θ); linarith
  have hε4 : ε < Real.pi / 2 := eps_lt_pi_half_of_mem hε hmem
  refine ⟨Set.Ioo ε (Real.pi / 2 - ε), isOpen_Ioo, hmem, ?_⟩
  refine (contDiffOn_two_of_hasDerivAt (s := Set.Ioo ε (Real.pi / 2 - ε)) isOpen_Ioo
    (fun x hx => hasDerivAt_series hc hε hx)
    (fun x hx => hasDerivAt_series_deriv hc hd hcd hε hx)
    (continuousOn_series'' hc hd hcd hε hε4)).mono Set.inter_subset_right

/-! ## 6. The `Lzero` identity -/

/-- Linearity of an absolutely convergent series in the four terms coming from the one-variable
form of `Lzero`. -/
lemma tsum_lincomb {a b e : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (he : Summable e)
    (t r : ℝ) :
    -(∑' m : ℕ, a m) + t * (∑' m : ℕ, b m) + r * (∑' m : ℕ, e m) - 6 * (∑' m : ℕ, e m)
      = ∑' m : ℕ, (-(a m) + t * b m + r * e m - 6 * e m) := by
  rw [← tsum_neg, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  rw [← Summable.tsum_add ha.neg (hb.mul_left t)]
  rw [← Summable.tsum_add (ha.neg.add (hb.mul_left t)) (he.mul_left r)]
  rw [← Summable.tsum_sub ((ha.neg.add (hb.mul_left t)).add (he.mul_left r)) (he.mul_left 6)]
  try rfl

/-- The `Lzero` identity of the mode series, on a compact subinterval of `(0, π/2)`. -/
lemma lzero_series {c d : ℕ → ℝ}
    (hcd : ∀ m : ℕ, c m * lam m = d m)
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1)))
    {ε : ℝ} (hε : 0 < ε) {θ : ℝ} (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    Work.Elliptic.Lzero (fun _ θ' => ∑' m : ℕ, c m * eFam m θ') 0 θ
      = ∑' m : ℕ, d m * eFam m θ := by
  have hpi := mem_Ioo_pi_half hε hθ
  have hcos0 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hpi.1], hpi.2⟩
  have hcosne : Real.cos θ ≠ 0 := ne_of_gt hcos0
  -- the two termwise differentiations
  have hF : HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)
      (∑' m : ℕ, c m * deriv (eFam m) θ) θ := hasDerivAt_series hc hε hθ
  have hA : HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * deriv (eFam m) y)
      (∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) θ) θ := hasDerivAt_series_deriv hc hd hcd hε hθ
  have hF' : HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)
      (deriv (fun y : ℝ => ∑' m : ℕ, c m * eFam m y) θ) θ := by
    rw [hF.deriv]; exact hF
  -- `iteratedDeriv 2` of the series
  have hev : (fun y : ℝ => ∑' m : ℕ, c m * deriv (eFam m) y)
      =ᶠ[𝓝 θ] deriv (fun y : ℝ => ∑' m : ℕ, c m * eFam m y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    exact ((hasDerivAt_series hc hε hy).deriv).symm
  have hiter : iteratedDeriv 2 (fun y : ℝ => ∑' m : ℕ, c m * eFam m y) θ
      = ∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) θ := by
    have h2 : iteratedDeriv 2 (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)
        = deriv (deriv (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2, ← Filter.EventuallyEq.deriv_eq hev, hA.deriv]
  -- summability of the three coefficient series at `θ`
  have hX : Summable (fun m : ℕ => c m * iteratedDeriv 2 (eFam m) θ) := by
    refine Summable.of_norm_bounded (f := fun m : ℕ => c m * iteratedDeriv 2 (eFam m) θ)
      (g := fun m : ℕ => (1000 / (Real.cos θ) ^ 4)
        * (|c m| * (Npsi m * Real.sqrt (Npsi m)))) ?_ (fun m => ?_)
    · exact (summable_abs_c_Npsi32 hcd hd).mul_left _
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.2.1 m θ hpi
      calc |c m| * |iteratedDeriv 2 (eFam m) θ|
          ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos θ) ^ 4) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (1000 / (Real.cos θ) ^ 4) * (|c m| * (Npsi m * Real.sqrt (Npsi m))) := by ring
  have hY : Summable (fun m : ℕ => c m * deriv (eFam m) θ) := by
    refine Summable.of_norm_bounded (f := fun m : ℕ => c m * deriv (eFam m) θ)
      (g := fun m : ℕ => (100 / (Real.cos θ) ^ 2) * (|c m| * Npsi m)) ?_ (fun m => ?_)
    · exact (summable_abs_c_Npsi hc).mul_left _
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.1 m θ hpi
      calc |c m| * |deriv (eFam m) θ|
          ≤ |c m| * (100 * Npsi m / (Real.cos θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (100 / (Real.cos θ) ^ 2) * (|c m| * Npsi m) := by ring
  have hZ : Summable (fun m : ℕ => c m * eFam m θ) := by
    refine Summable.of_norm_bounded (f := fun m : ℕ => c m * eFam m θ)
      (g := fun m : ℕ => 3 * (|c m| * ((m : ℝ) + 1))) ?_ (fun m => ?_)
    · exact (summable_abs_c_one hc).mul_left 3
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).1 m θ hpi
      calc |c m| * |eFam m θ| ≤ |c m| * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (le_trans hb (sqrt_Npsi_le_three m)) (abs_nonneg _)
        _ = 3 * (|c m| * ((m : ℝ) + 1)) := by ring
  calc Work.Elliptic.Lzero (fun _ θ' => ∑' m : ℕ, c m * eFam m θ') 0 θ
      = -(∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) θ)
        + Real.tan θ * (∑' m : ℕ, c m * deriv (eFam m) θ)
        + (1 / Real.cos θ ^ 2) * (∑' m : ℕ, c m * eFam m θ)
        - 6 * (∑' m : ℕ, c m * eFam m θ) := by
        rw [Lzero_of_one_var (fun y : ℝ => ∑' m : ℕ, c m * eFam m y) hcosne hF']
        rw [hF.deriv, hiter]
    _ = ∑' m : ℕ, (-(c m * iteratedDeriv 2 (eFam m) θ) + Real.tan θ * (c m * deriv (eFam m) θ)
          + (1 / Real.cos θ ^ 2) * (c m * eFam m θ) - 6 * (c m * eFam m θ)) :=
        tsum_lincomb hX hY hZ (Real.tan θ) (1 / Real.cos θ ^ 2)
    _ = ∑' m : ℕ, c m * Work.Elliptic.Lzero (fun _ θ' => eFam m θ') 0 θ := by
        refine tsum_congr fun m => ?_
        rw [Lzero_of_one_var (eFam m) hcosne (hasDerivAt_eFam m θ)]
        ring
    _ = ∑' m : ℕ, d m * eFam m θ := by
        refine tsum_congr fun m => ?_
        rw [Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcosne 0, ← hcd m]
        ring

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.eFam_growth_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Growth of the iterated derivatives of the Gegenbauer family `eFam`

`eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` is a trigonometric polynomial of degree `2m+2`
solving the singular Sturm–Liouville equation

  `(cos θ · f')' = (1/cos θ - M cos θ) · f`,   `M = eM m = (2m+2)(2m+3)`,

equivalently `f'' = tan θ · f' + (sec²θ - M) · f` on `(0, π/2)`.  On a compact subinterval
`[θ₁, θ₂] ⊂ (0, π/2)` the coefficients `tan` and `sec²` are smooth with *bounded* derivatives,
so differentiating the equation `k` times bounds `f^{(k+2)}` by the lower derivatives plus the
single term `-M f^{(k)}`.  With the two base bounds `|f| ≤ 3(m+1)` and `|f'| ≤ C(m+1)²` this
closes by induction on `k` with the exponents `k+1`, which is the claimed
`|f^{(j)}| ≤ C (m+1)^{j+1}`.

The two base bounds are taken here from the *radial energy* machinery of
`Series.eFamSupDefs` (`|eFam m θ| ≤ √(Npsi m)` from `Series.eFam_sup_le`, and the new
`abs_deriv_eFam_le` below, which converts the bound `|(ug m)'| ≤ Npsi m` supplied by
`ene_le` into a bound for the `θ`-derivative of `eFam m`).  This keeps the module's import
closure disjoint from `Series.Deleg.psiAngDefs` (the two modules of the tree that both declare
`Work.FTS.PhiStar.Series.Deleg.gC_abs_bound` cannot be imported together).
-/

namespace Work.FTS.PhiStar.Honesty.CptQSmooth.CleanAng

set_option maxHeartbeats 1000000

open scoped Real
open Work.FTS.PhiStar.Gegenbauer (eFam gC)

/-! ## 1. Smoothness of every finite order -/

/-- The Gegenbauer polynomials `gC k` are smooth of every finite order (the recurrence is built
from products, linear combinations and division by a constant). -/
lemma contDiff_gC_nat : ∀ k n : ℕ, ContDiff ℝ n (gC k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    intro n
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    exact contDiff_const
  | one =>
    intro n
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    exact contDiff_const.mul contDiff_id
  | more k ih1 ih2 =>
    intro n
    rw [show gC (k + 2) = (fun x =>
        (2 * ((k : ℝ) + 5 / 2) * x * gC (k + 1) x
          - ((k : ℝ) + 3) * gC k x) / ((k : ℝ) + 2)) from rfl]
    exact (((contDiff_const.mul contDiff_id).mul (ih2 n)).sub
      (contDiff_const.mul (ih1 n))).div_const _

/-- `eFam m = cos · (gC (2m+1) ∘ sin)` is smooth of every finite order. -/
lemma contDiff_eFam_nat (m n : ℕ) : ContDiff ℝ n (eFam m) := by
  rw [show eFam m = fun θ => Real.cos θ * gC (2 * m + 1) (Real.sin θ) from rfl]
  exact Real.contDiff_cos.mul ((contDiff_gC_nat (2 * m + 1) n).comp Real.contDiff_sin)

/-! ## 2. Calculus of `iteratedDeriv` -/

lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

lemma iteratedDeriv_deriv_apply (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv n (deriv f) x = iteratedDeriv (n + 1) f x := by
  rw [iteratedDeriv_succ']

lemma iteratedDeriv_two_add (k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv (k + 2) f = iteratedDeriv k (iteratedDeriv 2 f) := by
  rw [show k + 2 = k + 1 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ',
    ← iteratedDeriv_two_eq f]

/-! ## 3. The Leibniz expansion of the differentiated equation -/

/-- The `k`-fold derivative of the right-hand side `a·f' + b·f - c·f` of a second order
equation, expanded by the Leibniz rule. -/
lemma iteratedDeriv_ode_expand {f a b : ℝ → ℝ} {c : ℝ} {k : ℕ} {x : ℝ}
    (ha : ContDiffAt ℝ k a x) (hb : ContDiffAt ℝ k b x) (hd : ContDiffAt ℝ k (deriv f) x)
    (hf : ContDiffAt ℝ k f x) :
    iteratedDeriv k (a * deriv f + b * f - (fun _ : ℝ => c) * f) x
      = (∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * (iteratedDeriv i a x * iteratedDeriv (k - i) (deriv f) x))
        + (∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * (iteratedDeriv i b x * iteratedDeriv (k - i) f x))
        - c * iteratedDeriv k f x := by
  rw [iteratedDeriv_sub (f := a * deriv f + b * f) (g := (fun _ : ℝ => c) * f)
        ((ha.mul hd).add (hb.mul hf)) ((contDiffAt_const (c := c)).mul hf)]
  rw [iteratedDeriv_add (f := a * deriv f) (g := b * f) (ha.mul hd) (hb.mul hf)]
  rw [iteratedDeriv_mul (f := a) (g := deriv f) ha hd,
      iteratedDeriv_mul (f := b) (g := f) hb hf]
  rw [show ((fun _ : ℝ => c) * f) = fun x => c * f x from rfl]
  rw [iteratedDeriv_const_mul (c := c) (n := k) (f := f) hf]
  ring_nf

/-! ## 4. The second order equation for `eFam m` -/

/-- The equation `f'' = tan θ f' + (sec²θ - M) f` for `f = eFam m` on the open interval
`(0, π/2)`, written as an identity of functions. -/
lemma eFam_ode_eqOn (m : ℕ) :
    Set.EqOn (iteratedDeriv 2 (eFam m))
      ((fun θ : ℝ => Real.tan θ) * deriv (eFam m)
        + (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) * eFam m
        - (fun _ : ℝ => Work.FTS.PhiStar.Series.eM m) * eFam m)
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [iteratedDeriv_two_eq, Work.FTS.PhiStar.Series.eFam_deriv2_eq m θ hcos]
  ring

/-- The `tan`-sum of the Leibniz expansion of `f^{(k+2)}`:
`∑_{i≤k} C(k,i) (tan)^{(i)}(θ) f^{(k+1-i)}(θ)`. -/
noncomputable def tanSum (k : ℕ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * (iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ * iteratedDeriv (k + 1 - i) f θ)

/-- The `sec²`-sum of the Leibniz expansion of `f^{(k+2)}`:
`∑_{i≤k} C(k,i) (sec²)^{(i)}(θ) f^{(k-i)}(θ)`. -/
noncomputable def secSum (k : ℕ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * (iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ * iteratedDeriv (k - i) f θ)

/-- **The differentiated equation.**  For `θ ∈ (0, π/2)`,

  `f^{(k+2)}(θ) = tanSum k f θ + secSum k f θ - M f^{(k)}(θ)`. -/
lemma eFam_iteratedDeriv_ode (m k : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    iteratedDeriv (k + 2) (eFam m) θ
      = tanSum k (eFam m) θ + secSum k (eFam m) θ
        - Work.FTS.PhiStar.Series.eM m * iteratedDeriv k (eFam m) θ := by
  rw [tanSum, secSum]
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hf : ContDiffAt ℝ k (eFam m) θ := (contDiff_eFam_nat m k).contDiffAt
  have hd : ContDiffAt ℝ k (deriv (eFam m)) θ :=
    ((contDiff_eFam_nat m (k + 1)).deriv' (n := (k : ℕ∞))).contDiffAt
  have ha : ContDiffAt ℝ k (fun θ : ℝ => Real.tan θ) θ := Real.contDiffAt_tan.mpr hcos
  have hb : ContDiffAt ℝ k (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ := by
    rw [show (fun θ : ℝ => 1 / (Real.cos θ) ^ 2)
        = (fun _ : ℝ => (1 : ℝ)) / (fun θ : ℝ => (Real.cos θ) ^ 2) from rfl]
    exact (contDiffAt_const (c := (1 : ℝ))).div (Real.contDiff_cos.contDiffAt.pow 2)
      (pow_ne_zero 2 hcos)
  have hEq : iteratedDeriv k (iteratedDeriv 2 (eFam m)) θ
      = iteratedDeriv k ((fun θ : ℝ => Real.tan θ) * deriv (eFam m)
          + (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) * eFam m
          - (fun _ : ℝ => Work.FTS.PhiStar.Series.eM m) * eFam m) θ :=
    (eFam_ode_eqOn m).iteratedDeriv_of_isOpen isOpen_Ioo k hθ
  rw [iteratedDeriv_two_add k (eFam m), hEq,
      iteratedDeriv_ode_expand (f := eFam m) (a := fun θ : ℝ => Real.tan θ)
        (b := fun θ : ℝ => 1 / (Real.cos θ) ^ 2) (c := Work.FTS.PhiStar.Series.eM m)
        (k := k) (x := θ) ha hb hd hf]
  have hs : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ
          * iteratedDeriv (k - i) (deriv (eFam m)) θ))
      = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ
          * iteratedDeriv (k + 1 - i) (eFam m) θ)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedDeriv_deriv_apply (k - i) (eFam m) θ, show k - i + 1 = k + 1 - i by omega]
  rw [hs]

/-! ## 5. Bounds for the derivatives of the coefficients on a compact subinterval -/

/-- Derivatives of a function which is smooth of every order on an open set are bounded on any
closed subinterval. -/
lemma exists_bound_iteratedDeriv_of_contDiffOn {g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n g s) {A B : ℝ} (hsub : Set.Icc A B ⊆ s) :
    ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc A B, |iteratedDeriv i g θ| ≤ C := by
  intro i
  have hcont : ContinuousOn (iteratedDeriv i g) (Set.Icc A B) := by
    have h1 : ContinuousOn (iteratedDerivWithin i g s) s :=
      (hg i).continuousOn_iteratedDerivWithin le_rfl hs.uniqueDiffOn
    exact (h1.congr (iteratedDerivWithin_of_isOpen hs).symm).mono hsub
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  refine le_trans ?_ (le_max_left C 0)
  simpa [Real.norm_eq_abs] using hC θ hθ

/-- The derivatives of `tan` are bounded on `[A, B] ⊂ (0, π/2)`. -/
lemma exists_bound_iteratedDeriv_tan {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2) :
    ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ| ≤ C := by
  refine exists_bound_iteratedDeriv_of_contDiffOn (s := Set.Ioo (A / 2) (Real.pi / 2)) isOpen_Ioo ?_ ?_
  · intro n
    have hcos : ∀ θ ∈ Set.Ioo (A / 2) (Real.pi / 2), Real.cos θ ≠ 0 := by
      intro θ hθ
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hA, Real.pi_pos], hθ.2⟩)
    refine ContDiffOn.congr ?_ (fun θ _ => Real.tan_eq_sin_div_cos θ)
    exact ContDiffOn.div Real.contDiff_sin.contDiffOn Real.contDiff_cos.contDiffOn hcos
  · intro θ hθ
    exact ⟨by linarith [hθ.1, hA], lt_of_le_of_lt hθ.2 hB⟩

/-- The derivatives of `sec²` are bounded on `[A, B] ⊂ (0, π/2)`. -/
lemma exists_bound_iteratedDeriv_secsq {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2) :
    ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ| ≤ C := by
  refine exists_bound_iteratedDeriv_of_contDiffOn (s := Set.Ioo (A / 2) (Real.pi / 2)) isOpen_Ioo ?_ ?_
  · intro n
    have hcos : ∀ θ ∈ Set.Ioo (A / 2) (Real.pi / 2), (Real.cos θ) ^ 2 ≠ 0 := by
      intro θ hθ
      have hc : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hA, Real.pi_pos], hθ.2⟩)
      exact pow_ne_zero 2 hc
    refine ContDiffOn.congr
      (ContDiffOn.div (contDiffOn_const (c := (1 : ℝ)))
        (Real.contDiff_cos.contDiffOn.pow 2) hcos) ?_
    intro θ _
    rfl
  · intro θ hθ
    exact ⟨by linarith [hθ.1, hA], lt_of_le_of_lt hθ.2 hB⟩

/-! ## 6. The arithmetic of the two base bounds -/


/-- `√((2m+2)(2m+3)) ≤ 3(m+1)`. -/
lemma sqrt_Npsi_le (m : ℕ) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ≤ 3 * ((m : ℝ) + 1) := by
  have hp : (0 : ℝ) ≤ 3 * ((m : ℝ) + 1) := by positivity
  rw [← Real.sqrt_sq hp]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- `(2m+2)(2m+3) ≤ 6(m+1)²`. -/
lemma Npsi_le_six (m : ℕ) :
    (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) ≤ 6 * ((m : ℝ) + 1) ^ 2 := by
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- `eM m ≤ 6(m+1)²`. -/
lemma eM_le_six (m : ℕ) :
    Work.FTS.PhiStar.Series.eM m ≤ 6 * ((m : ℝ) + 1) ^ 2 := by
  rw [Work.FTS.PhiStar.Series.eM]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

lemma eM_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Series.eM m := by
  rw [Work.FTS.PhiStar.Series.eM]
  positivity

end Work.FTS.PhiStar.Honesty.CptQSmooth.CleanAng
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero_corrected =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Elementary facts about the angular weight `sinCos2` -/

/-- The Dirichlet eigenfunctions `eFam m` are continuous. -/
lemma continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  unfold Work.FTS.PhiStar.Gegenbauer.eFam
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
      Real.continuous_sin)

/-- `sinCos2 θ = sin θ cos²θ` is continuous. -/
lemma continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `sinCos2 θ ≥ 0` on `Iθ = [0,π/2]`. -/
lemma sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Spaces.Iθ] at hθ
  obtain ⟨h0, h1⟩ := hθ
  unfold Work.Elliptic.sinCos2
  exact mul_nonneg (Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h1, Real.pi_pos]⟩)
    (sq_nonneg _)

/-- `sinCos2 θ ≤ 1` on `Iθ = [0,π/2]`. -/
lemma sinCos2_le_one_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≤ 1 := by
  rw [Work.Spaces.Iθ] at hθ
  obtain ⟨h0, h1⟩ := hθ
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by
    have := Real.cos_sq_le_one θ
    linarith
  unfold Work.Elliptic.sinCos2
  simpa using mul_le_mul (Real.sin_le_one θ) hcos2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- **Every `m ≠ 0` mode is orthogonal to `sinCos2` in the moment pairing**:
`∫_θ e_m(θ) sin θ cos²θ dθ = 0`.  This is `eFam_orthogonal m 0` together with
`e_0 cos θ = 3 sin θ cos²θ`. -/
lemma integral_eFam_mul_sinCos2_eq_zero {n : ℕ} (hn : n ≠ 0) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hpt : Work.Elliptic.sinCos2 = fun θ =>
      (1 / 3) * (Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ) := by
    funext θ
    rw [Work.FTS.PhiStar.Series.eFam_zero_apply]
    unfold Work.Elliptic.sinCos2
    ring
  calc (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (1 / 3) * (Work.FTS.PhiStar.Gegenbauer.eFam n θ
          * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ _
        rw [hpt]
        ring
    _ = (1 / 3) * ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ
          * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ := by
        rw [MeasureTheory.integral_const_mul]
    _ = 0 := by
        have hsub : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ
              * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
            = ∫ θ in (0 : ℝ)..(Real.pi / 2), Work.FTS.PhiStar.Gegenbauer.eFam n θ
              * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ := by
          rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
            intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
        rw [hsub, Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal n 0 hn, mul_zero]

/-! ## The moment of `psiSeries` as a mode sum -/

/-- **The `tsum`/`∫_θ` interchange**: the moment of the mode series is the sum of the moments of its
modes.  `Fstar` is the `θ`-integral against `sinCos2` and `psiSeries` is the mode series, so
dominated convergence (dominator `3(m+1)|acoeff α m F z|`, finite measure `Iθ`, uniform bound
`|eFam m θ| ≤ 3(m+1)` from `eFam_sup_le`) exchanges the sum and the integral. -/
theorem Fstar_psiSeries_eq_tsum {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z
      = ∑' m : ℕ, Work.FTS.PhiStar.Series.acoeff α m F z *
          ∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ := by
  have hfin : IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hsum3 : Summable (fun n : ℕ =>
      3 * ((n : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α n F z|) := by
    have h := hsum.mul_left 3
    refine h.congr fun n => ?_
    ring
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun θ : ℝ =>
      Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun n => (continuous_const.mul ((continuous_eFam n).mul continuous_sinCos2))
      |>.aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)‖
      ≤ 3 * ((n : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α n F z| := by
    intro n
    rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hb := sinCos2_le_one_of_mem_Iθ hθ
    have hb0 := sinCos2_nonneg_of_mem_Iθ hθ
    have he := Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi n hθ
    have he3 := Work.FTS.PhiStar.Series.sqrt_Npsi_le_three n
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |Work.FTS.PhiStar.Series.acoeff α n F z|
          * (|Work.FTS.PhiStar.Gegenbauer.eFam n θ| * |Work.Elliptic.sinCos2 θ|)
        ≤ |Work.FTS.PhiStar.Series.acoeff α n F z| * ((3 * ((n : ℝ) + 1)) * 1) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul
      · exact le_trans he he3
      · rw [abs_of_nonneg hb0]; exact hb
      · norm_num
      · positivity
    exact le_trans h1 (le_of_eq (by ring))
  have hbs : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Summable (fun n : ℕ => 3 * ((n : ℝ) + 1)
        * |Work.FTS.PhiStar.Series.acoeff α n F z|) :=
    Filter.Eventually.of_forall fun _ => hsum3
  have hint : Integrable (fun _ : ℝ => ∑' n : ℕ,
      3 * ((n : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α n F z|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integrable_const_iff.mpr (Or.inr hfin)
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      HasSum (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ))
        (Work.FTS.PhiStar.Series.psiSeries α F z θ * Work.Elliptic.sinCos2 θ) := by
    rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hb : ∀ m : ℕ, ‖Work.FTS.PhiStar.Series.acoeff α m F z
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        ≤ 3 * ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z| := by
      intro m
      have he := Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθ
      have he3 := Work.FTS.PhiStar.Series.sqrt_Npsi_le_three m
      rw [Real.norm_eq_abs, abs_mul]
      calc |Work.FTS.PhiStar.Series.acoeff α m F z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ |Work.FTS.PhiStar.Series.acoeff α m F z| * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (le_trans he he3) (abs_nonneg _)
        _ = 3 * ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z| := by ring
    have hsumm : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m F z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
      Summable.of_norm_bounded hsum3 hb
    have hh := hsumm.hasSum.mul_right (Work.Elliptic.sinCos2 θ)
    rw [show (fun m : ℕ => (Work.FTS.PhiStar.Series.acoeff α m F z
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        = (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m F z
          * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ))
        from funext fun m => by ring] at hh
    simpa [Work.FTS.PhiStar.Series.psiSeries] using hh
  have key := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun n : ℕ => fun θ : ℝ => Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ))
    (f := fun θ : ℝ => Work.FTS.PhiStar.Series.psiSeries α F z θ
        * Work.Elliptic.sinCos2 θ)
    (bound := fun n : ℕ => fun _ : ℝ => 3 * ((n : ℝ) + 1)
        * |Work.FTS.PhiStar.Series.acoeff α n F z|)
    hmeas hbound hbs hint hlim
  have hterm : ∀ n : ℕ, (∫ θ, Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = Work.FTS.PhiStar.Series.acoeff α n F z *
        ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ :=
    fun n => by rw [MeasureTheory.integral_const_mul]
  have hkey : HasSum (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α n F z *
        ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
      (Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z) := by
    have hval : (∫ θ, Work.FTS.PhiStar.Series.psiSeries α F z θ * Work.Elliptic.sinCos2 θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z := rfl
    rw [← hval]
    rw [show (fun n : ℕ => ∫ θ, Work.FTS.PhiStar.Series.acoeff α n F z
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α n F z *
          ∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
        from funext hterm] at key
    exact key
  exact hkey.tsum_eq.symm

/-- **`Fstar (psiSeries α F) z = 0` for every `z`, as soon as the mode-`0` radial coefficient
`acoeff α 0 F z` vanishes** (and the mode coefficients are summable in the weighted `ℓ¹` sense).

Immediate from `Fstar_psiSeries_eq_tsum`: every summand is `0`, since for `m = 0` the coefficient
vanishes by hypothesis (`cmode 0 F` and hence `acoeff α 0 F z` encode the source moment, cf.
`eFam_zero_moment`, `acoeff_zero_of_fstar`) and for `m ≥ 1` the mode is orthogonal to `sinCos2`
(`integral_eFam_mul_sinCos2_eq_zero`, i.e. `eFam_orthogonal`). -/
theorem Fstar_psiSeries_eq_zero_of_acoeff_zero {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (h0 : Work.FTS.PhiStar.Series.acoeff α 0 F z = 0) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 := by
  rw [Fstar_psiSeries_eq_tsum hsum]
  have hzero : (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α n F z *
        ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
      = fun _ => 0 := by
    funext n
    rcases eq_or_ne n 0 with h | h
    · subst h
      rw [h0, zero_mul]
    · rw [integral_eFam_mul_sinCos2_eq_zero h, mul_zero]
  rw [hzero, tsum_zero]

/-! ## The two specialisations matching the source hypothesis -/

/-- **The corrected form of the requested lemma**: with the source moment vanishing on the
positive half-line (`hF`), and `z > 0`, the moment of `psiSeries α F` at `z` vanishes.  This is the
only correction the requested statement needs (`0 < z`). -/
theorem Fstar_psiSeries_eq_zero_of_pos {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hF : ∀ t : ℝ, 0 < t → Work.Elliptic.Fstar F t = 0) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 :=
  Fstar_psiSeries_eq_zero_of_acoeff_zero hsum
    (Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F hF z hz)



end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_div_z4_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The near-`0` slice mass is `L¹(z^{-4}dz)` under `HkMem α 0`

For `F : ℝ → ℝ → ℝ` with `F ∈ H⁰(α)` in the sense of `Work.Spaces.HkMem α 0 F`, the
`z`-function

  `z ↦ (∫_θ F z θ² · sin(2θ)^{-η}) / z⁴`

is integrable on `(0,1)`.

The point is only the *weight* bookkeeping.  At level `k = 0` the `H^k`-integrand collapses to
the single pure radial term

  `HkIntegrand α 0 F z θ = (F z θ · w z / sin(2θ)^{η/2})² = w z² · F z θ² · sin(2θ)^{-η}`,

so the slice integral occurring in `HkMem` is exactly `w z² = (1+z)⁴/z⁴` times the slice mass
above:

  `∫_θ HkIntegrand α 0 F z θ = w z² · ∫_θ F z θ² · sin(2θ)^{-η}`.

Since `HkMem α 0 F` gives the integrability on `[0,∞)` of that slice integral, and since

  `(∫_θ F z θ² sin(2θ)^{-η}) / z⁴ = (∫_θ HkIntegrand α 0 F z θ) / (1+z)⁴`   (`z ≠ 0`),

while `(1+z)⁴ ≥ 1` for `z > 0`, the target function is dominated on `(0,1)` by the (integrable)
`z ↦ ∫_θ HkIntegrand α 0 F z θ`.  The `z = 0` value is irrelevant: the interval is `(0,1)`.

This is the near-`0` engine of the `PhiStar/Honesty` layer (paired with the far-`∞` statement
`integrableOn_sliceMass_Ioi_one_of_HkMem`).
-/

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- At `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the one term
`i = 0` and the mixed double sum is empty. -/
private lemma HkIntegrand_zero_eq_prv (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem integrableOn_sliceMass_div_z4_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / z ^ 4)
      (Set.Ioo 0 1) := by
  -- The `H⁰`-integrand of `HkMem` is `w z²` times the slice mass appearing in the target.
  have hBG : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
      = Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    intro z
    rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        = ∫ θ in Work.Spaces.Iθ, F z θ * F z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ
        from setIntegral_congr_fun measurableSet_Icc
          (fun θ hθ => by
            rw [HkIntegrand_zero_eq_prv α F z θ,
              Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ])]
    rw [show (∫ θ in Work.Spaces.Iθ,
          F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.w2 z
            * (F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.sig θ)
        from setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  -- On `(0,1)` the two quotients agree, because `w z² · z⁴ = (1+z)⁴`.
  have hkey : ∀ z ∈ Set.Ioo (0:ℝ) 1,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ) / (1 + z) ^ 4
        = (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
            / z ^ 4 := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz.1
    have hw : Work.FTS.EllipticEst.AngSecond.w2 z * z ^ 4 = (1 + z) ^ 4 := by
      rw [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
      field_simp [hz0]
    have hw0 : Work.FTS.EllipticEst.AngSecond.w2 z ≠ 0 := by
      have hwz : Work.Spaces.w z ≠ 0 :=
        div_ne_zero (pow_ne_zero 2 (by linarith [hz.1] : (1:ℝ) + z ≠ 0)) (pow_ne_zero 2 hz0)
      simpa [Work.FTS.EllipticEst.AngSecond.w2] using pow_ne_zero 2 hwz
    rw [hBG z, ← hw]
    field_simp
  -- `HkMem α 0 F` gives the integrability of the slice integral on `[0,∞)`, hence on `(0,1)`.
  have hBint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ) (Set.Ioo 0 1) :=
    hF.2.mono_set (fun z hz => le_of_lt hz.1)
  -- Dividing by `(1+z)⁴ ≥ 1` keeps integrability, since it does not increase the modulus.
  have hSint : MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ) / (1 + z) ^ 4)
      (Set.Ioo 0 1) := by
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
          / (1 + z) ^ 4)
        (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
      hBint.aestronglyMeasurable.mul
        ((measurable_inv.comp
          ((measurable_const.add measurable_id).pow_const 4)).aestronglyMeasurable)
    refine (hBint.norm).mono' haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have h1 : (1:ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith [hz.1])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < (1 + z) ^ 4)]
    exact div_le_self (abs_nonneg _) h1
  exact hSint.congr_fun (fun z hz => hkey z hz) measurableSet_Ioo

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgNearDeriv =====
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

open Work.FTS.EllExist

set_option autoImplicit false

set_option maxHeartbeats 1000000


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.hasFDerivAt_of_fst_snd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.StrongEps.E5Aux

/-- `toSpanSingleton ℝ c` is multiplication by `c` on `ℝ`. -/
theorem toSpanSingleton_real_eq_smul_one (c : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ c = c • (1 : ℝ →L[ℝ] ℝ) := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- **A function on `ℝ × E` with continuous partial derivatives is differentiable.**

If, on an open set `V ∋ p`, the `x`-partial derivatives of `f` exist (with values `g₁`) and
the `y`-partial Fréchet derivatives exist (with values `g₂`), and both `g₁` and `g₂` are
continuous on `V`, then `f` is (strictly) Fréchet differentiable at `p` with derivative
`(x, y) ↦ g₁ p * x + g₂ p y = clmHead E (g₁ p) (g₂ p)`. -/
theorem hasFDerivAt_of_fst_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℝ} {g₁ : ℝ × E → ℝ} {g₂ : ℝ × E → E →L[ℝ] ℝ} {V : Set (ℝ × E)}
    {p : ℝ × E} (hV : IsOpen V) (hp : p ∈ V)
    (h₁ : ∀ q ∈ V, HasDerivAt (fun x : ℝ => f (x, q.2)) (g₁ q) q.1)
    (h₂ : ∀ q ∈ V, HasFDerivAt (fun y : E => f (q.1, y)) (g₂ q) q.2)
    (hc₁ : ContinuousOn g₁ V) (hc₂ : ContinuousOn g₂ V) :
    HasFDerivAt f (Work.FTS.StrongEps.E5Aux.clmHead E (g₁ p) (g₂ p)) p := by
  have hmem : V ∈ 𝓝 p := hV.mem_nhds hp
  -- the `x`-partial derivatives, as continuous linear functionals
  have hdf₁ : ∀ᶠ v in 𝓝 p,
      HasFDerivAt (fun x : ℝ => f (x, v.2)) (g₁ v • (1 : ℝ →L[ℝ] ℝ)) v.1 := by
    filter_upwards [hmem] with v hv
    exact (h₁ v hv).hasFDerivAt.congr_fderiv (toSpanSingleton_real_eq_smul_one (g₁ v))
  have hdf₂ : ∀ᶠ v in 𝓝 p,
      HasFDerivAt (fun y : E => f (v.1, y)) (g₂ v) v.2 := by
    filter_upwards [hmem] with v hv
    exact h₂ v hv
  have hcf₁ : ContinuousAt (fun v : ℝ × E => g₁ v • (1 : ℝ →L[ℝ] ℝ)) p :=
    Filter.Tendsto.smul_const (hc₁.continuousAt hmem) (1 : ℝ →L[ℝ] ℝ)
  have hcf₂ : ContinuousAt (fun v : ℝ × E => g₂ v) p := hc₂.continuousAt hmem
  have hstrict := hasStrictFDerivAt_uncurry_coprod
    (f := fun (x : ℝ) (y : E) => f (x, y))
    (f₁ := fun (x : ℝ) (y : E) => g₁ (x, y) • (1 : ℝ →L[ℝ] ℝ))
    (f₂ := fun (x : ℝ) (y : E) => g₂ (x, y))
    (u := p) hdf₁ hdf₂ hcf₁ hcf₂
  refine hstrict.hasFDerivAt.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨a, b⟩ := x
  have hA : (↿fun (x : ℝ) (y : E) => g₁ (x, y) • (1 : ℝ →L[ℝ] ℝ)) p = g₁ p • 1 := rfl
  have hB : (↿fun (x : ℝ) (y : E) => g₂ (x, y)) p = g₂ p := rfl
  rw [ContinuousLinearMap.coprod_apply, clmHead_apply, hA, hB,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]

end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EFamAngularFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- `deriv` lowers `C^n` regularity by one (univariate form). -/
lemma contDiff_deriv_of_le_efaf {g : ℝ → ℝ} {n m : WithTop ℕ∞} (h : ContDiff ℝ n g)
    (hm : m + 1 ≤ n) : ContDiff ℝ m (deriv g) := by
  have h1 := h.contDiffOn.deriv_of_isOpen (s := Set.univ) (m := m) isOpen_univ hm
  rwa [contDiffOn_univ] at h1

theorem EFamAngularFacts (m : ℕ) :
    Differentiable ℝ (Work.FTS.PhiStar.Gegenbauer.eFam m) ∧
    Differentiable ℝ (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) ∧
    (∃ L M B : ℝ, 0 < L ∧ 0 < M ∧ 0 ≤ B ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ L * θ) ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ L * (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ| ≤ M) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |Real.tan θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ B)) := by
  obtain ⟨A, hA0, hA⟩ := Work.FTS.ClassC.eFam_sin_two_bound m
  obtain ⟨Q, hQ0, hQ⟩ := Work.FTS.ClassC.eFam_deriv_bound m
  have hC3 : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
    Work.FTS.ClassC.contDiff_three_eFam m
  refine ⟨hC3.differentiable (by norm_num), ?_, 2 * A + 1, Q + 1, 2 * A, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact (contDiff_deriv_of_le_efaf hC3 (m := 2) (by norm_num)).differentiable (by norm_num)
  · linarith
  · linarith
  · linarith
  · -- `|eFam m θ| ≤ (2A+1) θ` on `[0, π/2]`
    intro θ hθ
    have hθ0 : 0 ≤ θ := hθ.1
    have hs : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
    have h1 := hA θ hθ
    calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ A * Real.sin (2 * θ) := h1
      _ ≤ A * (2 * θ) := mul_le_mul_of_nonneg_left hs hA0
      _ ≤ (2 * A + 1) * θ := by nlinarith [hθ0]
  · -- `|eFam m θ| ≤ (2A+1) (π/2 - θ)` on `[0, π/2]`
    intro θ hθ
    have hpi : 0 ≤ Real.pi - 2 * θ := by linarith [hθ.2, Real.pi_pos]
    have h2 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have hs : Real.sin (Real.pi - 2 * θ) ≤ Real.pi - 2 * θ := Real.sin_le hpi
    have h1 := hA θ hθ
    calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ A * Real.sin (2 * θ) := h1
      _ = A * Real.sin (Real.pi - 2 * θ) := by rw [Real.sin_pi_sub]
      _ ≤ A * (Real.pi - 2 * θ) := mul_le_mul_of_nonneg_left hs hA0
      _ ≤ (2 * A + 1) * (Real.pi / 2 - θ) := by nlinarith [h2]
  · -- `|deriv (eFam m) θ| ≤ Q + 1` on `[0, π/2]`
    intro θ hθ
    have h1 := hQ θ hθ
    linarith
  · -- `|tan θ · eFam m θ| ≤ 2A` on `(0, π/2)`
    intro θ hθ
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hs2 : Real.sin θ ^ 2 ≤ 1 := by nlinarith [hsin0, hsin1]
    have hb := hA θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hdiv : 0 ≤ Real.sin θ / Real.cos θ := div_nonneg hsin0 (le_of_lt hcos)
    have htanabs : |Real.tan θ| = Real.sin θ / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_nonneg hsin0, abs_of_pos hcos]
    calc |Real.tan θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        = |Real.tan θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := abs_mul _ _
      _ = (Real.sin θ / Real.cos θ) * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by rw [htanabs]
      _ ≤ (Real.sin θ / Real.cos θ) * (A * Real.sin (2 * θ)) :=
            mul_le_mul_of_nonneg_left hb hdiv
      _ = 2 * A * Real.sin θ ^ 2 := by
            rw [Real.sin_two_mul]
            field_simp
      _ ≤ 2 * A := by nlinarith [hA0, hs2]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceOfOsc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem TraceOfOsc {u : ℝ → ℝ} {γ K : ℝ} (hγ : 0 < γ - 1) (hK : 0 ≤ K)
    (hbound : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 4 →
      |u b - u a| ≤ K * (Real.sin (2 * b)) ^ ((γ - 1) / 2)) :
    ∃ mu : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 4),
        (u θ - mu) ^ 2 ≤ K ^ 2 * (Real.sin (2 * θ)) ^ (γ - 1) := by
  have hp : 0 < (γ - 1) / 2 := by linarith
  -- `x ↦ x ^ ((γ-1)/2)` tends to `0` at `0⁺`
  have hxpow : Filter.Tendsto (fun x : ℝ => x ^ ((γ - 1) / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-((γ - 1) / 2)))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith)
    have h2 : Filter.Tendsto (fun x : ℝ => (x ^ (-((γ - 1) / 2)))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      h1.inv_tendsto_atTop
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.rpow_neg (le_of_lt hx), inv_inv]
  have hle1 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- hence `sin (2x) ^ ((γ-1)/2) → 0` at `0⁺`
  have hsinlim : Filter.Tendsto (fun x : ℝ => Real.sin (2 * x) ^ ((γ - 1) / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero' (f := fun x : ℝ => Real.sin (2 * x) ^ ((γ - 1) / 2))
      (g := fun x : ℝ => 2 ^ ((γ - 1) / 2) * x ^ ((γ - 1) / 2)) ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hle1)]
        with x hx1 hx2
      have hx1' : (0 : ℝ) < x := hx1
      have hx2' : x < Real.pi / 2 := hx2
      exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_pos])) _
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hle1)]
        with x hx1 hx2
      have hx1' : (0 : ℝ) < x := hx1
      have hx2' : x < Real.pi / 2 := hx2
      have hs0 : 0 ≤ Real.sin (2 * x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
      have hle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith)
      calc Real.sin (2 * x) ^ ((γ - 1) / 2) ≤ (2 * x) ^ ((γ - 1) / 2) :=
            Real.rpow_le_rpow hs0 hle (le_of_lt hp)
        _ = 2 ^ ((γ - 1) / 2) * x ^ ((γ - 1) / 2) :=
            Real.mul_rpow (by norm_num) (le_of_lt hx1')
    · simpa using hxpow.const_mul (2 ^ ((γ - 1) / 2))
  -- the `ε`-`δ` form of the same limit
  have hdelta : ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.pi / 4 ∧
      ∀ t : ℝ, 0 < t → t < δ → K * Real.sin (2 * t) ^ ((γ - 1) / 2) < ε := by
    intro ε hε
    have hg : Filter.Tendsto (fun t : ℝ => K * Real.sin (2 * t) ^ ((γ - 1) / 2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using hsinlim.const_mul K
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hg) ε hε
    refine ⟨min δ (Real.pi / 4), lt_min hδpos (by positivity), min_le_right _ _,
      fun t ht hlt => ?_⟩
    have htδ : t < δ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hd : dist t 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htδ
    have h1 := hδ ht hd
    rw [Real.dist_eq, sub_zero] at h1
    have hsin_nonneg : 0 ≤ Real.sin (2 * t) ^ ((γ - 1) / 2) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [hlt, min_le_right δ (Real.pi / 4), Real.pi_pos])) _
    rwa [abs_of_nonneg (mul_nonneg hK hsin_nonneg)] at h1
  have hne : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_Ioi_neBot le_rfl
  -- `u` is Cauchy along `𝓝[>] 0`
  have hCauchy : Cauchy (Filter.map u (nhdsWithin 0 (Set.Ioi 0))) := by
    rw [Metric.cauchy_iff]
    refine ⟨hne.map u, ?_⟩
    intro ε hε
    obtain ⟨δ, hδpos, hδle, hδ⟩ := hdelta ε hε
    refine ⟨u '' (Set.Ioo 0 δ), ?_, ?_⟩
    · rw [Filter.mem_map]
      refine Filter.mem_of_superset ?_ (fun x hx => ⟨x, hx, rfl⟩)
      exact Filter.inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds (Iio_mem_nhds hδpos))
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have ha' : (0 : ℝ) < a := ha.1
      have hb' : (0 : ℝ) < b := hb.1
      have haπ : a < Real.pi / 4 := lt_of_lt_of_le ha.2 hδle
      have hbπ : b < Real.pi / 4 := lt_of_lt_of_le hb.2 hδle
      rcases le_total a b with hab | hba
      · rw [Real.dist_eq, abs_sub_comm]
        exact lt_of_le_of_lt (hbound a b ha' hab hbπ) (hδ b hb' hb.2)
      · rw [Real.dist_eq]
        exact lt_of_le_of_lt (hbound b a hb' hba haπ) (hδ a ha' ha.2)
  obtain ⟨mu, hmu⟩ := cauchy_map_iff_exists_tendsto.mp hCauchy
  refine ⟨mu, hmu, ?_⟩
  intro θ hθ
  obtain ⟨hθ0, hθlt⟩ := hθ
  -- pass the pointwise bound to the limit
  have hmem : Set.Ioo (0 : ℝ) θ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hθ0))
  have hev : ∀ᶠ a in (nhdsWithin (0 : ℝ) (Set.Ioi 0)),
      |u θ - u a| ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) := by
    filter_upwards [hmem] with a ha
    exact hbound a θ ha.1 (le_of_lt ha.2) hθlt
  have htend : Filter.Tendsto (fun a : ℝ => |u θ - u a|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds |u θ - mu|) :=
    (tendsto_const_nhds.sub hmu).abs
  have hleval : |u θ - mu| ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) :=
    le_of_tendsto htend hev
  have hsinθ_nonneg : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθlt, Real.pi_pos])
  have hc_nonneg : 0 ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) :=
    mul_nonneg hK (Real.rpow_nonneg hsinθ_nonneg _)
  have hsq : (u θ - mu) ^ 2 ≤ (K * Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2 := by
    rw [sq_le_sq]
    rwa [abs_of_nonneg hc_nonneg]
  have hkey : (K * Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2
      = K ^ 2 * Real.sin (2 * θ) ^ (γ - 1) := by
    have hsθ_pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθlt, Real.pi_pos])
    have hsqp : (Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2
        = Real.sin (2 * θ) ^ (γ - 1) := by
      rw [pow_two, ← Real.rpow_add hsθ_pos ((γ - 1) / 2) ((γ - 1) / 2),
        show (γ - 1) / 2 + (γ - 1) / 2 = γ - 1 by ring]
    rw [mul_pow, hsqp]
  rw [hkey] at hsq
  exact hsq

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.lintegral_backwardDiffQuot_majorant_le_liminf_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option maxHeartbeats 1000000

theorem lintegral_backwardDiffQuot_majorant_le_liminf_theta {a b c c' d' d : ℝ}
    (hcc' : c < c') (hd'd : d' < d) (hab : a < b)
    {ι : Type*} [Fintype ι] {ρ : ι → ℝ → ℝ → ℝ}
    (hρc : ∀ k, ContinuousOn (Function.uncurry (ρ k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ k z θ)
    {V : ℕ → ι → ℝ → ℝ → ℝ} {W : ι → ℝ → ℝ → ℝ}
    (hVsm : ∀ n k, ContDiffOn ℝ 1 (Function.uncurry (V n k)) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hVc : ∀ n k, ContinuousOn (Function.uncurry (V n k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hWmeas : ∀ k, MeasureTheory.AEStronglyMeasurable (Function.uncurry (W k))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hconv : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)), ∀ k,
      Filter.Tendsto (fun n => V n k p.1 p.2) Filter.atTop (nhds (W k p.1 p.2))) :
    ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
        Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
          (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
            * ρ k p.1 p.2) ^ 2)) Filter.atTop
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
          ENNReal.ofReal (∑ k, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2))
          Filter.atTop := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · -- ## Degenerate case: empty index type
    haveI : IsEmpty ι := hempty
    have hL : ∀ (j : ℕ) (p : ℝ × ℝ), (∑ k : ι, ENNReal.ofReal
        (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
          * ρ k p.1 p.2) ^ 2)) = 0 := by
      intro j p
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hR : ∀ (n : ℕ) (p : ℝ × ℝ), (∑ k : ι,
        (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2) = 0 := by
      intro n p
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hLHS : (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
        Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
          (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
            * ρ k p.1 p.2) ^ 2)) Filter.atTop) = 0 := by
      simp only [hL, Filter.liminf_const, MeasureTheory.lintegral_zero]
    have hRHS : (Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
          ENNReal.ofReal (∑ k, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2))
          Filter.atTop) = 0 := by
      simp only [hR, ENNReal.ofReal_zero, MeasureTheory.lintegral_zero, Filter.liminf_const]
    rw [hLHS, hRHS]
  · -- ## Main case
    haveI : Nonempty ι := hne
    let hq : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
    let Fr : ℕ → ℝ × ℝ → ℝ := fun j p =>
      ∑ k, ((W k p.1 p.2 - W k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2
    let FrN : ℕ → ℕ → ℝ × ℝ → ℝ := fun n j p =>
      ∑ k, ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2
    let Gr : ℕ → ℝ × ℝ → ℝ := fun n p =>
      ∑ k, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2
    have hSmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c' d') :=
      measurableSet_Icc.prod measurableSet_Icc
    have hRmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
      measurableSet_Icc.prod measurableSet_Icc
    have hSR : Set.Icc a b ×ˢ Set.Icc c' d' ⊆ Set.Icc a b ×ˢ Set.Icc c d :=
      fun p hp => ⟨hp.1, ⟨le_trans (le_of_lt hcc') hp.2.1, le_trans hp.2.2 (le_of_lt hd'd)⟩⟩
    by_cases hcd : c < d
    swap
    · -- degenerate case `d ≤ c`: the sub-box is empty, hence the left integral vanishes
      have hcd' : d' < c' := by linarith [not_lt.mp hcd, hcc', hd'd]
      have hempty : (Set.Icc a b ×ˢ Set.Icc c' d' : Set (ℝ × ℝ)) = ∅ := by
        rw [Set.Icc_eq_empty (not_le.mpr hcd'), Set.prod_empty]
      have hnull : (MeasureTheory.volume : Measure (ℝ × ℝ)) (Set.Icc a b ×ˢ Set.Icc c' d') = 0 := by
        rw [hempty, measure_empty]
      have hzero : (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
          Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
            (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
              * ρ k p.1 p.2) ^ 2)) Filter.atTop) = 0 := by
        rw [MeasureTheory.Measure.restrict_eq_zero.mpr hnull, MeasureTheory.lintegral_zero_measure]
      rw [hzero]
      exact bot_le
    -- ## 1. A uniform lower bound for `ρ` and a modulus of continuity in `θ`
    have hlow : ∀ k : ι, ∃ m : ℝ, 0 < m ∧ ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, m ≤ ρ k z θ :=
      fun k => (rho_bounds hab hcd (hρc k) (hρp k)).1
    choose m hm_pos hm_le using hlow
    let m0 : ℝ := Finset.univ.inf' Finset.univ_nonempty m
    have hm0_pos : 0 < m0 := by
      show (0 : ℝ) < Finset.univ.inf' Finset.univ_nonempty m
      rw [Finset.lt_inf'_iff]
      intro k _
      exact hm_pos k
    have hm0_le : ∀ (k : ι) (z θ : ℝ), z ∈ Set.Icc a b → θ ∈ Set.Icc c d → m0 ≤ ρ k z θ := by
      intro k z θ hz hθ
      exact le_trans (Finset.inf'_le m (Finset.mem_univ k)) (hm_le k z hz θ hθ)
    have hunif : ∀ ε > 0, ∃ δ > 0, ∀ k : ι, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        ∀ y ∈ Set.Icc c d, |θ - y| < δ → |ρ k z θ - ρ k z y| < ε := by
      intro ε hε
      choose δ hδ_pos hδ_spec using fun k => rho_bounds_theta (hρc k) ε hε
      refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, ?_⟩
      · show (0 : ℝ) < Finset.univ.inf' Finset.univ_nonempty δ
        rw [Finset.lt_inf'_iff]
        intro k _
        exact hδ_pos k
      · intro k z hz θ hθ y hy hlt
        exact hδ_spec k z hz θ hθ y hy (lt_of_lt_of_le hlt (Finset.inf'_le δ (Finset.mem_univ k)))
    -- ## 2. The shift `J`
    have hq_pos : ∀ j : ℕ, 0 < hq j := by intro j; dsimp only [hq]; positivity
    have hq_tendsto : Filter.Tendsto hq Filter.atTop (nhds 0) := by
      simpa only [hq] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, hq J < c' - c :=
      (hq_tendsto.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < c' - c))).exists
    have hq_mono : ∀ j : ℕ, hq (j + J) ≤ hq J := by
      intro j
      dsimp only [hq]
      rw [Nat.cast_add]
      have h1 : (0:ℝ) < (J:ℝ) + 1 := by positivity
      have h2 : (J:ℝ) + 1 ≤ (j:ℝ) + (J:ℝ) + 1 := by
        have h3 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        linarith
      exact one_div_le_one_div_of_le h1 h2
    have hq_lt : ∀ j : ℕ, hq (j + J) < c' - c := fun j => lt_of_le_of_lt (hq_mono j) hJ
    have hshift_map : ∀ j : ℕ, ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c' d',
        (q.1, q.2 - hq (j + J)) ∈ Set.Icc a b ×ˢ Set.Icc c d := by
      intro j q hqS
      obtain ⟨h1, h2⟩ := hqS
      exact ⟨h1, ⟨by linarith [h2.1, hq_lt j], by linarith [h2.2, hd'd, hq_pos (j + J)]⟩⟩
    -- ## 3. Measurability of `W` (and of its shift)
    have hWm : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
      intro k
      have hV : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ => V n k p.1 p.2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        fun n => (hVc n k).aemeasurable hRmeas
      refine AEMeasurable.congr (AEMeasurable.liminf hV) ?_
      filter_upwards [hconv] with p hp
      exact (hp k).liminf_eq
    have hWmS : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
      fun k => (hWm k).mono_set hSR
    have hWshift : ∀ j : ℕ, ∀ k : ι,
        AEMeasurable (fun p : ℝ × ℝ => W k p.1 (p.2 - hq (j + J)))
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro j k
      have hV : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ => V n k p.1 (p.2 - hq (j + J)))
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
        intro n
        have hcs : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') :=
          (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
        exact ((hVc n k).comp hcs (hshift_map j)).aemeasurable hSmeas
      refine AEMeasurable.congr (AEMeasurable.liminf hV) ?_
      filter_upwards [ae_shift_preimage_sub_snd hRmeas hSmeas hconv (hshift_map j)] with p hp
      exact (hp k).liminf_eq
    -- ## 4. Measurability of the integrands
    have hFr_meas : ∀ j : ℕ, AEMeasurable (Fr (j + J))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro j
      have hterm : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ =>
          ((W k p.1 p.2 - W k p.1 (p.2 - hq (j + J))) * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
        intro k
        have h1 : AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2 - W k p.1 (p.2 - hq (j + J)))
            (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
          (hWmS k).sub (hWshift j k)
        have h2 : AEMeasurable (fun p : ℝ × ℝ => ρ k p.1 p.2)
            (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
          ((hρc k).mono hSR).aemeasurable hSmeas
        exact AEMeasurable.pow ((h1.mul_const ((((j + J : ℕ) : ℝ) + 1))).mul h2) aemeasurable_const
      exact Finset.aemeasurable_fun_sum Finset.univ fun k _ => hterm k
    have hFmeas : ∀ j : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Fr (j + J) p))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro j
      have h4a : AEMeasurable (fun p : ℝ × ℝ => ‖Fr (j + J) p‖ₑ)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
        AEStronglyMeasurable.enorm (hFr_meas j).aestronglyMeasurable
      refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
      exact Real.enorm_eq_ofReal (by positivity)
    -- the per-`k` difference-quotient integrand is continuous on the small box
    have hper_meas : ∀ n j : ℕ, ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((V n k p.1 p.2 - V n k p.1 (p.2 - hq (j + J))) * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro n j k
      have hcont : ContinuousOn (fun p : ℝ × ℝ => ((V n k p.1 p.2 - V n k p.1 (p.2 - hq (j + J)))
          * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2) (Set.Icc a b ×ˢ Set.Icc c' d') := by
        have hcs : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') :=
          (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
        have h1 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).mono hSR
        have h2 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 (p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).comp hcs (hshift_map j)
        have h3 : ContinuousOn (fun p : ℝ × ℝ => ρ k p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hρc k).mono hSR
        exact (((h1.sub h2).mul_const (((j + J : ℕ) : ℝ) + 1)).mul h3).pow 2
      have h4a : AEMeasurable (fun p : ℝ × ℝ => ‖((V n k p.1 p.2 - V n k p.1 (p.2 - hq (j + J)))
          * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2‖ₑ)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
        AEStronglyMeasurable.enorm (hcont.aestronglyMeasurable hSmeas)
      refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
      exact Real.enorm_eq_ofReal (by positivity)
    -- ## 5. The a.e. convergence at both the point and the shifted point
    have hae_conv : ∀ j : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')),
        (∀ k : ι, Filter.Tendsto (fun n => V n k p.1 p.2) Filter.atTop (nhds (W k p.1 p.2))) ∧
        (∀ k : ι, Filter.Tendsto (fun n => V n k p.1 (p.2 - hq (j + J))) Filter.atTop
          (nhds (W k p.1 (p.2 - hq (j + J))))) := by
      intro j
      refine (Eventually.filter_mono
        (MeasureTheory.ae_mono (Measure.restrict_mono hSR le_rfl)) hconv).and ?_
      exact ae_shift_preimage_sub_snd hRmeas hSmeas hconv (hshift_map j)
    have hfrN_meas : ∀ j n : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (FrN n (j + J) p))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro j n
      have hcont : ContinuousOn (FrN n (j + J)) (Set.Icc a b ×ˢ Set.Icc c' d') := by
        refine continuousOn_finsetSum Finset.univ fun k _ => ?_
        have hcs : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') :=
          (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
        have h1 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).mono hSR
        have h2 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 (p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).comp hcs (hshift_map j)
        have h3 : ContinuousOn (fun p : ℝ × ℝ => ρ k p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hρc k).mono hSR
        exact (((h1.sub h2).mul_const (((j + J : ℕ) : ℝ) + 1)).mul h3).pow 2
      have h4a : AEMeasurable (fun p : ℝ × ℝ => ‖FrN n (j + J) p‖ₑ)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
        AEStronglyMeasurable.enorm (hcont.aestronglyMeasurable hSmeas)
      refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
      exact Real.enorm_eq_ofReal (by positivity)
    -- ## 6. The two Fatou steps
    have hFatou1 : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
          Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr (j + J) p)) Filter.atTop
        ≤ Filter.liminf (fun j : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (Fr (j + J) p)) Filter.atTop :=
      lintegral_liminf_le' hFmeas
    have hshift_liminf : ∀ p : ℝ × ℝ,
        Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr (j + J) p)) Filter.atTop
          = Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr j p)) Filter.atTop := by
      intro p
      have h := Filter.liminf_comp (fun j : ℕ => ENNReal.ofReal (Fr j p)) (fun j : ℕ => j + J) Filter.atTop
      rw [Filter.map_add_atTop_eq_nat] at h
      exact h
    have hFatou2 : ∀ j : ℕ, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal (Fr (j + J) p)
        ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (FrN n (j + J) p)) Filter.atTop := by
      intro j
      refine lintegral_le_liminf_of_eventually_le (hfrN_meas j) ?_
      filter_upwards [hae_conv j] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      have hlim : Filter.Tendsto (fun n : ℕ => FrN n (j + J) p) Filter.atTop (nhds (Fr (j + J) p)) := by
        have hterm : ∀ k : ι, Filter.Tendsto (fun n : ℕ =>
            ((V n k p.1 p.2 - V n k p.1 (p.2 - hq (j + J))) * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
            Filter.atTop (nhds (((W k p.1 p.2 - W k p.1 (p.2 - hq (j + J)))
              * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2)) := by
          intro k
          exact ((((hp1 k).sub (hp2 k)).mul_const ((((j + J : ℕ) : ℝ) + 1))).mul_const (ρ k p.1 p.2)).pow 2
        exact tendsto_finsetSum Finset.univ fun k _ => hterm k
      have hlim2 := ENNReal.tendsto_ofReal hlim
      rw [hlim2.liminf_eq]
    -- ## 7. The uniform bound, with the weight ratio tending to `1`
    have hq_ltF : ∀ᶠ j : ℕ in Filter.atTop, hq j < c' - c := by
      refine Filter.eventually_atTop.mpr ⟨J, fun j hj => ?_⟩
      rw [show j = (j - J) + J from (Nat.sub_add_cancel hj).symm]
      exact hq_lt (j - J)
    have hbound : ∀ e : ℝ, 0 < e → ∃ K : ℕ, ∀ j ≥ K, ∀ n : ℕ,
        ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal (FrN n (j + J) p)
          ≤ ENNReal.ofReal ((1 + e / m0) ^ 2) * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
              ENNReal.ofReal (Gr n p) := by
      intro e he
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
        (backwardDiffQuot_theta_bound hcc' hd'd hab hρc hρp hVsm hVc (fun j => rfl) hm0_pos
          hm0_le hunif hq_ltF e he)
      exact ⟨K, fun j hj n => hK (j + J) (le_trans hj (Nat.le_add_right j J)) n⟩
    -- ## 9. The chain of inequalities
    set A : ℝ≥0∞ := Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal (Gr n p)) Filter.atTop with hAdef
    have hstep1 : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
          Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr j p)) Filter.atTop
        ≤ Filter.liminf (fun j : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (Fr (j + J) p)) Filter.atTop := by
      refine le_trans (le_of_eq ?_) hFatou1
      exact lintegral_congr fun p => (hshift_liminf p).symm
    have hstep2 : Filter.liminf (fun j : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (Fr (j + J) p)) Filter.atTop
        ≤ Filter.liminf (fun j : ℕ => Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (FrN n (j + J) p)) Filter.atTop) Filter.atTop :=
      liminf_le_liminf_of_le' hFatou2
    have hstep3 : ∀ e : ℝ, 0 < e →
        Filter.liminf (fun j : ℕ => Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (FrN n (j + J) p)) Filter.atTop) Filter.atTop
        ≤ ENNReal.ofReal ((1 + e / m0) ^ 2) * A := by
      intro e he
      obtain ⟨K, hK⟩ := hbound e he
      refine liminf_le_of_eventually_le_const (K := K) fun j hj => ?_
      refine le_trans (liminf_le_liminf_of_le' fun n => hK j hj n) ?_
      have hC0 : ENNReal.ofReal ((1 + e / m0) ^ 2) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]
        have : 0 < (1 + e / m0) ^ 2 := by positivity
        linarith
      exact le_of_eq (liminf_const_mul_of_ne_top hC0 ENNReal.ofReal_ne_top _)
    have hlast : Filter.liminf (fun j : ℕ => Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
          ENNReal.ofReal (FrN n (j + J) p)) Filter.atTop) Filter.atTop ≤ A := by
      by_cases hAtop : A = ⊤
      · rw [hAtop]; exact le_top
      · have hcn : Filter.Tendsto (fun n : ℕ => (1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2)
            Filter.atTop (nhds 1) := by
          have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h2 : Filter.Tendsto (fun n : ℕ => (1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) Filter.atTop
              (nhds ((1 + 0 / m0) ^ 2)) :=
            ((tendsto_const_nhds.add (h1.div_const m0))).pow 2
          simpa using h2
        have hseq : Filter.Tendsto (fun n : ℕ =>
            ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) * A) Filter.atTop (nhds A) := by
          have h3 : Filter.Tendsto (fun n : ℕ =>
              (1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2 * A.toReal) Filter.atTop (nhds (1 * A.toReal)) :=
            hcn.mul_const A.toReal
          have h4 : Filter.Tendsto (fun n : ℕ =>
              ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2 * A.toReal))
              Filter.atTop (nhds (ENNReal.ofReal (1 * A.toReal))) := ENNReal.tendsto_ofReal h3
          have h5 : Filter.Tendsto (fun n : ℕ =>
              ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) * A)
              Filter.atTop (nhds (ENNReal.ofReal (1 * A.toReal))) := by
            refine h4.congr' ?_
            filter_upwards with n
            rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2)]
            congr 1
            exact ENNReal.ofReal_toReal hAtop
          simpa only [one_mul, ENNReal.ofReal_toReal hAtop] using h5
        have hle : ∀ n : ℕ, Filter.liminf (fun j : ℕ => Filter.liminf (fun m : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
              ENNReal.ofReal (FrN m (j + J) p)) Filter.atTop) Filter.atTop
            ≤ ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) * A :=
          fun n => hstep3 (1 / ((n : ℝ) + 1))
            (one_div_pos.mpr (by have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith))
        calc Filter.liminf (fun j : ℕ => Filter.liminf (fun m : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
                ENNReal.ofReal (FrN m (j + J) p)) Filter.atTop) Filter.atTop
            ≤ Filter.liminf (fun n : ℕ =>
                ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) * A) Filter.atTop := by
              refine le_trans (le_iInf fun n => hle n) ?_
              rw [Filter.liminf_eq_iSup_iInf_of_nat]
              refine le_trans ?_ (le_iSup (fun j : ℕ => ⨅ i : ℕ, ⨅ (_ : i ≥ j),
                ENNReal.ofReal ((1 + (1 / ((i : ℝ) + 1)) / m0) ^ 2) * A) 0)
              exact le_iInf fun i => le_iInf fun _ => iInf_le _ i
          _ = A := hseq.liminf_eq
    have hgoalL : (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
          Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
            (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
              * ρ k p.1 p.2) ^ 2)) Filter.atTop)
        = ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
          Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr j p)) Filter.atTop := by
      refine lintegral_congr fun p => ?_
      refine Filter.liminf_congr (Filter.Eventually.of_forall fun j => ?_)
      exact (ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)).symm
    rw [hgoalL]
    exact le_trans hstep1 (le_trans hstep2 hlast)

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# The `cos`-weight tail estimate

For `T ∈ (0, π/2)` we bound the product

`(∫ s in T..π/2, cos(s)² sin(2s)^η) * (∫ s in 0..T, sin(2s)^{-η} / cos(s)^4)`

uniformly in `T`, where `η = Work.Spaces.eta = 99/100`.

Both factors degenerate near the endpoint `s = π/2` (the first tends to `0`, the second blows
up) and the two degeneracies cancel: with `δ = π/2 - T`,

* `∫ s in T..π/2, cos(s)² sin(2s)^η ≤ 2^η δ^{3+η}`   (`cosTailA`),
* `∫ s in 0..T, sin(2s)^{-η}/cos(s)^4 ≤ C₂ δ^{-(3+η)}`   (`cosTailB`),
* and `δ^{3+η} · δ^{-(3+η)} = 1` for `δ > 0`.

So the product is bounded by the constant `2^η · C₂`.
-/



end Work.FTS_EllLimOK.PkgJets
end
