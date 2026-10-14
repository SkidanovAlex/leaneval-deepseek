import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEnv
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.LinvI_solves
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.bessel_cmode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

theorem bessel_cmode (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hint : MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∑ m ∈ Finset.range (N + 1),
        (∫ θ in Work.Spaces.Iθ,
            F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          / (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
      ≤ ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Real.cos θ := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hInt : MeasureTheory.Integrable (fun θ => (F z θ) ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint
  -- the weight `cos` is nonnegative on `Iθ`, so the slice energy is a.e. nonnegative
  have hnonneg_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => (F z θ) ^ 2 * Real.cos θ) := by
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ (F z θ) ^ 2 * Real.cos θ
    rw [MeasureTheory.ae_restrict_iff' hIθ_meas]
    filter_upwards with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hnonnegR : 0 ≤ ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Real.cos θ :=
    MeasureTheory.integral_nonneg_of_ae hnonneg_ae
  -- Bessel's inequality in its normalised `ℝ≥0∞`-form, with the bound rewritten as `ofReal`
  have hb := Work.EllipticEst.ModalSolution.cmode_bessel F z N
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun θ => (F z θ) ^ 2 * Real.cos θ) hInt hnonneg_ae] at hb
  have hmain : (∑ m ∈ Finset.range (N + 1),
      Work.EllipticEst.ModalSolution.eNorm m *
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Real.cos θ :=
    (ENNReal.ofReal_le_ofReal_iff hnonnegR).1 hb
  -- the normalised summands are the summands of the statement
  have hsum : (∑ m ∈ Finset.range (N + 1),
      Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      = ∑ m ∈ Finset.range (N + 1),
        (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          / (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Work.EllipticEst.ModalSolution.cmode_eq m F z]
    rw [Work.EllipticEst.ModalSolution.eNorm]
    -- the `√cos · √cos` form of `bInt` is the numerator of the statement
    have hbInt : Work.EllipticEst.ModalSolution.bInt m F z
        = ∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
      rw [Work.EllipticEst.ModalSolution.bInt]
      refine MeasureTheory.setIntegral_congr_fun hIθ_meas (fun θ hθ => ?_)
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have hsq : Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ) = Real.cos θ := by
        rw [← sq, Real.sq_sqrt hc]
      calc (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * (Real.sqrt (Real.cos θ) * F z θ)
          = (Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ))
              * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * F z θ) := by ring
        _ = Real.cos θ * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * F z θ) := by rw [hsq]
        _ = F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by ring
    rw [hbInt]
    field_simp
  rw [hsum] at hmain
  exact hmain

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## `cmode` as a set integral over `Iθ` -/

/-- `numW` written with the interval integral appearing in the definition of `cmode`. -/
theorem numW_eq_interval (m : ℕ) (G : ℝ → ℝ → ℝ) (z : ℝ) :
    numW m G z = ∫ θ in (0 : ℝ)..(Real.pi / 2),
      G z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
  rw [numW, intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2),
    Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
  simp only [phiW]
  ring

/-- The mode coefficient as `numW` divided by the explicit mode normalisation constant. -/
theorem cmode_eq_numW_div (m : ℕ) (G : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode m G z
      = numW m G z / (((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5)) := by
  rw [Work.FTS.PhiStar.Series.cmode, numW_eq_interval m G z,
    Work.FTS.PhiStar.Gegenbauer.FamNormValue m]

/-- `numW m (D_z G) z = z · pwF m G z`. -/
theorem numW_Dz (m : ℕ) (G : ℝ → ℝ → ℝ) (z : ℝ) :
    numW m (Work.Spaces.Dz G) z = z * pwF m G z := by
  rw [numW, pwF]
  rw [show (fun θ => Work.Spaces.Dz G z θ * phiW m θ)
      = (fun θ => z * (Work.Spaces.pz G z θ * phiW m θ)) from by
    funext θ; simp only [Work.Spaces.Dz]; ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## Elementary interval facts -/


end Work.FTS.ClassCHon.Zpz
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.gssgFKBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-! ## Elementary facts about the weights

The two rows `N₄^{gs}`, `N₅^{gs}` carry the radial factor `r/(1+r)²` next to the *energy*
`√Φ(r)` of the datum; after the two Cauchy–Schwarz steps the radial weight to integrate is
`r⁻¹·(r/(1+r)²) = 1/(1+r)²`.  Hence the two elementary integrals below. -/



/-! ## The angular energy `Φ₀(g)` of the datum and the pointwise Cauchy–Schwarz for `FK g` -/


/-- The pointwise Cauchy–Schwarz bound for the angular moment: `(FK g r)² ≤ 16·Φ₀(g)(r)`. -/
theorem FK_sq_le_sixteen_Phi0 {g : Fn} {r : ℝ} (hr : 0 < r)
    (hsl : MeasureTheory.IntegrableOn (fun θ => (g r θ) ^ 2) Work.Spaces.Iθ)
    (haesm : AEStronglyMeasurable (fun θ => g r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (Work.Construction.FK g r) ^ 2
      ≤ 16 * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
  have h1 := FK_g_pt (g := g) hr hsl haesm
  calc (Work.Construction.FK g r) ^ 2 = |Work.Construction.FK g r| ^ 2 := (sq_abs _).symm
    _ ≤ (4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = 16 * (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
        norm_num
    _ = 16 * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
        rw [Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0]

/-! ## The `N₄^{gs}`, `N₅^{gs}` rows -/

/-- Pointwise angular bound for `N₄^{gs}`: `|K θ N₄^{gs}| ≤ 40α² r/(1+r)² |FK g r|`. -/
theorem N4gs_pt {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
        ≤ (40 * α ^ 2 * (r / (1 + r) ^ 2)) * |Work.Construction.FK g r| := by
  intro r hr θ hθ
  have h1 := K_pthFstar_pt (α := α) (r := r) (θ := θ) hα hα1 hr hθ.1 hθ.2
  have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hFKnn : (0 : ℝ) ≤ |Work.Construction.FK g r| := abs_nonneg _
  have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
      = (1 / 2) * (|Work.Construction.s2 θ|
          * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|)
        * |Work.Construction.FK g r| := by
    simp only [Work.FTS.Nonlin.N4gs, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
    ring
  rw [habs]
  have hstep : |Work.Construction.s2 θ|
        * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ 1 * (80 * α ^ 2 * (r / (1 + r) ^ 2)) :=
    mul_le_mul hs2 h1 (abs_nonneg _) (by norm_num)
  calc (1 / 2) * (|Work.Construction.s2 θ|
        * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|)
        * |Work.Construction.FK g r|
      ≤ (1 / 2) * (1 * (80 * α ^ 2 * (r / (1 + r) ^ 2)))
          * |Work.Construction.FK g r| := by
        refine mul_le_mul_of_nonneg_right ?_ hFKnn
        exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 40 * α ^ 2 * (r / (1 + r) ^ 2) * |Work.Construction.FK g r| := by ring

/-- Pointwise angular bound for `N₅^{gs}`: `|K θ N₅^{gs}| ≤ 60α r/(1+r)² |FK g r|`. -/
theorem N5gs_pt {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
        ≤ (60 * α * (r / (1 + r) ^ 2)) * |Work.Construction.FK g r| := by
  intro r hr θ hθ
  have hFKnn : (0 : ℝ) ≤ |Work.Construction.FK g r| := abs_nonneg _
  have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
    nlinarith [Real.sin_le_one θ, sq_nonneg (Real.sin θ)]
  have hF := Fstar_pt (α := α) (z := r) (θ := θ) hα hα1 hr ⟨hθ.1.le, hθ.2.le⟩
  have hFnn : (0 : ℝ) ≤ 20 * α * r / (1 + r) ^ 2 := by positivity
  have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
      = (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * |Work.Construction.FK g r|
        * |Work.Construction.Fstar α r θ| := by
    simp only [Work.FTS.Nonlin.N5gs, abs_mul, abs_neg,
      abs_of_nonneg (sq_nonneg (Real.sin θ))]
    ring
  rw [habs]
  have hstep : (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * |Work.Construction.FK g r|
      ≤ 1 * 3 * |Work.Construction.FK g r| := by
    calc (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * |Work.Construction.FK g r|
        ≤ (1 * 3) * |Work.Construction.FK g r| :=
          mul_le_mul (mul_le_mul hsin hK (abs_nonneg _) (by norm_num)) le_rfl
            (abs_nonneg _) (by norm_num)
      _ = 1 * 3 * |Work.Construction.FK g r| := by ring
  calc (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * |Work.Construction.FK g r|
        * |Work.Construction.Fstar α r θ|
      ≤ (1 * 3 * |Work.Construction.FK g r|) * (20 * α * r / (1 + r) ^ 2) :=
        mul_le_mul hstep hF (abs_nonneg _) (by norm_num)
    _ = 60 * α * (r / (1 + r) ^ 2) * |Work.Construction.FK g r| := by ring




/-! ## The `N₄^{sg}`, `N₅^{sg}` rows -/





/-! ## The absorption of the rates into `Env` -/

/-- `√α·|g|_{ℋ⁴} ≤ Env α g`. -/
theorem sqrt_alpha_mul_Xn_le_Env {α : ℝ} (g : Fn) (hα : 0 ≤ α) :
    Real.sqrt α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
  rw [Env]
  have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα _) (sq_nonneg _)
  linarith

/-- `α·|g|_{ℋ⁴} ≤ Env α g` for `0 < α ≤ 1`. -/
theorem alpha_mul_Xn_le_Env_dfca1e {α : ℝ} (g : Fn) (hα : 0 < α) (hα1 : α ≤ 1) :
    α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have h1 : α ≤ Real.sqrt α := (Real.le_sqrt hα.le hα.le).mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_right h1 hX0).trans (sqrt_alpha_mul_Xn_le_Env g hα.le)

/-
The four rows whose coefficient is an angular moment: `N4gs = -(1/2)sin2θ·FK(g)·∂_θF_*`,
`N5gs = -sin²θ·FK(g)·F_*`, `N4sg = -(1/2)FK(F_*)·D_θg`, `N5sg = -sin²θ·FK(F_*)·g`.  Only
`α` and `g` occur (`F_* = Fstar α`), so `GalClass α g` is the whole hypothesis.

Bounds to use: `|FK g z| ≤ 4√(∫_θ (g z θ)²)` (`Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le`),
`FK (Fstar α) z = α·2z/(1+z)²` exactly (`Work.FTS.Nonlin.FK_Fstar`, re-exported as
`Work.FTS.NonlinRows.Rl1.FK_Fstar_pt`), the profile bounds `Fstar_pt`, `DthFstar_pt`,
`K_pthFstar_pt` in `Rl1/tools.lean`, the slot energies via `slot0`/`slot1`
(`Phi0 g`, `Phi1 g`), and `Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep` for the rows whose
θ-bound is θ-free.  Rates: `O(α·Xn α g)` for all four, and `α·Xn ≤ √α·Xn ≤ Env α g`.
-/

end

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.PhiStar.FamDerivDivLinv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts about `eFam`, `s2` and `μ` -/

/-- `eFam m 0 = 0`: the Dirichlet eigenfunctions vanish at the left endpoint (the odd-indexed
Gegenbauer polynomials vanish at the origin). -/
lemma eFam_zero_end (m : ℕ) : Gegenbauer.eFam m 0 = 0 := by
  simp only [Gegenbauer.eFam, Real.sin_zero, Real.cos_zero, one_mul]
  exact Gegenbauer.gC_odd_zero m

/-- The angular eigenfunctions are `C³`. -/
lemma contDiff_eFam_fam (m : ℕ) : ContDiff ℝ 3 (Gegenbauer.eFam m) :=
  Real.contDiff_cos.mul ((Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)

/-- `deriv (sin (2·)) = 2 cos (2·)`. -/
lemma deriv_s2_fam : deriv Work.Construction.s2 = fun t : ℝ => 2 * Real.cos (2 * t) := by
  funext t
  have h : HasDerivAt (fun s : ℝ => Real.sin (2 * s)) (Real.cos (2 * t) * 2) t :=
    (Real.hasDerivAt_sin (2 * t)).comp t (by simpa using (hasDerivAt_id t).const_mul 2)
  rw [show Work.Construction.s2 = fun s : ℝ => Real.sin (2 * s)
    from funext Work.Construction.s2_eq, h.deriv]
  ring

lemma differentiable_s2_fam : Differentiable ℝ Work.Construction.s2 := by
  rw [show Work.Construction.s2 = fun s : ℝ => Real.sin (2 * s)
    from funext Work.Construction.s2_eq]
  fun_prop


/-! ## Differentiability of `v = e_m / sin 2θ` and of `v'` -/

lemma differentiableOn_div_s2 (m : ℕ) :
    DifferentiableOn ℝ (fun t : ℝ => Gegenbauer.eFam m t / Work.Construction.s2 t)
      (Set.Ioo 0 (π / 2)) := by
  intro t ht
  exact ((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt
    |>.div (differentiable_s2_fam.differentiableAt) (linv_s2_ne_zero ht)
    |>.differentiableWithinAt

/-- The explicit form of `v'` on the open interval. -/
lemma deriv_div_s2_eventuallyEq (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) =ᶠ[𝓝 t]
      fun s : ℝ => (deriv (Gegenbauer.eFam m) s * Work.Construction.s2 s
        - Gegenbauer.eFam m s * deriv Work.Construction.s2 s)
          / Work.Construction.s2 s ^ 2 := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  have hde : HasDerivAt (Gegenbauer.eFam m) (deriv (Gegenbauer.eFam m) s) s :=
    (((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hds : HasDerivAt Work.Construction.s2 (deriv Work.Construction.s2 s) s :=
    (differentiable_s2_fam.differentiableAt).hasDerivAt
  exact (hde.div hds (linv_s2_ne_zero hs)).deriv

/-- The explicit value of `v'` at a point of the open interval. -/
lemma deriv_div_s2_eq (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) t
      = (deriv (Gegenbauer.eFam m) t * Work.Construction.s2 t
        - Gegenbauer.eFam m t * deriv Work.Construction.s2 t)
          / Work.Construction.s2 t ^ 2 :=
  (deriv_div_s2_eventuallyEq m ht).eq_of_nhds

/-- `v'` is differentiable on the open interval. -/
lemma differentiableOn_deriv_div_s2 (m : ℕ) :
    DifferentiableOn ℝ (deriv (fun t : ℝ => Gegenbauer.eFam m t / Work.Construction.s2 t))
      (Set.Ioo 0 (π / 2)) := by
  intro t ht
  refine (DifferentiableAt.congr_of_eventuallyEq ?_
    (deriv_div_s2_eventuallyEq m ht)).differentiableWithinAt
  have hde : DifferentiableAt ℝ (deriv (Gegenbauer.eFam m)) t :=
    ((ContDiff.deriv' (n := 2) (contDiff_eFam_fam m)).differentiable (by norm_num)).differentiableAt
  have hds : DifferentiableAt ℝ (deriv Work.Construction.s2) t := by
    rw [deriv_s2_fam]; fun_prop
  have he : DifferentiableAt ℝ (Gegenbauer.eFam m) t :=
    ((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt
  have hs2 : DifferentiableAt ℝ Work.Construction.s2 t := differentiable_s2_fam.differentiableAt
  exact ((hde.mul hs2).sub (he.mul hds)).div (hs2.pow 2) (pow_ne_zero 2 (linv_s2_ne_zero ht))

/-! ## The `Lzero1`-congruence and the second-order equation for `v` -/

/-- `Lzero1` only depends on the germ of the function. -/
lemma Lzero1_congr_of_eventuallyEq {f g : ℝ → ℝ} {θ : ℝ} (h : f =ᶠ[𝓝 θ] g) :
    Work.FTS.EllipticEst.Lzero1 f θ = Work.FTS.EllipticEst.Lzero1 g θ := by
  simp only [Work.FTS.EllipticEst.Lzero1]
  have h2 : deriv (deriv f) θ = deriv (deriv g) θ := h.deriv.deriv_eq
  have h3 : (fun t : ℝ => Real.tan t * f t) =ᶠ[𝓝 θ] (fun t : ℝ => Real.tan t * g t) :=
    (Filter.EventuallyEq.refl (𝓝 θ) (fun t : ℝ => Real.tan t)).mul h
  rw [h2, h3.deriv_eq, h.eq_of_nhds]

/-- The second-order equation satisfied by `v = e_m / sin 2θ`: with `H = λ_m e_m`,

  `-sin 2θ · v'' + (6 - 10 cos²θ) v' = H`. -/
lemma deriv2_ode (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    -Real.sin (2 * x)
        * deriv (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      + (6 - 10 * Real.cos x ^ 2)
        * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x
      = Gegenbauer.lam m * Gegenbauer.eFam m x := by
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have hsub := Lzero1_sin2_mul (v := fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)
    hx (differentiableOn_div_s2 m) (differentiableOn_deriv_div_s2 m)
  have hcongr : Work.FTS.EllipticEst.Lzero1
        (fun s : ℝ => Real.sin (2 * s) * (Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      = Work.FTS.EllipticEst.Lzero1 (Gegenbauer.eFam m) x := by
    refine Lzero1_congr_of_eventuallyEq ?_
    have hmem : ∀ᶠ s in 𝓝 x, Work.Construction.s2 s ≠ 0 :=
      continuous_s2.continuousAt.eventually_ne (linv_s2_ne_zero hx)
    filter_upwards [hmem] with s hs
    show Real.sin (2 * s) * (Gegenbauer.eFam m s / Work.Construction.s2 s) = Gegenbauer.eFam m s
    rw [← Work.Construction.s2_eq, mul_div_assoc', mul_div_cancel_left₀ _ hs]
  have hLz : Work.FTS.EllipticEst.Lzero1 (Gegenbauer.eFam m) x
      = Gegenbauer.lam m * Gegenbauer.eFam m x := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero (Gegenbauer.eFam m) 0]
    exact Gegenbauer.eFam_Lzero m hcos 0
  exact (hsub.symm.trans hcongr).trans hLz

/-! ## The key algebraic identity and the derivative of `μ v'` -/

/-- `σμ' + μ(6 - 10cos²θ) = 0` with `σ = sin 2θ`, `μ = sin²θcos³θ` — the reason
`(μ v')' = -μ H/σ` follows from the second-order equation. -/
lemma linv_mu_key (x : ℝ) :
    Real.sin (2 * x) * (2 * Real.sin x * Real.cos x ^ 4 - 3 * Real.sin x ^ 3 * Real.cos x ^ 2)
      + (Real.sin x ^ 2 * Real.cos x ^ 3) * (6 - 10 * Real.cos x ^ 2) = 0 := by
  have h1 := Real.sin_sq_add_cos_sq x
  rw [Real.sin_two_mul]
  linear_combination (-(6 * Real.sin x ^ 2 * Real.cos x ^ 3)) * h1

/-- The value of the derivative of `θ ↦ μ θ · v' θ` on the open interval:

  `(2 sinθcos⁴θ - 3 sin³θcos²θ) v' + μ v'' = -μ H / sin 2θ`. -/
lemma linvMu_mul_deriv_value (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    (2 * Real.sin x * Real.cos x ^ 4 - 3 * Real.sin x ^ 3 * Real.cos x ^ 2)
        * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x
      + LinvMu x
        * deriv (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      = -(LinvMu x * (Gegenbauer.lam m * Gegenbauer.eFam m x)
          / Work.Construction.s2 x) := by
  have hσ : Real.sin (2 * x) ≠ 0 := by
    rw [← Work.Construction.s2_eq]; exact linv_s2_ne_zero hx
  have hODE := deriv2_ode m hx
  have hODE' : Real.sin (2 * x)
        * deriv (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      = (6 - 10 * Real.cos x ^ 2)
          * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x
        - Gegenbauer.lam m * Gegenbauer.eFam m x := by
    linarith [hODE]
  have hW' : deriv (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      = ((6 - 10 * Real.cos x ^ 2)
            * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x
          - Gegenbauer.lam m * Gegenbauer.eFam m x) / Real.sin (2 * x) := by
    rw [eq_div_iff hσ]; linarith [hODE']
  have hkey := linv_mu_key x
  rw [hW', LinvMu, show Work.Construction.s2 x = Real.sin (2 * x)
    from Work.Construction.s2_eq x]
  field_simp
  linear_combination (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x) * hkey

/-! ## A bound for the source and the limits at `0⁺` -/

/-- `s ↦ λ_m e_m(s)` is bounded on the open angular interval. -/
lemma lam_eFam_bdd (m : ℕ) :
    ∃ M : ℝ, ∀ s ∈ Set.Ioo 0 (π / 2),
      |Gegenbauer.lam m * Gegenbauer.eFam m s| ≤ M := by
  have hcont : ContinuousOn (fun s : ℝ => Gegenbauer.lam m * Gegenbauer.eFam m s)
      (Set.Icc 0 (π / 2)) :=
    (continuous_const.mul ((contDiff_eFam_fam m).continuous)).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨M, fun s hs => by
    have h := hM s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    rwa [Real.norm_eq_abs] at h⟩

lemma lam_eFam_contOn (m : ℕ) :
    ContinuousOn (fun s : ℝ => Gegenbauer.lam m * Gegenbauer.eFam m s)
      (Set.Ioo 0 (π / 2)) :=
  (continuous_const.mul ((contDiff_eFam_fam m).continuous)).continuousOn

/-- `ε ↦ μ ε · v' ε → 0` at `0⁺`: on `(0, π/2)` it equals the continuous expression
`(cos ε/4)(e_m' ε · sin 2ε - e_m ε · (sin 2·)' ε)`, whose value at `0` is `0`. -/
lemma tendsto_linvMu_mul_deriv_div_s2 (m : ℕ) :
    Tendsto (fun ε : ℝ =>
        LinvMu ε * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcont : ContinuousAt (fun ε : ℝ => Real.cos ε / 4
      * (deriv (Gegenbauer.eFam m) ε * Work.Construction.s2 ε
        - Gegenbauer.eFam m ε * deriv Work.Construction.s2 ε)) 0 := by
    refine ContinuousAt.mul ?_ ?_
    · exact (Real.continuous_cos.continuousAt).div_const 4
    · refine ContinuousAt.sub (ContinuousAt.mul ?_ ?_) (ContinuousAt.mul ?_ ?_)
      · exact (ContDiff.deriv' (n := 2) (contDiff_eFam_fam m)).continuous.continuousAt
      · exact differentiable_s2_fam.continuous.continuousAt
      · exact (contDiff_eFam_fam m).continuous.continuousAt
      · rw [deriv_s2_fam]; fun_prop
  have h0 : Real.cos 0 / 4 * (deriv (Gegenbauer.eFam m) 0 * Work.Construction.s2 0
      - Gegenbauer.eFam m 0 * deriv Work.Construction.s2 0) = 0 := by
    simp [eFam_zero_end m]
  have hlim : Tendsto (fun ε : ℝ => Real.cos ε / 4
      * (deriv (Gegenbauer.eFam m) ε * Work.Construction.s2 ε
        - Gegenbauer.eFam m ε * deriv Work.Construction.s2 ε)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h1 := hcont.tendsto
    rwa [h0] at h1
  have hlim' : Tendsto (fun ε : ℝ => Real.cos ε / 4
      * (deriv (Gegenbauer.eFam m) ε * Work.Construction.s2 ε
        - Gegenbauer.eFam m ε * deriv Work.Construction.s2 ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hlim.mono_left nhdsWithin_le_nhds
  refine hlim'.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos])] with ε hε
  refine (Eq.symm ?_)
  have hε' : ε ∈ Set.Ioo 0 (π / 2) := ⟨hε.1, hε.2⟩
  have hsin : Real.sin ε ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hε.1 (by linarith [Real.pi_pos, hε.2]))
  have hcos : Real.cos ε ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hε.1], hε.2⟩)
  have hval : LinvMu ε / Work.Construction.s2 ε ^ 2 = Real.cos ε / 4 := by
    rw [LinvMu, Work.Construction.s2_eq, Real.sin_two_mul]
    field_simp
    ring
  rw [deriv_div_s2_eq m hε', mul_div_assoc', mul_div_right_comm, hval]

/-- `ε ↦ ∫_0^ε μ H / sin 2θ → 0` at `0⁺` (`O(ε²)`). -/
lemma tendsto_LinvPrim_fam (m : ℕ) :
    Tendsto (fun ε : ℝ => ∫ s in (0 : ℝ)..ε,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨M, hM⟩ := lam_eFam_bdd m
  have hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖(∫ s in (0 : ℝ)..ε,
          LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s)‖
        ≤ M * ε ^ 2 / 4 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos])] with ε hε
    rw [Real.norm_eq_abs]
    exact abs_LinvPrim_le (lam_eFam_contOn m) hM ⟨hε.1, hε.2⟩ ⟨hε.1, le_rfl⟩
  have hg : Tendsto (fun ε : ℝ => M * ε ^ 2 / 4) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h2 : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun ε : ℝ => ε ^ 2 := by fun_prop
      simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun ε : ℝ => M * ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (M * 0)) := h2.const_mul M
    rw [mul_zero] at h3
    have h4 : Tendsto (fun ε : ℝ => M * ε ^ 2 / 4) (𝓝[>] (0 : ℝ)) (𝓝 (0 / 4)) := h3.div_const 4
    rwa [zero_div] at h4
  have habs : Tendsto (fun ε : ℝ => ‖(∫ s in (0 : ℝ)..ε,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbd hg
  exact tendsto_zero_iff_norm_tendsto_zero.mpr habs

/-! ## The constancy argument -/

/-- `Φ m t = μ t · v'(t) + ∫_0^t μ H / sin 2θ`, the quantity whose constancy on `(0, π/2)`
encodes the identity `μ v' = -∫_0^· μH/σ`. -/
def PhiFam (m : ℕ) : ℝ → ℝ := fun t : ℝ =>
  LinvMu t * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) t
    + ∫ s in (0 : ℝ)..t,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s


/-- The derivative of `Φ = μ v' + ∫_0^θ μH/σ` vanishes at every point of `(0, π/2)`. -/
lemma PhiFam_hasDerivAt_zero (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (PhiFam m) 0 x := by
  set V : ℝ → ℝ :=
    deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) with hV
  have hW : HasDerivAt V (deriv V x) x :=
    ((differentiableOn_deriv_div_s2 m x hx).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hA : HasDerivAt (fun t : ℝ => LinvMu t * V t)
      (-(LinvMu x * (Gegenbauer.lam m * Gegenbauer.eFam m x) / Work.Construction.s2 x)) x := by
    refine ((hasDerivAt_LinvMu x).mul hW).congr_deriv ?_
    exact linvMu_mul_deriv_value m hx
  have hB : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s)
      (LinvMu x * (Gegenbauer.lam m * Gegenbauer.eFam m x) / Work.Construction.s2 x) x :=
    hasDerivAt_LinvPrim (h := fun s : ℝ => Gegenbauer.lam m * Gegenbauer.eFam m s)
      (lam_eFam_contOn m) (lam_eFam_bdd m) hx
  exact (hA.add hB).congr_deriv (by ring)

/-- `Φ = μ v' + ∫_0^θ μH/σ` vanishes identically on `(0, π/2)`. -/
lemma PhiFam_eq_zero (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : PhiFam m θ = 0 := by
  have hderiv : ∀ x ∈ Set.Ioo 0 (π / 2), HasDerivAt (PhiFam m) 0 x :=
    fun x hx => PhiFam_hasDerivAt_zero m hx
  have hconst : ∀ ε : ℝ, 0 < ε → ε < θ → PhiFam m θ = PhiFam m ε := by
    intro ε hε0 hεθ
    have hmin : min ε θ = ε := min_eq_left hεθ.le
    have hmax : max ε θ = θ := max_eq_right hεθ.le
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := PhiFam m) (f' := fun _ : ℝ => 0)
      (a := ε) (b := θ)
      (fun y hy => hderiv y ⟨lt_of_lt_of_le hε0 (by rw [← hmin]; exact hy.1),
        lt_of_le_of_lt (by rw [← hmax]; exact hy.2) hθ.2⟩)
      intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at h
    linarith
  have hlim0 : Tendsto (PhiFam m) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (PhiFam m) (𝓝[>] (0 : ℝ)) (𝓝 (0 + 0)) :=
      (tendsto_linvMu_mul_deriv_div_s2 m).add (tendsto_LinvPrim_fam m)
    rwa [add_zero] at h
  have hevent : PhiFam m =ᶠ[𝓝[>] (0 : ℝ)] fun _ => PhiFam m θ := by
    filter_upwards [Ioo_mem_nhdsGT hθ.1] with ε hε
    exact (hconst ε hε.1 hε.2).symm
  have hlimθ : Tendsto (PhiFam m) (𝓝[>] (0 : ℝ)) (𝓝 (PhiFam m θ)) :=
    tendsto_const_nhds.congr' hevent.symm
  have h00 : (0 : ℝ) = PhiFam m θ := tendsto_nhds_unique hlim0 hlimθ
  exact h00.symm

/-! ## The target identity -/

theorem FamDerivDivLinv (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : deriv (fun θ' => Work.FTS.PhiStar.Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ = Work.FTS.PhiStar.Linv (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ := by
  have hΦ := PhiFam_eq_zero m hθ
  have hΦ' : LinvMu θ * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ
      + (∫ s in (0 : ℝ)..θ,
          LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s) = 0 := hΦ
  have hμ : LinvMu θ ≠ 0 := LinvMu_ne_zero_of_mem_Ioo hθ
  have hIP : LinvPrim (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') θ
      = -(LinvMu θ * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ) := by
    change (∫ s in (0 : ℝ)..θ,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s) = _
    linarith [hΦ']
  rw [Linv_apply, hIP]
  have hfin : -((LinvMu θ)⁻¹ * -(LinvMu θ
        * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ))
      = deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ := by
    rw [show -((LinvMu θ)⁻¹ * -(LinvMu θ
          * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ))
        = ((LinvMu θ)⁻¹ * LinvMu θ)
          * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ from by ring,
      inv_mul_cancel₀ hμ, one_mul]
  exact hfin.symm

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.cmode_hasDerivAt_pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptQSmooth

/-- The set integral over `Iθ = [0,π/2]` is the interval integral over `0..π/2`. -/
private theorem setIntegral_Iθ_eq_intervalIntegral (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- **Differentiation of the mode coefficient in `z`.**  For a source `F` smooth on all of
`ℝ²`, the `m`-th angular mode coefficient `cmode m F z` (an integral over `Iθ = [0,π/2]` of
the slice `F z ·` against the mode `e_m` and the weight `cos θ`, divided by a constant) is
differentiable in `z`, with derivative the `m`-th mode coefficient of the partial derivative
`∂_z F`: differentiation under the integral sign. -/
theorem cmode_hasDerivAt_pz {F : ℝ → ℝ → ℝ}
    (hF : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry F)) (m : ℕ) (z : ℝ) :
    HasDerivAt (fun z' => Work.FTS.PhiStar.Series.cmode m F z')
      (Work.FTS.PhiStar.Series.cmode m (Work.Spaces.pz F) z) z := by
  -- smoothness of `F` as a function of two variables
  have hFdiff : Differentiable ℝ (Function.uncurry F) := (hF 1).differentiable (by norm_num)
  have hFcont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := (hF 0).continuous
  -- joint continuity of the partial derivative `∂_z F`
  have hpz_cont : Continuous (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) := by
    have hfderiv_cont : Continuous (fderiv ℝ (Function.uncurry F)) :=
      (hF 1).continuous_fderiv (by norm_num)
    refine (hfderiv_cont.clm_apply
      (continuous_const : Continuous fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)))).congr fun p => ?_
    exact (Work.Spaces.pz_eq_fderiv (hFdiff.differentiableAt)).symm
  -- continuity of the angular mode `e_m`
  have he_cont : Continuous fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
    show Continuous (fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
    exact Real.continuous_cos.mul
      ((Work.FTS.PhiStar.Gegenbauer.continuous_gC (2 * m + 1)).comp Real.continuous_sin)
  -- joint continuity of the two integrands on `Set.univ ×ˢ Iθ`
  have hg : ContinuousOn
      (Function.uncurry fun s θ => F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        F p.1 p.2 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) :=
      (hFcont.mul (he_cont.comp continuous_snd)).mul
        (Real.continuous_cos.comp continuous_snd)
    exact h.continuousOn
  have hgz : ContinuousOn
      (Function.uncurry fun s θ =>
        Work.Spaces.pz F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        Work.Spaces.pz F p.1 p.2 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) :=
      (hpz_cont.mul (he_cont.comp continuous_snd)).mul
        (Real.continuous_cos.comp continuous_snd)
    exact h.continuousOn
  -- the pointwise derivative of the integrand is the integrand of the claimed derivative
  have hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ s ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun s => F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        (Work.Spaces.pz F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) s := by
    intro θ _ s _
    have hslice : DifferentiableAt ℝ (fun s' => F s' θ) s :=
      Work.Spaces.differentiableAt_curry_left (hFdiff.differentiableAt)
    have h1 : HasDerivAt (fun s' => F s' θ) (Work.Spaces.pz F s θ) s := hslice.hasDerivAt
    exact (h1.mul_const (Work.FTS.PhiStar.Gegenbauer.eFam m θ)).mul_const (Real.cos θ)
  -- differentiation under the integral sign over `Iθ`
  have hmain := Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt (V := Set.univ)
    isOpen_univ (Set.mem_univ z) hg hgz hdiff
  -- rewrite the integrals over `Iθ` as interval integrals over `0..π/2`
  have hmain' : HasDerivAt
      (fun s => ∫ θ in (0 : ℝ)..(Real.pi / 2),
        F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.Spaces.pz F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) z := by
    rw [show (fun s => ∫ θ in (0 : ℝ)..(Real.pi / 2),
          F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        = (fun s => ∫ θ in Work.Spaces.Iθ,
          F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) from
      funext fun s => (setIntegral_Iθ_eq_intervalIntegral _).symm]
    exact hmain.congr_deriv (setIntegral_Iθ_eq_intervalIntegral _)
  -- divide by the (constant) normalising factor
  have hfin := hmain'.div_const
    (∫ θ in (0 : ℝ)..(Real.pi / 2), Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  simpa [Work.FTS.PhiStar.Series.cmode] using hfin

end Work.FTS.PhiStar.Honesty.CptQSmooth
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.eFam_cos_sq_sin_rpow_integral_le_eNorm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `cos θ ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
private lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-- `θ ↦ sin (2θ)^η` is continuous on `Iθ` (`η` is the nonzero constant `99/100`). -/
private lemma continuousOn_sin_two_rpow_eta :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun _ _ => Or.inr (by norm_num [Work.Spaces.eta]))

theorem eFam_cos_sq_sin_rpow_integral_le_eNorm (m : ℕ) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      ≤ Work.EllipticEst.ModalSolution.eNorm m := by
  rw [Work.EllipticEst.ModalSolution.eNorm]
  have hI : MeasurableSet Work.Spaces.Iθ := Work.EllipticEst.ModalSolution.measurableSet_Iθ
  -- integrability of the two integrands on the compact `Iθ`
  have hcontL : ContinuousOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
    (((Work.EllipticEst.ModalSolution.continuous_eFam m).mul
      Real.continuous_cos).pow 2).continuousOn.mul continuousOn_sin_two_rpow_eta
  have hcontR : Continuous
      (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) :=
    ((Work.EllipticEst.ModalSolution.continuous_eFam m).pow 2).mul Real.continuous_cos
  refine MeasureTheory.setIntegral_mono_on
    (hcontL.integrableOn_compact isCompact_Icc)
    (hcontR.continuousOn.integrableOn_compact isCompact_Icc) hI ?_
  intro θ hθ
  have hcos0 : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hrpow : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hs0 hs1 Work.Spaces.eta_nonneg
  have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith
  have hsq : (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
      = Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ ^ 2 := by ring
  calc (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
      ≤ (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hrpow (sq_nonneg _)
    _ = (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 := mul_one _
    _ = Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ ^ 2 := hsq
    _ ≤ Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ :=
        mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.SummableModes =====
section

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

/-! ## The `m = 0` coefficient of `bmode` vanishes -/

/-- For an angular model (`AngModel α ψ` carries the moment condition `∫ψ sinCos2 = 0`), the
`m = 0` mode coefficient of `ψ` vanishes: `e_0 = 3 sinθcosθ`, so `bmode 0 ψ` is `3·Fstar`. -/
theorem bmode_zero (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  have h := Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF
  rw [bmode_eq_cmode 0 ψ 0]
  exact h

/-! ## Summability of the mode series -/

/-- **The mode series is absolutely summable at every point of the open quadrant**, given the
three crux estimates. -/
theorem summable_modes (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hrad : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ z : ℝ, 0 < z →
      |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ))) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Summable (fun m : ℕ => acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cr, hCr, hrad⟩ := hrad
  intro z hz θ hθ
  set K : ℝ := α ^ 2 * Cd * Cr * Cg * (1 + 1 / z) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : 0 < 1 + 1 / z := by
      have hz' : 0 < 1 / z := one_div_pos.mpr hz
      linarith
    positivity
  have hg0 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 : ℝ))) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(3 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(3 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(3 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  refine Summable.of_norm_bounded (hg0.mul_left K) (fun m => ?_)
  by_cases hm : m = 0
  · subst hm
    have hz0 : acoeff α 0 (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 0 := by
      rw [acoeff_RemSource, bmode_zero ψ hψ.moment]
      simp
    rw [hz0, norm_zero]
    exact mul_nonneg (le_of_lt hKpos) (by positivity)
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    rw [Real.norm_eq_abs, acoeff_RemSource]
    calc |α ^ 2 * bmode m ψ
              * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        = |α ^ 2| * |bmode m ψ|
            * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by rw [abs_mul, abs_mul, abs_mul]
      _ = α ^ 2 * |bmode m ψ|
            * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
      _ ≤ (α ^ 2 * (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
            * (Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)))
            * (Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) := by
          have hb := hdec m hm1
          have hr := hrad m hm1 z hz
          have he := hgr m θ hθ
          gcongr
      _ = K * ((m : ℝ) + 1) ^ (-(3 : ℝ)) := by
          have hp : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1) ^ (-(2 : ℝ))
              * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) = ((m : ℝ) + 1) ^ (-(3 : ℝ)) := by
            rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
            norm_num
          rw [← hp, hK]
          ring

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.eFam_energy_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series

open Work.FTS.PhiStar.Gegenbauer (eFam gC contDiff_gC gC_ode gC_rec)

namespace EB

set_option autoImplicit false

/-! ## The Sturm–Liouville set-up -/

/-- `Npsi m = (2m+2)(2m+3)`: the spectral constant of the `θ`-equation of `eFam m`
(namely `n(n+3)+2` for `n = 2m+1`). -/
def Npsi (m : ℕ) : ℝ := (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)

lemma Npsi_pos (m : ℕ) : 0 < Npsi m := by
  have h1 : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  have h2 : (0 : ℝ) < 2 * (m : ℝ) + 3 := by positivity
  unfold Npsi
  exact mul_pos h1 h2

/-- `ug m x = (1 - x²)·gC (2m+1) x`. -/
def ug (m : ℕ) : ℝ → ℝ := fun x => (1 - x ^ 2) * gC (2 * m + 1) x

/-- The energy of `ug m`, written without denominators:
`ene m x = u'(x)² + N·(1-x²)·q(x)²`.  For `x ≠ ±1` this equals `u'(x)² + N·u(x)²/(1-x²)`. -/
def ene (m : ℕ) : ℝ → ℝ :=
  fun x => (deriv (ug m) x) ^ 2 + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x) ^ 2)

/-! ## Smoothness of the Gegenbauer polynomials -/

lemma differentiable_gC (k : ℕ) : Differentiable ℝ (gC k) :=
  (contDiff_gC k).differentiable (by norm_num)

lemma differentiable_deriv_gC (k : ℕ) : Differentiable ℝ (deriv (gC k)) :=
  ((contDiff_gC k).deriv' (n := 2)).differentiable (by norm_num)

/-- `C^{(3/2)}_k(1) = (k+1)(k+2)/2`. -/
lemma gC_at_one (k : ℕ) : gC k 1 = (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2 := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    norm_num
  | one =>
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    norm_num
  | more n ih1 ih2 =>
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h : ((n : ℝ) + 2) * gC (n + 2) 1
        = ((n : ℝ) + 2) * ((((n : ℝ) + 2) + 1) * (((n : ℝ) + 2) + 2) / 2) := by
      rw [gC_rec n 1, ih1, ih2]
      push_cast
      ring
    have hh := mul_left_cancel₀ h2 h
    rw [hh]
    push_cast
    ring

/-! ## The first and second derivatives of `ug` -/

lemma deriv_ug (m : ℕ) (x : ℝ) :
    deriv (ug m) x
      = -2 * x * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub (1 : ℝ))
  have h2 : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) x) x :=
    (differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y)
      ((-(2 * x)) * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x) x :=
    h1.mul h2
  have h4 : deriv (ug m) x
      = (-(2 * x)) * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
    rw [show ug m = fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y from rfl]
    exact h3.deriv
  rw [h4]
  ring

lemma deriv2_ug (m : ℕ) (x : ℝ) :
    deriv (deriv (ug m)) x
      = -2 * gC (2 * m + 1) x - 4 * x * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x := by
  have hfun : deriv (ug m)
      = fun y : ℝ => -2 * y * gC (2 * m + 1) y + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y :=
    funext (deriv_ug m)
  rw [hfun]
  have hlin : HasDerivAt (fun y : ℝ => (-2 : ℝ) * y) (-2) x := hasDerivAt_const_mul (-2)
  have h1 : HasDerivAt (fun y : ℝ => -2 * y * gC (2 * m + 1) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x) x :=
    hlin.mul ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h1' : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub (1 : ℝ))
  have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((-(2 * x)) * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x) x :=
    h1'.mul ((differentiable_deriv_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h3 : HasDerivAt
      (fun y : ℝ => -2 * y * gC (2 * m + 1) y + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      (((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x)
        + ((-(2 * x)) * deriv (gC (2 * m + 1)) x
          + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x)) x :=
    h1.add h2
  rw [h3.deriv]
  ring

/-- **The Sturm–Liouville equation in `u`-form**: `u'' = -N·q`. -/
lemma ug_deriv2 (m : ℕ) (x : ℝ) :
    deriv (deriv (ug m)) x = -(Npsi m) * gC (2 * m + 1) x := by
  have hode := (gC_ode (2 * m + 1)).2 x
  have hkey : (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x
      = 4 * x * deriv (gC (2 * m + 1)) x
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * gC (2 * m + 1) x := by
    linarith [hode]
  have hN : Npsi m = (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 := by
    unfold Npsi
    push_cast
    ring
  rw [deriv2_ug m x, hkey, hN]
  ring

/-- `u'(1) = -N`. -/
lemma deriv_ug_one (m : ℕ) : deriv (ug m) 1 = -Npsi m := by
  rw [deriv_ug m 1]
  have hg : gC (2 * m + 1) 1 = Npsi m / 2 := by
    rw [gC_at_one (2 * m + 1)]
    unfold Npsi
    push_cast
    ring
  rw [hg]
  ring

lemma differentiable_deriv_ug (m : ℕ) : Differentiable ℝ (deriv (ug m)) := by
  rw [funext (deriv_ug m)]
  exact (((differentiable_const (-2 : ℝ)).mul differentiable_id).mul
      (differentiable_gC (2 * m + 1))).add
    (((differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)).mul
      (differentiable_deriv_gC (2 * m + 1)))

/-! ## The energy and its monotonicity -/

lemma differentiable_ene (m : ℕ) : Differentiable ℝ (ene m) := by
  have h1 : Differentiable ℝ (fun x : ℝ => (deriv (ug m) x) ^ 2) :=
    (differentiable_deriv_ug m).pow 2
  have h2 : Differentiable ℝ (fun x : ℝ => (1 : ℝ) - x ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  have h3 : Differentiable ℝ (fun x : ℝ => (gC (2 * m + 1) x) ^ 2) :=
    (differentiable_gC (2 * m + 1)).pow 2
  have h4 : Differentiable ℝ
      (fun x : ℝ => Npsi m * (((1 : ℝ) - x ^ 2) * (gC (2 * m + 1) x) ^ 2)) :=
    (differentiable_const (Npsi m)).mul (h2.mul h3)
  exact h1.add h4

lemma continuous_ene (m : ℕ) : Continuous (ene m) := (differentiable_ene m).continuous

/-- On `x ≠ ±1` the denominator-free energy is the usual `u'² + N·u²/(1-x²)`. -/
lemma ene_eq (m : ℕ) {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) :
    ene m x = (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 := by
  show (deriv (ug m) x) ^ 2 + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x) ^ 2)
      = (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
  rw [show ug m x = (1 - x ^ 2) * gC (2 * m + 1) x from rfl]
  field_simp

/-- `E'(x) = 2xN·q(x)²`. -/
lemma deriv_ene (m : ℕ) (x : ℝ) :
    deriv (ene m) x = 2 * x * Npsi m * (gC (2 * m + 1) x) ^ 2 := by
  have hdu : HasDerivAt (deriv (ug m)) (deriv (deriv (ug m)) x) x :=
    (differentiable_deriv_ug m).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => (deriv (ug m) y) ^ 2)
      (2 * (deriv (ug m) x) ^ (2 - 1) * deriv (deriv (ug m)) x) x := hdu.pow 2
  have hsq : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub (1 : ℝ))
  have h2 : HasDerivAt (fun y : ℝ => ((1 : ℝ) - y ^ 2) * (gC (2 * m + 1) y) ^ 2)
      ((-(2 * x)) * (gC (2 * m + 1) x) ^ 2
        + (1 - x ^ 2) * (2 * (gC (2 * m + 1) x) ^ (2 - 1)
            * deriv (gC (2 * m + 1)) x)) x := by
    have hg : HasDerivAt (fun y : ℝ => (gC (2 * m + 1) y) ^ 2)
        (2 * (gC (2 * m + 1) x) ^ (2 - 1) * deriv (gC (2 * m + 1)) x) x :=
      ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt).pow 2
    exact hsq.mul hg
  have h3 : HasDerivAt
      (fun y : ℝ => Npsi m * (((1 : ℝ) - y ^ 2) * (gC (2 * m + 1) y) ^ 2))
      (Npsi m * ((-(2 * x)) * (gC (2 * m + 1) x) ^ 2
        + (1 - x ^ 2) * (2 * (gC (2 * m + 1) x) ^ (2 - 1)
            * deriv (gC (2 * m + 1)) x))) x :=
    h2.const_mul (Npsi m)
  have h4 : HasDerivAt (ene m)
      (2 * (deriv (ug m) x) ^ (2 - 1) * deriv (deriv (ug m)) x
        + Npsi m * ((-(2 * x)) * (gC (2 * m + 1) x) ^ 2
          + (1 - x ^ 2) * (2 * (gC (2 * m + 1) x) ^ (2 - 1)
              * deriv (gC (2 * m + 1)) x))) x :=
    h1.add h3
  rw [h4.deriv, ug_deriv2 m x, deriv_ug m x]
  ring

/-- `E(1) = N²`. -/
lemma ene_one (m : ℕ) : ene m 1 = Npsi m ^ 2 := by
  show (deriv (ug m) 1) ^ 2 + Npsi m * ((1 - (1 : ℝ) ^ 2) * (gC (2 * m + 1) 1) ^ 2)
      = Npsi m ^ 2
  rw [deriv_ug_one m]
  ring

/-- `E ≤ E(1) = N²` on `[0,1]`. -/
lemma ene_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : ene m x ≤ Npsi m ^ 2 := by
  have hmono : MonotoneOn (ene m) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_ene m).continuousOn
      (differentiable_ene m).differentiableOn ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    rw [deriv_ene m y]
    exact mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * y) (le_of_lt (Npsi_pos m)))
      (sq_nonneg _)
  have h1 : ene m x ≤ ene m 1 := hmono hx ⟨by norm_num, le_rfl⟩ hx.2
  rwa [ene_one m] at h1

/-! ## The pointwise bound on `u` and on `eFam` -/

lemma ug_bound (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (ug m x) ^ 2 ≤ Npsi m * (1 - x ^ 2) := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hc : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hE : (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
        ≤ Npsi m ^ 2 := by
      rw [← ene_eq m hne]
      exact ene_le m hx
    have h3 : (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 ≤ Npsi m ^ 2 := by
      linarith [hE, sq_nonneg (deriv (ug m) x)]
    rw [div_mul_eq_mul_div₀, div_le_iff₀ hc] at h3
    have h5 : Npsi m * (ug m x) ^ 2 ≤ Npsi m * (Npsi m * (1 - x ^ 2)) := by
      calc Npsi m * (ug m x) ^ 2 ≤ Npsi m ^ 2 * (1 - x ^ 2) := h3
        _ = Npsi m * (Npsi m * (1 - x ^ 2)) := by ring
    exact le_of_mul_le_mul_left h5 (Npsi_pos m)
  · subst heq
    simp [ug]

/-- **The energy bound**: `|eFam m θ| ≤ √((2m+2)(2m+3))` for `θ ∈ (0, π/2)`. -/
lemma eFam_abs_le_sqrt_N (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |eFam m θ| ≤ Real.sqrt (Npsi m) := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsq : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hb := ug_bound m (show (Real.sin θ) ∈ Set.Icc (0 : ℝ) 1 from ⟨hs0, hs1⟩)
  have h2 : (ug m (Real.sin θ)) ^ 2 = (Real.cos θ) ^ 2 * (eFam m θ) ^ 2 := by
    show ((1 - (Real.sin θ) ^ 2) * gC (2 * m + 1) (Real.sin θ)) ^ 2
        = (Real.cos θ) ^ 2 * (Real.cos θ * gC (2 * m + 1) (Real.sin θ)) ^ 2
    rw [hsq]
    ring
  rw [h2] at hb
  have hsq2 : (eFam m θ) ^ 2 ≤ Npsi m := by
    have hc2 : 0 < (Real.cos θ) ^ 2 := pow_pos hc 2
    have hbb : (Real.cos θ) ^ 2 * (eFam m θ) ^ 2 ≤ (Real.cos θ) ^ 2 * Npsi m := by
      calc (Real.cos θ) ^ 2 * (eFam m θ) ^ 2 ≤ Npsi m * (1 - (Real.sin θ) ^ 2) := hb
        _ = Npsi m * (Real.cos θ) ^ 2 := by rw [hsq]
        _ = (Real.cos θ) ^ 2 * Npsi m := by ring
    exact le_of_mul_le_mul_left hbb hc2
  calc |eFam m θ| = Real.sqrt ((eFam m θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Npsi m) := Real.sqrt_le_sqrt hsq2

/-! ## The final arithmetic -/

/-- `√((2m+2)(2m+3)) ≤ 2·(2m+1)^{3/2}·(cos θ)^{-1/2}` for `m ≥ 1`, `θ ∈ (0, π/2)`. -/
lemma sqrt_Npsi_le (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sqrt (Npsi m) ≤ 2 * ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
      * Real.sqrt (1 / Real.cos θ) := by
  have hmn : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn0 : 0 ≤ 2 * (m : ℝ) + 1 := by linarith
  have hle : Npsi m ≤ (2 * (2 * (m : ℝ) + 1)) ^ 2 := by
    have hsq : 0 ≤ ((m : ℝ) - 1) ^ 2 := sq_nonneg _
    unfold Npsi
    nlinarith [hmn, hsq]
  have h2n : (0 : ℝ) ≤ 2 * (2 * (m : ℝ) + 1) := by linarith
  have h1 : Real.sqrt (Npsi m) ≤ 2 * (2 * (m : ℝ) + 1) := by
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg h2n] at h
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hs : 1 ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hn0]
    linarith
  have hy : 1 ≤ Real.sqrt (1 / Real.cos θ) := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ 1 / Real.cos θ)]
    rw [le_div_iff₀ hc]
    linarith
  have hmid : (1 : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (1 / Real.cos θ) :=
    by simpa using mul_le_mul hs hy zero_le_one (Real.sqrt_nonneg _)
  have h2 : 2 * (2 * (m : ℝ) + 1) ≤ 2 * ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
      * Real.sqrt (1 / Real.cos θ) := by
    have hstep : (2 * (m : ℝ) + 1)
        ≤ ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) * Real.sqrt (1 / Real.cos θ) := by
      have h0 := mul_le_mul_of_nonneg_left hmid hn0
      calc (2 * (m : ℝ) + 1) = (2 * (m : ℝ) + 1) * 1 := by ring
        _ ≤ (2 * (m : ℝ) + 1)
            * (Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (1 / Real.cos θ)) := h0
        _ = ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
            * Real.sqrt (1 / Real.cos θ) := by ring
    linarith [hstep]
  linarith [h1, h2]

end EB


end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.sum_bmode_eFam_eq =====
section

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

/-! ## elementary conversions -/

/-- The set integral over `Iθ = Icc 0 (π/2)` is the interval integral over `0..π/2`. -/
lemma iota_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]

/-- `bmode 0 ψ = 0` for an angular model (the moment condition kills the kernel `e_0`). -/
lemma bmode_zero_loc (α : ℝ) (ψ : ℝ → ℝ) (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    bmode 0 ψ = 0 := by
  have hF0 : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hψ.moment
  rw [bmode_eq_cmode 0 ψ 0]
  exact Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF0

/-- The normalisation of `eFam m` in the weight `cos θ dθ` is positive. -/
lemma eFam_norm_pos (m : ℕ) :
    0 < ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
  rw [iota_eq_interval, Work.FTS.PhiStar.Gegenbauer.FamNormValue]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  positivity

/-- The defining relation of `bmode`, in set-integral form. -/
lemma bmode_mul_norm (m : ℕ) (ψ : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = bmode m ψ * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
  have hden := iota_eq_interval
    (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  have hnum := iota_eq_interval
    (fun θ => ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
  have hne : (∫ θ in (0 : ℝ)..(π / 2),
      Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) ≠ 0 := by
    rw [← hden]
    exact ne_of_gt (eFam_norm_pos m)
  simp only [bmode]
  rw [hnum, hden, div_mul_cancel₀ _ hne]

/-! ## auxiliary versions of the three delegated lemmas -/

/-- `Σ (m+1)^{-s}` converges for `s > 1`. -/
lemma summable_one_add_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-s)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    (Real.summable_nat_rpow (p := -s)).mpr (by linarith)
  have h' := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-s)) 1).mpr h
  simpa only [Nat.cast_add, Nat.cast_one] using h'

/-- The pointwise bound behind the summability, continuity and integration lemmas. -/
lemma abs_bmode_mul_eFam_le_aux (α : ℝ) (ψ : ℝ → ℝ) (hψ : Work.FTS.PhiStar.AngModel α ψ)
    {Cg Cd : ℝ} (hCg : 0 < Cg) (hCd : 0 < Cd)
    (hsup : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * ((m : ℝ) + 1))
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [bmode_zero_loc α ψ hψ, zero_mul, abs_zero]
    exact le_of_lt (mul_pos (mul_pos hCd hCg) (Real.rpow_pos_of_pos (by norm_num) _))
  · rw [abs_mul]
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    calc |bmode m ψ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) * (Cg * ((m : ℝ) + 1)) :=
          mul_le_mul (hdec m hm) (hsup m θ hθ) (abs_nonneg _)
            (le_of_lt (mul_pos hCd (Real.rpow_pos_of_pos hmpos _)))
      _ = Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
          have hp : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1)
              = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
            calc ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1)
                = ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1) ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
              _ = ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ) + 1) := (Real.rpow_add hmpos _ _).symm
              _ = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by norm_num
          rw [← hp]
          ring

theorem summable_bmode_eFam_aux (α : ℝ) (ψ : ℝ → ℝ)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :
    ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  intro θ hθ
  refine Summable.of_norm_bounded
    ((summable_one_add_rpow (3 / 2) (by norm_num)).mul_left (Cd * Cg)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  exact abs_bmode_mul_eFam_le_aux α ψ hψ hCg hCd hsup hdec m hθ

theorem continuousOn_tsum_bmode_eFam_aux (α : ℝ) (ψ : ℝ → ℝ)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hsum : ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ)) :
    ContinuousOn (fun θ : ℝ => ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  refine continuousOn_tsum (fun m => (continuous_const.mul (continuous_eFam m)).continuousOn)
    ((summable_one_add_rpow (3 / 2) (by norm_num)).mul_left (Cd * Cg)) (fun m θ hθ => ?_)
  rw [Real.norm_eq_abs]
  exact abs_bmode_mul_eFam_le_aux α ψ hψ hCg hCd hsup hdec m hθ

theorem integral_series_mul_eFam_aux (α : ℝ) (ψ : ℝ → ℝ) (n : ℕ)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hsum : ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ)) :
    (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ)
      = Work.FTS.PhiStar.Series.bmode n ψ *
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  have hB : 0 ≤ Cg * ((n : ℝ) + 1) :=
    le_of_lt (mul_pos hCg (by positivity))
  have hmain : HasSum (fun m : ℕ => ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) := by
    refine hasSum_integral_of_dominated_convergence
      (μ := volume.restrict Work.Spaces.Iθ)
      (F := fun m θ => (Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (f := fun θ => (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (fun m _ => (Cd * Cg * (Cg * ((n : ℝ) + 1))) * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))
      ?_ ?_ ?_ ?_ ?_
    · intro m
      exact ((continuous_const.mul (continuous_eFam m)).mul
        ((continuous_eFam n).mul Real.continuous_cos)).aestronglyMeasurable
    · intro m
      simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_bmode_mul_eFam_le_aux α ψ hψ hCg hCd hsup hdec m ha
      have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n a * Real.cos a|
          ≤ Cg * ((n : ℝ) + 1) := by
        rw [abs_mul]
        calc |Work.FTS.PhiStar.Gegenbauer.eFam n a| * |Real.cos a|
            ≤ (Cg * ((n : ℝ) + 1)) * 1 :=
              mul_le_mul (hsup n a ha) (Real.abs_cos_le_one a) (abs_nonneg _) hB
          _ = Cg * ((n : ℝ) + 1) := by ring
      have h3 : (0 : ℝ) ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) :=
        le_of_lt (mul_pos (mul_pos hCd hCg) (Real.rpow_pos_of_pos (by positivity) _))
      calc |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m a|
            * |Work.FTS.PhiStar.Gegenbauer.eFam n a * Real.cos a|
          ≤ (Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) * (Cg * ((n : ℝ) + 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) h3
        _ = (Cd * Cg * (Cg * ((n : ℝ) + 1))) * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by ring
    · exact Filter.Eventually.of_forall
        (fun _ => (summable_one_add_rpow (3 / 2) (by norm_num)).mul_left _)
    · exact integrable_const _
    · simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      exact ((hsum a ha).hasSum).mul_right _
  -- identify the two sides
  set G : ℕ → ℝ := fun m => ∫ θ in Work.Spaces.Iθ,
    Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
      * Real.cos θ with hG
  have hterm : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      = Work.FTS.PhiStar.Series.bmode m ψ * G m := by
    intro m
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [h1, integral_const_mul, hG]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  have hGzero : ∀ m : ℕ, m ≠ n → G m = 0 := by
    intro m hmn
    show (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) = 0
    rw [iota_eq_interval]
    exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  have hGn : G n = ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ := by
    rw [hG]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  calc (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    _ = ∑' m : ℕ, ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := hmain.tsum_eq.symm
    _ = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * G m := tsum_congr hterm
    _ = Work.FTS.PhiStar.Series.bmode n ψ * G n :=
        tsum_eq_single n (fun m hm => by rw [hGzero m hm, mul_zero])
    _ = Work.FTS.PhiStar.Series.bmode n ψ *
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
        rw [hGn]

/-! ## the assembly -/

theorem sum_bmode_eFam_eq (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :
    ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  have hsum := summable_bmode_eFam_aux α ψ hψ hsup hdec
  have hcont := continuousOn_tsum_bmode_eFam_aux α ψ hψ hsup hdec hsum
  set F : ℝ → ℝ := fun θ => ∑' m : ℕ, bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
    with hFdef
  have hFcont : ContinuousOn F Work.Spaces.Iθ := hcont
  have hcontSub : ContinuousOn (fun θ : ℝ => ψ θ - F θ) Work.Spaces.Iθ :=
    hψ.cont.sub hFcont
  -- the `e_m`-coefficients of `psi` and of the series
  have hψcoef : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = bmode n ψ * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    rw [← bmode_mul_norm n ψ]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  have hFcoef : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = bmode n ψ * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    rw [← integral_series_mul_eFam_aux α ψ n hψ hsup hdec hsum]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  -- orthogonality of the difference against every eigenfunction
  have horth : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ) = 0 := by
    intro n
    have hψint : IntegrableOn
        (fun θ : ℝ => ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hψ.cont.mul ((continuous_eFam n).continuousOn.mul Real.continuous_cos.continuousOn))
    have hFint : IntegrableOn
        (fun θ : ℝ => F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hFcont.mul ((continuous_eFam n).continuousOn.mul Real.continuous_cos.continuousOn))
    have hcongr : (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ)
          * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            (ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
              - F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [hcongr, integral_sub hψint hFint, hψcoef n, hFcoef n, sub_self]
  -- measurability and integrability of the difference
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => ψ θ - F θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hcontSub.aestronglyMeasurable measurableSet_Icc
  have hint : IntegrableOn (fun θ : ℝ => (ψ θ - F θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hcontSub.pow 2).mul Real.continuous_cos.continuousOn)
  have hae : (fun θ : ℝ => ψ θ - F θ) =ᵐ[volume.restrict Work.Spaces.Iθ] 0 :=
    Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ : ℝ => ψ θ - F θ) hmeas hint horth
  -- transfer to the open interval and use continuity
  have hsub : Set.Ioo (0 : ℝ) (π / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hae' : (fun θ : ℝ => ψ θ - F θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have heq : EqOn (fun θ : ℝ => ψ θ - F θ) 0 (Set.Ioo 0 (π / 2)) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) hae' isOpen_Ioo
      (hcontSub.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
      continuousOn_const
  intro θ hθ hθ2
  have h0 : ψ θ - F θ = 0 := heq ⟨hθ, hθ2⟩
  have : F θ = ψ θ := by linarith
  exact this

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingConstMul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Scalar multiples in the elementary slot pairing

The elementary slot pairing
`slotPairing ρ a b u v = ∫_z ∫_θ ρ · (D_z^bD_θ^a u) · (D_z^bD_θ^a v)`
(`Work.FTS.TransportS.slotPairing`) is `ℝ`-linear in its first slot *whenever the other
factors are fixed only by the weight `ρ` and the second slot*: for every constant `c : ℝ`,

`slotPairing ρ a b (c·v) f = c · slotPairing ρ a b v f`.

The whole content is that the iterated operators `D_z^b`, `D_θ^a` (and hence `mixed b a`)
commute with multiplication by a *constant* scalar factor, and that a constant is pulled out
of the iterated integral.  Both are unconditional (no smoothness of `v` is needed): the
`deriv` of a constant multiple is the constant multiple of the `deriv` — `deriv_const_mul_field`
holds for the totalised `deriv` as well, because `λ·v` is differentiable exactly where `v` is,
and elsewhere both sides vanish.

This is the linearity step used to reduce a pairing of a scalar multiple of the vorticity to
the pairing of the vorticity itself.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The iterated operators commute with constant scalar factors -/


/-- `D_θ^i(c·f) = c·D_θ^i f`, unconditionally (pointwise in `(z,θ)`). -/
theorem DthIter_const_mul_pure (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const_mul_field c]
    ring

/-- `D_z^j(c·f) = c·D_z^j f`, unconditionally (pointwise in `(z,θ)`). -/
theorem DzIter_const_mul_pure (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [deriv_const_mul_field c]
    ring

/-- `D_z^jD_θ^i(c·f) = c·D_z^jD_θ^i f`, unconditionally (pointwise in `(z,θ)`). -/
theorem mixed_const_mul_pure (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_const_mul_pure, DzIter_const_mul_pure]

/-! ## The pairing -/

/-- **The elementary slot pairing is `ℝ`-homogeneous in its first slot**: multiplying the
first argument by a constant multiplies the pairing by that constant. -/
theorem SlotPairingConstMul {ρ : ℝ → ℝ → ℝ} (a b : ℕ) (c : ℝ) {v f : ℝ → ℝ → ℝ}
      (hv : Work.FTS.EllipticEst.SmoothOpen v) :
      Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * v z θ) f
        = c * Work.FTS.TransportS.slotPairing ρ a b v f := by
  unfold Work.FTS.TransportS.slotPairing
  rw [mixed_const_mul_pure c v b a]
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ,
          ρ z θ * (c * Work.Spaces.mixed b a v z θ) * Work.Spaces.mixed b a f z θ)
        = c * ∫ θ in Work.Spaces.Iθ,
            ρ z θ * Work.Spaces.mixed b a v z θ * Work.Spaces.mixed b a f z θ := by
    intro z
    rw [show (fun θ => ρ z θ * (c * Work.Spaces.mixed b a v z θ)
            * Work.Spaces.mixed b a f z θ)
          = fun θ => c * (ρ z θ * Work.Spaces.mixed b a v z θ
            * Work.Spaces.mixed b a f z θ) from funext fun θ => by ring]
    rw [MeasureTheory.integral_const_mul]
  rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (c * Work.Spaces.mixed b a v z θ) * Work.Spaces.mixed b a f z θ)
      = ∫ z in Work.Spaces.Iz, c * (∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a v z θ * Work.Spaces.mixed b a f z θ) from
    integral_congr_ae (Filter.Eventually.of_forall hinner)]
  rw [MeasureTheory.integral_const_mul]

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0`

The term `N₀ α (F_* + f) f` of the modulation (§Modulation of Elgindi's paper) is `C^∞` on the
*open* quadrant `(0,∞) × (0,π/2)` as soon as the perturbation `f` and the *radial* function
`z ↦ L₁₂(f)(z)` are.

`N₀` is a sum of six products of the angular factors `sin 2θ`, `c2m θ = cos 2θ - sin²θ`, the
radial factors `z ↦ L₁₂(F_*)(z)`, `z ↦ L₁₂(f)(z)`, and the fields `f`, `∂_θf`, `D_zf`,
`∂_θ(F_*+f)`, `D_z(F_*+f)`, `∂_θF_*`, `D_zF_*`.

* `F_*` is `C^∞` on the open quadrant for **every real** `α` (`LocData.SmoothQuad_Fstar`, no
  hypothesis on `α`), and the class `SmoothOpen` is closed under `+`, `-`, `·`, constants and
  the operators `pz`, `pth`, `Dz`;
* `z ↦ L₁₂(F_*)(z)` is smooth *without* any hypothesis on `α`: the angular and radial variables
  of `L₁₂(F_*)` separate,
  `L₁₂(F_*)(z) = C(α) · (2/(1+z))` with `C(α) = ∫_0^{π/2} K(θ)·α·(Γ(θ)/c(α)) dθ` a constant
  (this is the `α ≤ 1`-free form of `Construction.L12_Fstar_eq`, whose hypothesis `α ≤ 1` only
  serves to produce `c(α) ≠ 0` for the cancellation `C(α) = α`; the *smoothness* never needs
  the cancellation);
* `z ↦ L₁₂(f)(z)` is smooth on `(0,∞)` by hypothesis (`hL`).

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Work.FTS.EllipticEst

/-! ## Elementary closure of `SmoothOpen`

Local copies (the tree's `SmoothOpen`-API modules are partly unbuildable), proved directly from
Mathlib's `ContDiffOn` API. -/

theorem so_add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ + g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf hg ⊢
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact hf.add hg

theorem so_sub {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ - g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf hg ⊢
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact hf.sub hg

theorem so_mul {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ * g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf hg ⊢
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact hf.mul hg

theorem so_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => c * f z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf ⊢
  have h : Function.uncurry (fun z θ => c * f z θ) = c • Function.uncurry f := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact hf.const_smul c

/-- The constant function is `C^∞` on the open quadrant. -/
theorem so_const (c : ℝ) : SmoothOpen (fun _ _ : ℝ => c) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  exact contDiffOn_const

/-- A function of `z` alone which is `C^n` on `(0,∞)` for every `n` is `C^∞` on the open
quadrant. -/
theorem so_radial {r : ℝ → ℝ} (hr : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0)) :
    SmoothOpen (fun z _ => r z) := by
  refine smoothOpen_of_forall fun n => ?_
  exact (hr n).comp contDiffOn_fst (fun p hp => (mem_Q0.mp hp).1)

/-- A function of `θ` alone which is `C^∞` on `ℝ` is `C^∞` on the open quadrant. -/
theorem so_snd {g : ℝ → ℝ} (hg : ContDiff ℝ Work.Stability.smoothOrder g) :
    SmoothOpen (fun _ (θ : ℝ) => g θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  exact (hg.comp_contDiffOn contDiff_snd.contDiffOn).mono (Set.subset_univ _)

/-- `sin(2·)` is `C^∞`. -/
theorem contDiff_s2 : ContDiff ℝ Work.Stability.smoothOrder Work.Construction.s2 := by
  unfold Work.Construction.s2
  exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

/-- `c2m θ = cos 2θ - sin²θ` is `C^∞`. -/
theorem contDiff_c2m : ContDiff ℝ Work.Stability.smoothOrder Work.Construction.c2m := by
  unfold Work.Construction.c2m
  have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.cos (2 * θ)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ ^ 2) :=
    Real.contDiff_sin.pow 2
  exact h1.sub h2

/-! ## `F_*` and the radial function `L₁₂(F_*)` -/

/-- The model profile `F_*` is `C^∞` on the open quadrant, for every real `α`. -/
theorem smoothOpen_Fstar (α : ℝ) : SmoothOpen (Work.Construction.Fstar α) :=
  (Work.FTS.LocData.SmoothQuad_Fstar α).mono
    (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl)

/-- **The angular density of `L₁₂(F_*)` is a *constant* times `F_*(s)/s`**, for every real `α`
(no hypothesis on `α`, and in particular no use of `c(α) ≠ 0`): the angle and the radius
separate in `F_*(s,θ) = α·(Γ(θ)/c(α))·F_*(s)`. -/
theorem L12dens_Fstar_mul_const (α s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
      = (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
        * (Work.FM.Fstar s / s) := by
  rw [Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
        * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpoint θ)]
  rw [MeasureTheory.integral_mul_const]

/-- **`L₁₂(F_*)(z) = C(α)·2/(1+z)` for every real `α` and every `z ≥ 0`**, the `α ≤ 1`-free
form of `Construction.L12_Fstar_eq`. -/
theorem L12_Fstar_mul_const (α z : ℝ) (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z
      = (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
        * (2 / (1 + z)) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => L12dens_Fstar_mul_const α s)]
  rw [MeasureTheory.integral_const_mul, Work.FM.integral_Ioi_Fstar_div z hz]

/-- **The radial function `z ↦ L₁₂(F_*)(z)` is `C^∞` on `(0,∞)`**, for every real `α`. -/
theorem smoothOpen_L12_Fstar (α : ℝ) :
    SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  refine so_radial (fun n => ?_)
  have hc : ContDiffOn ℝ n (fun z : ℝ =>
      (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
        * (2 / (1 + z))) (Set.Ioi 0) := by
    refine contDiffOn_const.mul ?_
    refine contDiffOn_const.div (contDiffOn_const.add contDiffOn_id) ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    show (1 : ℝ) + z ≠ 0
    linarith
  exact hc.congr (fun z hz => L12_Fstar_mul_const α z (le_of_lt hz))

/-! ## The target -/

theorem SmoothN0 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
      (hf : Work.FTS.EllipticEst.SmoothOpen f)
      (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) := by
  have hFstar : SmoothOpen (Work.Construction.Fstar α) := smoothOpen_Fstar α
  have hT : SmoothOpen (fun z θ => Work.Construction.Fstar α z θ + f z θ) :=
    so_add hFstar hf
  have hLF : SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    smoothOpen_L12_Fstar α
  -- the six summands of `N₀`
  have hT1 : SmoothOpen (fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ) :=
    so_mul (so_mul (so_const_mul (3 / (2 * α)) (so_snd contDiff_s2)) hLF) hFstar.pth
  have hT2 : SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    so_mul (so_mul (so_snd contDiff_c2m) hLF) hFstar.Dz
  have hT3 : SmoothOpen (fun z θ => (1 / α) * Work.Construction.L12 f z * f z θ) :=
    so_mul (so_const_mul (1 / α) hL) hf
  have hT4 : SmoothOpen (fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 f z
      * Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ) :=
    so_mul (so_mul (so_const_mul (3 / (2 * α)) (so_snd contDiff_s2)) hL) hT.pth
  have hT5 : SmoothOpen (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
      * Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ) :=
    so_mul (so_mul (so_snd contDiff_c2m) hL) hT.Dz
  have hT6 : SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz f z θ) :=
    so_mul (so_mul (so_snd contDiff_c2m) hLF) hf.Dz
  have key : SmoothOpen (fun z θ =>
      (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + (1 / α) * Work.Construction.L12 f z * f z θ
        + (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 f z
          * Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 f z
          * Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz f z θ) :=
    ((((hT1.sub hT2).add hT3).add hT4).sub hT5).sub hT6
  refine ContDiffOn.congr
    (f₁ := Function.uncurry (fun z θ =>
      Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ))
    key ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N0]

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The data of a coefficient field `A` available for the level-six rows.**

`K0` prices the field itself pointwise on the open quadrant (for the perturbation residual this
is `row_N_resid_pt`; for a star field `StarPkg6`; for `FK f` its explicit bound), `K4` prices its
`ℋ⁴`-norm (`Xn α A`, from `EllPkgGo`) and `K6` its `ℋ⁶`-norm (from `EllPkgK α 6`). -/
structure CoefData (α : ℝ) (A : Fn) (K0 K4 K6 : ℝ) : Prop where
  /-- interior smoothness on the open quadrant. -/
  sm : Work.FTS.EllipticEst.SmoothOpen A
  /-- `ℋ⁴`-honesty. -/
  h4 : Work.Spaces.HkMem α 4 A
  /-- `ℋ⁶`-honesty. -/
  h6 : Work.Spaces.HkMem α 6 A
  /-- the pointwise pricing on the open quadrant. -/
  val : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0
  /-- the `ℋ⁴`-pricing. -/
  n4 : Work.FTS.Nonlin.Xn α A ≤ K4
  /-- the `ℋ⁶`-pricing. -/
  n6 : Work.Spaces.HkNorm α 6 A ≤ K6

/-- **The data of the datum `f`** for the level-six rows: the slice class `H6Adm` (honest `ℋ⁶`
with the angular/axis vanishing), order-seven honesty (needed by the transport lemmas), and the
a-priori `ℋ⁴`-bound `Xn α f ≤ M`. -/
structure DatData (α : ℝ) (f : Fn) (M : ℝ) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen f
  h6 : Work.Spaces.HkMem α 6 f
  h7 : Work.Spaces.HkMem α 7 f
  vanish : Work.Spaces.VanishTheta f
  axis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0
  bdd : Work.FTS.Nonlin.Xn α f ≤ M

/-- The datum data of a slice in `L6Ctx`. -/
theorem datData_of_H6Adm {α M : ℝ} {f : Fn}
    (hreg : Work.FTS.StrongPersist.H6Adm α f) (h7 : Work.Spaces.HkMem α 7 f)
    (hbdd : Work.FTS.Nonlin.Xn α f ≤ M) :
    DatData α f M :=
  ⟨hreg.reg.1, hreg.reg.2, h7, hreg.vanish, hreg.axis, hbdd⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZaux.PertResidPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PertResidPt`: the pointwise bounds of the perturbation residual `ℛ, 𝒰/ sin 2θ, 𝒱`

This file proves the pointwise (`L^∞`) form of the three inequalities carried by the
open-quadrant elliptic package `Work.FTS.VocabO.EllPkgGo α Ce f Ef`.  The package gives,
for each of the three residual coefficients

* `ℛ := Rop α (PhiTil α f Ef)`,
* `𝒰 := Uop α (PhiTil α f Ef) / s2`,
* `𝒱 := Vop (PhiTil α f Ef)`,

both the honesty of the datum at level `ℋ⁴` (`HQo α 4 · = SmoothOpen · ∧ HkMem α 4 ·`) and
the norm bound `Xn α · ≤ Ce · Xn α f`.  The missing link is the pointwise bound

  `|·(z,θ)| ≤ C / √(γ-1) · Xn α ·`  (`z > 0`, `0 < θ < π/2`),

which is Elgindi's Corollary `SecondDerivativesBounded` in the open class: it is exactly the
`b = 0` instance of `Work.FTS.TransportS.sup_dz_le_hk` applied to the residual coefficient
itself, since `D_z^0 = id`.  Composing the two inequalities gives

  `|·(z,θ)| ≤ C₀ · (1/√(γ-1)) · (Ce · Xn α f) ≤ (4 C₀ + 1) · α^{-1/2} · Ce · Xn α f`,

because `γ - 1 = α/10 ≥ α/16`, i.e. `1/√(γ-1) ≤ 4 α^{-1/2}` (`inv_sqrt_gam_le` below).

The sign of `Ce` has to be handled: the package only asserts `Xn α · ≤ Ce · Xn α f`, with no
positivity of `Ce`.  For `Ce < 0` that inequality forces `Xn α · = 0`, and since the residual
is `SmoothOpen` with `HkMem α 4`, `HkSqZeroOnQuad` upgrades `HkSq α 4 · = 0` to the honest
pointwise vanishing on the open quadrant, so the bound holds with both sides `0`
(it also forces `Xn α f = 0`).

Everything rests on the axioms `propext`, `Classical.choice`, `Quot.sound` only.

(Scratch: this directory still contains the elaboration harness `_probe_PRP.lean` /
`_probe_PRP2.lean` used while developing the proof; nothing imports them.)
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.NZaux

/-- For the Elgindi exponent `γ = 1 + α/10` one has `1/√(γ-1) ≤ 4 α^{-1/2}`
(quantitatively: `γ - 1 = α/10 ≥ α/16`, so `√(γ-1) ≥ √α/4`). -/
private lemma inv_sqrt_gam_le {α : ℝ} (hα : 0 < α) :
    1 / Real.sqrt (Work.Spaces.gam α - 1) ≤ 4 * α ^ (-(1 / 2 : ℝ)) := by
  have h4 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h16 : Real.sqrt (α / 16) = Real.sqrt α / 4 := by
    rw [Real.sqrt_div hα.le, h4]
  have hmono : Real.sqrt α / 4 ≤ Real.sqrt (Work.Spaces.gam α - 1) := by
    rw [← h16]
    exact Real.sqrt_le_sqrt (by rw [Work.Spaces.gam_sub_one]; linarith)
  have hpos : (0 : ℝ) < Real.sqrt α / 4 := by
    have := Real.sqrt_pos_of_pos hα
    linarith
  have h1 : 1 / Real.sqrt (Work.Spaces.gam α - 1) ≤ 1 / (Real.sqrt α / 4) :=
    one_div_le_one_div_of_le hpos hmono
  have h2 : 1 / (Real.sqrt α / 4) = 4 * α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow α, one_div_div, div_eq_mul_inv]
  calc 1 / Real.sqrt (Work.Spaces.gam α - 1)
      ≤ 1 / (Real.sqrt α / 4) := h1
    _ = 4 * α ^ (-(1 / 2 : ℝ)) := h2

/-- **The pointwise bounds for the residual coefficients of the elliptic package.**
The universal constant is `4 C₀ + 1`, where `C₀` is the universal constant of
`Work.FTS.TransportS.sup_dz_le_hk`. -/
theorem PertResidPt : ∃ C : ℝ, 0 < C ∧ ∀ {α Ce : ℝ} {f Ef : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.VocabO.EllPkgGo α Ce f Ef →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ / Work.Construction.s2 θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) := by
  obtain ⟨C0, hC0pos, hsup⟩ := Work.FTS.TransportS.sup_dz_le_hk
  refine ⟨4 * C0 + 1, by linarith, ?_⟩
  intro α Ce f Ef hα hα1 hpkg
  -- the generic step: `SmoothOpen` + `HkMem α 4` + `Xn α w ≤ Ce · Xn α f` give the
  -- pointwise bound for `w` with the universal constant `4 C₀ + 1`
  have key : ∀ (w : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen w → Work.Spaces.HkMem α 4 w →
      Work.FTS.Nonlin.Xn α w ≤ Ce * Work.FTS.Nonlin.Xn α f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |w z θ| ≤ (4 * C0 + 1) * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
    intro w hsm hmem hle z θ hz hθ hθπ
    by_cases hCe : 0 ≤ Ce
    · -- the generic case `Ce ≥ 0`: chain the sup-bound with the package's norm bound
      have h1 : |w z θ| ≤ C0 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α w := by
        have h := hsup α w hα hα1 hsm hmem 0 (by norm_num) z θ hz hθ hθπ
        simpa using h
      have hcoef : 0 ≤ C0 / Real.sqrt (Work.Spaces.gam α - 1) :=
        div_nonneg hC0pos.le (Real.sqrt_nonneg _)
      have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
      have h3 : C0 / Real.sqrt (Work.Spaces.gam α - 1)
          ≤ (4 * C0 + 1) * α ^ (-(1 / 2 : ℝ)) := by
        have h := inv_sqrt_gam_le (α := α) hα
        have h1' : C0 * (1 / Real.sqrt (Work.Spaces.gam α - 1))
            ≤ C0 * (4 * α ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h hC0pos.le
        have h2' : C0 * (4 * α ^ (-(1 / 2 : ℝ)))
            ≤ (4 * C0 + 1) * α ^ (-(1 / 2 : ℝ)) := by
          rw [show C0 * (4 * α ^ (-(1 / 2 : ℝ))) = (4 * C0) * α ^ (-(1 / 2 : ℝ)) by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) hr
        have he : C0 / Real.sqrt (Work.Spaces.gam α - 1)
            = C0 * (1 / Real.sqrt (Work.Spaces.gam α - 1)) := by ring
        rw [he]
        linarith
      have h4 : 0 ≤ Ce * Work.FTS.Nonlin.Xn α f :=
        mul_nonneg hCe (Work.Spaces.HkNorm_nonneg α 4 f)
      calc |w z θ| ≤ C0 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α w := h1
        _ ≤ C0 / Real.sqrt (Work.Spaces.gam α - 1) * (Ce * Work.FTS.Nonlin.Xn α f) :=
            mul_le_mul_of_nonneg_left hle hcoef
        _ ≤ ((4 * C0 + 1) * α ^ (-(1 / 2 : ℝ))) * (Ce * Work.FTS.Nonlin.Xn α f) :=
            mul_le_mul_of_nonneg_right h3 h4
        _ = (4 * C0 + 1) * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by ring
    · -- the degenerate case `Ce < 0`: the package's bound forces `Xn α w = 0`, hence `w = 0`
      have hCe' : Ce < 0 := not_le.mp hCe
      have hnonneg_f : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
      have hXw0 : Work.FTS.Nonlin.Xn α w = 0 := by
        have h1 : Work.FTS.Nonlin.Xn α w ≤ 0 :=
          le_trans hle (mul_nonpos_of_nonpos_of_nonneg hCe'.le hnonneg_f)
        have h2 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
        linarith
      have hSq0 : Work.Spaces.HkSq α 4 w = 0 := by
        have hthis : Real.sqrt (Work.Spaces.HkSq α 4 w) = 0 := hXw0
        exact le_antisymm (Real.sqrt_eq_zero'.mp hthis) (Work.Spaces.HkSq_nonneg α 4 w)
      have hw0 : w z θ = 0 :=
        Work.FTS.StrongPersist.Degen.HkSqZeroOnQuad hsm hmem hSq0 z θ hz hθ hθπ
      have hXf0 : Work.FTS.Nonlin.Xn α f = 0 := by
        have h2 : 0 ≤ Ce * Work.FTS.Nonlin.Xn α f := by
          have h3 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
          linarith [hXw0]
        by_contra hne
        have hpos : 0 < Work.FTS.Nonlin.Xn α f :=
          lt_of_le_of_ne hnonneg_f (Ne.symm hne)
        nlinarith [h2, hpos, hCe']
      rw [hw0, abs_zero, hXf0, mul_zero]
  exact ⟨key (Work.Construction.Rop α (Work.Construction.PhiTil α f Ef))
          hpkg.R.1.1 hpkg.R.1.2 hpkg.R.2,
        key (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
            / Work.Construction.s2 θ) hpkg.U.1.1 hpkg.U.1.2 hpkg.U.2,
        key (Work.Construction.Vop (Work.Construction.PhiTil α f Ef))
          hpkg.V.1.1 hpkg.V.1.2 hpkg.V.2⟩

end Work.FTS.StrongPersist.H6Rows.NZaux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/Slots` — the slot functionals of the `N`-zero-mode estimate

The `L₁₂`-density functional `FaU` (without the angular weight `K`), its bound by the `ℋ⁴`-norm
of the datum for the three datum slots (`PsgAux.rl1_slot_le` applied with the coefficient
`(K θ)⁻¹`, whose `K θ`-weight is `1`), the six slots `slots α f`, the coefficient majorant
`Kcoef`, and the six-slot `Fa`-estimate `Fa_le_slots`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The *slot* functional of the zero-mode estimate: `FaU g = ∫⁻_r r⁻¹ ∫⁻_θ |g(r,θ)|`
(the `r⁻¹`-density of `L₁₂`, without the angular weight `K`). -/
def FaU (g : Fn) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
    * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|)

/-- **A slot bounded by the `ℋ⁴`-integrand.**  If `w(r)·B(r,θ)² ≤ HkIntegrand α 4 f r θ` a.e. in
`θ` (the shape of `PsgAux.slot_g`/`slot_dth`/`slot_dz`), then the slot functional of `B` is at
most `√(π/2)·|f|_{ℋ⁴}`.

Proof: apply `PsgAux.rl1_slot_le` with the coefficient `A = (K θ)⁻¹`, whose `K θ`-weight is `1`
a.e. on `Iθ`; the conclusion is the slot functional. -/
theorem FaU_slot_le {α : ℝ} {B f : Fn} (hα : 0 < α)
    (hB : ContinuousOn (Function.uncurry B) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α 4 f)
    (hBw : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (B r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ) :
    FaU B ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) := by
  have hA : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun _ θ' : ℝ => (Work.Spaces.K θ')⁻¹) r θ| ≤ 1 := by
    intro r hr
    refine Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hKpos : 0 < Work.Spaces.K θ := by
      have h1 : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      simp only [Work.Spaces.K]
      positivity
    show |Work.Spaces.K θ * (Work.Spaces.K θ)⁻¹| ≤ 1
    rw [mul_inv_cancel₀ (ne_of_gt hKpos), abs_one]
  have hBmeas : ∀ r : ℝ, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((B r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hB hr
  have hΦmeas : AEMeasurable
      (fun r => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hB
  have hE := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
    (A := fun _ θ' : ℝ => (Work.Spaces.K θ')⁻¹) (B := B) (g := f) (C := 1)
    (by norm_num) hmem hA hBmeas hΦmeas hBw
  have hcongr : (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * (fun _ θ' : ℝ => (Work.Spaces.K θ')⁻¹) r θ
          * B r θ|)
      = fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ| := by
    funext r
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => hθ)] with θ hθ
    have hKpos : 0 < Work.Spaces.K θ := by
      have h1 : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      simp only [Work.Spaces.K]
      positivity
    have : Work.Spaces.K θ * (Work.Spaces.K θ)⁻¹ * B r θ = B r θ := by
      rw [mul_inv_cancel₀ (ne_of_gt hKpos), one_mul]
    rw [this]
  have hkey : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|))
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            |Work.Spaces.K θ * (fun _ θ' : ℝ => (Work.Spaces.K θ')⁻¹) r θ * B r θ|)) := by
    refine MeasureTheory.lintegral_congr (fun r => ?_)
    rw [congrFun hcongr r]
  show FaU B ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f)
  rw [show FaU B = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|)) from rfl, hkey]
  exact hE.trans (le_of_eq (by rw [one_mul]))


/-! ## Small analytic helpers -/

/-- `(√(gam α - 1))⁻¹ = √10·α^{-1/2}` for `α > 0` (the conversion of the Agmon constant
`C/√(γ-1)` into the `α^{-1/2}` used throughout). -/
theorem inv_sqrt_gam_sub_one {α : ℝ} (hα : 0 < α) :
    (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  have hsq : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) :=
    (congrArg (fun x : ℝ => x⁻¹) (Real.sqrt_eq_rpow α)).trans
      (Real.rpow_neg hα.le (1 / 2 : ℝ)).symm
  rw [Work.Spaces.gam_sub_one, Real.sqrt_div hα.le 10, inv_div, div_eq_mul_inv, hsq]

/-- `1 ≤ α^{-1/2}` for `0 < α ≤ 1`. -/
theorem one_le_rpow_neg_half {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hα.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos hα _)).mpr
    (Real.rpow_le_one hα.le hα1 (by norm_num))

/-- The angular slice of a function continuous on the open quadrant is a.e. strongly
measurable (in the form `θ ↦ ofReal |g r θ|` needed by the `θ`-Cauchy–Schwarz). -/
theorem aesm_slot_abs {g : Fn}
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {r : ℝ}
    (hr : 0 < r) :
    AEMeasurable (fun θ => ENNReal.ofReal |g r θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ => g r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hg hr
  have h2 : AEMeasurable (fun θ => g r θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (aestronglyMeasurable_iff_aemeasurable).mp h1
  have hg' : Measurable (fun x : ℝ => ENNReal.ofReal |x|) := by fun_prop
  simpa only [Function.comp_def] using hg'.comp_aemeasurable h2

/-- The parametrised `θ`-integral `r ↦ ∫⁻_θ ofReal |g r θ|` is a.e. measurable. -/
theorem meas_slot_int {g : Fn}
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEMeasurable (fun r => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry g) hg
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hmeas_eq : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set hz
  rw [hmeas_eq] at h1
  have h2 : AEMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (aestronglyMeasurable_iff_aemeasurable).mp h1
  have hg' : Measurable (fun x : ℝ => ENNReal.ofReal |x|) := by fun_prop
  have h3 : AEMeasurable (Function.uncurry (fun r θ => ENNReal.ofReal |g r θ|))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hg'.comp_aemeasurable h2
  exact h3.lintegral_prod_right

/-- **The three datum slots.**  For `0 < α` and an `ℋ⁴`-datum `f`, each of the three slots
`f`, `D_θ f`, `D_z f` has slot functional at most `√(π/2)·|f|_{ℋ⁴}`. -/
theorem FaU_data_slots {α : ℝ} {f : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    FaU f ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) ∧
    FaU (Work.Spaces.Dth f)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) ∧
    FaU (Work.Spaces.Dz f)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) := by
  refine ⟨?_, ?_, ?_⟩
  · refine FaU_slot_le hα hso.continuousOn hmem (fun r hr => ?_)
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_g hα hr hθ f)
  · refine FaU_slot_le hα hso.Dth.continuousOn hmem (fun r hr => ?_)
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dth hα hr hθ f)
  · refine FaU_slot_le hα hso.Dz.continuousOn hmem (fun r hr => ?_)
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dz hα hr hθ f)

/-- The six slots of the zero-mode estimate: the three datum slots and the three profile
slots. -/
def slots (α : ℝ) (f : Fn) : Fin 6 → Fn :=
  ![f, Work.Spaces.Dth f, Work.Spaces.Dz f,
    Work.Construction.Fstar α, Work.Spaces.Dth (Work.Construction.Fstar α),
    Work.Spaces.Dz (Work.Construction.Fstar α)]

/-- The coefficient majorant of the zero-mode estimate. -/
def Kcoef (α M Ce Cs Cp Cu Cag : ℝ) : ℝ :=
  1000 * (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M)

theorem Kcoef_pos {α M Ce Cs Cp Cu Cag : ℝ} (hα : 0 < α) (hCp : 0 < Cp) (hCu : 0 < Cu)
    (hCag : 0 < Cag) (hM : 0 ≤ M) : 0 < Kcoef α M Ce Cs Cp Cu Cag := by
  rw [Kcoef]
  have h1 : 0 < Cp + Cu + Cag + 1 := by linarith
  have h2 : 0 < (1 : ℝ) + |Ce| + |Cs| := by positivity
  have h3 : 0 < α ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hα _
  have h4 : 0 < (1 : ℝ) + M := by linarith
  positivity


/-- **The zero-mode `Fa`-estimate.**  If `|K θ·N|` is pointwise dominated by `Kc` times the sum
of the six slots `G`, then the `L₁₂`-density of `N` is at most `Kc` times the sum of the six
slot functionals. -/
theorem Fa_le_slots {Kc : ℝ} {N : Fn} {G : Fin 6 → Fn} (hK0 : 0 ≤ Kc)
    (hpt : ∀ r θ : ℝ, 0 < r → 0 < θ → θ < π / 2 →
      |Work.Spaces.K θ * N r θ| ≤ Kc * ∑ j : Fin 6, |G j r θ|)
    (hm : ∀ j : Fin 6, ContinuousOn (Function.uncurry (G j))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Fa N ≤ ENNReal.ofReal Kc * ∑ j : Fin 6, FaU (G j) := by
  have hinner : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal Kc
          * (∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|) := by
    intro r hr
    have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Kc * ∑ j : Fin 6, |G j r θ|) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
        (fun θ hθ => hθ)] with θ hθ
      exact ENNReal.ofReal_le_ofReal (hpt r θ hr hθ.1 hθ.2)
    refine h1.trans ?_
    rw [show (fun θ => ENNReal.ofReal (Kc * ∑ j : Fin 6, |G j r θ|))
        = fun θ => ENNReal.ofReal Kc * ∑ j : Fin 6, ENNReal.ofReal |G j r θ| from by
      funext θ
      rw [ENNReal.ofReal_mul hK0,
        ENNReal.ofReal_sum_of_nonneg (fun j _ => abs_nonneg _)]]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [MeasureTheory.lintegral_finsetSum' _ (fun j _ => aesm_slot_abs (hm j) hr)]
  have h2 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (ENNReal.ofReal Kc
          * ∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_of_nonneg_left (hinner r hr) bot_le
  refine h2.trans ?_
  rw [show (fun r => ENNReal.ofReal r⁻¹ * (ENNReal.ofReal Kc
        * ∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|))
      = fun r => ENNReal.ofReal Kc * (ENNReal.ofReal r⁻¹
        * ∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|) from by
    funext r
    rw [← mul_assoc, mul_comm (ENNReal.ofReal r⁻¹) (ENNReal.ofReal Kc), mul_assoc]]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [show (fun r => ENNReal.ofReal r⁻¹
        * ∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|)
      = fun r => ∑ j : Fin 6, ENNReal.ofReal r⁻¹
        * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ| from
    funext fun r => Finset.mul_sum _ _ _]
  rw [MeasureTheory.lintegral_finsetSum' (Finset.univ : Finset (Fin 6))
    (f := fun j r => ENNReal.ofReal r⁻¹ * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|)
    (fun j _ => (ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable.mul
      (meas_slot_int (hm j)))]
  simp only [FaU]
  rfl
end Work.FTS.StrongPersist.H6Rows
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The data of a coefficient available in `L6Ctx`.**

* `K0` prices the sup of the coefficient (the `hres_pt` field of `Ell6Ctx`, or the
  `WlInf`-pricing of a star field);
* `K4` prices its `ℋ⁴`-norm (the `EllPkgGo` field `hgo` of `Ell6Ctx`);
* `K6` prices its `ℋ⁶`-norm (the `EllPkgK α 6` field `hell` of `Ell6Ctx`).

The rows derive from `h4`/`n4` the pointwise bounds of the coefficient's slots of order ≤ 2
(`sup_dz_le_hk`, `mixed_pointwise_le_Xn`, both with `Xn α A = HkNorm α 4 A ≤ K4`), and from
`h6`/`n6` the `L²(ρ)`-bounds of its slots of order ≤ 6 (`intSlotLeHkSq`). -/
structure CoefHyp (α : ℝ) (A : Fn) (K0 K4 K6 : ℝ) : Prop where
  /-- interior smoothness. -/
  sm : Work.FTS.EllipticEst.SmoothOpen A
  /-- `ℋ⁴`-honesty. -/
  h4 : Work.Spaces.HkMem α 4 A
  /-- `ℋ⁶`-honesty. -/
  h6 : Work.Spaces.HkMem α 6 A
  /-- the pointwise pricing. -/
  val : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0
  /-- the `ℋ⁴`-pricing. -/
  n4 : Work.FTS.Nonlin.Xn α A ≤ K4
  /-- the `ℋ⁶`-pricing. -/
  n6 : Work.Spaces.HkNorm α 6 A ≤ K6

/-- The `f`-side data of a slot row: the datum `f` is honest in `ℋ⁶`, its `ℋ⁴`-norm is
bounded by `M`, and it vanishes on the two angular boundary lines and (with its first radial
derivative) at the axis — the class `H6Adm` of the slices. -/
structure DatHyp (α : ℝ) (f : Fn) (M : ℝ) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen f
  h6 : Work.Spaces.HkMem α 6 f
  h7 : Work.Spaces.HkMem α 7 f
  vanish : Work.Spaces.VanishTheta f
  axis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0
  bdd : Work.FTS.Nonlin.Xn α f ≤ M

end Work.FTS.StrongPersist.H6Rows.Npair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.Unfold =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false




end Work.FTS.StrongPersist.H6Rows.Npair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary helpers for the `A · D_z f` flat row

The canonical-weight algebra (`Work.FTS.TransportS.SlotT2.canonW q = w² sin(2θ)^{-q}`), weighted
AM–GM, the per-term three-factor bound, and the `(0,0)`-splitting of a double `range`-sum.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem rowDz_sin2_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The defining equation of the canonical weight. -/
theorem rowDz_canonW_eq (q z θ : ℝ) :
    canonW q z θ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := rfl

/-- Multiplying a canonical weight by a power of `sin(2θ)` shifts the exponent. -/
theorem rowDz_canonW_mul_sigma {q t z θ : ℝ} (hσ : 0 < Real.sin (2 * θ)) :
    canonW q z θ * (Real.sin (2 * θ)) ^ t = canonW (q - t) z θ := by
  rw [rowDz_canonW_eq, rowDz_canonW_eq, mul_assoc, ← Real.rpow_add hσ]
  ring_nf

/-- The canonical weight determines its exponent. -/
theorem rowDz_canonW_eq_of {ρ : ℝ → ℝ → ℝ} {q q₀ : ℝ} (hρ : ρ = canonW q)
    (hρ' : ρ = canonW q₀) : q = q₀ := by
  have h1 : canonW q 1 (Real.pi / 8) = canonW q₀ 1 (Real.pi / 8) := by rw [← hρ, hρ']
  rw [rowDz_canonW_eq, rowDz_canonW_eq] at h1
  have hw : (Work.Spaces.w 1) ^ 2 = 16 := by rw [Work.Spaces.w]; norm_num
  have hs : Real.sin (2 * (Real.pi / 8)) = Real.sin (Real.pi / 4) := by ring_nf
  rw [hw, hs] at h1
  have hspos : 0 < Real.sin (Real.pi / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hslt : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 / 2), h2]
  have h2 : Real.sin (Real.pi / 4) ^ (-q) = Real.sin (Real.pi / 4) ^ (-q₀) := by
    nlinarith [h1]
  have hlog := congrArg Real.log h2
  rw [Real.log_rpow hspos, Real.log_rpow hspos] at hlog
  have hne : Real.log (Real.sin (Real.pi / 4)) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hspos (ne_of_lt hslt)
  have h3 : (q₀ - q) * Real.log (Real.sin (Real.pi / 4)) = 0 := by linarith [hlog]
  have h4 : q₀ - q = 0 := (mul_eq_zero.mp h3).resolve_right hne
  linarith [h4]

/-- Weighted AM–GM. -/
theorem rowDz_canonW_abs_mul_le {e z θ : ℝ} (hσ : 0 ≤ Real.sin (2 * θ)) (Y Z : ℝ) :
    canonW e z θ * |Y| * |Z| ≤ canonW e z θ * Y ^ 2 + canonW e z θ * Z ^ 2 := by
  have hc : 0 ≤ canonW e z θ := by
    rw [rowDz_canonW_eq]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσ _)
  set s := Real.sqrt (canonW e z θ) with hs
  have hs2 : s ^ 2 = canonW e z θ := Real.sq_sqrt hc
  have h : 2 * (s * |Y|) * (s * |Z|) ≤ (s * |Y|) ^ 2 + (s * |Z|) ^ 2 := by
    nlinarith [sq_nonneg (s * |Y| - s * |Z|)]
  have e1 : 2 * (s * |Y|) * (s * |Z|) = 2 * (canonW e z θ * |Y| * |Z|) := by
    rw [← hs2]; ring
  have e2 : (s * |Y|) ^ 2 + (s * |Z|) ^ 2 = canonW e z θ * Y ^ 2 + canonW e z θ * Z ^ 2 := by
    rw [← hs2, mul_pow, mul_pow, sq_abs, sq_abs]
  have hnn : 0 ≤ canonW e z θ * Y ^ 2 + canonW e z θ * Z ^ 2 :=
    add_nonneg (mul_nonneg hc (sq_nonneg _)) (mul_nonneg hc (sq_nonneg _))
  linarith [h, e1, e2, hnn]

/-- **The per-term three-factor bound**: a coefficient slot whose weighted absolute value is at
most `M·canonW e`, paired against two datum slots whose `canonW e`-weighted squares are dominated
by `A₁` and `A₂`. -/
theorem rowDz_term_le {α q e M : ℝ} {X Y Z A₁ A₂ : ℝ → ℝ → ℝ} (hM : 0 ≤ M)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |X z θ| ≤ M * canonW e z θ)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW e z θ * (Y z θ) ^ 2 ≤ A₁ z θ)
    (hZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW e z θ * (Z z θ) ^ 2 ≤ A₂ z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |X z θ| * |Y z θ| * |Z z θ| ≤ M * (A₁ z θ + A₂ z θ) := by
  intro z θ hz hθ hθ2
  have hσ : 0 ≤ Real.sin (2 * θ) := le_of_lt (rowDz_sin2_pos ⟨hθ, hθ2⟩)
  have h1 : canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
      ≤ M * (canonW e z θ * |Y z θ| * |Z z θ|) := by
    have h2 : canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
        = (canonW q z θ * |X z θ|) * (|Y z θ| * |Z z θ|) := by ring
    have h3 : M * (canonW e z θ * |Y z θ| * |Z z θ|)
        = (M * canonW e z θ) * (|Y z θ| * |Z z θ|) := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_right (hX z θ hz hθ hθ2)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
      ≤ M * (canonW e z θ * |Y z θ| * |Z z θ|) := h1
    _ ≤ M * (canonW e z θ * (Y z θ) ^ 2 + canonW e z θ * (Z z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left (rowDz_canonW_abs_mul_le hσ _ _) hM
    _ ≤ M * (A₁ z θ + A₂ z θ) :=
        mul_le_mul_of_nonneg_left (add_le_add (hY z θ hz hθ hθ2) (hZ z θ hz hθ hθ2)) hM

/-- Splitting off the `(0,0)`-summand of a double `range`-sum. -/
theorem rowDz_dsum_split (a b : ℕ) (C : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j)
      = C 0 0 + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0 else C i j) := by
  have hL : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j)
      = (∑ j ∈ Finset.range (b + 1), C 0 j)
        + ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range (b + 1), C (i + 1) j := by
    rw [Finset.sum_range_succ']; ring
  have hL0 : (∑ j ∈ Finset.range (b + 1), C 0 j)
      = C 0 0 + ∑ j ∈ Finset.range b, C 0 (j + 1) := by
    rw [Finset.sum_range_succ']; ring
  have hD : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ) else C i j))
      = (∑ j ∈ Finset.range (b + 1), (if (0 : ℕ) = 0 ∧ j = 0 then (0 : ℝ) else C 0 j))
        + ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range (b + 1),
            (if (i + 1) = 0 ∧ j = 0 then (0 : ℝ) else C (i + 1) j) := by
    rw [Finset.sum_range_succ']; ring
  have hD0 : (∑ j ∈ Finset.range (b + 1), (if (0 : ℕ) = 0 ∧ j = 0 then (0 : ℝ) else C 0 j))
      = ∑ j ∈ Finset.range b, C 0 (j + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have hDtail : (∑ i ∈ Finset.range a, ∑ j ∈ Finset.range (b + 1),
        (if (i + 1) = 0 ∧ j = 0 then (0 : ℝ) else C (i + 1) j))
      = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range (b + 1), C (i + 1) j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    exact Nat.succ_ne_zero i h
  rw [hL, hL0, hD, hD0, hDtail]
  ring

/-- `|A| ≤ K` from the `𝒲^{6,∞}`-bound. -/
theorem rowDz_A_le {α K : ℝ} {A : ℝ → ℝ → ℝ} (hAwl : Work.Spaces.WlInfMem α 6 A)
    (hAK : Work.Spaces.WlInf α 6 A ≤ K) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K := by
  intro z θ hz hθ hθ2
  have h := Work.Spaces.pz_sup_bound α 6 A hAwl 0 (by norm_num) z θ (le_of_lt hz)
    ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have h2 : Work.Spaces.WlInf α 6 A / (z + 1) ^ 0 ≤ K := by
    rw [pow_zero, div_one]; exact hAK
  exact le_trans h h2

/-- `|D_z A| ≤ K` from the `𝒲^{6,∞}`-bound. -/
theorem rowDz_DzA_le {α K : ℝ} {A : ℝ → ℝ → ℝ} (hAwl : Work.Spaces.WlInfMem α 6 A)
    (hAK : Work.Spaces.WlInf α 6 A ≤ K) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dz A z θ| ≤ K := by
  intro z θ hz hθ hθ2
  have h := Work.Spaces.pz_sup_bound α 6 A hAwl 1 (by norm_num) z θ (le_of_lt hz)
    ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have h2 : |Work.Spaces.pzIter 1 A z θ| ≤ K / (z + 1) := by
    refine le_trans h ?_
    rw [pow_one]
    exact div_le_div_of_nonneg_right hAK hz1.le
  rw [Work.Spaces.Dz, abs_mul, abs_of_pos hz]
  calc z * |Work.Spaces.pzIter 1 A z θ| ≤ z * (K / (z + 1)) :=
        mul_le_mul_of_nonneg_left h2 hz.le
    _ ≤ K := by
        rw [mul_div_assoc', div_le_iff₀ hz1]
        have hK0 : 0 ≤ K := le_trans (Work.Spaces.WlInf_nonneg α 6 A hAwl) hAK
        nlinarith [hK0]

/-- The constant `2·1000K` is dominated by `4000(1+C1f)(1+K+Kf)`. -/
theorem rowDz_const1 {C1f K Kf : ℝ} (hC1f : 0 < C1f) (hK : 0 ≤ K) (hKf : 0 ≤ Kf) :
    2 * (1000 * K) ≤ 4000 * (1 + C1f) * (1 + K + Kf) := by
  have h1 : (1 : ℝ) ≤ 1 + C1f := by linarith
  have h2 : (1 + K) ≤ 1 + K + Kf := by linarith
  have h3 : (0 : ℝ) ≤ 1 + K := by linarith
  have h4 : (1 : ℝ) * (1 + K) ≤ (1 + C1f) * (1 + K + Kf) :=
    mul_le_mul h1 h2 h3 (by linarith)
  calc 2 * (1000 * K) = 2000 * K := by ring
    _ ≤ 4000 * (1 + K) := by nlinarith
    _ = 4000 * (1 * (1 + K)) := by ring
    _ ≤ 4000 * ((1 + C1f) * (1 + K + Kf)) := mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 4000 * (1 + C1f) * (1 + K + Kf) := by ring

/-- The constant `2·C1f·Kf` is dominated by `4000(1+C1f)(1+K+Kf)`. -/
theorem rowDz_const2 {C1f K Kf : ℝ} (hC1f : 0 < C1f) (hK : 0 ≤ K) (hKf : 0 ≤ Kf) :
    2 * (C1f * Kf) ≤ 4000 * (1 + C1f) * (1 + K + Kf) := by
  have h1 : C1f * Kf ≤ (1 + C1f) * (1 + Kf) := by nlinarith [hC1f.le, hKf]
  have h2 : (1 + C1f) * (1 + Kf) ≤ (1 + C1f) * (1 + K + Kf) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : 2 * ((1 + C1f) * (1 + K + Kf)) ≤ 4000 * ((1 + C1f) * (1 + K + Kf)) := by
    have h4 : (0 : ℝ) ≤ (1 + C1f) * (1 + K + Kf) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h4]
  calc 2 * (C1f * Kf) ≤ 2 * ((1 + C1f) * (1 + Kf)) := by linarith
    _ ≤ 2 * ((1 + C1f) * (1 + K + Kf)) := by linarith
    _ ≤ 4000 * ((1 + C1f) * (1 + K + Kf)) := h3
    _ = 4000 * (1 + C1f) * (1 + K + Kf) := by ring

/-- The constant `2·2000K` is dominated by `4000(1+C1f)(1+K+Kf)`. -/
theorem rowDz_const3 {C1f K Kf : ℝ} (hC1f : 0 < C1f) (hK : 0 ≤ K) (hKf : 0 ≤ Kf) :
    2 * (2000 * K) ≤ 4000 * (1 + C1f) * (1 + K + Kf) := by
  have h1 : K ≤ (1 + C1f) * (1 + K + Kf) := by
    have h2 : (1 : ℝ) ≤ 1 + C1f := by linarith
    have h3 : (1 + K) ≤ 1 + K + Kf := by linarith
    calc K ≤ 1 + K := by linarith
      _ = 1 * (1 + K) := by ring
      _ ≤ (1 + C1f) * (1 + K + Kf) := mul_le_mul h2 h3 (by linarith) (by linarith)
  calc 2 * (2000 * K) = 4000 * K := by ring
    _ ≤ 4000 * ((1 + C1f) * (1 + K + Kf)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 4000 * (1 + C1f) * (1 + K + Kf) := by ring

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The six coefficients and the six slots -/

/-- `ℛ(Ξ₁)`, the `ℛ`-coefficient of the *star* residual `Ξ₁ = PhiTs α Φs`. -/
abbrev coefR1 (α : ℝ) (Φs : Fn) : Fn :=
  Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)

/-- `ℛ(Ξ₂)`, the `ℛ`-coefficient of the *perturbation* residual `Ξ₂ = PhiTil α f Ef`. -/
abbrev coefR2 (α : ℝ) (f Ef : Fn) : Fn :=
  Work.Construction.Rop α (Work.Construction.PhiTil α f Ef)

/-- `𝒰(Ξ₁)/sin 2θ`. -/
abbrev coefU1 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ

/-- `𝒰(Ξ₂)/sin 2θ`. -/
abbrev coefU2 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
    / Work.Construction.s2 θ

/-- `𝒱(Ξ₁)`. -/
abbrev coefV1 (α : ℝ) (Φs : Fn) : Fn := Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)

/-- `𝒱(Ξ₂)`. -/
abbrev coefV2 (α : ℝ) (f Ef : Fn) : Fn := Work.Construction.Vop (Work.Construction.PhiTil α f Ef)

/-- The radial `(F_*,K)`-coefficient, `z ↦ (F_*(·,θ),K)`. -/
abbrev coefKs (α : ℝ) : Fn := fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z

/-- The radial `(f,K)`-coefficient, `z ↦ (f, K)`. -/
abbrev coefKf (f : Fn) : Fn := fun z (_ : ℝ) => Work.Construction.FK f z

/-- The `F_*`-slot. -/
abbrev slotFs (α : ℝ) : Fn := Work.Construction.Fstar α

/-- The `D_θF_*`-slot. -/
abbrev slotTs (α : ℝ) : Fn := Work.Spaces.Dth (Work.Construction.Fstar α)

/-- The `D_zF_*`-slot. -/
abbrev slotZs (α : ℝ) : Fn := Work.Spaces.Dz (Work.Construction.Fstar α)

/-- The `D_θf`-slot. -/
abbrev slotTf (f : Fn) : Fn := Work.Spaces.Dth f

/-- The `D_zf`-slot. -/
abbrev slotZf (f : Fn) : Fn := Work.Spaces.Dz f

/-- The angular factor `sin²θ`. -/
abbrev angSin2 : Fn := fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2

/-! ## The twenty pieces

`nsP0 … nsP19` in the order of the five terms of `N` and, inside each, the star/perturbation
split of the coefficient and the `F_*`/`f` split of the slot. -/

abbrev nsP0 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => 2 * coefR1 α Φs z θ * slotFs α z θ

abbrev nsP1 (α : ℝ) (Φs f : Fn) : Fn :=
  fun z θ => 2 * coefR1 α Φs z θ * f z θ

abbrev nsP2 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => 2 * coefR2 α f Ef z θ * slotFs α z θ

abbrev nsP3 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => 2 * coefR2 α f Ef z θ * f z θ

abbrev nsP4 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => -2 * coefU1 α Φs z θ * slotTs α z θ

abbrev nsP5 (α : ℝ) (Φs f : Fn) : Fn :=
  fun z θ => -2 * coefU1 α Φs z θ * slotTf f z θ

abbrev nsP6 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => -2 * coefU2 α f Ef z θ * slotTs α z θ

abbrev nsP7 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => -2 * coefU2 α f Ef z θ * slotTf f z θ

abbrev nsP8 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => -2 * α * coefV1 α Φs z θ * slotZs α z θ

abbrev nsP9 (α : ℝ) (Φs f : Fn) : Fn :=
  fun z θ => -2 * α * coefV1 α Φs z θ * slotZf f z θ

abbrev nsP10 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => -2 * α * coefV2 α f Ef z θ * slotZs α z θ

abbrev nsP11 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => -2 * α * coefV2 α f Ef z θ * slotZf f z θ

abbrev nsP12 (α : ℝ) : Fn :=
  fun z θ => -(1 / 2) * coefKs α z θ * slotTs α z θ

abbrev nsP13 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -(1 / 2) * coefKs α z θ * slotTf f z θ

abbrev nsP14 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -(1 / 2) * coefKf f z θ * slotTs α z θ

abbrev nsP15 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -(1 / 2) * coefKf f z θ * slotTf f z θ

abbrev nsP16 (α : ℝ) : Fn :=
  fun z θ => -angSin2 z θ * coefKs α z θ * slotFs α z θ

abbrev nsP17 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -angSin2 z θ * coefKs α z θ * f z θ

abbrev nsP18 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -angSin2 z θ * coefKf f z θ * slotFs α z θ

abbrev nsP19 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -angSin2 z θ * coefKf f z θ * f z θ

/-- The sum of the twenty pieces, in the association used by the splitting identity. -/
abbrev nsum (α : ℝ) (f Ef Φs : Fn) : Fn :=
  fun z θ => nsP0 α Φs z θ + nsP1 α Φs f z θ + nsP2 α f Ef z θ + nsP3 α f Ef z θ
    + nsP4 α Φs z θ + nsP5 α Φs f z θ + nsP6 α f Ef z θ + nsP7 α f Ef z θ
    + nsP8 α Φs z θ + nsP9 α Φs f z θ + nsP10 α f Ef z θ + nsP11 α f Ef z θ
    + nsP12 α z θ + nsP13 α f z θ + nsP14 α f z θ + nsP15 α f z θ
    + nsP16 α z θ + nsP17 α f z θ + nsP18 α f z θ + nsP19 α f z θ

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Identities =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `D_θF_* = α qfun θ · F_*` on `Iθ`. -/
theorem Dth_Fstar_eq {α : ℝ} (hα : 0 < α) :
    ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = α * Work.Spaces.qfun θ * Work.Construction.Fstar α z θ := by
  intro z θ hθ
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · have hfac : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          = (α * (2 * z / (1 + z) ^ 2) / Work.Spaces.c α)
              * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ := by
        simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.dthU,
          Work.Construction.Fstar, Work.FM.Fstar]
        rw [show (fun θ' => α * (Work.Spaces.Gam α θ' / Work.Spaces.c α)
              * (2 * z / (1 + z) ^ 2))
            = fun θ' => (α * (2 * z / (1 + z) ^ 2) / Work.Spaces.c α)
                * Work.Spaces.Gam α θ' from by funext θ'; ring]
        rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
        ring
      rw [hfac, Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩,
        Work.Construction.Fstar, Work.FM.Fstar]
      ring
    · subst h1
      rw [Work.Spaces.Dth, Work.Spaces.pth,
        show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
      have hG := Work.Spaces.Gam_zero_right α (ne_of_gt hα)
      simp only [Work.Construction.Fstar, Work.FM.Fstar, hG, zero_div]
      ring
  · subst h0
    rw [Work.Spaces.Dth, Work.Spaces.pth, show (2 : ℝ) * 0 = 0 by ring,
      Real.sin_zero, zero_mul]
    have hG := Work.Spaces.Gam_zero_left α (ne_of_gt hα)
    simp only [Work.Construction.Fstar, Work.FM.Fstar, hG, zero_div]
    ring

/-- `z/(1+z)·D_zF_* = ((1-z)/(1+z))·(α·AK α)` on `Iz`. -/
theorem Dz_Fstar_eq {α : ℝ} :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ) := by
  intro z hz θ _hθ
  have hfac : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * deriv Work.FM.Fstar z := by
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' => Work.Construction.Fstar α z' θ)
        = fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z' from by
          funext z'; simp only [Work.Construction.Fstar] <;> ring]
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
    ring
  have hz1 : (-1 : ℝ) < z := by
    have h := hz; simp only [Work.Spaces.Iz, Set.mem_Ici] at h; linarith
  rw [hfac, Work.FM.deriv_Fstar z hz1, Work.Construction.AK]
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp <;> ring

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.RowAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `SmoothOpen` is stable under multiplication by a constant.  (Local helper: the
`ContDiffOn`-instance for `•` is not available in this Mathlib, so the product form is used.) -/
theorem smoothOpen_const_mul' (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => ?_)
  have h := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf n
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => c * Function.uncurry f p)
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul h
  exact h2



end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.PhiStar.Honesty.integrableOn_eFam_cos_sq_sin_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PhiStar.Honesty

/-- `eFam m = cos · gC (2m+1) (sin ·)` is continuous (a polynomial composed with `sin`,
multiplied by `cos`). -/
lemma continuous_eFam (m : ℕ) :
    Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
  Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- `sin (2θ)^{η}` is continuous on `Iθ = [0, π/2]` (the base `sin (2θ)` is nonnegative there
and the exponent `η = 99/100` is nonnegative). -/
lemma continuousOn_sin_two_rpow_eta :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun _ _ => Or.inr (by norm_num [Work.Spaces.eta]))

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ`. -/
lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem integrableOn_eFam_cos_sq_sin_rpow (m : ℕ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      Work.Spaces.Iθ
    ∧ 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
  -- The integrand is continuous on the compact set `Iθ`, hence integrable.
  have hcont : ContinuousOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
    (((continuous_eFam m).mul Real.continuous_cos).pow 2).continuousOn.mul
      continuousOn_sin_two_rpow_eta
  have hI : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  constructor
  · exact hcont.integrableOn_compact isCompact_Icc
  · -- the integrand is nonnegative on `Iθ`
    exact MeasureTheory.setIntegral_nonneg hI (fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _))

end Work.PhiStar.Honesty
end
-- ===== merged: Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PhiStar.Honesty

open scoped Real

/-- The two `sin(2θ)`-weights in the `η`-weighted pairing multiply to `1` on the open
interval: `sin(2θ)^{-η} · sin(2θ)^{η} = 1` for `θ ∈ (0, π/2)`. -/
theorem sqrt_weight_mul_eq_of_mem_Ioo (F : ℝ → ℝ → ℝ) (m : ℕ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sqrt ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * Real.sqrt ((Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      = |F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| := by
  have hs : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hnegη : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg hs.le _
  have hposη : 0 ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
    Real.rpow_nonneg hs.le _
  have hprod : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) = 1 := by
    rw [← Real.rpow_add hs]
    simp
  have hsqrt : Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      * Real.sqrt ((Real.sin (2 * θ)) ^ (Work.Spaces.eta)) = 1 := by
    rw [← Real.sqrt_mul hnegη, hprod]
    simp
  rw [Real.sqrt_mul (sq_nonneg (F z θ)), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  calc |F z θ| * Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * (|Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
            * Real.sqrt ((Real.sin (2 * θ)) ^ (Work.Spaces.eta)))
      = (|F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|)
        * (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            * Real.sqrt ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by ring
    _ = (|F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|) * 1 := by
          rw [hsqrt]
    _ = |F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| := by ring

end Work.PhiStar.Honesty
end
