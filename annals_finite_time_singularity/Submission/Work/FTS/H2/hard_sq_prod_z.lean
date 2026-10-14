import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.C0thetaIBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- `C0h` has derivative `C0g` everywhere (i.e. `C0g = C0h'`); from `C0h_deriv`. -/
theorem C0h_hasDerivAt (θ : ℝ) : HasDerivAt C0h (C0g θ) θ := by
  rw [← C0h_deriv]
  show HasDerivAt C0h (deriv C0h θ) θ
  rw [hasDerivAt_deriv_iff]
  show DifferentiableAt ℝ C0h θ
  unfold C0h Spaces.K
  fun_prop

/-- `C0h` vanishes at the two endpoints of `Iθ = [0, π/2]`. -/
theorem C0h_zero : C0h 0 = 0 ∧ C0h (π / 2) = 0 := by
  constructor
  · simp [C0h, Spaces.K]
  · rw [C0h, Spaces.K]
    have h2 : 2 * (π / 2) = π := by ring
    rw [h2, Real.sin_pi]
    ring


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.CommutZAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity.CommutZ

set_option autoImplicit false

/-! ## Differentiation under the `θ`-integral -/


/-! ## The density of `D_z f` -/

/-- The `L₁₂`-density of `D_z f` is the `K`-average of `∂_z f`, away from `s = 0`. -/
theorem L12dens_Dz_eq (f : ℝ → ℝ → ℝ) (s : ℝ) (hs : 0 < s) :
    FM.L12dens Spaces.K (Spaces.Dz f) s = Kav (Spaces.pz f) s := by
  have hs' : s ≠ 0 := ne_of_gt hs
  rw [FM.L12dens, Kav]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [Spaces.Dz]
  field_simp


/-! ## The pointwise expansion of the defect `E₂` -/




/-! ## Elementary books for the assembly -/




end Work.Coercivity.CommutZ
end
end
-- ===== merged: Submission.Work.Coercivity.DthGam_sq_lintegral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.EcommT_split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The summands of `𝓛_Γ^T` in radial-profile form

`𝓛_Γ^T = 𝓛 - T1fun - Transport + T4fun` with
`T1fun = (2zΓ/(c(1+z)²))·L₁₂`, `T4fun = (Γ/c)(2z²/(1+z)³)·C₀`, and likewise for the two
`D_θΓ`-terms `T2`, `T4` of `D_θ(𝓛_Γ^T)`.  Writing each of them as `Γ(θ)·pcoef(z)·(…)` or
`Γ(θ)·Wcoef(z)·(…)` (respectively with `D_θΓ` in place of `Γ`) is what lets the final
pointwise identity be closed by `ring`.

The identities say, for instance,
`(Γ/c)(2z²/(1+z)³) = Γ·Wcoef`, i.e. `Γ` is a common factor of numerator and the
denominator `c(1+z)³` may be gathered: this is the field identity
`(a/c)·(b/d) = a·(b/(cd))` (`div_mul_div_comm`), valid with no non-vanishing hypothesis
because Lean's division is total on `ℝ`. -/






/-! ## The splitting -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Eztheta1_eq_HkSq_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## 1. The pointwise split of the `H¹`-integrand -/

theorem hkIntegrand_one_split (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.HkIntegrand α 1 f z θ
      = (U0 f z θ) ^ 2 + (U1 f z θ) ^ 2 + (U2 α f z θ) ^ 2 := by
  simp only [Spaces.HkIntegrand, U0, U1, U2, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-! ## 2. Additivity of the iterated integral -/

/-- The iterated integral over `[0,∞) × [0,π/2]` of a sum of three honest integrands
splits into the sum of the iterated integrals. -/
theorem iterated_integral_add3 {A B C : ℝ → ℝ → ℝ}
    (hA : I2Mem A) (hB : I2Mem B) (hC : I2Mem C) :
    (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (A z θ + B z θ + C z θ))
      = (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, A z θ)
        + (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, B z θ)
        + (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, C z θ) := by
  have hinner : Set.EqOn
      (fun z => ∫ θ in Spaces.Iθ, (A z θ + B z θ + C z θ))
      (fun z => (∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ)
        + (∫ θ in Spaces.Iθ, C z θ)) Spaces.Iz := by
    intro z hz
    change (∫ θ in Spaces.Iθ, (A z θ + B z θ + C z θ))
        = (∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ) + (∫ θ in Spaces.Iθ, C z θ)
    have e1 : (∫ θ in Spaces.Iθ, (A z θ + B z θ + C z θ))
        = (∫ θ in Spaces.Iθ, (A z θ + B z θ)) + (∫ θ in Spaces.Iθ, C z θ) :=
      MeasureTheory.integral_add ((hA.1 z hz).add (hB.1 z hz)) (hC.1 z hz)
    have e2 : (∫ θ in Spaces.Iθ, (A z θ + B z θ))
        = (∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ) :=
      MeasureTheory.integral_add (hA.1 z hz) (hB.1 z hz)
    rw [e1, e2]
  rw [MeasureTheory.setIntegral_congr_fun (s := Spaces.Iz) measurableSet_Ici hinner]
  have f1 : (∫ z in Spaces.Iz, ((∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ)
        + (∫ θ in Spaces.Iθ, C z θ)))
      = (∫ z in Spaces.Iz, ((∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ)))
        + (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, C z θ) :=
    MeasureTheory.integral_add ((hA.2).add (hB.2)) hC.2
  have f2 : (∫ z in Spaces.Iz, ((∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ)))
      = (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, A z θ)
        + (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, B z θ) :=
    MeasureTheory.integral_add hA.2 hB.2
  rw [f1, f2]

/-- `L2Mem` for the pure `D_z`-summand of `HkIntegrand`. -/
theorem L2Mem_DzIter_Hwt (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hsm : Spaces.SmoothNbhd f) (hmem : Spaces.HkMem α k f) (b : ℕ) (hb : b ≤ k) :
    Spaces.L2Mem (fun z θ => Spaces.DzIter b f z θ
      * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) := by
  constructor
  · intro z hz
    refine Integrable.mono' (hmem.1 z hz)
      ((Spaces.HPRZ.aesm_DzIter_H_weight_slice f hsm b hz).pow 2) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)]
      with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Spaces.sq_le_HkIntegrand_z α k f z θ b hb
  · have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Spaces.DzIter b f p.1 p.2
          * (Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Spaces.eta / 2))) ^ 2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
      (Spaces.HPRZ.aesm_DzIter_H_weight_prod f hsm b).pow 2
    refine Integrable.mono' hmem.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => Spaces.sq_le_HkIntegrand_z α k f z θ b hb))


/-! ## 3. Identification of the three `L²Sq`'s with the energies -/

theorem L2Sq_U0_eq_EfEta (f : ℝ → ℝ → ℝ) : Spaces.L2Sq (U0 f) = EfEta f := by
  simp only [Spaces.L2Sq, U0, EfEta, wtEta, wtGam, Spaces.DzIter_zero]
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iz) measurableSet_Ici
    fun z hz => ?_
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iθ) measurableSet_Icc
    fun θ hθ => ?_
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have h : Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)
      = Spaces.w z * Real.sin (2 * θ) ^ (-(Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs]
  rw [h]

theorem L2Sq_U1_eq_EDz (f : ℝ → ℝ → ℝ) : Spaces.L2Sq (U1 f) = EDz f := by
  simp only [Spaces.L2Sq, U1, EDz, wtEta, wtGam, Spaces.DzIter_succ, Spaces.DzIter_zero]
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iz) measurableSet_Ici
    fun z hz => ?_
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iθ) measurableSet_Icc
    fun θ hθ => ?_
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have h : Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)
      = Spaces.w z * Real.sin (2 * θ) ^ (-(Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs]
  rw [h]

theorem L2Sq_U2_eq_EDth (α : ℝ) (f : ℝ → ℝ → ℝ) : Spaces.L2Sq (U2 α f) = EDth α f := rfl

/-! ## 4. Assembly -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L_mul_self_Weta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Pointwise (radial) form of the self-adjointness of `𝓛` against the angular weight
`Weta z θ = w(z)² sin(2θ)^{-η}`: for `g` smooth on a neighbourhood of the closed quadrant
and `z > 0`, `θ ∈ Iθ`,

  `𝓛g · g · Weta(z,θ) = ½ g² · Weta(z,θ) + ½ ∂_z(z (g w)²) · sin(2θ)^{-η}`.

This is the identity `𝓛g·w = g·w + z∂_z(g·w)` (`L_mul_w_deriv`) multiplied by `g·w` and
the angular factor `sin(2θ)^{-η}`, together with the Leibniz rule applied to
`z ↦ z (g(z,θ) w(z))²`.  Only smoothness of the `z`-slice (from `Spaces.SmoothNbhd`) is
needed — no boundary/decay hypotheses. -/
theorem L_mul_self_Weta (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) :
    L g z θ * g z θ * Weta z θ
      = (1 / 2) * (g z θ) ^ 2 * Weta z θ
        + (1 / 2) * deriv (fun z' => z' * (g z' θ * Spaces.w z') ^ 2) z
            * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  -- the `θ`-slice of `g` is differentiable at `z`, with derivative `pz g z θ`
  have hf : HasDerivAt (fun z' => g z' θ) (Spaces.pz g z θ) z :=
    Spaces.hardyZ_hasDerivAt_slice g hg hθ hzmem
  -- `𝓛g · w = g·w + z ∂_z(g·w)`
  have hLw : L g z θ * Spaces.w z
      = g z θ * Spaces.w z + z * Spaces.pz (fun z θ => g z θ * Spaces.w z) z θ :=
    L_mul_w_deriv hz hf
  have hgw : DifferentiableAt ℝ (fun z' => g z' θ * Spaces.w z') z :=
    (hf.mul (hasDerivAt_w (ne_of_gt hz))).differentiableAt
  have hsq : DifferentiableAt ℝ (fun z' => (g z' θ * Spaces.w z') ^ 2) z := hgw.pow 2
  -- Leibniz rule for `z ↦ z (g w)²`
  have hD1 : deriv (fun z' => z' * (g z' θ * Spaces.w z') ^ 2) z
      = (g z θ * Spaces.w z) ^ 2 + z * deriv (fun z' => (g z' θ * Spaces.w z') ^ 2) z := by
    have h : HasDerivAt (fun z' => z' * (g z' θ * Spaces.w z') ^ 2)
        (1 * (g z θ * Spaces.w z) ^ 2
          + z * deriv (fun z' => (g z' θ * Spaces.w z') ^ 2) z) z :=
      (hasDerivAt_id z).mul hsq.hasDerivAt
    rw [h.deriv]; ring
  -- chain rule for the square
  have hD2 : deriv (fun z' => (g z' θ * Spaces.w z') ^ 2) z
      = 2 * (g z θ * Spaces.w z) * Spaces.pz (fun z θ => g z θ * Spaces.w z) z θ := by
    have h1 := (hgw.hasDerivAt).pow 2
    have h2 : deriv (fun z' => (g z' θ * Spaces.w z') ^ 2) z
        = 2 * (g z θ * Spaces.w z) ^ (2 - 1) * deriv (fun z' => g z' θ * Spaces.w z') z :=
      h1.deriv
    rw [h2]
    simp only [Nat.reduceSub, pow_one, Spaces.pz]
  rw [Weta, hD1, hD2]
  -- assemble
  have harith : L g z θ * g z θ * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      = ((g z θ * Spaces.w z + z * Spaces.pz (fun z θ => g z θ * Spaces.w z) z θ)
          * (g z θ * Spaces.w z)) * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    rw [← hLw]; ring
  rw [harith]
  ring

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.box_deriv_ftc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem box_deriv_ftc (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hC : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
      |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C)
    {R : ℝ} (hR : 0 < R) :
    (∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ,
        deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
          * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      = ∫ θ in Spaces.Iθ, R * (Spaces.Dz f R θ * Spaces.w R) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  obtain ⟨M, hMpos, hMbd⟩ := box_joint_bound f hsm hC hR
  -- the angular weight and its integrability
  let p : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-Spaces.eta)
  have hp_int : IntegrableOn p Spaces.Iθ :=
    (Spaces.sin_two_rpow (-Spaces.eta) (by linarith [Spaces.eta_lt_one])
      (by linarith [Spaces.eta_nonneg])).1
  -- the integrand of the iterated integral
  let F : ℝ → ℝ → ℝ := fun z θ =>
    deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z * p θ
  have hμν : (volume.restrict (Set.Ioo (0 : ℝ) R)).prod (volume.restrict Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  -- integrability of the product integrand, by domination with `M * p`
  have hdom : Integrable (fun q : ℝ × ℝ => M * p q.2)
      ((volume.restrict (Set.Ioo (0 : ℝ) R)).prod (volume.restrict Spaces.Iθ)) := by
    have h1 : Integrable (fun _ : ℝ => M) (volume.restrict (Set.Ioo (0 : ℝ) R)) :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have h2 : Integrable p (volume.restrict Spaces.Iθ) := hp_int
    exact h1.mul_prod h2
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioo (0 : ℝ) R)).prod (volume.restrict Spaces.Iθ)) := by
    refine Integrable.mono' (g := fun q : ℝ × ℝ => M * p q.2) hdom ?_ ?_
    · -- a.e. strong measurability
      rw [hμν]
      have hbox : Set.Ioo (0 : ℝ) R ×ˢ Spaces.Iθ ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
        rintro ⟨z, θ⟩ hq
        exact ⟨hq.1.1, ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
      have hm1 : AEStronglyMeasurable (Function.uncurry (Spaces.pz (BoxG f)))
          ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ)) :=
        ((contDiffOn_uncurry_pz_BoxG f hsm).continuousOn.mono hbox).aestronglyMeasurable
          (measurableSet_Ioo.prod measurableSet_Icc)
      have hm2 : AEStronglyMeasurable (fun q : ℝ × ℝ => p q.2)
          ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ)) := by
        rw [← hμν]
        exact (Integrable.aestronglyMeasurable hp_int).comp_snd
      refine (hm1.mul hm2).congr (Filter.Eventually.of_forall (fun q => ?_))
      simp only [Function.uncurry, Pi.mul_apply, F, BoxG, Spaces.pz]
    · -- the pointwise bound
      rw [hμν]
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Icc)] with q hq
      obtain ⟨hqz, hqθ⟩ := hq
      have hpnn : 0 ≤ p q.2 :=
        Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hqθ.1])
          (by linarith [hqθ.2])) _
      have hb : |deriv (fun z' => z' * (Spaces.Dz f z' q.2 * Spaces.w z') ^ 2) q.1| ≤ M :=
        hMbd q.1 hqz q.2 hqθ
      have hnorm : ‖Function.uncurry F q‖
          = |deriv (fun z' => z' * (Spaces.Dz f z' q.2 * Spaces.w z') ^ 2) q.1| * p q.2 := by
        have hval : Function.uncurry F q
            = deriv (fun z' => z' * (Spaces.Dz f z' q.2 * Spaces.w z') ^ 2) q.1 * p q.2 := rfl
        rw [hval, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpnn]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right hb hpnn
  -- Fubini
  have hswap := MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Ioo (0 : ℝ) R))
    (ν := volume.restrict Spaces.Iθ) hFint
  change (∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ, F z θ)
      = ∫ θ in Spaces.Iθ, R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 * p θ
  rw [hswap]
  -- the radial slice identity
  have hinner : ∀ θ ∈ Spaces.Iθ,
      (∫ z, F z θ ∂(volume.restrict (Set.Ioo (0 : ℝ) R)))
        = R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 * p θ := by
    intro θ hθ
    have h1 : (∫ z, F z θ ∂(volume.restrict (Set.Ioo (0 : ℝ) R)))
        = (∫ z, deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
            ∂(volume.restrict (Set.Ioo (0 : ℝ) R))) * p θ := by
      simp only [F]
      rw [MeasureTheory.integral_mul_const]
    have h2 : (∫ z, deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
            ∂(volume.restrict (Set.Ioo (0 : ℝ) R)))
        = R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 :=
      box_slice_ftc f hsm hbd hC hR hθ
    rw [h1, h2]
  have hae : (fun θ => ∫ z, F z θ ∂(volume.restrict (Set.Ioo (0 : ℝ) R)))
      =ᵐ[volume.restrict Spaces.Iθ]
      (fun θ => R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 * p θ) :=
    (ae_restrict_mem measurableSet_Icc).mono (fun θ hθ => hinner θ hθ)
  rw [MeasureTheory.integral_congr_ae hae]

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.box_ineq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false




end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.monotone_interval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.pth_bounds_box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.slice_ibp_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.wip_TrV_ge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.FixedPoint =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false









end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.H4N_rhoR_shape4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

noncomputable section

open scoped Topology

/-!
# The closed form of the fourth `D_z`-iterate of `ρ(z) = z²/(1+z)⁴`

`D_z` acts on functions of `z` alone as `Work.Spaces.Zop φ = fun z ↦ z·φ'(z)`
(`Work.Spaces.Zop`).  Writing `(Zop^[k] ρ)(z) = z²·N_k(z)/(1+z)^{4+k}`, one checks
that `N_0 = 1`, `N_1 = 2 - 2z`, `N_2 = 4 - 12z + 4z²` (the exact closed forms for
`k = 1, 2` are `H4N_rhoR_shape12`), and that the iterate obeys the elementary
recursion

`N_{k+1}(z) = (2·N_k(z) + z·N_k'(z))·(1+z) - (4+k)·z·N_k(z)`,

obtained by differentiating `z ↦ z²N_k(z)/(1+z)^{4+k}` and multiplying by `z`.
This yields `N_3 = 8 - 52z + 52z² - 8z³` and
`N_4 = 16 - 196z + 416z² - 196z³ + 16z⁴`, i.e. the statement below.
-/

/-- The derivative of the degree-`4` numerator `w ↦ w²(4-12w+4w²)` of `g₂`. -/
private lemma deriv_num2 (x : ℝ) :
    deriv (fun w : ℝ => w^2*(4 - 12*w + 4*w^2)) x = 8*x - 36*x^2 + 16*x^3 := by
  have hfun : (fun w : ℝ => w^2*(4 - 12*w + 4*w^2))
      = fun w : ℝ => 0 + 0*w + 4*w^2 + (-12)*w^3 + 4*w^4 + 0*w^5 := by
    funext w; ring
  rw [hfun, deriv_mono5 0 0 4 (-12) 4 0 x]
  ring

/-- The derivative of the degree-`5` numerator `w ↦ w²(8-52w+52w²-8w³)` of `g₃`. -/
private lemma deriv_num3 (x : ℝ) :
    deriv (fun w : ℝ => w^2*(8 - 52*w + 52*w^2 - 8*w^3)) x
      = 16*x - 156*x^2 + 208*x^3 - 40*x^4 := by
  have hfun : (fun w : ℝ => w^2*(8 - 52*w + 52*w^2 - 8*w^3))
      = fun w : ℝ => 0 + 0*w + 8*w^2 + (-52)*w^3 + 52*w^4 + (-8)*w^5 := by
    funext w; ring
  rw [hfun, deriv_mono5 0 0 8 (-52) 52 (-8) x]
  ring

/-- The closed form of `Zop²ρ = Zop (Zop ρ)`, restated as the function `g₂`. -/
private def g2 (w : ℝ) : ℝ := w^2*(4 - 12*w + 4*w^2)/(1+w)^6

/-- The closed form of `Zop³ρ`, written as the function `g₃`. -/
private def g3 (w : ℝ) : ℝ := w^2*(8 - 52*w + 52*w^2 - 8*w^3)/(1+w)^7

/-- The derivative of `g₂` away from `w = -1`. -/
private lemma deriv_g2 (x : ℝ) (hx : x ≠ -1) :
    deriv g2 x = x*(8 - 52*x + 52*x^2 - 8*x^3)/(1+x)^7 := by
  have hden : (1+x)^6 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hnum : DifferentiableAt ℝ (fun w : ℝ => w^2*(4 - 12*w + 4*w^2)) x := by fun_prop
  have hden' : DifferentiableAt ℝ (fun w : ℝ => (1+w)^6) x := by fun_prop
  have hdden : deriv (fun w : ℝ => (1+w)^6) x = 6*(1+x)^5 := by
    change deriv ((fun w : ℝ => 1+w)^6) x = 6*(1+x)^5
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1+w) x)]
    simp
  show deriv ((fun w : ℝ => w^2*(4 - 12*w + 4*w^2)) / (fun w : ℝ => (1+w)^6)) x = _
  rw [deriv_div hnum hden' hden, deriv_num2 x, hdden]
  have h7 : (1+x)^7 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  field_simp
  ring

/-- The derivative of `g₃` away from `w = -1`. -/
private lemma deriv_g3 (x : ℝ) (hx : x ≠ -1) :
    deriv g3 x = x*(16 - 196*x + 416*x^2 - 196*x^3 + 16*x^4)/(1+x)^8 := by
  have hden : (1+x)^7 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hnum : DifferentiableAt ℝ (fun w : ℝ => w^2*(8 - 52*w + 52*w^2 - 8*w^3)) x := by
    fun_prop
  have hden' : DifferentiableAt ℝ (fun w : ℝ => (1+w)^7) x := by fun_prop
  have hdden : deriv (fun w : ℝ => (1+w)^7) x = 7*(1+x)^6 := by
    change deriv ((fun w : ℝ => 1+w)^7) x = 7*(1+x)^6
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1+w) x)]
    simp
  show deriv ((fun w : ℝ => w^2*(8 - 52*w + 52*w^2 - 8*w^3)) / (fun w : ℝ => (1+w)^7)) x = _
  rw [deriv_div hnum hden' hden, deriv_num3 x, hdden]
  have h8 : (1+x)^8 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  field_simp
  ring

/-- The closed form of `Zop³ρ` away from `z = -1`. -/
private lemma Zop3_rhoR (w : ℝ) (hw : w ≠ -1) :
    (Work.Spaces.Zop^[3] rhoR) w = g3 w := by
  have hev2 : (Work.Spaces.Zop^[2] rhoR) =ᶠ[𝓝 w] g2 := by
    filter_upwards [eventually_ne_nhds hw] with x hx
    exact (H4N_rhoR_shape12).2 x hx
  rw [show (3 : ℕ) = 2 + 1 by norm_num, Function.iterate_succ_apply']
  show Work.Spaces.Zop (Work.Spaces.Zop^[2] rhoR) w = g3 w
  rw [Zop_apply, hev2.deriv_eq, deriv_g2 w hw]
  show w * (w * (8 - 52*w + 52*w^2 - 8*w^3) / (1 + w)^7) = g3 w
  rw [g3]
  ring

theorem H4N_rhoR_shape4 :
    ∀ z : ℝ, z ≠ -1 → (Work.Spaces.Zop^[4] Work.Construction.rhoR) z
        = z^2 * (16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4) / (1 + z)^8 := by
  intro z hz
  have hev3 : (Work.Spaces.Zop^[3] rhoR) =ᶠ[𝓝 z] g3 := by
    filter_upwards [eventually_ne_nhds hz] with x hx
    exact Zop3_rhoR x hx
  rw [show (4 : ℕ) = 3 + 1 by norm_num, Function.iterate_succ_apply']
  show Work.Spaces.Zop (Work.Spaces.Zop^[3] rhoR) z
      = z^2 * (16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4) / (1 + z)^8
  rw [Zop_apply, hev3.deriv_eq, deriv_g3 z hz]
  ring

end

end Work.Construction
end
-- ===== merged: Submission.Work.Cyl =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.Elliptic.L12Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
-- import Submission.Work.Elliptic.HardyLeft
-- import Submission.Work.Elliptic.HardyRight

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Vocabulary -/

/-- The angular moment `Q_j(z) = ∫_θ K(θ) · (D_z^j g)(z,θ) dθ`.  Note `Q_0(z) = z · L12dens g z`
and `L₁₂(g)(z) = ∫_z^∞ Q_0(s)/s ds`. -/
def Qang (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Ktheta θ * Work.Spaces.DzIter j g z θ

/-- The one-dimensional operator `z ∂_z` acting on functions of `z` alone. -/
def Dzd (u : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv u z

/-- Iterated `z ∂_z` on functions of one variable. -/
def DzdIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, u => u
  | k + 1, u => Dzd (DzdIter k u)

@[simp] theorem DzdIter_zero (u : ℝ → ℝ) : DzdIter 0 u = u := rfl
@[simp] theorem DzdIter_succ (k : ℕ) (u : ℝ → ℝ) :
    DzdIter (k + 1) u = Dzd (DzdIter k u) := rfl

/-- `L12dens` is `Q_0` divided by `z`. -/
theorem L12dens_eq_Qang_div (g : ℝ → ℝ → ℝ) (s : ℝ) :
    L12dens g s = Qang g 0 s / s := by
  rw [L12dens, Qang]
  simp only [Work.Spaces.DzIter_zero]
  rw [MeasureTheory.integral_div]

/-! ## `D_z`-iterates of a radial function -/

theorem DzIter_rad (u : ℝ → ℝ) : ∀ (k : ℕ) (z θ : ℝ),
    Work.Spaces.DzIter k (fun z θ => u z) z θ = DzdIter k u z := by
  intro k
  induction k with
  | zero => intro z θ; rfl
  | succ k ih =>
      intro z θ
      have hfun : (fun z' => Work.Spaces.DzIter k (fun z θ => u z) z' θ) = DzdIter k u :=
        funext fun z' => ih z' θ
      have h1 : Work.Spaces.DzIter (k + 1) (fun z θ => u z) z θ
          = z * deriv (fun z' => Work.Spaces.DzIter k (fun z θ => u z) z' θ) z := rfl
      rw [h1, hfun]
      rfl

theorem DthIter_rad_succ (u : ℝ → ℝ) : ∀ (k : ℕ),
    Work.Spaces.DthIter (k + 1) (fun z θ => u z) = fun _ _ => (0 : ℝ) := by
  intro k
  induction k with
  | zero =>
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => u z) θ = 0
      rw [deriv_const]
      ring
  | succ k ih =>
      funext z θ
      have h1 : Work.Spaces.DthIter (k + 1 + 1) (fun z θ => u z)
          = Work.Spaces.Dth (Work.Spaces.DthIter (k + 1) (fun z θ => u z)) := rfl
      rw [h1, ih]
      show Real.sin (2 * θ) * deriv (fun θ' => (0 : ℝ)) θ = 0
      rw [deriv_const]
      ring

theorem mixed_rad_eq_zero (u : ℝ → ℝ) {j i : ℕ} (hi : 1 ≤ i) :
    Work.Spaces.mixed j i (fun z θ => u z) = fun _ _ => (0 : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [Work.Spaces.mixed, DthIter_rad_succ u k]
  induction j with
  | zero => rfl
  | succ j ih =>
      funext z θ
      show z * deriv (fun z' => Work.Spaces.DzIter j (fun _ _ => (0:ℝ)) z' θ) z = 0
      have hfun : (fun z' => Work.Spaces.DzIter j (fun _ _ => (0:ℝ)) z' θ) = fun _ => (0:ℝ) :=
        funext fun z' => congrFun (congrFun ih z') θ
      rw [hfun, deriv_const]
      ring

/-! ## The `H^k`-integrand and the `H^k`-norm of a radial function -/

theorem sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
  have := hθ.2
  linarith [Real.pi_pos]

/-! ## Integrability of the `H^4`-integrand on the product measure -/



/-! ## Smoothness on the neighbourhood `nbhU` and the pointwise domination -/

theorem contDiffOn_uncurry_Dz_nbhU {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.nbhU) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz g)) Work.Spaces.nbhU := by
  have hpz := Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_nbhU h
  have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz g) p)
      Work.Spaces.nbhU := contDiffOn_fst.mul hpz
  refine h1.congr ?_
  intro p hp
  rfl

theorem contDiffOn_uncurry_DzIter_nbhU {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.nbhU) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter n g)) Work.Spaces.nbhU := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [Work.Spaces.DzIter_succ]; exact contDiffOn_uncurry_Dz_nbhU ih


/-- A.e. (for the product measure) a point of `Iz × Iθ` lies in the open quadrant. -/
theorem ae_mem_Qd_prod :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (π/2) := by
  rw [MeasureTheory.Measure.prod_restrict]
  change ∀ᵐ p ∂(volume.prod volume).restrict (Set.Ici (0:ℝ) ×ˢ Set.Icc 0 (π / 2)),
      p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (π / 2)
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm)]
  exact MeasureTheory.ae_restrict_mem ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)

theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (pow_pos hz 2)]
  nlinarith

theorem one_le_sin_two_rpow_neg_eta {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π/2) :
    (1:ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have := Real.rpow_le_rpow_of_nonpos hsin hle
    (by linarith [Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≤ 0)
  rwa [Real.one_rpow] at this

/-- Pointwise domination on the open quadrant: any pure `D_z`-term of the `H^4`-integrand
is dominated by the whole integrand. -/
theorem sq_DzIter_le_HkIntegrand_Qd (α : ℝ) (g : ℝ → ℝ → ℝ) {j : ℕ} (hj : j ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π/2) :
    (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw := one_le_w hz
  have hsinp := one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hw2 : (1:ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
  have hstep : (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    calc (Work.Spaces.DzIter j g z θ) ^ 2
        = (Work.Spaces.DzIter j g z θ) ^ 2 * 1 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)) hsinp ?_ (by positivity)
          positivity
  have heq : (Work.Spaces.DzIter j g z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  rw [← heq] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ j hj)




/-- The integral over `Iθ` is the interval integral over `0..π/2`. -/
theorem integral_Iθ_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0:ℝ)..(π/2), f θ := by
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ π/2)]
  change (∫ θ in Set.Icc (0:ℝ) (π/2), f θ) = ∫ θ in Set.Ioc (0:ℝ) (π/2), f θ
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm]


/-- The `H^k`-integrand of the radial function `(z,θ) ↦ u z`: only the pure `D_z` sum
survives, and the weight `w z / sin(2θ)^{η/2}` squares to `(w z)² sin(2θ)^{-η}`. -/
theorem HkIntegrand_rad (α : ℝ) (k : ℕ) (u : ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => u z) z θ
      = (∑ i ∈ Finset.range (k + 1), (DzdIter i u z) ^ 2) * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem hθ
  have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => u z) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    split_ifs with h
    · rw [mixed_rad_eq_zero u h.1]
      ring
    · rfl
  rw [Work.Spaces.HkIntegrand, h2, add_zero]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [DzIter_rad]
  have hthis : ((DzdIter i u z) * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (DzdIter i u z) ^ 2 * (((Work.Spaces.w z) ^ 2) / (Real.sin (2 * θ)
          ^ (Work.Spaces.eta / 2)) ^ 2) := by
    rw [mul_pow, div_pow]
  rw [hthis, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
  ring

/-- The `H^k`-norm of a radial function is the product of `∫_θ sin(2θ)^{-η}` with the
`z`-integral of `∑_i (D_z^i u)² w²`. -/
theorem HkSq_rad (α : ℝ) (k : ℕ) (u : ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => u z)
      = (∫ z in Work.Spaces.Iz,
            ∑ i ∈ Finset.range (k + 1), (DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [Work.Spaces.HkSq]
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => u z) z θ)
        = (∑ i ∈ Finset.range (k + 1), (DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro z
    simp only [Work.Spaces.Iθ]
    rw [setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => by rw [HkIntegrand_rad α k u z hθ, Finset.sum_mul])]
    rw [MeasureTheory.integral_const_mul, ← Finset.sum_mul]
  rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => u z) z θ)
      = ∫ z in Work.Spaces.Iz, (∑ i ∈ Finset.range (k + 1),
            (DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      from setIntegral_congr_fun measurableSet_Ici (fun z _ => hinner z)]
  rw [MeasureTheory.integral_mul_const]


end Work.Elliptic

namespace Work.Elliptic

/-- The elementary consequences of `L₁₂(g)(0) = 0` and the integrability of `L12dens g`:
the value formula, the decay at infinity, and continuity on `[0,1]`. -/
theorem L12_values (g : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0))
    (h0 : Work.Elliptic.L12 g 0 = 0) :
    (∀ z : ℝ, 0 ≤ z →
        Work.Elliptic.L12 g z = - ∫ s in (0)..z, Work.Elliptic.L12dens g s)
      ∧ Filter.Tendsto (fun z => Work.Elliptic.L12 g z) Filter.atTop (nhds 0)
      ∧ ContinuousOn (fun z => Work.Elliptic.L12 g z) (Set.Icc 0 1) := by
  have hval : ∀ z : ℝ, 0 ≤ z →
      Work.Elliptic.L12 g z = - ∫ s in (0)..z, Work.Elliptic.L12dens g s := by
    intro z hz
    have h1 : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi z) :=
      hint.mono_set (Set.Ioi_subset_Ioi hz)
    have hadd := intervalIntegral.integral_interval_add_Ioi (f := Work.Elliptic.L12dens g)
      (a := (0:ℝ)) (b := z) hint h1
    have hz0 : (∫ s in Set.Ioi (0:ℝ), Work.Elliptic.L12dens g s) = 0 := h0
    simp only [Work.Elliptic.L12] at hz0 ⊢
    linarith
  refine ⟨hval, ?_, ?_⟩
  · have hanti := MeasureTheory.tendsto_setIntegral_of_antitone (μ := volume)
      (f := Work.Elliptic.L12dens g) (s := fun z : ℝ => Set.Ioi z)
      (fun z => measurableSet_Ioi) (fun a b hab => Set.Ioi_subset_Ioi hab) ⟨0, hint⟩
    have hempty : (⋂ z : ℝ, Set.Ioi z) = (∅ : Set ℝ) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨x, lt_irrefl x⟩
    rw [hempty, MeasureTheory.setIntegral_empty] at hanti
    simpa only [Work.Elliptic.L12] using hanti
  · have hii : IntervalIntegrable (Work.Elliptic.L12dens g) volume (0:ℝ) 1 := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hint.mono_set (Set.Ioc_subset_Ioi_self)
    have hprim : ContinuousOn (fun z => ∫ s in (0)..z, Work.Elliptic.L12dens g s)
        (Set.Icc (0:ℝ) 1) := by
      have h := intervalIntegral.continuousOn_primitive_interval' hii (Set.left_mem_uIcc (a := (0:ℝ)) (b := 1))
      simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using h
    refine ContinuousOn.congr (s := Set.Icc (0:ℝ) 1)
      (f := fun z => - ∫ s in (0)..z, Work.Elliptic.L12dens g s)
      (g := fun z => Work.Elliptic.L12 g z) hprim.neg ?_
    intro z hz
    exact hval z hz.1

end Work.Elliptic

namespace Work.Elliptic

/-- `volume` restricted to the open half-line and to `Iz` agree. -/
theorem restrict_Ioi_eq_restrict_Iz :
    volume.restrict (Set.Ioi (0:ℝ)) = volume.restrict Work.Spaces.Iz := by
  rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0:ℝ)))

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.WtoH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic
open Work.Spaces

/-! ## Angular power bookkeeping -/

theorem sin_two_rpow_mul' {θ a b : ℝ} (hθ : θ ∈ Iθ) (h : a + b ≠ 0) :
    (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ b = (Real.sin (2 * θ)) ^ (a + b) :=
  (Real.rpow_add' (sin_two_nonneg_Iθ hθ) h).symm

/-- `(a * (w z / sin(2θ)^{η/2}))² = (w z * a)² * sin(2θ)^{-η}`. -/
theorem sq_mul_div_sin {z θ a : ℝ} (hθ : θ ∈ Iθ) :
    (a * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      = (w z * a) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hne : eta / 2 + eta / 2 ≠ 0 := by
    rw [show eta / 2 + eta / 2 = eta by ring]; exact ne_of_gt eta_pos
  have h2 : ((Real.sin (2 * θ)) ^ (eta / 2)) ^ 2 = (Real.sin (2 * θ)) ^ eta := by
    rw [pow_two, ← Real.rpow_add' hs hne, show eta / 2 + eta / 2 = eta by ring]
  rw [mul_pow, div_pow, h2, div_eq_mul_inv, Real.rpow_neg hs]
  ring

/-! ## The weighted `D_z`-bound -/

theorem abs_w_DzIter_le {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {i : ℕ}
    (hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Iθ) (hM : 0 ≤ M) (hi : i ≤ 4)
    (hbound : ∀ k ≤ i, |w z * (z ^ k * pzIter k h z θ)| ≤ M) :
    |w z * DzIter i h z θ| ≤ 100 * M := by
  have h1 : w z * DzIter i h z θ
      = ∑ k ∈ Finset.range (i + 1), (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ)) := by
    rw [DzIter_eq_sum_scoef hsmooth i z hz θ hθ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1]
  calc |∑ k ∈ Finset.range (i + 1), (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ))|
      ≤ (bell i : ℝ) * M :=
        abs_sum_scoef_mul_le i M _ (fun k hk => hbound k hk)
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le i hi) hM

/-! ## The pointwise bound for `HkIntegrand` -/

theorem hkIntegrand_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : SmoothNbhd f) {Wl : ℝ} (hWl : 0 ≤ Wl)
    (hA : ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Iθ →
      |(1 + z) * w z * z ^ m * pzIter m f z θ| ≤ 200000 * Wl)
    (hB : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Iθ →
      |(1 + z) * w z * z ^ l * pzIter l (DthIter i f) z θ|
        ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    ∀ (z : ℝ), z ∈ Iz → ∀ (θ : ℝ), θ ∈ Iθ →
      HkIntegrand α 4 f z θ
        ≤ Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  by_cases hz0 : z = 0
  · subst hz0
    rw [HkIntegrand_apply_zero]
    have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(eta)) := Real.rpow_nonneg hsin _
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := Real.rpow_nonneg hsin _
    have h3 : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    have h4 : (0 : ℝ) ≤ 1 / (1 + 0) ^ 2 := by norm_num
    have h5 : (0 : ℝ) ≤ 2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
        + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) :=
      add_nonneg (mul_nonneg (by norm_num) h1)
        (mul_nonneg (by norm_num) (mul_nonneg h3 h2))
    exact mul_nonneg (mul_nonneg (sq_nonneg _) h4) h5
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have hzIoi : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
    have hwnn : 0 ≤ w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsmoothf : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1)) :=
      (SmoothInt.of_smoothNbhd hsm).2
    have hsmoothD : ∀ (i : ℕ) (θ' : ℝ), θ' ∈ Iθ →
        ContDiffOn ℝ ⊤ (fun z => DthIter i f z θ') (Set.Ioi (-1)) :=
      fun i θ' hθ' => DthIter_contDiffOn_slice' (SmoothInt.of_smoothNbhd hsm) i θ' hθ'
    -- per-term bound: pure D_z-family
    have hZ : ∀ i ≤ 4,
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          ≤ (20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) := by
      intro i hi
      have hb : ∀ k ≤ i, |w z * (z ^ k * pzIter k f z θ)| ≤ 200000 * Wl / (1 + z) := by
        intro k hk
        have h1 := hA k (le_trans hk hi) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le k)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le k),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (w z * DzIter i f z θ) ^ 2 ≤ (20000000 * Wl / (1 + z)) ^ 2 := by
        have h2 : |w z * DzIter i f z θ| ≤ 100 * (200000 * Wl / (1 + z)) :=
          abs_w_DzIter_le hsmoothf hzIoi hθ (by positivity) hi hb
        have h3 : |w z * DzIter i f z θ| ≤ 20000000 * Wl / (1 + z) := by
          convert h2 using 1; ring
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 20000000 * Wl / (1 + z))]
        exact h3
      rw [sq_mul_div_sin hθ]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- angular bookkeeping for the mixed family
    have hsq5 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      have hne : α / 5 + α / 5 ≠ 0 := by intro h; have := hα; linarith
      rw [pow_two, sin_two_rpow_mul' hθ hne, show α / 5 + α / 5 = 2 * α / 5 by ring]
    have hcomb : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        = (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := by
      have hne : 2 * α / 5 + -(gam α) ≠ 0 := by
        rw [gam]; intro h; linarith
      rw [hsq5, sin_two_rpow_mul' hθ hne]
      ring_nf
    -- per-term bound: mixed family
    have hM : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 4 →
        (mixed j i f z θ * Wt α z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
      intro i j hi hij
      have hb : ∀ l ≤ j,
          |w z * (z ^ l * pzIter l (DthIter i f) z θ)|
            ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z) := by
        intro l hl
        have h1 := hB i l hi (by omega) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le l)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le l),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (w z * mixed j i f z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 := by
        have h2 : |w z * DzIter j (DthIter i f) z θ|
            ≤ 100 * (200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z)) :=
          abs_w_DzIter_le (hsmoothD i) hzIoi hθ (by positivity) (by omega) hb
        have h3 : |w z * mixed j i f z θ|
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z) := by
          rw [show mixed j i f = DzIter j (DthIter i f) from rfl]
          convert h2 using 1; ring
        rw [sq_le_sq,
          abs_of_nonneg (by positivity : (0 : ℝ)
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z))]
        exact h3
      have hWt : (mixed j i f z θ * Wt α z θ) ^ 2
          = (w z * mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
        rw [mul_pow, bt_Wt_sq α z θ hα hθ]
        ring
      rw [hWt]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- assemble the two sums
    rw [HkIntegrand]
    have hZsum : ∑ i ∈ Finset.range (4 + 1),
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta))) := by
      calc ∑ i ∈ Finset.range (4 + 1),
            (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (4 + 1),
              (20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) :=
            Finset.sum_le_sum fun i hi => hZ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = 5 * ((20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta))) := by
            rw [div_pow]; ring
    have hMsum : ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
        ≤ (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
      set Yv : ℝ := (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) with hYv
      have hYvnn : 0 ≤ Yv := by rw [hYv]; positivity
      calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), Yv := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases h : 1 ≤ i ∧ i + j ≤ 4
            · rw [if_pos h]; exact hM i j h.1 h.2
            · rw [if_neg h]; exact hYvnn
        _ = 25 * Yv := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
        _ = (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
            rw [hYv]
            have hexp :
                (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                    / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
                  = (20000000 : ℝ) ^ 2 * Wl ^ 2 * (α + Real.sin (2 * θ)) ^ 2 / (1 + z) ^ 2
                    * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(gam α))) := by
              rw [div_pow, mul_pow, mul_pow, mul_pow]
              ring
            rw [hexp, hcomb]
            ring
    calc ∑ i ∈ Finset.range (4 + 1),
            (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta)))
          + (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
              * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) :=
          add_le_add hZsum hMsum
      _ = Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by ring

/-! ## The inner angular integral -/


/-! ## The outer radial integral -/



/-! ## The main theorem -/



end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.cylOp_polar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The polar change of variables for the axisymmetric Biot--Savart operator

This file proves `Work.Elliptic.cylOp_polar`: with `ρ = rhoP r z = √(r²+z²)`,
`θ = thetaP r z = arctan (z/r)` and `ψ(r,z) = ρ² Ψ (ρ^α, θ)`, the cylindrical elliptic
operator `cylOp` of (3dBSL) reproduces the operator `bslOp` of (PolarBSL) in the self-similar
variables `R = ρ^α`, `θ`.

The proof follows the paper's computation line by line:

* `pdRR_add_pdZZ_comp_polar` (delegated): the Cartesian Laplacian of `(r,z) ↦ F (ρ r z) (θ r z)`
  is the polar Laplacian `F_ρρ + F_ρ/ρ + F_θθ/ρ²`;
* `first_derivs_mul_pow_rpow`, `pdRR_mul_pow_rpow` (delegated): the first and second `p`-derivatives
  of `(p,q) ↦ p² Ψ (p^α) q`;
* `Work.Cyl.pdR_comp_polar_rho` (existing): the radial derivative of `F ∘ (ρ,θ)`;
* `pth_tan_mul` (delegated): the angular derivative of `tan θ · Ψ`.

Only the pointwise algebra of the final step is done here.
-/

noncomputable section

open scoped Real Topology

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Slice derivatives of the polar coordinates in the radial variable -/

private lemma hasDerivAt_rhoP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.const_add (z ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hfun : (fun r' : ℝ => Work.Cyl.rhoP r' z) = fun r' => Real.sqrt (r' ^ 2 + z ^ 2) := by
    funext r'; rw [Work.Cyl.rhoP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp

private lemma hasDerivAt_thetaP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r := by
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => Work.Cyl.thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [Work.Cyl.thetaP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-! ## The partial derivatives of a `C²` function are differentiable -/

private theorem diffAt2_pdR_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) :
    Work.Cyl.DiffAt2 (Work.Cyl.pdR f) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => Work.Cyl.pdR f p.1 p.2) (r, z)
  have hev : ∀ᶠ p in 𝓝 ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have heq : (fun p : ℝ × ℝ => Work.Cyl.pdR f p.1 p.2) =ᶠ[𝓝 (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0)) := by
    filter_upwards [hev] with p hp
    exact (Work.Cyl.fderiv_prod_apply_fst f p.1 p.2 hp).symm
  rw [Filter.EventuallyEq.differentiableAt_iff heq]
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  exact hG.clm_apply (differentiableAt_const ((1, 0) : ℝ × ℝ))

private theorem diffAt2_pdZ_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) :
    Work.Cyl.DiffAt2 (Work.Cyl.pdZ f) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => Work.Cyl.pdZ f p.1 p.2) (r, z)
  have hev : ∀ᶠ p in 𝓝 ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have heq : (fun p : ℝ × ℝ => Work.Cyl.pdZ f p.1 p.2) =ᶠ[𝓝 (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (0, 1)) := by
    filter_upwards [hev] with p hp
    exact (Work.Cyl.fderiv_prod_apply_snd f p.1 p.2 hp).symm
  rw [Filter.EventuallyEq.differentiableAt_iff heq]
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  exact hG.clm_apply (differentiableAt_const ((0, 1) : ℝ × ℝ))

/-! ## The two-variable function `(p,q) ↦ p² Ψ (p^α) q` is `C²` -/

private theorem contDiffAt_uncurry_mul_pow (Ψ : ℝ → ℝ → ℝ) (α ρ θ : ℝ) (hρ : 0 < ρ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (ρ ^ α, θ)) :
    ContDiffAt ℝ 2 (Function.uncurry (fun p q => p ^ 2 * Ψ (p ^ α) q)) (ρ, θ) := by
  show ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ 2 * Ψ (y.1 ^ α) y.2) (ρ, θ)
  have hsq : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ 2) (ρ, θ) := by fun_prop
  have hpow : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ α) (ρ, θ) := by
    have h1 : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1) (ρ, θ) := contDiffAt_fst
    have hr : ContDiffAt ℝ 2 (fun x : ℝ => x ^ α) ρ :=
      Real.contDiffAt_rpow_const (x := ρ) (p := α) (n := 2) (Or.inl (ne_of_gt hρ))
    have h := hr.comp (ρ, θ) h1
    simpa [Function.comp_def] using h
  have hpsi : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => Ψ (y.1 ^ α) y.2) (ρ, θ) := by
    have hpair : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => (y.1 ^ α, y.2)) (ρ, θ) :=
      hpow.prodMk (contDiffAt_snd : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.2) (ρ, θ))
    have h := hΨ.comp (ρ, θ) hpair
    simpa [Function.comp_def, Function.uncurry_apply_pair] using h
  exact hsq.mul hpsi

/-! ## The polar form of `tan` -/

private lemma tan_thetaP {r : ℝ} (hr : 0 < r) (z : ℝ) :
    Real.tan (Work.Cyl.thetaP r z) = z / r := by
  rw [Real.tan_eq_sin_div_cos, Work.Cyl.sin_thetaP hr z, Work.Cyl.cos_thetaP hr z]
  field_simp [Work.Cyl.rhoP_ne_zero hr z]

end Work.Elliptic

namespace Work.Elliptic

theorem cylOp_polar (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (Work.Cyl.rhoP r z ^ α, Work.Cyl.thetaP r z)) :
    Work.Cyl.cylOp (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = Work.Elliptic.bslOp α Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
  have hρpos : 0 < (Work.Cyl.rhoP r z) := Work.Cyl.rhoP_pos hr z
  have hρne : (Work.Cyl.rhoP r z) ≠ 0 := ne_of_gt hρpos
  have hcosne : Real.cos (Work.Cyl.thetaP r z) ≠ 0 := ne_of_gt (Work.Cyl.cos_thetaP_pos hr z)
  -- the model function `(p,q) ↦ p²Ψ(p^α,q)` is `C²` and its partials are differentiable
  have hF2 : ContDiffAt ℝ 2 (Function.uncurry (fun p q => p ^ 2 * Ψ (p ^ α) q)) ((Work.Cyl.rhoP r z), (Work.Cyl.thetaP r z)) :=
    contDiffAt_uncurry_mul_pow Ψ α _ _ hρpos hΨ
  have hF2' : Work.Cyl.DiffAt2 (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) := hF2.differentiableAt (by simp)
  have hpdRF : Work.Cyl.DiffAt2 (Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q)) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) :=
    diffAt2_pdR_of_contDiffAt_two _ _ _ hF2
  have hpdZF : Work.Cyl.DiffAt2 (Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q)) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) :=
    diffAt2_pdZ_of_contDiffAt_two _ _ _ hF2
  have hpdRΨ : Work.Cyl.DiffAt2 (Work.Cyl.pdR Ψ) (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) :=
    diffAt2_pdR_of_contDiffAt_two Ψ _ _ hΨ
  -- the polar Laplacian and the radial derivative
  have hLap : Work.Cyl.pdRR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z + Work.Cyl.pdZZ (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = Work.Cyl.pdRR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) + Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) / (Work.Cyl.rhoP r z)
        + Work.Cyl.pdZZ (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) / (Work.Cyl.rhoP r z) ^ 2 := by
    exact pdRR_add_pdZZ_comp_polar (fun p q => p ^ 2 * Ψ (p ^ α) q) r z hr hF2 hpdRF hpdZF
  have hDr : Work.Cyl.pdR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = Real.cos (Work.Cyl.thetaP r z) * Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
        - Real.sin (Work.Cyl.thetaP r z) / (Work.Cyl.rhoP r z) * Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) := by
    exact Work.Cyl.pdR_comp_polar_rho (fun p q => p ^ 2 * Ψ (p ^ α) q) r z hr hF2'
  -- the partial derivatives of the model function
  have hD1 : Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
      = 2 * (Work.Cyl.rhoP r z) * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) + α * (Work.Cyl.rhoP r z) ^ (α + 1) * Work.Cyl.pdR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact (first_derivs_mul_pow_rpow Ψ α (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) hρpos hΨ).1
  have hD2 : Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) = (Work.Cyl.rhoP r z) ^ 2 * Work.Cyl.pdZ Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact (first_derivs_mul_pow_rpow Ψ α (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) hρpos hΨ).2.1
  have hD3 : Work.Cyl.pdZZ (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) = (Work.Cyl.rhoP r z) ^ 2 * Work.Cyl.pdZZ Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact (first_derivs_mul_pow_rpow Ψ α (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) hρpos hΨ).2.2
  have hD4 : Work.Cyl.pdRR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
      = 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) + α * (α + 3) * (Work.Cyl.rhoP r z ^ α) * Work.Cyl.pdR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) + α ^ 2 * (Work.Cyl.rhoP r z) ^ (2 * α) * Work.Cyl.pdRR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact pdRR_mul_pow_rpow Ψ α (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) hρpos hΨ hpdRΨ
  -- the angular derivative of `tan θ · Ψ`
  have hslice : DifferentiableAt ℝ (fun θ' => Ψ (Work.Cyl.rhoP r z ^ α) θ') (Work.Cyl.thetaP r z) :=
    Work.Cyl.differentiableAt_slice_snd Ψ _ _ (hΨ.differentiableAt (by simp))
  have htan : Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)
      = Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z) ^ 2 + Real.tan (Work.Cyl.thetaP r z) * Work.Cyl.pdZ Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact pth_tan_mul Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) hcosne hslice
  -- the `pz`/`pdR` dictionary is definitional
  have hId1 : Work.Spaces.pzIter 2 Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) = Work.Cyl.pdRR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := rfl
  have hId2 : Work.Spaces.pz Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) = Work.Cyl.pdR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := rfl
  have hId3 : Work.Spaces.pthIter 2 Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) = Work.Cyl.pdZZ Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := rfl
  -- trig and `rpow` rewrites
  have hcosθ : Real.cos (Work.Cyl.thetaP r z) = r / (Work.Cyl.rhoP r z) := Work.Cyl.cos_thetaP hr z
  have hsinθ : Real.sin (Work.Cyl.thetaP r z) = z / (Work.Cyl.rhoP r z) := Work.Cyl.sin_thetaP hr z
  have htanθ : Real.tan (Work.Cyl.thetaP r z) = z / r := tan_thetaP hr z
  have hpow1 : (Work.Cyl.rhoP r z) ^ (α + 1) = (Work.Cyl.rhoP r z ^ α) * (Work.Cyl.rhoP r z) := Real.rpow_add_one hρne α
  have hpow2 : (Work.Cyl.rhoP r z) ^ (2 * α) = (Work.Cyl.rhoP r z ^ α) ^ 2 := by
    rw [show (2 : ℝ) * α = α * 2 by ring, Real.rpow_mul hρpos.le, Real.rpow_two]
  -- the computation
  rw [show Work.Cyl.cylOp (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = -Work.Cyl.pdRR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z - Work.Cyl.pdZZ (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
        - Work.Cyl.pdR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z / r + (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z / r ^ 2 from rfl]
  rw [Work.Elliptic.bslOp_apply]
  simp only [Work.Elliptic.Lzero]
  rw [show -Work.Cyl.pdRR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z - Work.Cyl.pdZZ (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = -(Work.Cyl.pdRR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z + Work.Cyl.pdZZ (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z) by ring, hLap, hDr,
    hD1, hD2, hD3, hD4, hId1, hId2, hId3, htan, hcosθ, hsinθ, htanθ, hpow1, hpow2]
  field_simp
  ring

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AgmonFts.abs_deriv_cutU_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AgmonFts

open MeasureTheory Set Filter
open scoped Real Topology
open Work.FTS.EllipticEst.AgmonSlice

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The derivative of `z ↦ ρ z · z` -/

private lemma cutRho_eq (z : ℝ) : cutRho z = (1 + z) ^ 4 / z ^ 4 := by
  simp only [cutRho, Work.Spaces.w, div_pow]
  ring

private lemma deriv_cutRho_mul_id {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => cutRho y * y) z = (z - 3) / (1 + z) * cutRho z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hfun : (fun y : ℝ => cutRho y * y) = fun y : ℝ => (1 + y) ^ 4 / y ^ 3 := by
    funext y
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num [cutRho, Work.Spaces.w]
    · rw [cutRho_eq]
      field_simp
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (fun w : ℝ => (1 + w) ^ 4) z := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun w : ℝ => w ^ 3) z := by fun_prop
  have hd3 : (fun w : ℝ => w ^ 3) z ≠ 0 := by simpa using pow_ne_zero 3 hz0
  rw [show (fun w : ℝ => (1 + w) ^ 4 / w ^ 3)
      = (fun w : ℝ => (1 + w) ^ 4) / (fun w : ℝ => w ^ 3) from rfl]
  rw [deriv_div hd1 hd2 hd3]
  have hv1 : deriv (fun w : ℝ => (1 + w) ^ 4) z = 4 * (1 + z) ^ 3 := by
    change deriv ((fun w : ℝ => 1 + w) ^ 4) z = 4 * (1 + z) ^ 3
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1 + w) z)]
    simp
  have hv2 : deriv (fun w : ℝ => w ^ 3) z = 3 * z ^ 2 := by
    change deriv ((fun w : ℝ => w) ^ 3) z = 3 * z ^ 2
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => w) z)]
    simp
  rw [hv1, hv2, cutRho_eq]
  field_simp
  ring

/-- `|(ρ z)'| ≤ 3 ρ` for `z > 0`: the first summand of the product rule. -/
private lemma abs_deriv_cutRho_mul_id_le {z : ℝ} (hz : 0 < z) :
    |deriv (fun w : ℝ => cutRho w * w) z| ≤ 3 * cutRho z := by
  have h1 : 0 < 1 + z := by linarith
  have h2 : |z - 3| ≤ 3 * (1 + z) := by
    rcases le_total 3 z with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  have h3 : |z - 3| / (1 + z) ≤ 3 := by
    rw [div_le_iff₀ h1]
    linarith
  rw [deriv_cutRho_mul_id hz, abs_mul, abs_div, abs_of_pos h1,
    abs_of_nonneg (cutRho_nonneg z)]
  exact mul_le_mul_of_nonneg_right h3 (cutRho_nonneg z)

private lemma contDiffOn_cutRho_mul_id :
    ContDiffOn ℝ 1 (fun y : ℝ => cutRho y * y) (Set.Ioi (0:ℝ)) := by
  have heq : (fun y : ℝ => cutRho y * y) = fun y : ℝ => (1 + y) ^ 4 / y ^ 3 := by
    funext y
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num [cutRho, Work.Spaces.w]
    · rw [cutRho_eq]; field_simp
  rw [heq]
  exact ContDiffOn.div (by fun_prop) (by fun_prop) (fun y hy => pow_ne_zero 3 (ne_of_gt hy))

/-- The triangle inequality for a sum of four terms. -/
private lemma abs_sum_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-! ## The pointwise bound -/

theorem abs_deriv_cutU_mul_le (h ψ : ℝ → ℝ) (K : ℝ)
    (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0))
    (hψ1 : ∀ z : ℝ, |ψ z| ≤ 1)
    (hK : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ K) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) z|
        ≤ 3 * Work.FTS.EllipticEst.AgmonSlice.cutRho z * ψ z ^ 2 * |z * deriv h z|
          + 2 * K * Work.FTS.EllipticEst.AgmonSlice.cutRho z * |ψ z| * |z * deriv h z|
          + Work.FTS.EllipticEst.AgmonSlice.cutRho z * ψ z ^ 2
              * |Work.FTS.EllipticEst.rDzIter 2 h z| := by
  intro z hz
  have hz0 : 0 < z := hz
  have hρnn : 0 ≤ cutRho z := cutRho_nonneg z
  have hsqψ : |ψ z| * |ψ z| = ψ z ^ 2 := by rw [← sq, sq_abs]
  -- differentiability of the factors of `cutU h ψ` at `z`
  have hψ_at : DifferentiableAt ℝ ψ z :=
    (hψ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdh_cd : ContDiffOn ℝ 1 (deriv h) (Set.Ioi (0 : ℝ)) :=
    hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdh_at : DifferentiableAt ℝ (deriv h) z :=
    (hdh_cd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hA_at : DifferentiableAt ℝ (fun y : ℝ => cutRho y * y) z :=
    (contDiffOn_cutRho_mul_id.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hC_at : DifferentiableAt ℝ (fun y : ℝ => y * deriv h y) z :=
    differentiableAt_id.mul hdh_at
  -- the product rule for `cutU`
  have hU : cutU h ψ = ((fun y : ℝ => cutRho y * y) * ψ * ψ) * (fun y : ℝ => y * deriv h y) := by
    funext y; simp only [cutU, Pi.mul_apply]; ring
  have hCderiv : deriv (fun y : ℝ => y * deriv h y) z = deriv h z + z * deriv (deriv h) z := by
    change deriv (id * deriv h) z = deriv h z + z * deriv (deriv h) z
    rw [deriv_mul differentiableAt_id hdh_at, deriv_id]
    simp only [id_eq, one_mul]
  have hderiv : deriv (cutU h ψ) z
      = deriv (fun y : ℝ => cutRho y * y) z * (ψ z * ψ z) * (z * deriv h z)
        + ((cutRho z * z) * deriv ψ z * ψ z) * (z * deriv h z)
        + ((cutRho z * z) * ψ z * deriv ψ z) * (z * deriv h z)
        + (cutRho z * z * (ψ z * ψ z)) * (deriv h z + z * deriv (deriv h) z) := by
    rw [hU]
    rw [deriv_mul ((hA_at.mul hψ_at).mul hψ_at) hC_at,
      deriv_mul (hA_at.mul hψ_at) hψ_at,
      deriv_mul hA_at hψ_at,
      hCderiv]
    simp only [Pi.mul_apply]
    ring_nf
  -- the first summand
  have hT1 : |deriv (fun y : ℝ => cutRho y * y) z * (ψ z * ψ z) * (z * deriv h z)|
      ≤ 3 * cutRho z * ψ z ^ 2 * (z * |deriv h z|) := by
    rw [show |deriv (fun y : ℝ => cutRho y * y) z * (ψ z * ψ z) * (z * deriv h z)|
        = |deriv (fun y : ℝ => cutRho y * y) z| * ψ z ^ 2 * (z * |deriv h z|) by
      simp only [abs_mul, abs_of_pos hz0, hsqψ]]
    have h1 := abs_deriv_cutRho_mul_id_le hz0
    have h3 := mul_le_mul_of_nonneg_right h1
      (mul_nonneg (sq_nonneg (ψ z)) (mul_nonneg hz0.le (abs_nonneg (deriv h z))))
    linarith [h3]
  have hzψ : z * |deriv ψ z| ≤ K := by
    have h := hK z hz
    rwa [abs_mul, abs_of_pos hz0] at h
  -- the two middle summands
  have hT2 : |((cutRho z * z) * deriv ψ z * ψ z) * (z * deriv h z)|
      ≤ K * cutRho z * |ψ z| * (z * |deriv h z|) := by
    rw [show |((cutRho z * z) * deriv ψ z * ψ z) * (z * deriv h z)|
        = (cutRho z * z) * |deriv ψ z| * |ψ z| * (z * |deriv h z|) by
      simp only [abs_mul, abs_of_pos hz0, abs_of_nonneg hρnn]]
    rw [show (cutRho z * z) * |deriv ψ z| * |ψ z| * (z * |deriv h z|)
        = (z * |deriv ψ z|) * cutRho z * |ψ z| * (z * |deriv h z|) by ring]
    have hstep : (z * |deriv ψ z|) * cutRho z * |ψ z| ≤ K * cutRho z * |ψ z| := by
      have hh := mul_le_mul_of_nonneg_right hzψ (mul_nonneg hρnn (abs_nonneg (ψ z)))
      linarith [hh]
    exact mul_le_mul_of_nonneg_right hstep (mul_nonneg hz0.le (abs_nonneg (deriv h z)))
  have hT3 : |((cutRho z * z) * ψ z * deriv ψ z) * (z * deriv h z)|
      ≤ K * cutRho z * |ψ z| * (z * |deriv h z|) := by
    rw [show |((cutRho z * z) * ψ z * deriv ψ z) * (z * deriv h z)|
        = (cutRho z * z) * |ψ z| * |deriv ψ z| * (z * |deriv h z|) by
      simp only [abs_mul, abs_of_pos hz0, abs_of_nonneg hρnn]]
    rw [show (cutRho z * z) * |ψ z| * |deriv ψ z| * (z * |deriv h z|)
        = (z * |deriv ψ z|) * cutRho z * |ψ z| * (z * |deriv h z|) by ring]
    have hstep : (z * |deriv ψ z|) * cutRho z * |ψ z| ≤ K * cutRho z * |ψ z| := by
      have hh := mul_le_mul_of_nonneg_right hzψ (mul_nonneg hρnn (abs_nonneg (ψ z)))
      linarith [hh]
    exact mul_le_mul_of_nonneg_right hstep (mul_nonneg hz0.le (abs_nonneg (deriv h z)))
  -- `z (h' + z h'') = rDzIter 2 h`
  have hE : z * (deriv h z + z * deriv (deriv h) z) = Work.FTS.EllipticEst.rDzIter 2 h z := by
    have hrDz_h : (Work.FTS.EllipticEst.rDz h) = fun y : ℝ => y * deriv h y := rfl
    have h2u : Work.FTS.EllipticEst.rDzIter 2 h
        = Work.FTS.EllipticEst.rDz (Work.FTS.EllipticEst.rDz h) := by
      simp only [Work.FTS.EllipticEst.rDzIter_succ, Work.FTS.EllipticEst.rDzIter_zero]
    rw [h2u, hrDz_h]
    show z * (deriv h z + z * deriv (deriv h) z) = z * deriv (fun y : ℝ => y * deriv h y) z
    rw [hCderiv]
  -- the last summand
  have hT4 : |(cutRho z * z * (ψ z * ψ z)) * (deriv h z + z * deriv (deriv h) z)|
      ≤ cutRho z * ψ z ^ 2 * |Work.FTS.EllipticEst.rDzIter 2 h z| := by
    rw [show |(cutRho z * z * (ψ z * ψ z)) * (deriv h z + z * deriv (deriv h) z)|
        = (cutRho z * z * ψ z ^ 2) * |deriv h z + z * deriv (deriv h) z| by
      simp only [abs_mul, abs_of_pos hz0, abs_of_nonneg hρnn, hsqψ]]
    rw [show (cutRho z * z * ψ z ^ 2) * |deriv h z + z * deriv (deriv h) z|
        = cutRho z * ψ z ^ 2 * (z * |deriv h z + z * deriv (deriv h) z|) by ring]
    rw [show z * |deriv h z + z * deriv (deriv h) z| = |Work.FTS.EllipticEst.rDzIter 2 h z| by
      conv_rhs => rw [← hE]
      rw [abs_mul, abs_of_pos hz0]]
  have hzabs : z * |deriv h z| = |z * deriv h z| := by rw [abs_mul, abs_of_pos hz0]
  calc |deriv (cutU h ψ) z|
      ≤ 3 * cutRho z * ψ z ^ 2 * (z * |deriv h z|)
          + K * cutRho z * |ψ z| * (z * |deriv h z|)
          + K * cutRho z * |ψ z| * (z * |deriv h z|)
          + cutRho z * ψ z ^ 2 * |Work.FTS.EllipticEst.rDzIter 2 h z| := by
        rw [hderiv]
        refine le_trans (abs_sum_four_le _ _ _ _) ?_
        linarith [hT1, hT2, hT3, hT4]
    _ = 3 * cutRho z * ψ z ^ 2 * |z * deriv h z|
          + 2 * K * cutRho z * |ψ z| * |z * deriv h z|
          + cutRho z * ψ z ^ 2 * |Work.FTS.EllipticEst.rDzIter 2 h z| := by
        rw [hzabs]
        ring

end Work.FTS.EllipticEst.AgmonFts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AgmonFts.cut_IBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AgmonFts

theorem cut_IBP (h ψ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0))
    (hψsupp : ∀ z : ℝ, 0 < z → z ≤ a ∨ b ≤ z → ψ z = 0) :
    MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AgmonSlice.cutF h ψ) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn
        (fun z => deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) z * h z) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.AgmonSlice.cutF h ψ z)
        = -(∫ z in Set.Ioi (0 : ℝ),
            deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) z * h z) := by
  -- `[a,b]` sits inside the half-line on which `h` and `ψ` are differentiable
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  -- a point of `(0,∞) \ [a,b]` lies to the left of `a` or to the right of `b`
  have hsplit : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) \ Set.Icc a b → x < a ∨ b < x := by
    intro x hx
    have h2 := hx.2
    simp only [Set.mem_Icc, not_and_or, not_le] at h2
    exact h2
  -- `ρ = w²` is smooth (hence `C¹`) on `(0,∞)`
  have hrhoCont : ContDiffOn ℝ 1 Work.FTS.EllipticEst.AgmonSlice.cutRho (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 1 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
      apply ContDiffOn.div
      · fun_prop
      · fun_prop
      · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
    exact h1.pow 2
  -- `cutU h ψ = ρ z ψ² (z h')` is `C¹` on `(0,∞)`
  have hC1 : ContDiffOn ℝ 1 (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) (Set.Ioi 0) := by
    have hψ1 : ContDiffOn ℝ 1 ψ (Set.Ioi 0) := hψ.of_le (by norm_num)
    have hdh : ContDiffOn ℝ 1 (deriv h) (Set.Ioi 0) :=
      hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have h2 : ContDiffOn ℝ 1 (fun z : ℝ => z * deriv h z) (Set.Ioi 0) :=
      contDiffOn_id.mul hdh
    have h3 : ContDiffOn ℝ 1 (fun z : ℝ => ψ z ^ 2) (Set.Ioi 0) := hψ1.pow 2
    exact ((hrhoCont.mul contDiffOn_id).mul h3).mul h2
  have hcdU : ContinuousOn (deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ)) (Set.Icc a b) :=
    (hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hch : ContinuousOn h (Set.Icc a b) := hh.continuousOn.mono hsub
  have hcdh : ContinuousOn (deriv h) (Set.Icc a b) :=
    (hh.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  -- the two integrands vanish off `[a,b]`
  have hvanishF : ∀ z, 0 < z → (z < a ∨ b < z) →
      Work.FTS.EllipticEst.AgmonSlice.cutF h ψ z = 0 := by
    intro z hz hc
    have hψz : ψ z = 0 := by
      rcases hc with h' | h'
      · exact hψsupp z hz (Or.inl (le_of_lt h'))
      · exact hψsupp z hz (Or.inr (le_of_lt h'))
    simp only [Work.FTS.EllipticEst.AgmonSlice.cutF, hψz]; ring
  have hvanishdU : ∀ z, 0 < z → (z < a ∨ b < z) →
      deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) z = 0 := by
    intro z hz hc
    -- `cutU h ψ` vanishes in a whole neighbourhood of `z`, hence so does its derivative
    have hev : Work.FTS.EllipticEst.AgmonSlice.cutU h ψ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      rcases hc with h' | h'
      · filter_upwards
          [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo 0 a from ⟨hz, h'⟩)] with y hy
        simp only [Work.FTS.EllipticEst.AgmonSlice.cutU,
          hψsupp y hy.1 (Or.inl (le_of_lt hy.2))]
        ring
      · filter_upwards
          [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo b (z + 1) from ⟨h', by linarith⟩)] with y hy
        simp only [Work.FTS.EllipticEst.AgmonSlice.cutU,
          hψsupp y (by linarith [hy.1]) (Or.inr (le_of_lt hy.1))]
        ring
    rw [hev.deriv_eq]; simp
  -- `cutF h ψ` is continuous on `[a,b]`
  have hcF : ContinuousOn (Work.FTS.EllipticEst.AgmonSlice.cutF h ψ) (Set.Icc a b) := by
    have hrho_c : ContinuousOn Work.FTS.EllipticEst.AgmonSlice.cutRho (Set.Icc a b) :=
      hrhoCont.continuousOn.mono hsub
    have hψ2_c : ContinuousOn (fun z : ℝ => ψ z ^ 2) (Set.Icc a b) :=
      (hψ.continuousOn.mono hsub).pow 2
    have hz2_c : ContinuousOn (fun z : ℝ => (z * deriv h z) ^ 2) (Set.Icc a b) :=
      (continuousOn_id.mul hcdh).pow 2
    exact (hrho_c.mul hψ2_c).mul hz2_c
  -- integrability of the two sides
  have hIntF : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AgmonSlice.cutF h ψ)
      (Set.Ioi 0) :=
    (hcF.integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hvanishF x hx.1 (hsplit x hx))
  have hintUV : MeasureTheory.IntegrableOn
      (fun x => Work.FTS.EllipticEst.AgmonSlice.cutU h ψ x * deriv h x) (Set.Ioi 0) :=
    hIntF.congr_fun (fun x _ => (Work.FTS.EllipticEst.AgmonSlice.cutU_mul_deriv h ψ x).symm)
      measurableSet_Ioi
  have hIntdU : MeasureTheory.IntegrableOn
      (fun x => deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) x * h x) (Set.Ioi 0) :=
    ((hcdU.mul hch).integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => by rw [Pi.mul_apply, hvanishdU x hx.1 (hsplit x hx), zero_mul])
  refine ⟨hIntF, hIntdU, ?_⟩
  simp only [← Work.FTS.EllipticEst.AgmonSlice.cutU_mul_deriv]
  -- integration by parts on `(0,∞)`; both boundary terms vanish since `ψ` is supported in `[a,b]`
  rw [MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) (v := h)
    (u' := deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ)) (v' := deriv h)
    (fun x hx => ((hC1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)).hasDerivAt)
    (fun x hx => ((hh.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)).hasDerivAt)
    hintUV hIntdU
    (by
      have hev : (fun x => Work.FTS.EllipticEst.AgmonSlice.cutU h ψ x * h x)
          =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioo_mem_nhdsGT ha] with x hx
        simp only [Work.FTS.EllipticEst.AgmonSlice.cutU,
          hψsupp x hx.1 (Or.inl (le_of_lt hx.2))]
        ring
      exact tendsto_const_nhds.congr' hev.symm)
    (by
      have hev : (fun x => Work.FTS.EllipticEst.AgmonSlice.cutU h ψ x * h x)
          =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
        filter_upwards [eventually_ge_atTop b] with x hx
        have hx0 : 0 < x := lt_of_lt_of_le (lt_trans ha hab) hx
        simp only [Work.FTS.EllipticEst.AgmonSlice.cutU, hψsupp x hx0 (Or.inr hx)]
        ring
      exact tendsto_const_nhds.congr' hev.symm)]
  ring

end Work.FTS.EllipticEst.AgmonFts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.I4_lower_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

theorem setIntegral_Ioo_Iθ (g : ℝ → ℝ) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), g θ) = ∫ θ in Work.Spaces.Iθ, g θ := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))

theorem integrableOn_continuousOn_mul {f : ℝ → ℝ} {A : Set ℝ} (hf : IntegrableOn f A)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 (Real.pi / 2)))
    (hAm : MeasurableSet A) (hA : A ⊆ Set.Icc 0 (Real.pi / 2)) :
    IntegrableOn (fun x => f x * g x) A :=
  hf.mul_continuousOn_of_subset hg hAm isCompact_Icc hA

theorem integrableOn_of_mul_w2 {g : ℝ → ℝ} {s : Set ℝ} {z : ℝ} (hz : 0 < z)
    (hs : MeasurableSet s) (h : IntegrableOn (fun θ => g θ * w2 z) s) : IntegrableOn g s := by
  have hw : w2 z ≠ 0 := ne_of_gt (by rw [w2]; exact pow_pos (w_pos hz) 2)
  have h' := h.const_mul ((w2 z))⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h' ?_ hs
  intro θ hθ
  field_simp

theorem cos_two_mul_mul_div_cos_sq_le {a θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos (2 * θ) * (a / Real.cos θ) ^ 2 ≤ 2 * a ^ 2 := by
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc2 : 0 < Real.cos θ ^ 2 := sq_pos_of_pos hcpos
  have hkey : (2 * Real.cos θ ^ 2 - 1) * (a ^ 2 / Real.cos θ ^ 2)
      = 2 * a ^ 2 - a ^ 2 / Real.cos θ ^ 2 := by
    field_simp
  rw [div_pow, Real.cos_two_mul, hkey]
  have hnn : 0 ≤ a ^ 2 / Real.cos θ ^ 2 := div_nonneg (sq_nonneg a) (le_of_lt hc2)
  linarith


/-! ## The pointwise identity in the language of `Ψ` -/

theorem pth_tan_sub (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ
      = Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ := by
  have hz1 : (-1 : ℝ) < z := by linarith
  have hdiff : DifferentiableAt ℝ (fun θ => Ψ z θ) θ := by
    have hs : ContDiffOn ℝ ⊤ (fun t : ℝ => Ψ z t) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
      have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
        contDiffOn_const.prodMk contDiffOn_id
      have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
      simpa [Function.comp_def, Function.uncurry] using h
    exact (hs.contDiffAt (Ioo_mem_nhds (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))).differentiableAt (by simp)
  simpa [Work.Spaces.pth] using I4_tan_mul_sub_deriv (fun θ => Ψ z θ) hθ hdiff

/-! ## The slice identity, from the fundamental theorem of calculus -/

theorem slice_ident (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu1 : u (Real.pi / 2) = 0)
    (hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ / Real.cos θ| ≤ C ∧ |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ C)
    (hiA : IntegrableOn (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hiB : IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hiC : IntegrableOn (fun θ => Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
      * deriv (deriv u) θ * sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        * deriv (deriv u) θ * sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sig θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2),
            acoef θ * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ := by
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  set P1 : ℝ → ℝ := fun θ => acoef θ * (deriv ψ θ) ^ 2 * sig θ with hP1
  set P2 : ℝ → ℝ := fun θ => Real.sin θ * deriv ψ θ * deriv (deriv u) θ * sig θ with hP2
  set P3 : ℝ → ℝ := fun θ => (((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ)) * ψ θ ^ 2 * sig θ
    with hP3
  have hI : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hcA : ContinuousOn acoef (Set.Icc 0 (Real.pi / 2)) := by
    unfold acoef; fun_prop
  have hcC : ContinuousOn (fun θ => ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ))
      (Set.Icc 0 (Real.pi / 2)) := by fun_prop
  have hP1int : IntegrableOn P1 (Set.Ioo 0 (Real.pi / 2)) := by
    have h := integrableOn_continuousOn_mul (g := acoef) hiA hcA hI hsub
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ hI
    intro θ hθ
    first
      | (simp only [hP1, hψ]; ring)
      | (simp only [hP1, hψ])
  have hP2int : IntegrableOn P2 (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hiC ?_ hI
    intro θ hθ
    first
      | (simp only [hP2, hψ]; ring)
      | (simp only [hP2, hψ])
  have hP3int : IntegrableOn P3 (Set.Ioo 0 (Real.pi / 2)) := by
    have h := integrableOn_continuousOn_mul
      (g := fun θ => ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ)) hiB hcC hI hsub
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ hI
    intro θ hθ
    first
      | (simp only [hP3, hψ, mul_assoc]; ring)
      | (simp only [hP3, hψ]; ring)
      | (simp only [hP3, hψ])
  have hHint : IntegrableOn (Hintegrand u) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := (hP1int.add hP2int).sub hP3int
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ hI
    intro θ hθ
    simp only [Hintegrand, hP1, hP2, hP3, hψ, Pi.add_apply, Pi.sub_apply]
    try ring
  have hG := I4_Gprim_deriv u hu hu1 hbdd
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hint : IntervalIntegrable (Hintegrand u) volume 0 (Real.pi / 2) := by
    constructor
    · exact hHint.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume)).symm
    · have hset : Set.Ioc (Real.pi / 2) (0 : ℝ) = ∅ :=
        Set.Ioc_eq_empty_iff.mpr (by linarith [Real.pi_pos])
      rw [hset]
      exact integrableOn_empty
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hπ hG.1 hint hG.2.1 hG.2.2
  have hzero : (∫ θ in Set.Ioo 0 (Real.pi / 2), Hintegrand u θ) = 0 := by
    have h1 : (∫ θ in Set.Ioc 0 (Real.pi / 2), Hintegrand u θ) = 0 := by
      rw [← intervalIntegral.integral_of_le hπ.le]
      simpa using hFTC
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume))]
    exact h1
  have hsplit : (∫ θ in Set.Ioo 0 (Real.pi / 2), Hintegrand u θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ) + (∫ θ in Set.Ioo 0 (Real.pi / 2), P2 θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ := by
    have hcongr : (∫ θ in Set.Ioo 0 (Real.pi / 2), Hintegrand u θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ + P2 θ - P3 θ := by
      refine MeasureTheory.setIntegral_congr_fun hI fun θ hθ => ?_
      simp only [Hintegrand, hP1, hP2, hP3, hψ]
      try ring
    rw [hcongr]
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ + P2 θ - P3 θ)
        = (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ + P2 θ)
          - ∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ :=
      MeasureTheory.integral_sub (hP1int.add hP2int) hP3int
    have h3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ + P2 θ)
        = (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ)
          + ∫ θ in Set.Ioo 0 (Real.pi / 2), P2 θ :=
      MeasureTheory.integral_add hP1int hP2int
    linarith [h2, h3]
  have hP3rew : (∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sig θ) := by
    have hcongr : (∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2),
            ((1 - Work.Spaces.eta) / 2)
              * (Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sig θ) := by
      refine MeasureTheory.setIntegral_congr_fun hI fun θ hθ => ?_
      simp only [hP3, hψ]
      try ring
    rw [hcongr, MeasureTheory.integral_const_mul]
  have hP1rew : (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          acoef θ * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ := by
    refine MeasureTheory.setIntegral_congr_fun hI fun θ hθ => ?_
    simp only [hP1, hψ]
  have hP2rew : (∫ θ in Set.Ioo 0 (Real.pi / 2), P2 θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
          * deriv (fun θ' => u θ' / Real.cos θ') θ * deriv (deriv u) θ * sig θ := by
    refine MeasureTheory.setIntegral_congr_fun hI fun θ hθ => ?_
    simp only [hP2, hψ]
  have key : (∫ θ in Set.Ioo 0 (Real.pi / 2), P2 θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ) - (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ) := by
    linarith [hzero, hsplit]
  rw [← hP2rew, key, hP3rew, ← hP1rew]

/-! ## The pointwise-in-`z` inequality -/

theorem slice_le (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hpi : ∀ z, Ψ z (Real.pi / 2) = 0) {z : ℝ} (hz : 0 < z)
    (hM1 : IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hM2 : IPMem Ψ (Work.Spaces.pthIter 2 Ψ))
    (hM3 : IPMem Ψ Ψ)
    (hM4 : IPMem (fun z θ => Ψ z θ / Real.cos θ) (fun z θ => Ψ z θ / Real.cos θ))
    (hM5 : IPMem (fun z θ => Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ)
      (fun z θ => Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ)) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      ≤ (1 - Work.Spaces.eta) * (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ * w2 z * sig θ) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hIooM : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  set u : ℝ → ℝ := fun θ => Ψ z θ with hu
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  have hzu : ContDiffOn ℝ ⊤ u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
    simpa [Function.comp_def, Function.uncurry, hu] using h
  have hzu2 : ContDiffOn ℝ 2 u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hzu.of_le (by norm_num)
  have hu1 : u (Real.pi / 2) = 0 := by simp only [hu]; exact hpi z
  have hA : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hM5.1 z hzI
    have h' : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sig θ * w2 z) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [Work.Spaces.pth, hψ, hu]
      ring
    exact (integrableOn_of_mul_w2 hz measurableSet_Icc h').mono_set Set.Ioo_subset_Icc_self
  have hB : IntegrableOn (fun θ => ψ θ ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hM4.1 z hzI
    have h' : IntegrableOn (fun θ => ψ θ ^ 2 * sig θ * w2 z) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [hψ, hu]
      ring
    exact (integrableOn_of_mul_w2 hz measurableSet_Icc h').mono_set Set.Ioo_subset_Icc_self
  have hN : IntegrableOn (fun θ => Ψ z θ * Ψ z θ * sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hM3.1 z hzI
    have h' : IntegrableOn (fun θ => (Ψ z θ * Ψ z θ * sig θ) * w2 z) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [Pi.sub_apply]
      ring
    exact (integrableOn_of_mul_w2 hz measurableSet_Icc h').mono_set Set.Ioo_subset_Icc_self
  have hC : IntegrableOn (fun θ => Real.sin θ * deriv ψ θ * deriv (deriv u) θ * sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hd : IntegrableOn (fun θ => (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        - Ψ z θ) * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ) Work.Spaces.Iθ := by
      have h := (hM1.1 z hzI).sub (hM2.1 z hzI)
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [Pi.sub_apply]
      ring
    have hd' : IntegrableOn
        (fun θ => (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
          * deriv (deriv u) θ * sig θ) * w2 z) (Set.Ioo 0 (Real.pi / 2)) := by
      refine MeasureTheory.IntegrableOn.congr_fun (hd.mono_set Set.Ioo_subset_Icc_self)
        ?_ hIooM
      intro θ hθ
      have htan := pth_tan_sub Ψ hsm hz hθ
      have hf : Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv u) θ := rfl
      dsimp only
      rw [htan, hf]
      ring
    exact integrableOn_of_mul_w2 hz hIooM hd'
  have hbdd := I4_psi_bounds_alt u hzu2 hu1
  have hident := slice_ident u hzu2 hu1 hbdd hA hB hC
  have htan_all : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ
        = Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ :=
    fun θ hθ => pth_tan_sub Ψ hsm hz hθ
  have step1 :
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
        - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ := by
    rw [← MeasureTheory.integral_sub (hM1.1 z hzI) (hM2.1 z hzI)]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
      simp only [Pi.sub_apply]; ring
  have step2 :
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ := by
    rw [setIntegral_Ioo_Iθ]
  have step3 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ) * w2 z := by
    refine MeasureTheory.setIntegral_congr_fun hIooM ?_
    intro θ hθ
    have hf : Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv u) θ := rfl
    dsimp only
    rw [htan_all θ hθ, hf]
    ring
  have step4 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ) * w2 z)
      = w2 z * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ := by
    rw [MeasureTheory.integral_mul_const, mul_comm]
  have step5 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
            * (Ψ z θ / Real.cos θ) ^ 2 * sig θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
            * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ := by
    simpa [Work.Spaces.pth] using hident
  have hPnn : 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
      * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ := by
    refine MeasureTheory.setIntegral_nonneg hIooM fun θ hθ => ?_
    exact mul_nonneg (mul_nonneg (acoef_nonneg θ) (sq_nonneg _))
      (sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hcos_le : (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
        * (Ψ z θ / Real.cos θ) ^ 2 * sig θ)
      ≤ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hIooM fun θ hθ => ?_
    · have h := integrableOn_continuousOn_mul (g := fun θ => Real.cos (2 * θ)) hB
        (by fun_prop) hIooM fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ hIooM
      intro θ hθ
      first
        | (simp only [hψ, hu]; ring)
        | (simp only [hu]; ring)
        | (simp only [hψ]; ring)
        | ring
    · exact hN.const_mul 2
    · have h1 := cos_two_mul_mul_div_cos_sq_le (a := Ψ z θ) hθ
      have h2 : 0 ≤ sig θ := sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      nlinarith [h3]
  have hE3 : (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ * w2 z * sig θ)
      = w2 z * ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ := by
    rw [← setIntegral_Ioo_Iθ (fun θ => Ψ z θ * Ψ z θ * w2 z * sig θ)]
    have hcongr : (∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * w2 z * sig θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ * Ψ z θ * sig θ) * w2 z :=
      MeasureTheory.setIntegral_congr_fun hIooM fun θ _ => by ring
    rw [hcongr, MeasureTheory.integral_mul_const, mul_comm]
  rw [step1, step2, step3, step4, step5, hE3]
  have hw2nn : 0 ≤ w2 z := w2_nonneg z
  have heta2nn : 0 ≤ (1 - Work.Spaces.eta) / 2 := by linarith [one_sub_eta_pos]
  set B : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2),
      Real.cos (2 * θ) * (Ψ z θ / Real.cos θ) ^ 2 * sig θ with hBdef
  set P : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
      * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ with hPdef
  set N : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ with hNdef
  have hB' : B ≤ 2 * N := by rw [hBdef, hNdef]; exact hcos_le
  have hP' : 0 ≤ P := by rw [hPdef]; exact hPnn
  have e1 : w2 z * ((1 - Work.Spaces.eta) / 2 * B - P)
      ≤ w2 z * ((1 - Work.Spaces.eta) / 2 * B) := by
    apply mul_le_mul_of_nonneg_left _ hw2nn
    linarith [hP']
  have e2 : w2 z * ((1 - Work.Spaces.eta) / 2 * B)
      ≤ w2 z * ((1 - Work.Spaces.eta) / 2 * (2 * N)) := by
    apply mul_le_mul_of_nonneg_left _ hw2nn
    exact mul_le_mul_of_nonneg_left hB' heta2nn
  have e3 : w2 z * ((1 - Work.Spaces.eta) / 2 * (2 * N))
      = (1 - Work.Spaces.eta) * (w2 z * N) := by ring
  linarith [e1, e2, e3]




end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.GbarSin

open Work.Spaces

set_option autoImplicit false

/-- Two functions of the angle which agree on the open interval `(0,π/2)` agree almost
everywhere on `Iθ = [0,π/2]`. -/
private lemma ae_eq_of_eqOn_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ = g θ) :
    f =ᵐ[volume.restrict Iθ] g := by
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hμ]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall (fun x hx => h x hx))

theorem HkMem_congr_Q0 (α : ℝ) (k : ℕ) {u v : ℝ → ℝ → ℝ} (hu : Work.Spaces.HkMem α k u)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), u z θ = v z θ) :
    Work.Spaces.HkMem α k v := by
  obtain ⟨hu1, hu2⟩ := hu
  -- The hypothesis is agreement on the open quadrant.
  have hAg : Work.FTS.EllipticEst.AgreeOnQ u v :=
    fun z θ hz hθ hlt => h z hz θ ⟨hθ, hlt⟩
  -- The integrands agree at every interior point of the quadrant.
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      HkIntegrand α k u z θ = HkIntegrand α k v z θ :=
    Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := k) hAg
  -- Hence the `θ`-slices of the integrands agree a.e. on `Iθ` for every `z > 0`.
  have hae : ∀ z ∈ Set.Ioi (0 : ℝ),
      HkIntegrand α k v z =ᵐ[volume.restrict Iθ] HkIntegrand α k u z :=
    fun z hz => ae_eq_of_eqOn_Ioo (fun θ hθ => (hpt z θ hz hθ.1 hθ.2).symm)
  constructor
  · -- Slicewise integrability of the integrand of `v`.
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      simp only [Work.Coercivity.HkIntegrand_zero_left]
      exact integrableOn_zero
    · exact Integrable.congr (hu1 z hz) (hae z hzpos).symm
  · -- Integrability of the outer integral of `v`, by congruence with `u`.
    have hint : ∀ z ∈ Iz, (∫ θ in Iθ, HkIntegrand α k u z θ)
        = ∫ θ in Iθ, HkIntegrand α k v z θ := by
      intro z hz
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
      · subst hz0
        simp [Work.Coercivity.HkIntegrand_zero_left]
      · exact (integral_congr_ae (hae z hzpos)).symm
    exact IntegrableOn.congr_fun hu2 (fun z hz => hint z hz) measurableSet_Ici

end Work.FTS.EllipticEst.Cert.GbarSin
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.GbarSin.HkIntegrand_GbarSin_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst.GbarSin

set_option autoImplicit false

/-! ## Rewriting the `H^k`-integrand of a separated product -/


/-! ## The target estimate -/


end Work.FTS.EllipticEst.GbarSin
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Smoothness of the singular term `Gsing` and the second-order ODE it solves

`Work.Elliptic.Gsing α F = Gstar α F + Gbar α F` with
`Gstar α F = -(1/(4α)) L₁₂(F)` and
`Gbar α F z = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds`.

The assumptions of the statement feed us the *first derivative* of each of the two
non-elementary ingredients:

* `hL12` gives `∂_z(L₁₂ F)(z) = -3 F_*(z)/z`;
* `hFsm` and `hFint` give, through the fundamental theorem of calculus, the derivative of
  the integral `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds`, namely the integrand.

So both `L₁₂ F` and `J` are *antiderivatives of smooth functions* on the open set
`(0,∞)`, hence smooth to all orders there (`contDiffOn_all_of_forall_hasDerivAt`), and the
same holds for `Gsing`.  The second-order ODE is `Work.Elliptic.Gsing_ode`. -/

/-- **Smoothness of an antiderivative.**  If `f` has derivative `g` at every point of an
open set `s`, and `g` is `C^m` on `s` for every `m` (in particular `C^∞`), then `f` is `C^m`
on `s` for every `m`.

The derivative datum is only available pointwise, so the smoothness of `f` is obtained by
induction on the order: the `C^{m+1}`-criterion on an open set converts
`ContDiffOn ℝ (m+1) f s` into `DifferentiableOn ℝ f s ∧ ContDiffOn ℝ m (deriv f) s`, and
`deriv f` agrees with `g` on `s`. -/
theorem contDiffOn_all_of_forall_hasDerivAt {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasDerivAt f (g x) x) (hg : ∀ m : ℕ, ContDiffOn ℝ m g s) :
    ∀ m : ℕ, ContDiffOn ℝ m f s := by
  have hstep : ∀ m : ℕ, ContDiffOn ℝ (m + 1) f s := by
    intro m
    rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro hm
      exact absurd hm (WithTop.natCast_ne_top m)
    · exact (hg m).congr fun x hx => (hf x hx).deriv
  intro m
  cases m with
  | zero => exact contDiffOn_zero.mpr (hstep 0).continuousOn
  | succ m => exact hstep m

theorem Gsing_contDiffOn_ode_of_Fstar_facts (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi 0))
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (15 / 4) * Work.Elliptic.Fstar F z := by
  -- ## 1. the two derivative data
  -- `F_*` is differentiable at every `z > 0`, with derivative `deriv F_* z`
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- the integral `∫_0^z s^{(5-α)/α} F_*(s) ds` has derivative the integrand
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    intro z hz
    have hzpos : 0 < z := hz
    set p : ℝ := (5 - α) / α with hp
    have hpow : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun s : ℝ => s ^ p) (Set.Ioi 0) :=
      ContDiffOn.rpow_const_of_ne contDiffOn_id (fun x hx => ne_of_gt hx)
    have hker : ContinuousOn (fun s : ℝ => s ^ p * Work.Elliptic.Fstar F s) (Set.Ioi 0) :=
      hpow.continuousOn.mul (hFsm 0).continuousOn
    have hmain : HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ p * Work.Elliptic.Fstar F s)
        (z ^ p * Work.Elliptic.Fstar F z) z := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · -- the integrand is integrable on `(0,z]`, because
        -- `|s^{(5-α)/α} F_*(s)| ≤ z^{5/α} |F_*(s)/s|` there
        rw [intervalIntegrable_iff, Set.uIoc_of_le hzpos.le]
        have hH : IntegrableOn (fun s : ℝ => Work.Elliptic.Fstar F s / s) (Set.Ioc 0 z) :=
          hFint.mono_set fun s hs => hs.1
        refine (hH.norm.const_mul (z ^ (5 / α))).mono' ?_ ?_
        · exact (hker.mono fun s hs => hs.1).aestronglyMeasurable measurableSet_Ioc
        · rw [ae_restrict_iff' measurableSet_Ioc]
          refine Eventually.of_forall fun s hs => ?_
          have hs0 : 0 < s := hs.1
          have hsz : s ≤ z := hs.2
          have hrpow : s ^ (5 / α) ≤ z ^ (5 / α) :=
            Real.rpow_le_rpow hs0.le hsz (by positivity)
          have hp' : p = 5 / α - 1 := by
            rw [hp]
            field_simp
          have hsp : s ^ p = s ^ (5 / α) / s := by
            rw [hp', Real.rpow_sub hs0, Real.rpow_one]
          rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hs0.le p), hsp, norm_div,
            Real.norm_of_nonneg hs0.le]
          rw [show s ^ (5 / α) / s * ‖Work.Elliptic.Fstar F s‖
              = s ^ (5 / α) * (‖Work.Elliptic.Fstar F s‖ / s) by ring]
          exact mul_le_mul_of_nonneg_right hrpow (div_nonneg (norm_nonneg _) hs0.le)
      · exact hker.stronglyMeasurableAtFilter isOpen_Ioi z hz
      · exact hker.continuousAt (isOpen_Ioi.mem_nhds hz)
    simpa only [hp] using hmain
  -- ## 2. smoothness of the two derivative functions
  have hSmL12 : ∀ m : ℕ, ContDiffOn ℝ m (fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
      (Set.Ioi 0) := by
    intro m
    have h3 : ContDiffOn ℝ m (fun z : ℝ => (3 : ℝ) * Work.Elliptic.Fstar F z) (Set.Ioi 0) :=
      contDiffOn_const.mul (hFsm m)
    have hdiv : ContDiffOn ℝ m (fun z : ℝ => (3 : ℝ) * Work.Elliptic.Fstar F z / z)
        (Set.Ioi 0) :=
      h3.div contDiffOn_id fun z hz => ne_of_gt hz
    exact hdiv.neg
  have hL12sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    contDiffOn_all_of_forall_hasDerivAt isOpen_Ioi hL12 hSmL12
  have hSmJ : ∀ m : ℕ,
      ContDiffOn ℝ m (fun z : ℝ => z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z)
        (Set.Ioi 0) := by
    intro m
    have hpow : ContDiffOn ℝ m (fun z : ℝ => z ^ ((5 - α) / α)) (Set.Ioi 0) :=
      ContDiffOn.rpow_const_of_ne contDiffOn_id fun x hx => ne_of_gt hx
    exact hpow.mul (hFsm m)
  have hJfun : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Jfun α F) (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    intro z hz
    change HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z',
      s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z
    exact hJ z hz
  have hJsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Jfun α F) (Set.Ioi 0) := by
    intro m
    change ContDiffOn ℝ m (fun z' => ∫ s in (0 : ℝ)..z',
      s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi 0)
    exact contDiffOn_all_of_forall_hasDerivAt isOpen_Ioi hJ hSmJ m
  -- ## 3. smoothness of the two summands
  have hGstar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    intro m
    have hfun : (Work.Elliptic.Gstar α F)
        = fun z : ℝ => -(1 / (4 * α)) * Work.Elliptic.L12 F z := rfl
    rw [hfun]
    exact (contDiffOn_const (c := -(1 / (4 * α)))).mul (hL12sm m)
  have hAbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Abar α) (Set.Ioi 0) := by
    intro m
    have hfun : (Work.Elliptic.Abar α)
        = fun z : ℝ => -(3 / (4 * α)) * z ^ (-(5 / α)) := rfl
    rw [hfun]
    have hpow : ContDiffOn ℝ m (fun z : ℝ => z ^ (-(5 / α))) (Set.Ioi 0) :=
      ContDiffOn.rpow_const_of_ne contDiffOn_id fun x hx => ne_of_gt hx
    exact (contDiffOn_const (c := -(3 / (4 * α)))).mul hpow
  have hGbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
    intro m
    have hfun : (Work.Elliptic.Gbar α F)
        = fun z : ℝ => (Work.Elliptic.Abar α z * Work.Elliptic.Jfun α F z) := rfl
    rw [hfun]
    exact (hAbar m).mul (hJsm m)
  -- ## 4. assembly
  refine ⟨fun m => ?_, fun z hz => ?_⟩
  · have hfun : (Work.Elliptic.Gsing α F)
        = fun z : ℝ => Work.Elliptic.Gstar α F z + Work.Elliptic.Gbar α F z := rfl
    rw [hfun]
    exact (hGstar m).add (hGbar m)
  · exact Work.Elliptic.Gsing_ode α F hα hL12 hFc hJ z hz

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.LzeroSolSpan =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The Wronskian of two solutions of `y'' = p y' + q y` -/





/-! ## `ContDiffOn ℝ 2` supplies the two derivative facts needed at each point -/

theorem hasDerivAt_of_contDiffOn {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) :
    (∀ x ∈ s, HasDerivAt f (deriv f x) x) ∧
      (∀ x ∈ s, HasDerivAt (deriv f) (deriv (deriv f) x) x) := by
  constructor
  · intro x hx
    have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt (hs.mem_nhds hx)
    exact ((h2.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).differentiableAt
      (show (1 : WithTop ℕ∞) ≠ 0 by norm_num)).hasDerivAt
  · intro x hx
    have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt (hs.mem_nhds hx)
    exact ((h2.derivWithin (m := 1) (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
      (show (1 : WithTop ℕ∞) ≠ 0 by norm_num)).hasDerivAt

/-! ## The two special solutions of `Lzero1 u = -u'' + (tan θ · u)' - 6u = 0` -/

private theorem deriv_sin_two (t : ℝ) :
    deriv (fun x : ℝ => Real.sin (2 * x)) t = 2 * Real.cos (2 * t) := by
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul 2
  have h : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * t) * 2) t := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_sin (2 * t)).comp t h2
  rw [h.deriv, mul_comm]









end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Gap9Open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-!
## `Gap9Open`: the constrained slice Poincaré inequality for `C²`-in-the-open functions

The target statement (`Work.FTS.EllipticEst.Honest.Gap9Open`) is

`9 ∫_{Iθ} f² ≤ ∫_{Iθ} (f')²`

for `f : ℝ → ℝ` which is `C²` on the *open* interval `(0,π/2)`, continuous on `[0,π/2]`,
vanishes at both endpoints, with `(f')²` integrable on `[0,π/2]` and `∫_{Iθ} f · sinθcos²θ = 0`.

The proof goes by *squeezing*: `θ ↦ δ + c(δ)·θ` maps `[0,π/2]` onto `[δ, π/2-δ]` with
`c(δ) = 1 - 2δ/(π/2)`, and for small `δ` the function

`g_δ(θ) = f(δ + c(δ)θ) - (f(δ) + ((f(π/2-δ) - f(δ))/(π/2))·θ)`

is `C²` on the *closed* interval (its arguments stay in the compact `[δ, π/2-δ] ⊂ (0,π/2)`),
vanishes at both endpoints, and converges to `f` in `L¹(Iθ)` as `δ → 0`.  Correcting the
second moment by a multiple of `sin 2θ` makes it satisfy the solvability condition, so the
already-proved strong version `Work.FTS.EllipticEst.P9.slicePoincare9_fts` applies.  The
estimates are the exact dilation identity
`∫ (f(δ+cθ)')² = c ∫_δ^{π/2-δ} (f')² - (f(π/2-δ) - f(δ))²/(π/2) ≤ ∫ (f')²`,
the two `L¹` bounds following from `|g_δ| ≤ 4M` (`M` a bound for `|f|`), and the limit
`∫ |g_δ - f| → 0` supplied by dominated convergence.
-/

/-! ### The squeeze parameters -/

/-- `δ n = 1/(n+2)`, the squeezing parameter. -/
def gapDelta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

/-- The dilation factor `c(δ) = 1 - 2δ/(π/2)`: the map `θ ↦ δ + c(δ)θ` sends `[0,π/2]`
onto `[δ, π/2 - δ]`. -/
def gapDC (δ : ℝ) : ℝ := 1 - 2 * δ / (Real.pi / 2)

/-- `Δ(δ) = f(π/2 - δ) - f δ`. -/
def gapDD (f : ℝ → ℝ) (δ : ℝ) : ℝ := f (Real.pi / 2 - δ) - f δ

/-- `c n = c(δ n)`. -/
def gapC (n : ℕ) : ℝ := gapDC (gapDelta n)

/-- `Δ n = Δ(δ n)`. -/
def gapD (f : ℝ → ℝ) (n : ℕ) : ℝ := gapDD f (gapDelta n)

/-- The affine correction `m_n(θ) = f(δ n) + (Δ n/(π/2))·θ`. -/
def gapM (f : ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ := f (gapDelta n) + gapD f n / (Real.pi / 2) * θ

/-- The squeezed function `g_n(θ) = f(δ n + c n·θ) - m_n(θ)`. -/
def gapG (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun θ => f (gapDelta n + gapC n * θ) - gapM f n θ

/-- The coefficient of the correction making the second moment vanish:
`a_n = (15/4) ∫_{Iθ} g_n θ · sinθcos²θ`. -/
def gapA (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (15 / 4) * ∫ θ in Work.Spaces.Iθ, gapG f n θ * Work.Elliptic.sinCos2 θ

/-- The corrected function `F_n = g_n - a_n · sin 2θ`, which satisfies all hypotheses of the
strong slice Poincaré inequality. -/
def gapF (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun θ => gapG f n θ - gapA f n * Real.sin (2 * θ)

/-! ### Elementary facts about the parameters -/

section Basic

variable {f : ℝ → ℝ}

theorem gapDelta_pos (n : ℕ) : 0 < gapDelta n := by
  unfold gapDelta; positivity

theorem gapDelta_nonneg (n : ℕ) : 0 ≤ gapDelta n := (gapDelta_pos n).le

theorem gapDelta_le_half' (n : ℕ) : gapDelta n ≤ 1 / 2 := by
  unfold gapDelta
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)


/-- `δ n ≤ π/4 = (π/2)/2`. -/
theorem gapDelta_le_half (n : ℕ) : gapDelta n ≤ Real.pi / 4 := by
  have h1 := gapDelta_le_half' n
  have h2 : (1 : ℝ) / 2 ≤ Real.pi / 4 := by nlinarith [Real.pi_gt_three]
  linarith

theorem tendsto_gapDelta : Tendsto gapDelta atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have hg : gapDelta = fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) := rfl
  rw [hg]
  exact h2

theorem eventually_gapDelta_lt_eighth : ∀ᶠ n in atTop, gapDelta n < Real.pi / 8 := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  have h1 : gapDelta n ≤ 1 / 5 := by
    unfold gapDelta
    refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
    have hn' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : (1 : ℝ) / 5 < Real.pi / 8 := by nlinarith [Real.pi_gt_three]
  linarith

theorem gapC_mul_pi (n : ℕ) : gapC n * (Real.pi / 2) = Real.pi / 2 - 2 * gapDelta n := by
  unfold gapC gapDC
  field_simp

theorem gapC_nonneg (n : ℕ) : 0 ≤ gapC n := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  have h1 : 2 * gapDelta n / (Real.pi / 2) ≤ 1 := by
    rw [div_le_one hL]; linarith [gapDelta_le_half n]
  unfold gapC gapDC
  linarith

theorem gapC_le_one (n : ℕ) : gapC n ≤ 1 := by
  have h1 : 0 ≤ 2 * gapDelta n / (Real.pi / 2) :=
    div_nonneg (by linarith [gapDelta_nonneg n]) (by positivity)
  unfold gapC gapDC
  linarith

theorem gapC_pos {n : ℕ} (h : gapDelta n < Real.pi / 8) : 0 < gapC n := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  have h1 : 2 * gapDelta n / (Real.pi / 2) < 1 := by
    rw [div_lt_one hL]; linarith
  unfold gapC gapDC
  linarith

/-- The squeeze map sends `Iθ` into `Iθ`. -/
theorem gap_shift_mem_Icc (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    gapDelta n + gapC n * θ ∈ Set.Icc 0 (Real.pi / 2) := by
  have hc0 := gapC_nonneg n
  have hcl := gapC_mul_pi n
  have h1 : gapDelta n ≤ Real.pi / 2 := by linarith [gapDelta_le_half n, Real.pi_pos]
  constructor
  · have h2 : 0 ≤ gapC n * θ := mul_nonneg hc0 hθ.1
    linarith [gapDelta_nonneg n]
  · have h2 : gapC n * θ ≤ gapC n * (Real.pi / 2) := mul_le_mul_of_nonneg_left hθ.2 hc0
    have h3 : (0:ℝ) < gapDelta n := gapDelta_pos n
    linarith [hcl ▸ h2]

/-- For `δ < π/8` the squeeze map sends `Iθ` into the *open* interval. -/
theorem gap_shift_mem_Ioo {n : ℕ} (h : gapDelta n < Real.pi / 8) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    gapDelta n + gapC n * θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hc0 := (gapC_pos h).le
  have hcl := gapC_mul_pi n
  have hδ := gapDelta_pos n
  constructor
  · have h2 : 0 ≤ gapC n * θ := mul_nonneg hc0 hθ.1
    linarith
  · have h2 : gapC n * θ ≤ gapC n * (Real.pi / 2) := mul_le_mul_of_nonneg_left hθ.2 hc0
    have h3 : gapDelta n < Real.pi / 2 := by linarith [Real.pi_pos]
    linarith [hcl ▸ h2]

end Basic

/-! ### Smoothness of the squeezed family -/

section Smooth

variable {f : ℝ → ℝ}

theorem gapG_contDiffOn (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    ContDiffOn ℝ 2 (gapG f n) (Set.Icc 0 (Real.pi / 2)) := by
  have hmap : MapsTo (fun θ : ℝ => gapDelta n + gapC n * θ) (Set.Icc 0 (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => gap_shift_mem_Ioo h hθ
  have hcomp : ContDiffOn ℝ 2 (fun θ : ℝ => f (gapDelta n + gapC n * θ))
      (Set.Icc 0 (Real.pi / 2)) := ContDiffOn.comp hf2 (by fun_prop) hmap
  have haff : ContDiffOn ℝ 2 (gapM f n) (Set.Icc 0 (Real.pi / 2)) := by
    unfold gapM; fun_prop
  exact (hcomp.sub haff).congr (fun θ _ => rfl)

theorem gapF_contDiffOn (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    ContDiffOn ℝ 2 (gapF f n) (Set.Icc 0 (Real.pi / 2)) := by
  have hG := gapG_contDiffOn hf2 h
  have hsin : ContDiffOn ℝ 2 (fun θ : ℝ => gapA f n * Real.sin (2 * θ))
      (Set.Icc 0 (Real.pi / 2)) := by fun_prop
  exact (hG.sub hsin).congr (fun θ _ => rfl)

theorem gapG_zero (n : ℕ) : gapG f n 0 = 0 := by
  simp [gapG, gapM]

theorem gapG_pi (n : ℕ) : gapG f n (Real.pi / 2) = 0 := by
  have hcl := gapC_mul_pi n
  have h1 : gapDelta n + gapC n * (Real.pi / 2) = Real.pi / 2 - gapDelta n := by linarith
  have h2 : gapM f n (Real.pi / 2) = f (Real.pi / 2 - gapDelta n) := by
    unfold gapM gapD gapDD
    rw [div_mul_cancel₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
    ring
  simp only [gapG, h1, h2]
  ring

theorem gapF_zero (n : ℕ) : gapF f n 0 = 0 := by
  simp [gapF, gapG_zero]

theorem gapF_pi (n : ℕ) : gapF f n (Real.pi / 2) = 0 := by
  have h2 : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  simp [gapF, gapG_pi, h2]

end Smooth

/-! ### The derivative of the squeezed family on the open interval -/

section Deriv

variable {f : ℝ → ℝ}

theorem deriv_gapG (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (gapG f n) θ
      = gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2) := by
  have hx : gapDelta n + gapC n * θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    gap_shift_mem_Ioo h ⟨hθ.1.le, hθ.2.le⟩
  have h2 : HasDerivAt f (deriv f (gapDelta n + gapC n * θ)) (gapDelta n + gapC n * θ) :=
    ((hf2.contDiffAt (Ioo_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num)).hasDerivAt
  have h1 : HasDerivAt (fun θ : ℝ => gapDelta n + gapC n * θ) (gapC n) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (gapC n)).const_add (gapDelta n)
  have h3 : HasDerivAt (fun θ : ℝ => f (gapDelta n + gapC n * θ))
      (gapC n * deriv f (gapDelta n + gapC n * θ)) θ := by
    have h3' := (h2.comp θ h1).congr_deriv (by rw [mul_comm])
    simpa [Function.comp_def] using h3'
  have h4 : HasDerivAt (gapM f n) (gapD f n / (Real.pi / 2)) θ := by
    have hmm : gapM f n
        = fun y : ℝ => f (gapDelta n) + (gapD f n / (Real.pi / 2)) * y := rfl
    rw [hmm]
    have hb : HasDerivAt (fun y : ℝ => (gapD f n / (Real.pi / 2)) * y)
        (gapD f n / (Real.pi / 2)) θ := by
      simpa using (hasDerivAt_id θ).const_mul (gapD f n / (Real.pi / 2))
    exact hb.const_add (f (gapDelta n))
  have h5 : HasDerivAt (gapG f n)
      (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) θ := by
    have hmm : gapG f n
        = fun y : ℝ => f (gapDelta n + gapC n * y) - gapM f n y := rfl
    rw [hmm]
    exact h3.sub h4
  exact h5.deriv

theorem deriv_gapF (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (gapF f n) θ = deriv (gapG f n) θ - gapA f n * (2 * Real.cos (2 * θ)) := by
  have hx : gapDelta n + gapC n * θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    gap_shift_mem_Ioo h ⟨hθ.1.le, hθ.2.le⟩
  have h2 : HasDerivAt f (deriv f (gapDelta n + gapC n * θ)) (gapDelta n + gapC n * θ) :=
    ((hf2.contDiffAt (Ioo_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num)).hasDerivAt
  have h1 : HasDerivAt (fun θ : ℝ => gapDelta n + gapC n * θ) (gapC n) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (gapC n)).const_add (gapDelta n)
  have hG : HasDerivAt (gapG f n)
      (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) θ := by
    have h3 : HasDerivAt (fun θ : ℝ => f (gapDelta n + gapC n * θ))
        (gapC n * deriv f (gapDelta n + gapC n * θ)) θ := by
      have h3' := (h2.comp θ h1).congr_deriv (by rw [mul_comm])
      simpa [Function.comp_def] using h3'
    have h4 : HasDerivAt (gapM f n) (gapD f n / (Real.pi / 2)) θ := by
      have hmm : gapM f n
          = fun y : ℝ => f (gapDelta n) + (gapD f n / (Real.pi / 2)) * y := rfl
      rw [hmm]
      have hb : HasDerivAt (fun y : ℝ => (gapD f n / (Real.pi / 2)) * y)
          (gapD f n / (Real.pi / 2)) θ := by
        simpa using (hasDerivAt_id θ).const_mul (gapD f n / (Real.pi / 2))
      exact hb.const_add (f (gapDelta n))
    have hmm : gapG f n
        = fun y : ℝ => f (gapDelta n + gapC n * y) - gapM f n y := rfl
    rw [hmm]
    exact h3.sub h4
  have hsin : HasDerivAt (fun θ : ℝ => gapA f n * Real.sin (2 * θ))
      (gapA f n * (2 * Real.cos (2 * θ))) θ := by
    have hinner : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have hs : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ hinner
    exact (hs.const_mul (gapA f n)).congr_deriv (by ring)
  have hmain : HasDerivAt (gapF f n)
      (deriv (gapG f n) θ - gapA f n * (2 * Real.cos (2 * θ))) θ := by
    have hmm : gapF f n
        = fun y : ℝ => gapG f n y - gapA f n * Real.sin (2 * y) := rfl
    rw [hmm]
    have hG' : HasDerivAt (gapG f n) (deriv (gapG f n) θ) θ :=
      hG.differentiableAt.hasDerivAt
    exact hG'.sub hsin
  exact hmain.deriv

end Deriv

/-! ### Bounds on the squeezed family -/

section Bounds

variable {f : ℝ → ℝ}

theorem gapM_bound {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M) (hMnn : 0 ≤ M)
    (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : |gapM f n θ| ≤ 3 * M := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  have h1 : |f (gapDelta n)| ≤ M := hM _ (Set.mem_Icc.mpr ⟨gapDelta_nonneg n, by
    linarith [gapDelta_le_half n, Real.pi_pos]⟩)
  have h2 : |f (Real.pi / 2 - gapDelta n)| ≤ M := hM _ (Set.mem_Icc.mpr ⟨by
    linarith [gapDelta_le_half n, Real.pi_pos], by linarith [gapDelta_nonneg n]⟩)
  have h3 : |gapD f n| ≤ 2 * M := by
    have hgd : gapD f n = f (Real.pi / 2 - gapDelta n) - f (gapDelta n) := rfl
    rw [hgd]
    calc |f (Real.pi / 2 - gapDelta n) - f (gapDelta n)|
        ≤ |f (Real.pi / 2 - gapDelta n)| + |f (gapDelta n)| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have h4 : |gapD f n / (Real.pi / 2) * θ| ≤ 2 * M := by
    rw [abs_mul, abs_div, abs_of_pos hL]
    have hθ' : |θ| ≤ Real.pi / 2 := by
      rw [abs_of_nonneg hθ.1]; exact hθ.2
    have h5 : |gapD f n| / (Real.pi / 2) * |θ| ≤ (2 * M) / (Real.pi / 2) * (Real.pi / 2) :=
      mul_le_mul (div_le_div_of_nonneg_right h3 hL.le) hθ' (abs_nonneg _) (by positivity)
    calc |gapD f n| / (Real.pi / 2) * |θ| ≤ (2 * M) / (Real.pi / 2) * (Real.pi / 2) := h5
      _ = 2 * M := by field_simp
  have hmain : |gapM f n θ| ≤ |f (gapDelta n)| + |gapD f n / (Real.pi / 2) * θ| := by
    unfold gapM
    exact abs_add_le _ _
  linarith

theorem gapG_bound {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M) (hMnn : 0 ≤ M)
    (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : |gapG f n θ| ≤ 4 * M := by
  have h1 : |f (gapDelta n + gapC n * θ)| ≤ M := hM _ (gap_shift_mem_Icc n hθ)
  have h2 := gapM_bound hM hMnn n hθ
  have hgg : gapG f n θ = f (gapDelta n + gapC n * θ) - gapM f n θ := rfl
  rw [hgg]
  calc |f (gapDelta n + gapC n * θ) - gapM f n θ|
      ≤ |f (gapDelta n + gapC n * θ)| + |gapM f n θ| := abs_sub _ _
    _ ≤ 4 * M := by linarith

theorem gapG_sub_f_bound {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M)
    (hMnn : 0 ≤ M) (n : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    |gapG f n θ - f θ| ≤ 5 * M := by
  have h1 := gapG_bound hM hMnn n hθ
  have h2 : |f θ| ≤ M := hM θ hθ
  calc |gapG f n θ - f θ| ≤ |gapG f n θ| + |f θ| := abs_sub _ _
    _ ≤ 5 * M := by linarith


end Bounds

/-! ### Continuity and integrability of the squeezed family -/

section ContInt

variable {f : ℝ → ℝ}

theorem continuousOn_gapG (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (n : ℕ) :
    ContinuousOn (gapG f n) (Set.Icc 0 (Real.pi / 2)) := by
  have hshift : Continuous (fun θ : ℝ => gapDelta n + gapC n * θ) := by fun_prop
  have h1 : ContinuousOn ((f) ∘ fun θ : ℝ => gapDelta n + gapC n * θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    ContinuousOn.comp hcont hshift.continuousOn (fun θ hθ => gap_shift_mem_Icc n hθ)
  have h1' : ContinuousOn (fun θ : ℝ => f (gapDelta n + gapC n * θ))
      (Set.Icc 0 (Real.pi / 2)) := by
    simpa only [Function.comp_def] using h1
  have h2 : ContinuousOn (gapM f n) (Set.Icc 0 (Real.pi / 2)) := by
    unfold gapM; fun_prop
  have h3 := h1'.sub h2
  have hgg : gapG f n = fun θ : ℝ => f (gapDelta n + gapC n * θ) - gapM f n θ := rfl
  rw [hgg]
  exact h3

theorem continuousOn_gapF (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (n : ℕ) :
    ContinuousOn (gapF f n) (Set.Icc 0 (Real.pi / 2)) := by
  have h1 := continuousOn_gapG hcont n
  have h2 : ContinuousOn (fun θ : ℝ => gapA f n * Real.sin (2 * θ))
      (Set.Icc 0 (Real.pi / 2)) := by fun_prop
  have h3 := h1.sub h2
  have hgg : gapF f n = fun θ : ℝ => gapG f n θ - gapA f n * Real.sin (2 * θ) := rfl
  rw [hgg]
  exact h3

theorem continuousOn_deriv_comp (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    ContinuousOn (fun θ : ℝ => deriv f (gapDelta n + gapC n * θ)) (Set.Icc 0 (Real.pi / 2)) := by
  have hderiv : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hshift : Continuous (fun θ : ℝ => gapDelta n + gapC n * θ) := by fun_prop
  have h1 : ContinuousOn ((deriv f) ∘ fun θ : ℝ => gapDelta n + gapC n * θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    ContinuousOn.comp hderiv hshift.continuousOn (fun θ hθ => gap_shift_mem_Ioo h hθ)
  simpa only [Function.comp_def] using h1

theorem integrableOn_deriv_comp_sq (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    IntegrableOn (fun θ : ℝ => (deriv f (gapDelta n + gapC n * θ)) ^ 2) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn ((continuousOn_deriv_comp hf2 h).pow 2)

theorem integrableOn_deriv_comp (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    IntegrableOn (fun θ : ℝ => deriv f (gapDelta n + gapC n * θ)) Work.Spaces.Iθ := by
  have hsq := integrableOn_deriv_comp_sq hf2 h
  have hmaj : IntegrableOn
      (fun θ : ℝ => (1 / 2) * ((deriv f (gapDelta n + gapC n * θ)) ^ 2 + 1))
      Work.Spaces.Iθ := by
    have h1 : IntegrableOn
        (fun θ : ℝ => (deriv f (gapDelta n + gapC n * θ)) ^ 2 + 1) Work.Spaces.Iθ :=
      hsq.add (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
    exact h1.const_mul (1 / 2)
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact (continuousOn_deriv_comp hf2 h).aestronglyMeasurable measurableSet_Icc
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
    rw [Real.norm_eq_abs]
    have hsq_abs : |deriv f (gapDelta n + gapC n * θ)| ^ 2
        = deriv f (gapDelta n + gapC n * θ) ^ 2 := sq_abs _
    have hnn := sq_nonneg (|deriv f (gapDelta n + gapC n * θ)| - 1)
    nlinarith [abs_nonneg (deriv f (gapDelta n + gapC n * θ))]

theorem integrableOn_An_sq (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    IntegrableOn
      (fun θ : ℝ => (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) ^ 2)
      Work.Spaces.Iθ := by
  have hx := integrableOn_deriv_comp hf2 h
  have hx2 := integrableOn_deriv_comp_sq hf2 h
  have h1 : IntegrableOn
      (fun θ : ℝ => gapC n ^ 2 * (deriv f (gapDelta n + gapC n * θ)) ^ 2
        - (2 * gapC n * (gapD f n / (Real.pi / 2))) * deriv f (gapDelta n + gapC n * θ)
        + (gapD f n / (Real.pi / 2)) ^ 2) Work.Spaces.Iθ :=
    ((hx2.const_mul (gapC n ^ 2)).sub (hx.const_mul (2 * gapC n * (gapD f n / (Real.pi / 2))))).add
      (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
  refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
  ring

end ContInt

/-! ### The dilation identity -/

section Dilation

variable {f : ℝ → ℝ}

theorem gap_integral_An_eq (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    (∫ θ in Work.Spaces.Iθ,
        (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) ^ 2)
      = gapC n * (∫ u in (gapDelta n)..(Real.pi / 2 - gapDelta n), (deriv f u) ^ 2)
        - (gapD f n) ^ 2 / (Real.pi / 2) := by
  set L : ℝ := Real.pi / 2 with hL
  set δ : ℝ := gapDelta n with hδ
  set c : ℝ := gapC n with hc
  set Δ : ℝ := gapD f n with hΔ
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hδpos : 0 < δ := by rw [hδ]; exact gapDelta_pos n
  have hδ4 : δ < L / 4 := by rw [hδ, hL]; linarith [h]
  have hclt : δ < L - δ := by linarith
  have hcne : c ≠ 0 := by
    have := gapC_pos h
    rw [hc]
    exact ne_of_gt this
  have hcL : c * L = L - 2 * δ := by
    rw [hc, hL, hδ]
    exact gapC_mul_pi n
  have hb : δ + c * L = L - δ := by linarith
  -- substitution
  have key : (∫ x in (0 : ℝ)..L, (fun u => (c * deriv f u - Δ / L) ^ 2) (δ + c * x))
      = c⁻¹ * ∫ x in δ..(L - δ), (c * deriv f x - Δ / L) ^ 2 := by
    rw [intervalIntegral.integral_comp_add_mul (fun u => (c * deriv f u - Δ / L) ^ 2) hcne δ]
    simp only [smul_eq_mul]
    rw [show δ + c * 0 = δ by ring, hb]
  have hlink : (∫ θ in Work.Spaces.Iθ,
        (c * deriv f (δ + c * θ) - Δ / L) ^ 2)
      = ∫ x in (0 : ℝ)..L, (fun u => (c * deriv f u - Δ / L) ^ 2) (δ + c * x) := by
    rw [Work.FTS.EllipticEst.P9.Iθ_eq_interval]
  -- the derivative is continuous on the compact subinterval
  have hderiv : ContinuousOn (deriv f) (Set.Ioo 0 L) := by
    rw [hL]
    exact hf2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdc : ContinuousOn (deriv f) (Set.uIcc δ (L - δ)) := by
    refine hderiv.mono ?_
    intro x hx
    rw [Set.uIcc_of_le hclt.le, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1, hδpos], by linarith [hx.2, hδ4, hLpos]⟩
  have hi1 : IntervalIntegrable (fun x : ℝ => (deriv f x) ^ 2) volume δ (L - δ) :=
    (hdc.pow 2).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x : ℝ => deriv f x) volume δ (L - δ) :=
    hdc.intervalIntegrable
  have hiA : IntervalIntegrable
      (fun x : ℝ => c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x) volume δ (L - δ) :=
    (hi1.const_mul (c ^ 2)).sub (hi2.const_mul (2 * c * (Δ / L)))
  have hiB : IntervalIntegrable (fun x : ℝ => (Δ / L) ^ 2) volume δ (L - δ) :=
    intervalIntegrable_const
  have hcongr : (∫ x in δ..(L - δ), (c * deriv f x - Δ / L) ^ 2)
      = ∫ x in δ..(L - δ),
          (c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x + (Δ / L) ^ 2) :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  have hsplit1 : (∫ x in δ..(L - δ),
          (c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x + (Δ / L) ^ 2))
      = (∫ x in δ..(L - δ), (c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x))
        + (∫ x in δ..(L - δ), ((Δ / L) ^ 2)) :=
    intervalIntegral.integral_add hiA hiB
  have hsplit2 : (∫ x in δ..(L - δ), (c ^ 2 * (deriv f x) ^ 2 - 2 * c * (Δ / L) * deriv f x))
      = (∫ x in δ..(L - δ), c ^ 2 * (deriv f x) ^ 2)
        - (∫ x in δ..(L - δ), 2 * c * (Δ / L) * deriv f x) :=
    intervalIntegral.integral_sub (hi1.const_mul (c ^ 2)) (hi2.const_mul (2 * c * (Δ / L)))
  have hsplit3 : (∫ x in δ..(L - δ), c ^ 2 * (deriv f x) ^ 2)
      = c ^ 2 * (∫ x in δ..(L - δ), (deriv f x) ^ 2) :=
    intervalIntegral.integral_const_mul (c ^ 2) _
  have hsplit4 : (∫ x in δ..(L - δ), 2 * c * (Δ / L) * deriv f x)
      = (2 * c * (Δ / L)) * (∫ x in δ..(L - δ), deriv f x) :=
    intervalIntegral.integral_const_mul (2 * c * (Δ / L)) _
  have hsplit5 : (∫ x in δ..(L - δ), ((Δ / L) ^ 2)) = (L - δ - δ) * ((Δ / L) ^ 2) := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hftc : (∫ x in δ..(L - δ), deriv f x) = Δ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := f) (f' := deriv f) ?_ hi2]
    · rw [hΔ]
      rfl
    · intro x hx
      rw [Set.uIcc_of_le hclt.le, Set.mem_Icc] at hx
      have hx' : x ∈ Set.Ioo 0 L := ⟨by linarith [hx.1, hδpos], by linarith [hx.2, hδ4, hLpos]⟩
      exact ((hf2.contDiffAt (by rw [hL]; exact Ioo_mem_nhds hx'.1 hx'.2)).differentiableAt
        (by norm_num)).hasDerivAt
  rw [hlink, key, hcongr, hsplit1, hsplit2, hsplit3, hsplit4, hsplit5, hftc]
  rw [show L - δ - δ = c * L by linarith]
  field_simp
  ring

theorem gap_integral_An_le (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) Work.Spaces.Iθ) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    (∫ θ in Work.Spaces.Iθ,
        (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2)) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  rw [gap_integral_An_eq hf2 h]
  set L : ℝ := Real.pi / 2 with hL
  set δ : ℝ := gapDelta n with hδ
  set c : ℝ := gapC n with hc
  set I : ℝ := ∫ x in δ..(L - δ), (deriv f x) ^ 2 with hI
  have hLpos : 0 < L := by rw [hL]; positivity
  have hδ4 : δ < L / 4 := by rw [hδ, hL]; linarith [h]
  have hδpos : 0 < δ := by rw [hδ]; exact gapDelta_pos n
  have hclt : δ < L - δ := by linarith
  have hc0 : 0 ≤ c := by rw [hc]; exact gapC_nonneg n
  have hc1 : c ≤ 1 := by rw [hc]; exact gapC_le_one n
  have hInn : 0 ≤ I := by rw [hI]; exact intervalIntegral.integral_nonneg hclt.le (fun x _ => sq_nonneg _)
  have hle1 : I ≤ ∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 := by
    rw [hI, intervalIntegral.integral_of_le hclt.le,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · exact ae_restrict_of_forall_mem measurableSet_Icc (fun x _ => sq_nonneg _)
    · refine Filter.Eventually.of_forall (fun x hx => ?_)
      have hx' : δ ≤ x ∧ x ≤ L - δ := hx
      obtain ⟨hx1, hx2⟩ := hx'
      change x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
      rw [Set.mem_Icc]
      exact ⟨by linarith, by linarith [hL]⟩
  have hb1 : c * I ≤ I := by
    have := mul_le_mul_of_nonneg_right hc1 hInn
    simpa using this
  have hb2 : c * I - (gapD f n) ^ 2 / L ≤ c * I := by
    have : 0 ≤ (gapD f n) ^ 2 / L := div_nonneg (sq_nonneg _) hLpos.le
    linarith
  linarith

end Dilation

/-! ### The `L¹` limit of the squeezed family -/

section Limits

variable {f : ℝ → ℝ}

theorem tendsto_gapC_tendsto_one : Tendsto gapC atTop (𝓝 1) := by
  have h2 : Tendsto (fun n : ℕ => 2 * gapDelta n / (Real.pi / 2)) atTop (𝓝 0) := by
    have := (tendsto_gapDelta.const_mul 2).div_const (Real.pi / 2)
    simpa using this
  have h3 : Tendsto (fun n : ℕ => 1 - 2 * gapDelta n / (Real.pi / 2)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h2
  have hgc : gapC = fun n : ℕ => 1 - 2 * gapDelta n / (Real.pi / 2) := rfl
  rw [hgc]
  simpa using h3

theorem tendsto_gapDelta_right :
    Tendsto (fun n : ℕ => Real.pi / 2 - gapDelta n) atTop (𝓝 (Real.pi / 2)) := by
  have h := (tendsto_const_nhds (x := Real.pi / 2) (f := atTop (α := ℕ))).sub tendsto_gapDelta
  simpa using h

theorem tendsto_f_gapDelta_left (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) :
    Tendsto (fun n : ℕ => f (gapDelta n)) atTop (𝓝 (f 0)) := by
  have hmem : ∀ᶠ n in atTop, gapDelta n ∈ Set.Icc 0 (Real.pi / 2) :=
    Filter.Eventually.of_forall (fun n => Set.mem_Icc.mpr ⟨gapDelta_nonneg n, by
      linarith [gapDelta_le_half n, Real.pi_pos]⟩)
  have ht : Tendsto gapDelta atTop (𝓝[Set.Icc 0 (Real.pi / 2)] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_gapDelta, hmem⟩
  have hcw : Tendsto f (𝓝[Set.Icc 0 (Real.pi / 2)] 0) (𝓝 (f 0)) :=
    hcont.continuousWithinAt (Set.left_mem_Icc.mpr (by positivity))
  simpa only [Function.comp_def] using hcw.comp ht

theorem tendsto_f_gapDelta_right (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) :
    Tendsto (fun n : ℕ => f (Real.pi / 2 - gapDelta n)) atTop (𝓝 (f (Real.pi / 2))) := by
  have hmem : ∀ᶠ n in atTop, Real.pi / 2 - gapDelta n ∈ Set.Icc 0 (Real.pi / 2) :=
    Filter.Eventually.of_forall (fun n => Set.mem_Icc.mpr ⟨by
      linarith [gapDelta_le_half n, Real.pi_pos], by linarith [gapDelta_nonneg n]⟩)
  have ht : Tendsto (fun n : ℕ => Real.pi / 2 - gapDelta n) atTop
      (𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_gapDelta_right, hmem⟩
  have hcw : Tendsto f (𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2)) (𝓝 (f (Real.pi / 2))) :=
    hcont.continuousWithinAt (Set.right_mem_Icc.mpr (by positivity))
  simpa only [Function.comp_def] using hcw.comp ht

theorem tendsto_gapG_sub (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0)
    (hπ : f (Real.pi / 2) = 0) :
    Tendsto (fun n : ℕ => ∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|) atTop (𝓝 0) := by
  obtain ⟨M₀, hM₀⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  set M : ℝ := max M₀ 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMb : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M := by
    intro θ hθ
    have h := hM₀ θ hθ
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hleft := tendsto_f_gapDelta_left hcont
  have hright := tendsto_f_gapDelta_right hcont
  have hD : Tendsto (fun n : ℕ => gapD f n) atTop (𝓝 0) := by
    have h3 := hright.sub hleft
    have h3' : Tendsto (fun n : ℕ => gapD f n) atTop (𝓝 (f (Real.pi / 2) - f 0)) := by
      have hfun : (fun n : ℕ => gapD f n)
          = fun n : ℕ => f (Real.pi / 2 - gapDelta n) - f (gapDelta n) := rfl
      rw [hfun]
      exact h3
    simpa [h0, hπ] using h3' 
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun θ : ℝ => |gapG f n θ - f θ|)
      (volume.restrict Work.Spaces.Iθ) := fun n =>
    ((continuousOn_gapG hcont n).sub hcont).abs.aestronglyMeasurable measurableSet_Icc
  have hintb : Integrable (fun _ : ℝ => 5 * M) (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const
  have hbnd : ∀ n : ℕ, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖|gapG f n θ - f θ|‖ ≤ 5 * M := by
    intro n
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact gapG_sub_f_bound hMb hMnn n hθ
  have hlim : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Tendsto (fun n : ℕ => |gapG f n θ - f θ|) atTop (𝓝 0) := by
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rcases eq_or_lt_of_le hθ.1 with hzero | hpos
    · have : (fun n : ℕ => |gapG f n θ - f θ|) = fun _ => (0 : ℝ) := by
        funext n
        rw [← hzero, gapG_zero n, h0, sub_zero, abs_zero]
      rw [this]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le hθ.2 with hpi | hlt
    · have : (fun n : ℕ => |gapG f n θ - f θ|) = fun _ => (0 : ℝ) := by
        funext n
        rw [hpi, gapG_pi n, hπ, sub_zero, abs_zero]
      rw [this]
      exact tendsto_const_nhds
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpos, hlt⟩
    have harg : Tendsto (fun n : ℕ => gapDelta n + gapC n * θ) atTop (𝓝 θ) := by
      have := tendsto_gapDelta.add (tendsto_gapC_tendsto_one.mul_const θ)
      simpa using this
    have hcf : Tendsto (fun n : ℕ => f (gapDelta n + gapC n * θ)) atTop (𝓝 (f θ)) :=
      (hcont.continuousAt (Icc_mem_nhds hθ'.1 hθ'.2)).tendsto.comp harg
    have hgM : Tendsto (fun n : ℕ => gapM f n θ) atTop (𝓝 0) := by
      have h4 : Tendsto (fun n : ℕ => f (gapDelta n) + (gapD f n / (Real.pi / 2)) * θ)
          atTop (𝓝 (0 + 0 * θ)) := by
        have h4' := hleft.add ((hD.div_const (Real.pi / 2)).mul_const θ)
        simpa [h0] using h4' 
      have hgm : (fun n : ℕ => gapM f n θ)
          = fun n : ℕ => f (gapDelta n) + (gapD f n / (Real.pi / 2)) * θ := by
        funext n; rw [gapM]
      rw [hgm]
      simpa [h0] using h4
    have h5 : Tendsto (fun n : ℕ => f (gapDelta n + gapC n * θ) - f θ) atTop (𝓝 0) := by
      have h5' := hcf.sub (tendsto_const_nhds (x := f θ) (f := atTop (α := ℕ)))
      simpa using h5' 
    have h6 := h5.sub hgM
    have h7 : Tendsto (fun n : ℕ => gapG f n θ - f θ) atTop (𝓝 0) := by
      have hgg : (fun n : ℕ => gapG f n θ - f θ)
          = fun n : ℕ => (f (gapDelta n + gapC n * θ) - f θ) - gapM f n θ := by
        funext n; rw [gapG]; ring
      rw [hgg]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h6
    simpa using h7.abs
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun n θ => |gapG f n θ - f θ|) (f := fun _ : ℝ => (0 : ℝ))
    (fun _ => 5 * M) hmeas hintb hbnd hlim
  simpa using hmain

end Limits

/-! ### The per-`n` bounds -/

section Bounds2

variable {f : ℝ → ℝ}

/-- `|a_n|` is controlled by the `L¹` distance of `g_n` from `f`. -/
theorem gapA_abs_le (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (horth : (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0) (n : ℕ) :
    |gapA f n| ≤ (15 / 4) * (∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|) := by
  have hψ1 : ContinuousOn (fun θ : ℝ => gapG f n θ * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    (continuousOn_gapG hcont n).mul Work.FTS.EllipticEst.P9.continuous_sinCos2.continuousOn
  have hψ2 : ContinuousOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    hcont.mul Work.FTS.EllipticEst.P9.continuous_sinCos2.continuousOn
  have hψ3 : ContinuousOn (fun θ : ℝ => (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    ((continuousOn_gapG hcont n).sub hcont).mul
      Work.FTS.EllipticEst.P9.continuous_sinCos2.continuousOn
  have hInt1 : IntegrableOn (fun θ : ℝ => gapG f n θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn hψ1
  have hInt2 : IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn hψ2
  have hInt3 : IntegrableOn (fun θ : ℝ => (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn hψ3
  have hsplit : (∫ θ in Work.Spaces.Iθ, gapG f n θ * Work.Elliptic.sinCos2 θ)
      = (∫ θ in Work.Spaces.Iθ, (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) := by
    rw [← MeasureTheory.integral_add hInt3 hInt2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  have hbound : |∫ θ in Work.Spaces.Iθ, (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ| := by
    have hInt4 : IntegrableOn
        (fun θ : ℝ => |(gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ|) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn hψ3.abs
    have hInt5 : IntegrableOn (fun θ : ℝ => |gapG f n θ - f θ|) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn
        ((continuousOn_gapG hcont n).sub hcont).abs
    have hnm : |∫ θ in Work.Spaces.Iθ, (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |(gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
          (f := fun θ : ℝ => (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ))
    refine le_trans hnm ?_
    refine MeasureTheory.integral_mono_ae hInt4 hInt5 ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
    change |(gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ| ≤ |gapG f n θ - f θ|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (Work.FTS.EllipticEst.P9.abs_sinCos2_le_one θ)
  have h2 : |gapA f n| = (15 / 4) * |∫ θ in Work.Spaces.Iθ,
      (gapG f n θ - f θ) * Work.Elliptic.sinCos2 θ| := by
    unfold gapA
    rw [hsplit, horth, add_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 4)]
  rw [h2]
  exact mul_le_mul_of_nonneg_left hbound (by norm_num)


end Bounds2

section Final

variable {f : ℝ → ℝ}

/-- The elementary pointwise bound for the corrected squeeze's derivative. -/
theorem gapF_pointwise (A : ℝ → ℝ) (a θ : ℝ) :
    (A θ - a * (2 * Real.cos (2 * θ))) ^ 2 ≤ (A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2 := by
  have hb : |2 * Real.cos (2 * θ)| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [Real.abs_cos_le_one (2 * θ)]
  have hab : |a| * |2 * Real.cos (2 * θ)| ≤ 2 * |a| := by
    have h := mul_le_mul_of_nonneg_left hb (abs_nonneg a)
    rw [mul_comm 2 |a|]
    exact h
  have hkey : |A θ - a * (2 * Real.cos (2 * θ))| ≤ |A θ| + 2 * |a| := by
    calc |A θ - a * (2 * Real.cos (2 * θ))|
        ≤ |A θ| + |a * (2 * Real.cos (2 * θ))| := abs_sub _ _
      _ = |A θ| + |a| * |2 * Real.cos (2 * θ)| := by rw [abs_mul]
      _ ≤ |A θ| + 2 * |a| := by linarith [hab]
  have hleft : |A θ - a * (2 * Real.cos (2 * θ))| ^ 2 ≤ (|A θ| + 2 * |a|) ^ 2 := by
    refine sq_le_sq' ?_ hkey
    linarith [abs_nonneg (A θ - a * (2 * Real.cos (2 * θ)))]
  have hexp : (|A θ| + 2 * |a|) ^ 2 = (A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2 := by
    have h1 : |A θ| ^ 2 = (A θ) ^ 2 := sq_abs (A θ)
    have h2 : |a| ^ 2 = a ^ 2 := sq_abs a
    nlinarith [h1, h2]
  have hgoal : (A θ - a * (2 * Real.cos (2 * θ))) ^ 2 ≤ (|A θ| + 2 * |a|) ^ 2 := by
    rw [← sq_abs (A θ - a * (2 * Real.cos (2 * θ)))]
    exact hleft
  linarith [hgoal, hexp.le, hexp.ge]

/-- `f` is close to its squeeze in `L¹`. -/
theorem gapG_sq_ge (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M) (hMnn : 0 ≤ M) (n : ℕ) :
    (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
        - 8 * M * (∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2 := by
  have hIntG : IntegrableOn (fun θ : ℝ => (gapG f n θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn ((continuousOn_gapG hcont n).pow 2)
  have hIntF : IntegrableOn (fun θ : ℝ => (f θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn (hcont.pow 2)
  have hIntE : IntegrableOn (fun θ : ℝ => |gapG f n θ - f θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn
      ((continuousOn_gapG hcont n).sub hcont).abs
  have hIntD : IntegrableOn (fun θ : ℝ => (gapG f n θ) ^ 2 - (f θ) ^ 2) Work.Spaces.Iθ :=
    hIntG.sub hIntF
  have hdiff : (∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2) - (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - (f θ) ^ 2) :=
    (MeasureTheory.integral_sub hIntG hIntF).symm
  have hbound : |∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - (f θ) ^ 2)|
      ≤ 8 * M * (∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|) := by
    have hnm : |∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - (f θ) ^ 2)|
        ≤ ∫ θ in Work.Spaces.Iθ, |(gapG f n θ) ^ 2 - (f θ) ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
          (f := fun θ : ℝ => (gapG f n θ) ^ 2 - (f θ) ^ 2))
    refine le_trans hnm ?_
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        |(gapG f n θ) ^ 2 - (f θ) ^ 2| ≤ 8 * M * |gapG f n θ - f θ| := by
      intro θ hθ
      have h1 : |gapG f n θ| ≤ 4 * M := gapG_bound hM hMnn n hθ
      have h2 : |f θ| ≤ M := hM θ hθ
      have h3 : |gapG f n θ + f θ| ≤ 8 * M := by
        calc |gapG f n θ + f θ| ≤ |gapG f n θ| + |f θ| := abs_add_le _ _
          _ ≤ 8 * M := by linarith
      rw [show (gapG f n θ) ^ 2 - (f θ) ^ 2
          = (gapG f n θ - f θ) * (gapG f n θ + f θ) from by ring, abs_mul]
      calc |gapG f n θ - f θ| * |gapG f n θ + f θ|
          ≤ |gapG f n θ - f θ| * (8 * M) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = 8 * M * |gapG f n θ - f θ| := by ring
    have hIntBig : IntegrableOn (fun θ : ℝ => 8 * M * |gapG f n θ - f θ|) Work.Spaces.Iθ :=
      hIntE.const_mul (8 * M)
    have hIntAbs : IntegrableOn (fun θ : ℝ => |(gapG f n θ) ^ 2 - (f θ) ^ 2|) Work.Spaces.Iθ :=
      hIntD.abs
    have h4 := MeasureTheory.integral_mono_ae hIntAbs hIntBig
      (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    rwa [MeasureTheory.integral_const_mul] at h4
  have h1 : -(8 * M * (∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ|))
      ≤ (∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2) - (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) := by
    rw [hdiff]
    linarith [neg_abs_le (∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - (f θ) ^ 2)), hbound]
  linarith

/-- The correction `a_n sin 2θ` costs at most `8M|a_n|` pointwise. -/
theorem gapF_sq_ge (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    {M : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M) (hMnn : 0 ≤ M) (n : ℕ) :
    (∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2)
        - 8 * M * |gapA f n| * (Real.pi / 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (gapF f n θ) ^ 2 := by
  have hIntG : IntegrableOn (fun θ : ℝ => (gapG f n θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn ((continuousOn_gapG hcont n).pow 2)
  have hIntF : IntegrableOn (fun θ : ℝ => (gapF f n θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn ((continuousOn_gapF hcont n).pow 2)
  have hIntA : IntegrableOn (fun θ : ℝ => (gapG f n θ) ^ 2 - 8 * M * |gapA f n|)
      Work.Spaces.Iθ :=
    hIntG.sub (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (gapG f n θ) ^ 2 - 8 * M * |gapA f n| ≤ (gapF f n θ) ^ 2 := by
    intro θ hθ
    have h1 : |gapG f n θ| ≤ 4 * M := gapG_bound hM hMnn n hθ
    have hs : |Real.sin (2 * θ)| ≤ 1 := by
      rw [abs_le]
      exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h2 : |gapG f n θ| * |Real.sin (2 * θ)| ≤ 4 * M := by
      have h3 : |gapG f n θ| * |Real.sin (2 * θ)| ≤ (4 * M) * 1 :=
        mul_le_mul h1 hs (abs_nonneg _) (by linarith)
      linarith
    have hsplit_abs : |2 * (gapG f n θ) * (gapA f n * Real.sin (2 * θ))|
        = 2 * |gapG f n θ| * (|gapA f n| * |Real.sin (2 * θ)|) := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    have habs : |2 * (gapG f n θ) * (gapA f n * Real.sin (2 * θ))| ≤ 8 * M * |gapA f n| := by
      rw [hsplit_abs]
      calc 2 * |gapG f n θ| * (|gapA f n| * |Real.sin (2 * θ)|)
          = 2 * (|gapA f n| * (|gapG f n θ| * |Real.sin (2 * θ)|)) := by ring
        _ ≤ 2 * (|gapA f n| * (4 * M)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (by norm_num)
        _ = 8 * M * |gapA f n| := by ring
    have hle : 2 * (gapG f n θ) * (gapA f n * Real.sin (2 * θ)) ≤ 8 * M * |gapA f n| :=
      le_trans (le_abs_self _) habs
    have hsq : (gapF f n θ) ^ 2 = (gapG f n θ) ^ 2
        - 2 * (gapG f n θ) * (gapA f n * Real.sin (2 * θ))
        + (gapA f n * Real.sin (2 * θ)) ^ 2 := by
      rw [gapF]; ring
    rw [hsq]
    have h9 : 0 ≤ (gapA f n * Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    linarith [hle, h9]
  have hmono := MeasureTheory.integral_mono_ae hIntA hIntF
    (ae_restrict_of_forall_mem measurableSet_Icc hpt)
  have hsplit : (∫ θ in Work.Spaces.Iθ, ((gapG f n θ) ^ 2 - 8 * M * |gapA f n|))
      = (∫ θ in Work.Spaces.Iθ, (gapG f n θ) ^ 2) - 8 * M * |gapA f n| * (Real.pi / 2) := by
    rw [MeasureTheory.integral_sub hIntG
      (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)]
    rw [MeasureTheory.setIntegral_const, Work.FTS.EllipticEst.P9.real_volume_Iθ, smul_eq_mul]
    ring
  linarith [hmono, hsplit.ge, hsplit.le]

/-- The `L²` bound for the derivative of the corrected squeeze. -/
theorem gapF_deriv_sq_le (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) Work.Spaces.Iθ) {n : ℕ}
    (h : gapDelta n < Real.pi / 8) :
    (∫ θ in Work.Spaces.Iθ, (deriv (gapF f n) θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
        + 2 * |gapA f n| * ((∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2) + Real.pi / 2)
        + 2 * Real.pi * (gapA f n) ^ 2 := by
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 with hB
  set a : ℝ := gapA f n with ha
  set A : ℝ → ℝ := fun θ => gapC n * deriv f (gapDelta n + gapC n * θ)
    - gapD f n / (Real.pi / 2) with hA
  have hIntA : IntegrableOn (fun θ : ℝ => A θ) Work.Spaces.Iθ := by
    rw [hA]
    exact ((integrableOn_deriv_comp hf2 h).const_mul (gapC n)).sub
      (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
  have hIntAbs : IntegrableOn (fun θ : ℝ => |A θ|) Work.Spaces.Iθ := hIntA.abs
  have hIntA2 : IntegrableOn (fun θ : ℝ => (A θ) ^ 2) Work.Spaces.Iθ := by
    rw [hA]
    exact integrableOn_An_sq hf2 h
  have hIntConst : IntegrableOn (fun _ : ℝ => (4 : ℝ) * a ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const
  have hIntBig : IntegrableOn (fun θ : ℝ => (A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2)
      Work.Spaces.Iθ :=
    (hIntA2.add (hIntAbs.const_mul (4 * |a|))).add hIntConst
  have hae : (fun θ : ℝ => deriv (gapF f n) θ) =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => A θ - a * (2 * Real.cos (2 * θ))) := by
    rw [ha, hA]
    rw [← Work.FTS.EllipticEst.P9.restrict_Ioo_eq_restrict_Iθ]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
      show deriv (gapF f n) θ
        = (gapC n * deriv f (gapDelta n + gapC n * θ) - gapD f n / (Real.pi / 2))
          - gapA f n * (2 * Real.cos (2 * θ))
      rw [deriv_gapF hf2 h hθ, deriv_gapG hf2 h hθ])
  have hIntDerivF : IntegrableOn (fun θ : ℝ => (deriv (gapF f n) θ) ^ 2) Work.Spaces.Iθ := by
    have hw := Work.FTS.EllipticEst.P9.integrableOn_w_sq (gapF_contDiffOn hf2 h)
    have haeeq : (fun θ : ℝ => (Work.FTS.EllipticEst.P9.w (gapF f n) θ) ^ 2)
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (deriv (gapF f n) θ) ^ 2) := by
      filter_upwards [Work.FTS.EllipticEst.P9.w_ae_eq_deriv (gapF f n)] with θ hθ
      rw [hθ]
    exact MeasureTheory.Integrable.congr hw haeeq
  have hIntArg : IntegrableOn (fun θ : ℝ => (A θ - a * (2 * Real.cos (2 * θ))) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.congr hIntDerivF ?_
    filter_upwards [hae] with θ hθ
    rw [hθ]
  have h1 : (∫ θ in Work.Spaces.Iθ, (deriv (gapF f n) θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (A θ - a * (2 * Real.cos (2 * θ))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    rw [hθ]
  rw [h1]
  have hmono := MeasureTheory.integral_mono_ae hIntArg hIntBig
    (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => gapF_pointwise A a θ))
  have hExpBig : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2))
      = (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2) + 4 * |a| * (∫ θ in Work.Spaces.Iθ, |A θ|)
        + 4 * a ^ 2 * (Real.pi / 2) := by
    have e1 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 4 * |a| * |A θ| + 4 * a ^ 2))
        = (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 4 * |a| * |A θ|))
          + (∫ θ in Work.Spaces.Iθ, ((4 : ℝ) * a ^ 2)) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => (A θ) ^ 2 + 4 * |a| * |A θ|)
        (g := fun _ : ℝ => (4 : ℝ) * a ^ 2)
        (hIntA2.add (hIntAbs.const_mul (4 * |a|))) hIntConst
    have e2 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 4 * |a| * |A θ|))
        = (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (4 * |a| * |A θ|)) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => (A θ) ^ 2)
        (g := fun θ : ℝ => 4 * |a| * |A θ|) hIntA2 (hIntAbs.const_mul (4 * |a|))
    have e3 : (∫ θ in Work.Spaces.Iθ, (4 * |a| * |A θ|))
        = 4 * |a| * (∫ θ in Work.Spaces.Iθ, |A θ|) :=
      MeasureTheory.integral_const_mul (4 * |a|) _
    have e4 : (∫ θ in Work.Spaces.Iθ, ((4 : ℝ) * a ^ 2)) = 4 * a ^ 2 * (Real.pi / 2) := by
      rw [MeasureTheory.setIntegral_const, Work.FTS.EllipticEst.P9.real_volume_Iθ, smul_eq_mul]
      ring
    rw [e1, e2, e3, e4]
  have hA2le : (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2) ≤ B := by
    rw [hA, hB]
    exact gap_integral_An_le hf2 hint h
  have hAbsle : (∫ θ in Work.Spaces.Iθ, |A θ|) ≤ (B + Real.pi / 2) / 2 := by
    have hIntMaj : IntegrableOn (fun θ : ℝ => ((A θ) ^ 2 + 1) / 2) Work.Spaces.Iθ := by
      have h2 : IntegrableOn (fun θ : ℝ => (A θ) ^ 2 + 1) Work.Spaces.Iθ :=
        hIntA2.add (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)
      have h3 := h2.const_mul (1 / 2)
      refine MeasureTheory.IntegrableOn.congr_fun h3 (fun θ _ => ?_) measurableSet_Icc
      ring
    have h1 : (∫ θ in Work.Spaces.Iθ, |A θ|) ≤ ∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 1) / 2 :=
      MeasureTheory.integral_mono_ae hIntAbs hIntMaj
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => by
          have hsq_abs : |A θ| ^ 2 = (A θ) ^ 2 := sq_abs _
          have hnn := sq_nonneg (|A θ| - 1)
          nlinarith [abs_nonneg (A θ)]))
    have h2 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 1) / 2)
        = ((∫ θ in Work.Spaces.Iθ, (A θ) ^ 2) + Real.pi / 2) / 2 := by
      have h3 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 + 1) / 2)
          = ∫ θ in Work.Spaces.Iθ, (1 / 2) * ((A θ) ^ 2 + 1) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
      rw [h3, MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_add hIntA2
        (Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn continuousOn_const)]
      rw [MeasureTheory.setIntegral_const, Work.FTS.EllipticEst.P9.real_volume_Iθ, smul_eq_mul]
      ring
    linarith
  have h3 : (∫ θ in Work.Spaces.Iθ, (A θ - a * (2 * Real.cos (2 * θ))) ^ 2)
      ≤ B + 2 * |a| * (B + Real.pi / 2) + 2 * Real.pi * a ^ 2 := by
    have hstep : 4 * |a| * (∫ θ in Work.Spaces.Iθ, |A θ|) ≤ 4 * |a| * ((B + Real.pi / 2) / 2) :=
      mul_le_mul_of_nonneg_left hAbsle (by positivity)
    have heq : B + 4 * |a| * ((B + Real.pi / 2) / 2) + 4 * a ^ 2 * (Real.pi / 2)
        = B + 2 * |a| * (B + Real.pi / 2) + 2 * Real.pi * a ^ 2 := by ring
    linarith [hmono, hExpBig.le, hExpBig.ge, hA2le, hstep, heq]
  exact h3

/-- The corrected squeeze satisfies the solvability condition. -/
theorem gapF_moment (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (horth : (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0) (n : ℕ) :
    (∫ θ in Work.Spaces.Iθ, gapF f n θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hcontψ : ContinuousOn Work.Elliptic.sinCos2 (Set.Icc 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.P9.continuous_sinCos2.continuousOn
  have hcont2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.mul hcontψ
  have hIntG : IntegrableOn (fun θ : ℝ => gapG f n θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn
      ((continuousOn_gapG hcont n).mul hcontψ)
  have hIntC : IntegrableOn
      (fun θ : ℝ => gapA f n * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.P9.integrableOn_Iθ_of_continuousOn (continuousOn_const.mul hcont2)
  have hsplit : (∫ θ in Work.Spaces.Iθ, gapF f n θ * Work.Elliptic.sinCos2 θ)
      = (∫ θ in Work.Spaces.Iθ, gapG f n θ * Work.Elliptic.sinCos2 θ)
        - gapA f n * (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    have hpt : ∀ θ : ℝ, gapF f n θ * Work.Elliptic.sinCos2 θ
        = gapG f n θ * Work.Elliptic.sinCos2 θ
          - gapA f n * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
      intro θ; rw [gapF]; ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_sub hIntG hIntC]
    rw [MeasureTheory.integral_const_mul]
  have h45 : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) = 4 / 15 := by
    rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
      (fun θ _ => mul_comm _ _)]
    simpa [Work.FTS.EllipticEst.P9.s2] using Work.FTS.EllipticEst.P9.integral_sinCos2_mul_s2
  rw [hsplit, h45]
  unfold gapA
  ring

end Final

theorem Gap9Open : ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 → f (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0 →
    9 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  intro f hf2 hcont h0 hπ hint horth
  obtain ⟨M₀, hM₀⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  set M : ℝ := max M₀ 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMb : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ M := by
    intro θ hθ
    have h := hM₀ θ hθ
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 with hB
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun θ => sq_nonneg _)
  set En : ℕ → ℝ := fun n => ∫ θ in Work.Spaces.Iθ, |gapG f n θ - f θ| with hEn
  have hEnnn : ∀ n, 0 ≤ En n := fun n => integral_nonneg (fun θ => abs_nonneg _)
  have htendEn : Tendsto En atTop (𝓝 0) := by
    rw [hEn]
    exact tendsto_gapG_sub hcont h0 hπ
  have hAg : ∀ n, |gapA f n| ≤ (15 / 4) * En n := by
    intro n
    rw [hEn]
    exact gapA_abs_le hcont horth n
  have hstrong : ∀ᶠ n in atTop,
      9 * (∫ θ in Work.Spaces.Iθ, (gapF f n θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (deriv (gapF f n) θ) ^ 2 := by
    filter_upwards [eventually_gapDelta_lt_eighth] with n hn
    exact Work.FTS.EllipticEst.P9.slicePoincare9_fts (gapF f n) (gapF_contDiffOn hf2 hn)
      (gapF_zero n) (gapF_pi n) (gapF_moment hcont horth n)
  set Err : ℕ → ℝ := fun n => 2 * |gapA f n| * (B + Real.pi / 2) + 2 * Real.pi * (gapA f n) ^ 2
    + 72 * M * |gapA f n| * (Real.pi / 2) + 72 * M * En n with hErr
  set Err2 : ℕ → ℝ := fun n => 2 * ((15 / 4) * En n) * (B + Real.pi / 2)
    + 2 * Real.pi * ((15 / 4) * En n) ^ 2 + 72 * M * ((15 / 4) * En n) * (Real.pi / 2)
    + 72 * M * En n with hErr2
  have hErrnn : ∀ n, 0 ≤ Err n := by
    intro n
    rw [hErr]
    have ha : 0 ≤ |gapA f n| := abs_nonneg _
    have hb : 0 ≤ (gapA f n) ^ 2 := sq_nonneg _
    have h1 : 0 ≤ 2 * |gapA f n| * (B + Real.pi / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) ha) (by linarith [hBnn, Real.pi_pos])
    have h2 : 0 ≤ 2 * Real.pi * (gapA f n) ^ 2 := mul_nonneg (by positivity) hb
    have h3 : 0 ≤ 72 * M * |gapA f n| * (Real.pi / 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMnn) ha) (by positivity)
    have h4 : 0 ≤ 72 * M * En n := mul_nonneg (mul_nonneg (by norm_num) hMnn) (hEnnn n)
    linarith
  have hErrle : ∀ n, Err n ≤ Err2 n := by
    intro n
    have h1 := hAg n
    have h3 : (gapA f n) ^ 2 ≤ ((15 / 4) * En n) ^ 2 := by
      have h5 : |gapA f n| ≤ |(15 / 4) * En n| := by
        rw [abs_of_nonneg (by linarith [hEnnn n] : (0 : ℝ) ≤ (15 / 4) * En n)]
        exact h1
      calc (gapA f n) ^ 2 = |gapA f n| ^ 2 := (sq_abs _).symm
        _ ≤ |(15 / 4) * En n| ^ 2 :=
            sq_le_sq' (by linarith [h5, abs_nonneg (gapA f n)]) h5
        _ = ((15 / 4) * En n) ^ 2 := sq_abs _
    have e1 : 2 * |gapA f n| * (B + Real.pi / 2) ≤ 2 * ((15 / 4) * En n) * (B + Real.pi / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith [hBnn, Real.pi_pos])
    have e2 : 2 * Real.pi * (gapA f n) ^ 2 ≤ 2 * Real.pi * ((15 / 4) * En n) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e3 : 72 * M * |gapA f n| * (Real.pi / 2)
        ≤ 72 * M * ((15 / 4) * En n) * (Real.pi / 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith [h1]) (by linarith [hMnn])
    rw [hErr, hErr2]
    linarith
  have htend2 : Tendsto Err2 atTop (𝓝 0) := by
    set φ : ℝ → ℝ := fun x => 2 * ((15 / 4) * x) * (B + Real.pi / 2)
      + 2 * Real.pi * ((15 / 4) * x) ^ 2 + 72 * M * ((15 / 4) * x) * (Real.pi / 2) + 72 * M * x
      with hφ
    have hφc : Continuous φ := by rw [hφ]; fun_prop
    have h1 : Tendsto (fun n => φ (En n)) atTop (𝓝 (φ 0)) := hφc.continuousAt.tendsto.comp htendEn
    have hφ0 : φ 0 = 0 := by rw [hφ]; ring
    have h2 : Tendsto (fun n => φ (En n)) atTop (𝓝 0) := by simpa [hφ0] using h1
    rw [hErr2]
    simpa [hφ, Function.comp_def] using h2
  have htendErr : Tendsto Err atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop (α := ℕ))) htend2 hErrnn hErrle
  have hkey : ∀ᶠ n in atTop, 9 * A - B ≤ Err n := by
    filter_upwards [hstrong, eventually_gapDelta_lt_eighth] with n hn hsmall
    have h1 := gapG_sq_ge hcont hMb hMnn n
    have h2 := gapF_sq_ge hcont hMb hMnn n
    have h3 := gapF_deriv_sq_le hf2 hint hsmall
    rw [hB, hErr, hEn]
    linarith
  have hneg : Tendsto (fun n : ℕ => -(Err n)) atTop (𝓝 0) := by
    simpa using htendErr.neg
  have hkey' : ∀ᶠ n in atTop, -(Err n) ≤ -(9 * A - B) :=
    hkey.mono (fun n hn => by linarith)
  have hfin := le_of_tendsto hneg hkey'
  rw [hA, hB]
  linarith

end
end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4CrossCont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of the `I₄` slice objects on a closed sub-interval

Given `Φ` of class `C²` on the open quadrant `(0, π/2)` and `0 < δ ≤ θ₁ < π/2`, all five
slice objects of the honest `I₄` estimate — `Φ`, `ψ = Φ/cos θ`, `ψ'`, the weight
`σ = sin(2θ)^{-99/100}` and the coefficient `Σ = (1-η)cos²θ + (3+η)sin²θ` — are continuous
on the closed interval `[δ, θ₁]`.

The substance is that `[δ, θ₁]` is a compact sub-interval of the *open* quadrant, so
`Φ ∈ C²` on a neighbourhood of it; the only non-trivial component is the derivative of the
quotient `ψ`, which is `ContinuousOn` by `continuousOn_deriv_I4psi`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

theorem I4CrossCont (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    {δ θ₁ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ < Real.pi / 2) :
    ContinuousOn Φ (Set.Icc δ θ₁) ∧ ContinuousOn (I4psi Φ) (Set.Icc δ θ₁)
      ∧ ContinuousOn (deriv (I4psi Φ)) (Set.Icc δ θ₁)
      ∧ ContinuousOn I4sig (Set.Icc δ θ₁) ∧ ContinuousOn I4Sig (Set.Icc δ θ₁) := by
  -- `[δ, θ₁]` sits inside the open quadrant, where `Φ` is `C²`
  have hIcc : Set.Icc δ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hδ hx.1, lt_of_le_of_lt hx.2 hθ₁⟩
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos θ) (Set.Icc δ θ₁) :=
    Real.continuous_cos.continuousOn
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin θ) (Set.Icc δ θ₁) :=
    Real.continuous_sin.continuousOn
  refine ⟨hsm.continuousOn.mono hIcc, ?_, ?_, continuousOn_I4sig hδ hθ₁, ?_⟩
  · exact (contDiffOn_I4psi Φ hsm).continuousOn.mono hIcc
  · exact continuousOn_deriv_I4psi Φ hsm hIcc
  · change ContinuousOn
      (fun θ : ℝ => (1 - 99 / 100) * (Real.cos θ) ^ 2 + (3 + 99 / 100) * (Real.sin θ) ^ 2)
      (Set.Icc δ θ₁)
    exact (continuousOn_const.mul (hcos.pow 2)).add (continuousOn_const.mul (hsin.pow 2))

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LzeroSingContDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst





end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.sliceIBPLight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The weight `σ_a` and its two derivatives -/

/-- The light angular weight `σ(θ) = sin(2θ)^a`. -/
def sigR (a θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ a

/-- The first derivative of `sigR`: `σ' = 2a cos(2θ) sin(2θ)^{a-1}`. -/
def sigDR (a θ : ℝ) : ℝ := 2 * a * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (a - 1)

/-- The second derivative of `sigR`:
`σ'' = -4a σ - 4a(1-a) cos²(2θ) sin(2θ)^{a-2}`. -/
def sigDDR (a θ : ℝ) : ℝ :=
  -4 * a * (Real.sin (2 * θ)) ^ a
    - 4 * a * (1 - a) * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2)

@[simp] theorem sigR_apply (a θ : ℝ) : sigR a θ = (Real.sin (2 * θ)) ^ a := rfl
@[simp] theorem sigDR_apply (a θ : ℝ) : sigDR a θ = 2 * a * Real.cos (2 * θ)
    * (Real.sin (2 * θ)) ^ (a - 1) := rfl
@[simp] theorem sigDDR_apply (a θ : ℝ) : sigDDR a θ =
    -4 * a * (Real.sin (2 * θ)) ^ a
      - 4 * a * (1 - a) * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2) := rfl

/-- On the open interval the base `sin(2θ)` is positive, so `sigR` is differentiable there with
derivative `sigDR`. -/
theorem sigR_hasDerivAt (a : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (sigR a) (sigDR a θ) θ := by
  have hsin_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  have hpow := hsin.rpow_const (p := a) (Or.inl (ne_of_gt hsin_pos))
  refine hpow.congr_deriv ?_
  rw [sigDR_apply]
  ring

/-- The second derivative of the weight on the open interval. -/
theorem sigDR_hasDerivAt (a : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (sigDR a) (sigDDR a θ) θ := by
  have hsin_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-(Real.sin (2 * θ) * 2)) θ :=
    (hlin.cos).congr_deriv (by ring)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  -- the second factor `sin(2θ)^{a-1}`
  have hpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (a - 1))
      ((Real.cos (2 * θ) * 2) * (a - 1) * (Real.sin (2 * θ)) ^ (a - 1 - 1)) θ :=
    hsin.rpow_const (p := a - 1) (Or.inl (ne_of_gt hsin_pos))
  have hprod : HasDerivAt
      (fun t : ℝ => (2 * a * Real.cos (2 * t)) * (Real.sin (2 * t)) ^ (a - 1))
      ((2 * a * (-(Real.sin (2 * θ) * 2))) * (Real.sin (2 * θ)) ^ (a - 1)
        + (2 * a * Real.cos (2 * θ))
          * ((Real.cos (2 * θ) * 2) * (a - 1) * (Real.sin (2 * θ)) ^ (a - 1 - 1))) θ :=
    (hcos.const_mul (2 * a)).mul hpow
  refine hprod.congr_deriv ?_
  -- identify with `sigDDR`
  rw [sigDDR_apply]
  have hs : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin_pos
  have hsplit : (Real.sin (2 * θ)) ^ (a - 1)
      = (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hsin_pos]
    ring_nf
  have hsplit2 : (Real.sin (2 * θ)) ^ (a - 1 - 1)
      = (Real.sin (2 * θ)) ^ (a - 2) := by ring_nf
  rw [hsplit2]
  -- express everything through `s^a` and `s^{a-2}`
  have hinv : (Real.sin (2 * θ)) ^ (-1 : ℝ) = (Real.sin (2 * θ))⁻¹ :=
    Real.rpow_neg_one _
  have h1 : (2 * a * (-(Real.sin (2 * θ) * 2))) * (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ))⁻¹
      = -4 * a * (Real.sin (2 * θ)) ^ a := by
    field_simp
    ring
  have h2 : (2 * a * Real.cos (2 * θ)) * ((Real.cos (2 * θ) * 2) * (a - 1)
      * (Real.sin (2 * θ)) ^ (a - 2))
      = 4 * a * (a - 1) * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2) := by ring
  rw [← hinv] at h1
  rw [hsplit] at *
  linarith [h1, h2]

/-! ## The double angular integration by parts for the light weight

The identity is assembled exactly as in `AngSecond.slice_ibp_sigma`: the two antiderivatives
`A = f·f'·σ` and `B = f²·σ'` are integrated with the generic `AngSecond.slice_ftc_zero`, and the
two resulting identities
`∫ ((f')²σ + f f''σ + f f'σ') = 0`, `∫ (2 f f'σ' + f²σ'') = 0`
are combined after expanding `σ''`.  The analytic side conditions (integrability of the five
pieces and the vanishing of the two endpoint limits) are *explicit hypotheses* here, so that this
lemma is independent of how they are discharged for a given slice. -/

/-- **The light-weight angular integration by parts.**

For `0 < a < 1` and `f : ℝ → ℝ` which is `C²` on the open interval `(0,π/2)` and for which the
five weighted integrals below are honest and the two boundary products vanish at the endpoints,

  `∫_θ (f')² σ = -∫_θ f f'' σ - 2a ∫_θ f² σ - 2a(1-a) ∫_θ f² cos²(2θ) sin(2θ)^{a-2}`,

with `σ θ = sin(2θ)^a` (`sigR a`). -/
theorem slice_ibp_light (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hI1 : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ)
      Work.Spaces.Iθ)
    (hI2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => f θ * deriv (deriv f) θ * sigR a θ) Work.Spaces.Iθ)
    (hI3 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv f θ * sigDR a θ)
      Work.Spaces.Iθ)
    (hI4 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigR a θ) Work.Spaces.Iθ)
    (hI5 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (a - 2)) Work.Spaces.Iθ)
    (hb1 : Filter.Tendsto (fun t : ℝ => f t * deriv f t * sigR a t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb2 : Filter.Tendsto (fun t : ℝ => f t * deriv f t * sigR a t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hb3 : Filter.Tendsto (fun t : ℝ => f t ^ 2 * sigDR a t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb4 : Filter.Tendsto (fun t : ℝ => f t ^ 2 * sigDR a t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ)
      = - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigR a θ)
        - 2 * a * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigR a θ)
        - 2 * a * (1 - a) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (a - 2)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- `f` is `C²` at interior points
  have hcd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContDiffAt ℝ 2 f θ := fun θ hθ =>
    (hf θ hθ).contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hdf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (deriv f θ) θ := fun θ hθ =>
    ((hcd θ hθ).differentiableAt (by norm_num)).hasDerivAt
  have hddf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv f) (deriv (deriv f) θ) θ := fun θ hθ =>
    (((hcd θ hθ).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  -- integrability of `f² σ''`
  have hI6 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigDDR a θ)
      Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => -4 * a * (f θ ^ 2 * sigR a θ)
        + (-4 * a * (1 - a)) * (f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (a - 2))) Work.Spaces.Iθ :=
      (hI4.const_mul (-4 * a)).add (hI5.const_mul (-4 * a * (1 - a)))
    refine h.congr_fun_ae ?_
    filter_upwards with θ
    simp only [sigDDR_apply, sigR_apply]
    ring_nf
  -- first integration by parts
  have hA_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t * deriv f t * sigR a t)
        (deriv f θ ^ 2 * sigR a θ + f θ * deriv (deriv f) θ * sigR a θ
          + f θ * deriv f θ * sigDR a θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hddf θ hθ)).mul (sigR_hasDerivAt a hθ)
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hA_int : IntervalIntegrable (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ
      + f θ * deriv (deriv f) θ * sigR a θ + f θ * deriv f θ * sigDR a θ)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ
        + f θ * deriv (deriv f) θ * sigR a θ + f θ * deriv f θ * sigDR a θ)
        Work.Spaces.Iθ := (hI1.add hI2).add hI3
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hA_zero : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ
      + f θ * deriv (deriv f) θ * sigR a θ + f θ * deriv f θ * sigDR a θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero
      (fun t : ℝ => f t * deriv f t * sigR a t)
      (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ + f θ * deriv (deriv f) θ * sigR a θ
        + f θ * deriv f θ * sigDR a θ) hA_deriv hA_int hb1 hb2
  have hA_split : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ
        + f θ * deriv (deriv f) θ * sigR a θ + f θ * deriv f θ * sigDR a θ)
      = (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigR a θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigDR a θ) := by
    have h12 : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ
        + f θ * deriv (deriv f) θ * sigR a θ) Work.Spaces.Iθ := hI1.add hI2
    rw [MeasureTheory.integral_add h12 hI3, MeasureTheory.integral_add hI1 hI2]
  -- second integration by parts
  have hB_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t ^ 2 * sigDR a t)
        (2 * (f θ * deriv f θ * sigDR a θ) + f θ ^ 2 * sigDDR a θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hdf θ hθ)).mul (sigDR_hasDerivAt a hθ)
    have hfun : (f * f) * (fun t : ℝ => sigDR a t) = fun t : ℝ => f t ^ 2 * sigDR a t := by
      funext t
      simp only [Pi.mul_apply]
      ring
    rw [hfun] at h
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hB_int : IntervalIntegrable (fun θ : ℝ => 2 * (f θ * deriv f θ * sigDR a θ)
      + f θ ^ 2 * sigDDR a θ) MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => 2 * (f θ * deriv f θ * sigDR a θ)
        + f θ ^ 2 * sigDDR a θ) Work.Spaces.Iθ := (hI3.const_mul 2).add hI6
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hB_zero : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigDR a θ)
      + f θ ^ 2 * sigDDR a θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero (fun t : ℝ => f t ^ 2 * sigDR a t)
      (fun θ : ℝ => 2 * (f θ * deriv f θ * sigDR a θ) + f θ ^ 2 * sigDDR a θ)
      hB_deriv hB_int hb3 hb4
  -- expand `σ''`
  have hI6_eq : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDDR a θ)
      = -4 * a * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigR a θ)
        + (-4 * a * (1 - a)) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (a - 2)) := by
    have hfun : (fun θ => f θ ^ 2 * sigDDR a θ)
        = (fun θ => -4 * a * (f θ ^ 2 * sigR a θ)
            + (-4 * a * (1 - a)) * (f θ ^ 2 * Real.cos (2 * θ) ^ 2
                * (Real.sin (2 * θ)) ^ (a - 2))) := by
      funext θ
      simp only [sigDDR_apply, sigR_apply]
      ring_nf
    rw [hfun, MeasureTheory.integral_add (hI4.const_mul (-4 * a))
        (hI5.const_mul (-4 * a * (1 - a))),
      MeasureTheory.integral_const_mul (-4 * a) (fun θ => f θ ^ 2 * sigR a θ),
      MeasureTheory.integral_const_mul (-4 * a * (1 - a))
        (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2))]
  have hB_split : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigDR a θ)
        + f θ ^ 2 * sigDDR a θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigDR a θ)
        + (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDDR a θ) := by
    rw [MeasureTheory.integral_add (hI3.const_mul 2) hI6,
      MeasureTheory.integral_const_mul 2 (fun θ => f θ * deriv f θ * sigDR a θ)]
  -- assemble
  set P := ∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ with hP
  set Q := ∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigR a θ with hQ
  set R := ∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigDR a θ with hR
  set D := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigR a θ with hD
  set E := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
    * (Real.sin (2 * θ)) ^ (a - 2) with hE
  have h1' : P + Q + R = 0 := by
    rw [← hA_split]; exact hA_zero
  have h2' : 2 * R + (-4 * a * D + (-4 * a * (1 - a)) * E) = 0 := by
    rw [← hI6_eq, ← hB_split]; exact hB_zero
  have hmain : P = -Q - 2 * a * D - 2 * a * (1 - a) * E := by linarith
  rw [hP, hQ, hD, hE] at hmain
  linarith [hmain]

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.H2.SupMixedLeH4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

open Work.Spaces

/-! ## Elementary angular and weight identities -/

/-- `Iθ` is a measurable set (in the folded form used by the set integrals of this file). -/
lemma measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

/-- `Iz` is a measurable set (in the folded form used by the set integrals of this file). -/
lemma measurableSet_Iz : MeasurableSet Iz := measurableSet_Ici

/-- `sin(2θ) ≥ 0` on the closed quadrant. -/
lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


/-- `(w z · sin(2θ)^{-γ/2})² = w(z)² · sin(2θ)^{-γ}` on the closed quadrant. -/
lemma Wt_sq (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Iθ) :
    (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs := sin_two_nonneg hθ
  have hne : (-(gam α / 2)) + (-(gam α / 2)) ≠ 0 := by
    have := gam_pos hα
    intro h
    linarith
  rw [mul_pow, pow_two, pow_two, ← Real.rpow_add' hs hne]
  congr 1
  ring

/-- `(∂_θ u)² sin(2θ)^{2-γ} = (D_θ u)² sin(2θ)^{-γ}` on the closed quadrant. -/
lemma pth_sq_mul_sin_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Iθ) :
    (pth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)
      = (Dth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs := sin_two_nonneg hθ
  have hne : 2 + (-(gam α)) ≠ 0 := by
    have hg1 : gam α ≤ 11 / 10 := by rw [gam]; linarith
    intro h
    linarith
  have hD : Dth u z θ = Real.sin (2 * θ) * pth u z θ := rfl
  rw [hD, mul_pow, show 2 - gam α = 2 + (-(gam α)) by ring, Real.rpow_add' hs hne]
  simp only [mul_assoc, mul_left_comm, mul_comm, Real.rpow_two]

/-- The angular slice `θ ↦ u z θ` of a `SmoothNbhd` function is continuous on `[0, π/2]`. -/
lemma slice_continuousOn {u : ℝ → ℝ → ℝ} (hsm : SmoothNbhd u) {z : ℝ} (hz : z ∈ Iz) :
    ContinuousOn (fun θ => u z θ) Iθ := by
  have hz1 : (-1 : ℝ) < z := by
    have h := hz
    simp only [Iz, Set.mem_Ici] at h
    linarith
  have hU : ContDiffOn ℝ ⊤ (fun t : ℝ => u z t) (Set.Ioo (-1 : ℝ) (π/2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (π/2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
    simpa [Function.comp_def, Function.uncurry] using h
  exact hU.continuousOn.mono
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_pos]⟩)

/-! ## `SmoothNbhd` of the slice subtraction -/



/-! ## The angular Hardy inequality for the oscillation away from `θ = 0` -/


/-! ## The radial Hardy inequality at almost every angle, `φ`-weighted -/


/-! ## `Z = ∫ sin(2θ)^{-η}` is bigger than `1` -/


/-! ## `VanishTheta` for mixed derivatives with positive `θ`-order -/




/-! ## The weight identities in integral form -/



/-! ## The `θ`-first forms of the two `H^4`-terms -/




end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.T2SliceHard =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The five "hard" summands in mixed-derivative form -/


/-- The angular weight of the `k = 0` term is `sin(2θ)^{-η}` (`η = 99/100 < 1`, so this
weight is integrable on `Iθ`). -/
theorem sghard_apply_zero (α θ : ℝ) :
    sghard α 0 θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

/-- The angular weight of a term with `k ≠ 0` is `sin(2θ)^{-γ}`, `γ = 1 + α/10`; the term
carries an additional second-order vanishing in `sin(2θ)`, so this weight is harmless. -/
theorem sghard_apply_ne (α : ℝ) (k : Fin 5) (hk : k.val ≠ 0) (θ : ℝ) :
    sghard α k θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  fin_cases k <;> simp_all [sghard]

/-! ## Each of the five summands is integrable in `θ` -/



end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.hard_sq_prod_mixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.hard_sq_prod_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology


end Work.FTS.H2
end
