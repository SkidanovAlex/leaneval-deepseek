import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Scaling.Defs
import Submission.Work.SolutionDelivery.Scaling.vorticity_rescale
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.BSSwirl.hasDerivAt_rotLE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

/-- **The `s`-derivative of the rotation about the `x₃`-axis is the angular vector field.**

Coordinatewise, `rotLE s x` is
`(cos s · x₀ - sin s · x₁, sin s · x₀ + cos s · x₁, x₂)`, whose `s`-derivative at `t` is
`(-sin t · x₀ - cos t · x₁, cos t · x₀ - sin t · x₁, 0)`.  At the rotated point
`y = rotLE t x` the angular vector is
`angularVec y = (-y₁, y₀, 0) = (-(sin t · x₀ + cos t · x₁), cos t · x₀ - sin t · x₁, 0)`,
which is the same vector.  This is the elementary instance of the identity
`d/dt (rotLE t) = J · rotLE t` (`J` = rotation by `π/2` in the `(x₀,x₁)`-plane) used to
transport the Biot–Savart law to the rotating frame. -/
theorem hasDerivAt_rotLE (t : ℝ) (x : Work.FTS.BSSwirl.R3) :
    HasDerivAt (fun s : ℝ => Work.ConstructionInstance.rotLE s x)
      (Work.Cyl.angularVec (Work.ConstructionInstance.rotLE t x)) t := by
  -- The coordinate vector `s ↦ rotCoord s x.ofLp` has the announced derivative componentwise.
  have hF : HasDerivAt (fun s : ℝ => Work.ConstructionInstance.rotCoord s x.ofLp)
      (fun i : Fin 3 =>
        (Work.Cyl.angularVec (Work.ConstructionInstance.rotLE t x)).ofLp i) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · show HasDerivAt (fun s : ℝ => Real.cos s * x.ofLp 0 - Real.sin s * x.ofLp 1)
          (-(Real.sin t * x.ofLp 0 + Real.cos t * x.ofLp 1)) t
      have h1 := (Real.hasDerivAt_cos t).mul_const (x.ofLp 0)
      have h2 := (Real.hasDerivAt_sin t).mul_const (x.ofLp 1)
      convert h1.sub h2 using 1
      ring
    · show HasDerivAt (fun s : ℝ => Real.sin s * x.ofLp 0 + Real.cos s * x.ofLp 1)
          (Real.cos t * x.ofLp 0 - Real.sin t * x.ofLp 1) t
      have h1 := (Real.hasDerivAt_sin t).mul_const (x.ofLp 0)
      have h2 := (Real.hasDerivAt_cos t).mul_const (x.ofLp 1)
      convert h1.add h2 using 1
      ring
    · show HasDerivAt (fun _ : ℝ => x.ofLp 2) 0 t
      exact hasDerivAt_const t (x.ofLp 2)
  -- Push the derivative through `WithLp.toLp` (a continuous linear equivalence).
  have hto := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (E := fun _ : Fin 3 => ℝ)
      (Work.ConstructionInstance.rotCoord t x.ofLp)).comp_hasDerivAt t hF
  simpa [Function.comp_def, Work.ConstructionInstance.rotLE_apply,
    PiLp.continuousLinearEquiv_symm_apply, WithLp.toLp_ofLp] using hto

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.norm_rotLE_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

open scoped Matrix

/-- The displacement of a rotation about the `x₃`-axis by the angle `h` is, in coordinates,
`((cos h - 1) x₀ - sin h x₁, sin h x₀ + (cos h - 1) x₁, 0)`. -/
theorem rotLE_sub_eq (h : ℝ) (x : Work.FTS.BSSwirl.R3) :
    Work.ConstructionInstance.rotLE h x - x
      = !₂[(Real.cos h - 1) * x 0 - Real.sin h * x 1,
           Real.sin h * x 0 + (Real.cos h - 1) * x 1, 0] := by
  ext i
  fin_cases i <;>
    simp [Work.ConstructionInstance.rotLE_apply, Work.ConstructionInstance.rotCoord] <;> ring

/-- Squared form of the displacement bound: the axis is fixed by `rotLE`, so the squared
displacement is `(2 - 2 cos h) r²`, where `r = Work.Cyl.radial x` is the distance to the axis. -/
theorem norm_rotLE_sub_sq (h : ℝ) (x : Work.FTS.BSSwirl.R3) :
    ‖Work.ConstructionInstance.rotLE h x - x‖ ^ 2
      = (2 - 2 * Real.cos h) * Work.Cyl.radSq x := by
  rw [rotLE_sub_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [Work.Cyl.radSq]
  norm_num
  ring_nf
  linear_combination ((x.ofLp 0) ^ 2 + (x.ofLp 1) ^ 2) * Real.cos_sq_add_sin_sq h

/-- **Rotation about the symmetry axis moves a point by at most `|h|` times its distance to the
axis.**  Since `rotLE h` is the rotation by the angle `h` about the `x₃`-axis, it fixes the axial
coordinate and rotates the planar part, so the displacement lies in the plane and its length is
`|x|·|e^{ih} - 1| = |x|·√(2 - 2 cos h) ≤ |x|·|h|`. -/
theorem norm_rotLE_sub_le (h : ℝ) (x : Work.FTS.BSSwirl.R3) :
    ‖Work.ConstructionInstance.rotLE h x - x‖ ≤ |h| * Work.Cyl.radial x := by
  have hle : (2 - 2 * Real.cos h) * Work.Cyl.radSq x ≤ h ^ 2 * Work.Cyl.radSq x := by
    have hc : 1 - h ^ 2 / 2 ≤ Real.cos h := Real.one_sub_sq_div_two_le_cos
    have hr : 0 ≤ Work.Cyl.radSq x := Work.Cyl.radSq_nonneg x
    nlinarith
  have hb : 0 ≤ |h| * Work.Cyl.radial x :=
    mul_nonneg (abs_nonneg h) (Work.Cyl.radial_nonneg x)
  have hsq : ‖Work.ConstructionInstance.rotLE h x - x‖ ^ 2
      ≤ (|h| * Work.Cyl.radial x) ^ 2 := by
    rw [norm_rotLE_sub_sq]
    have hsqr : (|h| * Work.Cyl.radial x) ^ 2 = h ^ 2 * Work.Cyl.radSq x := by
      rw [mul_pow, sq_abs, Work.Cyl.radial_sq]
    rw [hsqr]
    exact hle
  have h' := (sq_le_sq).mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hb] at h'

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.Cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The logarithmic cut-off, extended by zero to `z ≤ 0` -/

/-- The logarithmic cut-off `ZCuts.psiFun`, extended by `0` to `z ≤ 0`.  It is `C^∞` on
`(0,∞)`, lies in `[0,1]`, equals `1` on `[1/k, k]`, vanishes off `[1/k², k²]` (on the whole
line now), and satisfies `|z ζ'(z)| ≤ K / log k` for `z > 0`. -/
def zc (φ : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := fun z => if 0 < z then Work.FTS.EllipticEst.psiFun φ k z else 0
end Work.FTS.EllipticEst.Alpha4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sliceEtaPoincare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

/-!
# The weighted slice Poincaré inequality with the angular weight `sin(2θ)^{-η}`

For a function `u` that is `C^∞` on the open interval `(0, π/2)`, tends to `0` at both endpoints
and has `∫_{Iθ} (u'')² sin(2θ)^{-η} < ∞`, we prove that `u` and `u'` are square integrable against
the weight `sin(2θ)^{-η}` and that both weighted norms are controlled by the weighted norm of the
second derivative.  The proof writes `u' = c₀ + V` with `V = ∫_0^θ u''` the primitive of `u''`;
the constant `c₀` is pinned down by `∫_{Iθ} u' = 0` (a consequence of the vanishing endpoint
limits, via the fundamental theorem of calculus with limits) and is bounded by
`c₀² ≤ (2/π) ∫_{Iθ} V²`; the weighted Hardy inequality `HardyPrimEta` (primitive form) is then
applied to `g = u''` and to `g = u'`.
-/

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The iterated derivatives of a function that is `C^n` on the open interval `(0, π/2)` for every
`n` are again `C^m` there, for every `m`. -/
private theorem contDiffOn_iterate_deriv {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) (k : ℕ) :
    ∀ m : ℕ, ContDiffOn ℝ m ((deriv^[k]) u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  induction k with
  | zero => intro m; simpa using hu m
  | succ k ih =>
      intro m
      have h1 : ContDiffOn ℝ (m + 1) ((deriv^[k]) u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ih (m + 1)
      have h2 : ContDiffOn ℝ m (deriv ((deriv^[k]) u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.deriv_of_isOpen h1 isOpen_Ioo (by exact_mod_cast le_refl (m + 1))
      simpa only [Function.iterate_succ_apply'] using h2

/-- The first derivatives of a function in the class of the slice Poincaré lemma. -/
private theorem contDiffOn_deriv_one {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ m (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  simpa using contDiffOn_iterate_deriv hu 1 m

/-- The second derivatives of a function in the class of the slice Poincaré lemma. -/
private theorem contDiffOn_deriv_deriv {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ m (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  simpa using contDiffOn_iterate_deriv hu 2 m

/-- A closed unordered interval contained in `[0, π/2]` is contained in `Iθ`. -/
private theorem uIcc_subset_Iθ {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ Real.pi / 2)
    (hb' : b ≤ Real.pi / 2) : Set.uIcc a b ⊆ Work.Spaces.Iθ := by
  intro x hx
  exact ⟨le_trans (le_min ha hb) hx.1, le_trans hx.2 (max_le ha' hb')⟩

/-- An integrable function on `Iθ` is interval integrable on `[0, π/2]`. -/
private theorem intervalIntegrable_of_integrableOn_Iθ {f : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) :
    IntervalIntegrable f volume 0 (Real.pi / 2) := by
  have h' : MeasureTheory.IntegrableOn f (Set.uIcc (0 : ℝ) (Real.pi / 2)) volume := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2), ← Work.Spaces.Iθ]
    exact h
  exact h'.intervalIntegrable

theorem sliceEtaPoincare :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  obtain ⟨K, hKpos, hKmain⟩ := HardyPrimEta
  obtain ⟨hwint, hwle, hone, hwnn, hwcont⟩ := SliceEtaFacts
  refine ⟨(2 * 10 ^ 4 + 2) * (K + K ^ 2), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 2 * 10 ^ 4 + 2 := by norm_num
    have h2 : (0 : ℝ) < K + K ^ 2 := by nlinarith
    exact mul_pos h1 h2
  · intro u hu hlim0 hlim1 hint
    have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
    have hpi4 : (0 : ℝ) < Real.pi / 4 := by positivity
    -- the open interval and `Iθ` carry the same restricted measure
    have hIoo_ae : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
        = volume.restrict Work.Spaces.Iθ :=
      Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
    have hcontW : ContinuousOn (fun θ => Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      fun θ hθ => (hwcont θ hθ).continuousWithinAt
    have hone_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        1 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hone θ hθ
    -- smoothness of `u'` and `u''` on the open interval
    have hderiv1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u θ) θ :=
      fun θ hθ =>
        (((hu 1).differentiableOn_one).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hderiv2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (deriv u) (deriv (deriv u) θ) θ := fun θ hθ =>
      (((contDiffOn_deriv_one hu 1).differentiableOn_one).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hcontD1 : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_deriv_one hu 1).continuousOn
    have hcontD2 : ContinuousOn (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_deriv_deriv hu 1).continuousOn
    -- the weighted norm of `u''`
    set R : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hR
    have hRnn : 0 ≤ R := by
      rw [hR]
      exact setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (hwnn θ hθ))
    -- `(u'')²` and `u''` are integrable on `Iθ`
    have hu2sq_int : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) Work.Spaces.Iθ := by
      refine Integrable.mono'
        (g := fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) hint ?_ ?_
      · rw [← hIoo_ae]
        exact (hcontD2.pow 2).aestronglyMeasurable measurableSet_Ioo
      · filter_upwards [hone_ae] with θ hθ
        have h2 : (0 : ℝ) ≤ (deriv (deriv u) θ) ^ 2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg h2]
        nlinarith [h2, hθ]
    have hu2_int : IntegrableOn (fun θ => deriv (deriv u) θ) Work.Spaces.Iθ := by
      refine Integrable.mono'
        (g := fun θ => (1 / 2) * ((deriv (deriv u) θ) ^ 2 + 1)) ?_ ?_ ?_
      · exact (hu2sq_int.add (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))).const_mul
          (1 / 2)
      · rw [← hIoo_ae]
        exact hcontD2.aestronglyMeasurable measurableSet_Ioo
      · filter_upwards with θ
        rw [Real.norm_eq_abs]
        refine abs_le.2 ⟨?_, ?_⟩
        · nlinarith [sq_nonneg (deriv (deriv u) θ + 1)]
        · nlinarith [sq_nonneg (deriv (deriv u) θ - 1)]
    -- the primitive `V` of `u''`
    set V : ℝ → ℝ := fun θ => ∫ t in (0 : ℝ)..θ, deriv (deriv u) t with hV
    have hVval : ∀ θ : ℝ, V θ = ∫ t in (0 : ℝ)..θ, deriv (deriv u) t := fun θ => by simp [hV]
    have hVcont : ContinuousOn V Work.Spaces.Iθ := by
      have h : ContinuousOn (fun θ : ℝ => ∫ t in (0 : ℝ)..θ, deriv (deriv u) t)
          (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
        intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := Real.pi / 2)
          (f := fun t => deriv (deriv u) t) (by
            rw [Set.uIcc_of_le hpi.le, ← Work.Spaces.Iθ]; exact hu2_int)
      rwa [Set.uIcc_of_le hpi.le, ← Work.Spaces.Iθ] at h
    have hIθ_compact : IsCompact Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact isCompact_Icc
    obtain ⟨CV, hCV⟩ := hIθ_compact.exists_bound_of_continuousOn hVcont
    have hV2_int : IntegrableOn (fun θ => (V θ) ^ 2) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun _ : ℝ => (max CV 0) ^ 2) ?_ ?_ ?_
      · exact integrableOn_const (s := Work.Spaces.Iθ) (C := (max CV 0) ^ 2)
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      · exact (hVcont.pow 2).aestronglyMeasurable measurableSet_Icc
      · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with θ hθ
        have hb : ‖V θ‖ ≤ max CV 0 := (hCV θ hθ).trans (le_max_left _ _)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc (V θ) ^ 2 = ‖V θ‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
          _ ≤ (max CV 0) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hV_memLp : MemLp V 2 (volume.restrict Work.Spaces.Iθ) := by
      rw [memLp_two_iff_integrable_sq (hVcont.aestronglyMeasurable measurableSet_Icc)]
      exact hV2_int
    have h1_memLp : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := by
      rw [memLp_two_iff_integrable_sq aestronglyMeasurable_const]
      simpa using (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real_def,
        Work.Spaces.Iθ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    have hVsq_le : (∫ θ in Work.Spaces.Iθ, V θ) ^ 2 ≤ (Real.pi / 2)
        * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
      have hcs := Work.Spaces.cs_integral (u := V) (v := fun _ : ℝ => (1 : ℝ))
        (s := Work.Spaces.Iθ) hV_memLp h1_memLp
      simpa [mul_one, one_pow, hvol, mul_comm] using hcs
    -- the constant `c₀` and the identity `u' = c₀ + V`
    set c₀ : ℝ := deriv u (Real.pi / 4) - V (Real.pi / 4) with hc0
    have hFTCmid : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ∫ t in (Real.pi / 4)..θ, deriv (deriv u) t = deriv u θ - deriv u (Real.pi / 4) := by
      intro θ hθ
      have hsub1 : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
      have hsub2 : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
        ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩
      have hI1 : Set.uIcc (Real.pi / 4) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ (by positivity) hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have hI2 : Set.uIcc θ (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ hθ.1.le (by positivity) hθ.2.le (by linarith [Real.pi_pos])
      rcases le_total (Real.pi / 4) θ with hle | hle
      · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle (hcontD1.mono hsub1)
          (fun x hx => hderiv2 x (hsub1 ⟨hx.1.le, hx.2.le⟩))
          (hu2_int.mono_set hI1).intervalIntegrable
      · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle (hcontD1.mono hsub2)
          (fun x hx => hderiv2 x (hsub2 ⟨hx.1.le, hx.2.le⟩))
          (hu2_int.mono_set hI2).intervalIntegrable
        have hsym := intervalIntegral.integral_symm (μ := volume) (a := θ) (b := Real.pi / 4)
          (f := fun t => deriv (deriv u) t)
        linarith [h, hsym]
    have hdecomp : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv u θ = c₀ + V θ := by
      intro θ hθ
      have hI1 : Set.uIcc (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ le_rfl (by positivity) (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])
      have hI2 : Set.uIcc (Real.pi / 4) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ (by positivity) hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have hint1 : IntervalIntegrable (fun t => deriv (deriv u) t) volume (0 : ℝ)
          (Real.pi / 4) := (hu2_int.mono_set hI1).intervalIntegrable
      have hint2 : IntervalIntegrable (fun t => deriv (deriv u) t) volume (Real.pi / 4) θ :=
        (hu2_int.mono_set hI2).intervalIntegrable
      have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      rw [hVval θ, hc0, hVval (Real.pi / 4), ← hadd, hFTCmid θ hθ]
      ring
    -- `u'` is bounded, hence integrable
    have hderiv_bound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ‖deriv u θ‖ ≤ |c₀| + CV := by
      intro θ hθ
      have hVb : |V θ| ≤ CV := by
        have h := hCV θ (⟨hθ.1.le, hθ.2.le⟩ : θ ∈ Work.Spaces.Iθ)
        rwa [Real.norm_eq_abs] at h
      rw [hdecomp θ hθ, Real.norm_eq_abs]
      calc |c₀ + V θ| ≤ |c₀| + |V θ| := abs_add_le _ _
        _ ≤ |c₀| + CV := by linarith
    have hderiv_int : IntegrableOn (fun θ => deriv u θ) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun _ : ℝ => |c₀| + CV) ?_ ?_ ?_
      · exact integrableOn_const (s := Work.Spaces.Iθ) (C := |c₀| + CV)
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      · rw [← hIoo_ae]
        exact hcontD1.aestronglyMeasurable measurableSet_Ioo
      · rw [← hIoo_ae]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact hderiv_bound θ hθ
    -- `∫_{Iθ} u' = 0`, from the two vanishing endpoint limits
    have hzero : ∫ θ in (0 : ℝ)..(Real.pi / 2), deriv u θ = 0 := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
        (b := Real.pi / 2) (f := u) (f' := fun θ => deriv u θ) hpi hderiv1
        (intervalIntegrable_of_integrableOn_Iθ hderiv_int) hlim0 hlim1
      simpa using h
    have hkey : ∀ f : ℝ → ℝ,
        (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
      intro f
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hpi.le]
    -- the identity `c₀ = -(2/π) ∫_{Iθ} V`
    have hc0_eq : c₀ = -(2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, V θ := by
      have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
        rw [MeasureTheory.ae_iff]
        have hset : {x : ℝ | ¬(x ≠ Real.pi / 2)} = {Real.pi / 2} := by
          ext x; simp
        rw [hset]
        exact MeasureTheory.measure_singleton (Real.pi / 2)
      have hcongr_int : ∫ θ in (0 : ℝ)..(Real.pi / 2), deriv u θ
          = ∫ θ in (0 : ℝ)..(Real.pi / 2), (c₀ + V θ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hne] with x hx hmem
        rw [Set.uIoc_of_le hpi.le] at hmem
        exact hdecomp x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
      have hsplit : ∫ θ in (0 : ℝ)..(Real.pi / 2), (c₀ + V θ)
          = c₀ * (Real.pi / 2) + ∫ θ in (0 : ℝ)..(Real.pi / 2), V θ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (hVcont.intervalIntegrable_of_Icc hpi.le), intervalIntegral.integral_const]
        ring
      have hval : c₀ * (Real.pi / 2) + ∫ θ in (0 : ℝ)..(Real.pi / 2), V θ = 0 := by
        rw [← hsplit, ← hcongr_int, hzero]
      rw [hkey V] at ⊢
      rw [← hkey V] at hval
      field_simp at hval ⊢
      linarith
    -- `c₀²` is controlled by the weighted norm of `V`
    have hc0sq : c₀ ^ 2 ≤ (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
      have hsq : c₀ ^ 2 = (2 / Real.pi) ^ 2 * (∫ θ in Work.Spaces.Iθ, V θ) ^ 2 := by
        rw [hc0_eq]; ring
      rw [hsq]
      calc (2 / Real.pi) ^ 2 * (∫ θ in Work.Spaces.Iθ, V θ) ^ 2
          ≤ (2 / Real.pi) ^ 2 * ((Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hVsq_le (by positivity)
        _ = (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
            have hc : (2 / Real.pi) ^ 2 * (Real.pi / 2) = 2 / Real.pi := by field_simp
            rw [← mul_assoc, hc]
    -- the weighted Hardy inequality for the datum `u''`
    have hHard2 := hKmain (fun θ => deriv (deriv u) θ) hu2_int hint
      (fun θ hθ => hcontD2.continuousAt (isOpen_Ioo.mem_nhds hθ))
    have hfun_prim : (fun θ => (∫ t in (0 : ℝ)..θ, deriv (deriv u) t) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        = fun θ => (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      funext θ; rw [hVval θ]
    have hV2w_int : IntegrableOn
        (fun θ => (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      hHard2.1.congr (Filter.Eventually.of_forall (congrFun hfun_prim))
    have hV2w_le : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ K * R := by
      have h1 : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          = ∫ θ in Work.Spaces.Iθ,
              (∫ t in (0 : ℝ)..θ, deriv (deriv u) t) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        rw [hfun_prim]
      rw [h1, hR]
      exact hHard2.2
    have hV2_le_w : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      refine integral_mono_ae hV2_int hV2w_int ?_
      filter_upwards [hone_ae] with θ hθ
      nlinarith [sq_nonneg (V θ)]
    have hc0sq_le : c₀ ^ 2 ≤ K * R := by
      have h2π : (2 / Real.pi : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Real.pi_gt_three]
      have hKR : 0 ≤ K * R := mul_nonneg (le_of_lt hKpos) hRnn
      calc c₀ ^ 2 ≤ (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := hc0sq
        _ ≤ (2 / Real.pi) * (K * R) := by
            refine mul_le_mul_of_nonneg_left (le_trans hV2_le_w hV2w_le) (by positivity)
        _ ≤ K * R := by
            calc (2 / Real.pi) * (K * R) ≤ 1 * (K * R) :=
                  mul_le_mul_of_nonneg_right h2π hKR
              _ = K * R := one_mul _
    -- `u` is the primitive of `u'`
    have hu_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ = ∫ t in (0 : ℝ)..θ, deriv u t := by
      intro θ hθ
      have hcont : ContinuousAt u θ :=
        (hu 1).continuousOn.continuousAt (isOpen_Ioo.mem_nhds hθ)
      have hsub : Set.uIcc (0 : ℝ) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ le_rfl hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
        (b := θ) hθ.1 (fun x hx => hderiv1 x ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2.le⟩)
        (hderiv_int.mono_set hsub).intervalIntegrable hlim0
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      simpa using h.symm
    -- the weighted Hardy inequality for the datum `u'`
    have hdom_int : IntegrableOn
        (fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := by
      refine ((hwint.const_mul (2 * c₀ ^ 2)).add (hV2w_int.const_mul 2)).congr
        (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Pi.add_apply]
      ring
    have hae_dom : (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ) := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := hwnn θ ⟨hθ.1.le, hθ.2.le⟩
      have hpt : (deriv u θ) ^ 2 ≤ 2 * c₀ ^ 2 + 2 * (V θ) ^ 2 := by
        rw [hdecomp θ hθ]
        nlinarith [sq_nonneg (c₀ - V θ)]
      exact mul_le_mul_of_nonneg_right hpt hs
    have hderivsq_int : IntegrableOn
        (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ) hdom_int ?_ ?_
      · rw [← hIoo_ae]
        exact ((hcontD1.pow 2).mul hcontW).aestronglyMeasurable measurableSet_Ioo
      · rw [← hIoo_ae]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := hwnn θ ⟨hθ.1.le, hθ.2.le⟩
        have hpt : (deriv u θ) ^ 2 ≤ 2 * c₀ ^ 2 + 2 * (V θ) ^ 2 := by
          rw [hdecomp θ hθ]
          nlinarith [sq_nonneg (c₀ - V θ)]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
        exact mul_le_mul_of_nonneg_right hpt hs
    have hHard1 := hKmain (fun θ => deriv u θ) hderiv_int hderivsq_int
      (fun θ hθ => hcontD1.continuousAt (isOpen_Ioo.mem_nhds hθ))
    have hae_eq : (fun θ => (∫ t in (0 : ℝ)..θ, deriv u t) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      show (∫ t in (0 : ℝ)..θ, deriv u t) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [hu_eq θ hθ]
    have hu2w_int : IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := hHard1.1.congr hae_eq
    have hu2w_le : ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      rw [← integral_congr_ae hae_eq]
      exact hHard1.2
    -- `∫ (u')² w ≤ (2·10⁴ + 2) K R`
    have hderivsq_le : ∫ θ in Work.Spaces.Iθ,
        (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ (2 * 10 ^ 4 + 2) * K * R := by
      have hmono : ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ ∫ θ in Work.Spaces.Iθ,
              (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ :=
        integral_mono_ae hderivsq_int hdom_int hae_dom
      have hsplit2 : ∫ θ in Work.Spaces.Iθ,
          (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
          = (2 * c₀ ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
            + 2 * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        have hcongr : ∫ θ in Work.Spaces.Iθ,
            (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
            = ∫ θ in Work.Spaces.Iθ,
                ((2 * c₀ ^ 2) * Work.FTS.EllipticEst.sEta θ
                  + 2 * ((V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          show (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
            = (2 * c₀ ^ 2) * Work.FTS.EllipticEst.sEta θ
              + 2 * ((V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ring
        rw [hcongr, integral_add (hwint.const_mul (2 * c₀ ^ 2)) (hV2w_int.const_mul 2),
          integral_const_mul, integral_const_mul]
      rw [hsplit2] at hmono
      have hterm1 : (2 * c₀ ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          ≤ (2 * c₀ ^ 2) * 10 ^ 4 :=
        mul_le_mul_of_nonneg_left hwle (by positivity)
      have hterm2 : 2 * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ 2 * (K * R) := mul_le_mul_of_nonneg_left hV2w_le (by norm_num)
      have hcombine : (2 * c₀ ^ 2) * 10 ^ 4 + 2 * (K * R) ≤ (2 * 10 ^ 4 + 2) * K * R := by
        nlinarith [hc0sq_le, hRnn, hKpos]
      linarith [hmono, hterm1, hterm2, hcombine]
    refine ⟨hu2w_int, hderivsq_int, ?_, ?_⟩
    · have h1 : ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ K * ((2 * 10 ^ 4 + 2) * K * R) :=
        le_trans hu2w_le (mul_le_mul_of_nonneg_left hderivsq_le (le_of_lt hKpos))
      have h2 : K * ((2 * 10 ^ 4 + 2) * K * R) = (2 * 10 ^ 4 + 2) * K ^ 2 * R := by ring
      have h3 : (2 * 10 ^ 4 + 2) * K ^ 2 * R
          ≤ ((2 * 10 ^ 4 + 2) * (K + K ^ 2)) * R := by
        refine mul_le_mul_of_nonneg_right ?_ hRnn
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (le_of_lt hKpos)) (by norm_num)
      linarith [h1, h3, le_of_eq h2]
    · have hC : (2 * 10 ^ 4 + 2) * K ≤ (2 * 10 ^ 4 + 2) * (K + K ^ 2) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg K)) (by norm_num)
      exact le_trans hderivsq_le (mul_le_mul_of_nonneg_right hC hRnn)

end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.H2.T3Q.EasyMajorBoundQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T3Q

set_option maxHeartbeats 1000000

/-! ## The interior `f`-side pointwise bounds

These are the transport of `Work.FTS.H2.Transport3Aux.abs_dzIter_le_wlInf` /
`abs_mixed_le_wlInf` from the closed-quadrant class `Spaces.SmoothNbhd` to the interior class
`Work.FTS.LocData.SmoothQuad`, replacing the input by the interior-bound lemmas
`Work.FTS.H2.WPQ.DzIter_le_WlInf` (whose hypothesis is `θ ∈ Ioo 0 (π/2)`) and
`Work.FTS.H2.WPQ.Mixed_le_WlInf` (together with the slot comparison
`Work.FTS.H2.Transport3Aux.phi_le_two`). -/



/-! ## The absolute-value forms of the Leibniz summands -/



/-! ## The pointwise bound of the individual summands -/



/-! ## The assembly -/



end Work.FTS.H2.T3Q
end
end
-- ===== merged: Submission.Work.FTS.H2.T3Q.MultQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T3Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The multiplier bound on the open quadrant -/


/-! ## Vanishing of the pairing at the angular boundary -/



/-- The `ℋ⁴`-integrand vanishes at the angular boundary: both weights carry a positive
power of `sin(2θ)`. -/
theorem HkIntegrand_eq_zero_of_sin_two_eq_zero {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α 4 F z θ = 0 := by
  have hη : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [h, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)]
  have hγ : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) = 0 := by
    rw [h, Real.zero_rpow (by
      intro hc
      have h1 : Work.Spaces.gam α = 0 := by linarith [neg_eq_zero.mp hc]
      have h2 : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
      linarith)]
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, hη, hγ]
  simp



end Work.FTS.H2.T3Q
end
end
-- ===== merged: Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SupDzAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-
The uniform-in-`z` bound for the angular average of the pure `D_z`-derivatives of an open-class
`ℋ⁴` datum.  This is one of the two inputs of `Work.FTS.TransportS.sup_dz_le_hk`.

ROUTE (all ingredients are proved in the workspace):
1. `Work.FTS.TransportS.half_line_window_bound`
   (`Submission/Work/FTS/TransportS/SupDzAux/HalfLineWindow.lean`), applied slicewise in the
   angle `σ` to `h := fun x => Work.Spaces.DzIter b f x σ`, with
   `h' := fun x => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ`;
   note `x * h' x = Work.Spaces.DzIter (b+1) f x σ` (by `rfl`, `Work.Spaces.DzIter_succ`).
   Hypotheses of the window lemma, at the fixed angle `σ ∈ (0, π/2)`, a fixed `z > 0` and
   `R₀ ≥ z`:
   * `HasDerivAt` on `[z, 2R₀]`: `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice_DzIter`;
   * continuity of `h` and of `h'` on those intervals: `SmoothOpen.curry_z`;
   * integrability of `h²` on `[R₀, 2R₀]`: from the continuity of the slice on the compact
     interval `ContinuousOn.integrableOn_Icc`.
2. Pointwise domination on the open quadrant (`z > 0`, `0 < σ < π/2`):
   `(DzIter j f x σ)² * (w x)² ≤ HkIntegrand α 4 f x σ` for `j ≤ 4` is
   `Work.FTS.H2.dzIter_sq_w_le_HkIntegrand`; since `w ≥ 1` on `x > 0` this also gives
   `(DzIter j f x σ)² ≤ HkIntegrand α 4 f x σ` (`avgDzIter_sq_le` below).
3. For almost every `σ ∈ Iθ`, the σ-slice `x ↦ HkIntegrand α 4 f x σ` is integrable on
   `Work.Spaces.Iz`: Tonelli `Work.FTS.H2.swap_iterated_integral_of_nonneg` with the a.e.
   strong measurability supplied by `Work.Spaces.aesm_of_continuousOn_Qd` and
   `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`, and the two `HkMem` fields
   (`hmem.1`, `hmem.2`).  It also gives `∫_σ ∫_z HkIntegrand α 4 f = HkSq α 4 f`
   (`avgHkSqSwap` below).
4. Assemble: for a.e. `σ`, `h(z)² ≤ (2 + 2/R₀) * ∫_{x ∈ Iz} HkIntegrand α 4 f x σ`;
   integrate this a.e. inequality in `σ` over `Iθ` (both sides are integrable: the LHS by
   `hmem.1 z ⟨hz.le⟩` plus domination, the RHS by item 3) to get
   `∫_θ (DzIter b f z θ)² ≤ (2 + 2/R₀) * HkSq α 4 f` for every `R₀ ≥ z`; the choice
   `R₀ = max z 2` makes `2 + 2/R₀ ≤ 3`, so `C = 3` works.
-/

/-! ## Two auxiliary lemmas -/

/-- On the open quadrant, `(D_z^j f z θ)² ≤ HkIntegrand α 4 f z θ` for `j ≤ 4`: the plain
`D_z`-slot bound `dzIter_sq_w_le_HkIntegrand`, divided by `w² ≥ 1` at `z > 0`. -/
theorem avgDzIter_sq_le (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ 4) :
    (Work.Spaces.DzIter j f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have h := Work.FTS.H2.dzIter_sq_w_le_HkIntegrand (z := z) (θ := θ) α f hsin j hj
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  calc (Work.Spaces.DzIter j f z θ) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := h

/-- **Tonelli for the `ℋ⁴`-integrand of an open-class datum.**  For `f` of class `C^∞` on the
open quadrant with `HkMem α 4 f`, the iterated integral of `HkIntegrand α 4 f` in the order
`∫_θ ∫_z` equals `HkSq α 4 f`, its partially integrated function is integrable on the angles, and
for almost every angle the radial slice is integrable.  (The `SmoothOpen`-version of
`Work.FTS.H2.HkSqSwap`, whose hypothesis is the stronger, analytic `SmoothNbhd`.) -/
theorem avgHkSqSwap (α : ℝ) (f : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ
        = Work.Spaces.HkSq α 4 f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
          Work.Spaces.Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α 4)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  exact ⟨by rw [Work.Spaces.HkSq]; exact h1, h2, h3⟩

/-! ## The main estimate -/

theorem sup_dz_avg_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f → b ≤ 2 →
      ∀ z : ℝ, 0 < z →
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2
          ≤ C * Work.Spaces.HkSq α 4 f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f b hα hα1 hF hmem hb z hz
  obtain ⟨hswap, hGint, hGslice⟩ := avgHkSqSwap α f hF hmem
  -- almost every angle is interior
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo 0 (π/2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π/2)] with σ h
    exact fun hmem' => h.mpr hmem'
  -- the window bound, for every radius `R₀ ≥ z`
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π/2) →
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
          Work.Spaces.Iz →
        (Work.Spaces.DzIter b f z σ) ^ 2
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 < Real.sin (2 * σ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
      -- the hypotheses of the one-dimensional window inequality
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.DzIter b f x σ)
            (Work.Spaces.pz (Work.Spaces.DzIter b f) x σ) x :=
        fun x hx => hF.hasDerivAt_slice_DzIter b hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter b f x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        ((hF.DzIter b).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
          (Set.Icc z (2 * R₀)) :=
        (((hF.DzIter b).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : MeasureTheory.IntegrableOn
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
        (hcont.pow 2).integrableOn_Icc
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.DzIter b f x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
        hz hR hderiv hcont hcont' hint
      -- continuity of the two relevant slices on the window intervals
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x)
          (Set.Icc z (2 * R₀)) := by
        refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) ?_
        intro x hx
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
      have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.Icc z (2 * R₀)) := by
        have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
            Work.FTS.EllipticEst.Q0 :=
          fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
        have hc := (hF.continuousOn_HkIntegrand α 4).comp
          (continuousOn_id.prodMk continuousOn_const) hmap
        simpa only [Function.comp_def, id_eq] using hc
      have hIntL1 : IntervalIntegrable
          (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            * Work.Spaces.w x) ^ 2) volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            * Work.Spaces.w x) ^ 2) (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hcontW.pow 2
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2)
            (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hcont.pow 2
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      -- pointwise domination of the two window integrands
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            = Work.Spaces.DzIter (b + 1) f x σ := rfl
        rw [hcomm, mul_pow]
        exact Work.FTS.H2.dzIter_sq_w_le_HkIntegrand (z := x) (θ := σ) α f hsinσ (b + 1)
          (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Work.Spaces.DzIter b f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f x σ :=
        fun x hx => avgDzIter_sq_le α f (lt_of_lt_of_le hRpos hx.1) hsinσ b (by omega)
      -- the two window integrals are dominated by the full radial integral
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      calc (Work.Spaces.DzIter b f z σ) ^ 2
          ≤ 2 * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
              * Work.Spaces.w x) ^ 2)
            + (2 / R₀) * ∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter b f x σ) ^ 2 := hwin
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
            + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
              (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz,
              Work.Spaces.HkIntegrand α 4 f s σ) := by ring
    -- integrate the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.Integrable.mono' (hmem.1 z (show z ∈ Work.Spaces.Iz from le_of_lt hz))
        ?_ ?_
      · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2)
          ((hF.DzIter b).continuousOn) hz).pow 2
      · filter_upwards [Work.FTS.H2.ae_sin_two_pos] with σ hsin
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact avgDzIter_sq_le α f hz hsin b (by omega)
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          MeasureTheory.integral_mono_ae hLI (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by rw [hswap]
  -- take `R₀ = max z 2`, so that the coefficient is at most `3`
  have hzmax : z ≤ max z 2 := le_max_left z 2
  have hbnd := hbound (max z 2) hzmax
  have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
  have h2max : 2 ≤ max z 2 := le_max_right z 2
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ (2 + 2 / max z 2) * Work.Spaces.HkSq α 4 f := hbnd
    _ ≤ 3 * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

end Work.FTS.TransportS.SupDzAux
end
end
-- ===== merged: Submission.Work.R1G.HkIntegrand_gTest_expand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.HkMem_of_expBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.R1G

set_option linter.unusedVariables false


end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.bound_z_pz_gA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-!
# Boundedness of `z · ∂_z gA` on the quadrant

For the analytic perturbation `gA z θ = Zf z · Tf θ` (`Zf z = z²/(1+z²)⁴`, `Tf θ = sin (2θ)`)
we show that the weighted radial derivative `D_z gA = z ∂_z gA` is *bounded* on the quadrant
`z ≥ 0`, `θ ∈ [0,π/2]`, with the explicit (crude) constant `8`.

Indeed `∂_z gA z θ = Zf'(z) · Tf θ` (`pz_gA`), so

  `z · ∂_z gA z θ = (z · Zf'(z)) · Tf θ = Zf1 z · Tf θ`   (`Zf1_eq`),

and it remains to bound the rational function `Zf1 z = (2z² - 6z⁴)/(1+z²)⁵` and the angular
factor `|sin (2θ)| ≤ 1`.
-/



end Work.R1G
end
-- ===== merged: Submission.Work.R1G.gA_Tit_sq_mul_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G




end Work.R1G
end
-- ===== merged: Submission.Work.R1G.gA_Zit_mul_w_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- Elementary bound: for `z ≥ 0`, `(1+z)^4 ≤ 4 (1+z²)^4`.
Indeed `(1+z)^2 ≤ 2(1+z²)` (AM–GM) and `(1+z²)^2 ≤ (1+z²)^4`. -/
theorem one_add_pow_four_le (z : ℝ) (hz : 0 ≤ z) : (1 + z) ^ 4 ≤ 4 * (1 + z ^ 2) ^ 4 := by
  have hb : (1 : ℝ) ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have h1 : (1 + z) ^ 2 ≤ 2 * (1 + z ^ 2) := by nlinarith [sq_nonneg (1 - z)]
  have hub : (1 + z ^ 2) ^ 2 ≤ (1 + z ^ 2) ^ 4 :=
    pow_le_pow_right₀ hb (by norm_num : (2 : ℕ) ≤ 4)
  have h2 : ((1 + z) ^ 2) ^ 2 ≤ (2 * (1 + z ^ 2)) ^ 2 := by
    apply sq_le_sq' <;> nlinarith [h1, sq_nonneg z]
  have h3 : (2 * (1 + z ^ 2)) ^ 2 = 4 * (1 + z ^ 2) ^ 2 := by ring
  calc (1 + z) ^ 4 = ((1 + z) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (1 + z ^ 2)) ^ 2 := h2
    _ = 4 * (1 + z ^ 2) ^ 2 := h3
    _ ≤ 4 * (1 + z ^ 2) ^ 4 := by linarith [hub]



end Work.R1G
end
-- ===== merged: Submission.Work.R1G.gA_dz_slice_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.gTest_decayInZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Filter Topology
open scoped Topology

namespace Work.R1G



end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.gTest_holder_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G





end Work.R1G
end
-- ===== merged: Submission.Work.R1G.gTest_holder_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-! ## Elementary bounds on the radial factor `gPhi z = z²e^{-z}`

`gPhi` vanishes to second order at `0`, is entire and decays exponentially, so on `[0,∞)` it is
bounded (`|gPhi| ≤ 2`) with bounded derivative (`|gPhi'| ≤ 4`).  The two estimates are proved from
`s + 1 ≤ e^s` and `1 + s + s²/2 ≤ e^s` (`Real.sum_le_exp_of_nonneg`). -/







end Work.R1G
end
-- ===== merged: Submission.Work.R1G.gTest_hvan =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Set

namespace Work.R1G

/-! ## The radial factor -/


/-! ## The angular factor -/


/-! ## The estimate -/


end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.gTest_meas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.R1G


end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.gTest_profile_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G



end Work.R1G
end
-- ===== merged: Submission.Work.R1G.gTest_zpz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-! ## Auxiliary bounds for the proof of `gTest_zpz`

We bound the radial factor `z ↦ z · ∂_z gPhi z` using the elementary inequality
`1 + t ≤ e^t`, and the angular factor by `1 ≤ 1` on the quadrant.  The numerical
constant is deliberately crude; only its existence matters. -/






end Work.R1G
end
-- ===== merged: Submission.Work.R1G.hasDerivAt_profile_of_differentiable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.hkNorm_gTest_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Homogeneity of `HkNorm` in the amplitude of the visible test perturbation

The visible test perturbation `gTest c = c·z²e^{-z}·sin(2θ)` (`Work.R1G.GTest`) is the scalar
multiple `c • gTest 1` of the normalised one.  Since every operator entering the weighted `H^k`
integrand (`pz`, `pth`, `Dz`, `Dth`, `DzIter`, `DthIter`, `mixed`) is linear, the integrand
`HkIntegrand α k` is homogeneous of degree two in the amplitude, hence so is `HkSq`, and therefore
`HkNorm α 2 (gTest c) = c · HkNorm α 2 (gTest 1)` for `c ≥ 0` (the square root kills the sign, and
`|c| = c`).  This is the estimate requested here.

The proof is purely algebraic: the homogeneity of the integrand is proved for an arbitrary
`f : ℝ → ℝ → ℝ` (so it applies to any scalar multiple), and the two Lebesgue integrals are pulled
apart with `MeasureTheory.integral_const_mul`.
-/

namespace Work.R1G

/-! ## Unconditional `deriv`-linearity

`deriv_const_mul` in Mathlib needs differentiability; the statement below holds *unconditionally*,
because `deriv` is `0` at non-differentiable points (and if `fun y => c * f y` were differentiable
at a point where `f` is not, then `c ≠ 0` would make `f` differentiable there too).  This is what
lets the homogeneity of the integrand be proved without any regularity hypothesis on `f` (in
particular the `z < 0` region, which is irrelevant to the norms but still present in the
definitions, causes no trouble). -/

private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-! ## Pointwise linearity of the differential operators -/

private theorem pz_const_mul_prv (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_uncond]

private theorem Dz_const_mul_prv (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.Dz g z θ := by
  funext z θ
  simp only [Work.Spaces.Dz]
  rw [pz_const_mul_prv]
  ring

private theorem pth_const_mul_prv (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_uncond]

private theorem Dth_const_mul_prv (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.Dth g z θ := by
  funext z θ
  simp only [Work.Spaces.Dth]
  rw [pth_const_mul_prv]
  ring

private theorem DzIter_const_mul_prv (i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Work.Spaces.DzIter_succ, ih, Dz_const_mul_prv]

private theorem DthIter_const_mul_prv (i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Work.Spaces.DthIter_succ, ih, Dth_const_mul_prv]

private theorem mixed_const_mul_prv (j i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul_prv, DzIter_const_mul_prv]

/-! ## Homogeneity of the weighted integrand and of `HkSq` -/

/-- The weighted `H^k` integrand is homogeneous of degree two in the amplitude. -/
private theorem HkIntegrand_const_mul_prv (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ)
      = fun z θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  funext z θ
  simp only [Work.Spaces.HkIntegrand, DzIter_const_mul_prv, mixed_const_mul_prv]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (c * Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (c * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> ring
  rw [h1, h2, mul_add]



/-! ## The requested estimate -/


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.holderTh_gA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G





end Work.R1G
end
-- ===== merged: Submission.Work.R1G.holderZ_gA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-!
# Hölder continuity in `z` of the analytic perturbation `gA z θ = Zf z · Tf θ`

The goal is `|gA z θ - gA z' θ| ≤ L·|z - z'|^α` for `z, z' ≥ 0`, `θ ∈ Iθ` and `0 < α ≤ 1`.

Since `gA z θ - gA z' θ = (Zf z - Zf z')·Tf θ` and `|Tf θ| ≤ 1`, it suffices to control the radial
factor: `Zf` is smooth on the halfline with

* `|Zf| ≤ 1` on `[0,∞)` (so `|Zf z - Zf z'| ≤ 2`), and
* `|Zf'| ≤ 8` on `[0,∞)` (from the closed form `Zf'(z) = (2z - 6z³)/(1+z²)⁵`),

whence `|Zf z - Zf z'| ≤ 8|z - z'|` by the mean value inequality.  A Lipschitz function with these
two bounds is `α`-Hölder on `[0,∞)` for every `0 < α ≤ 1`: on `|z - z'| ≤ 1` use
`|z - z'| ≤ |z - z'|^α`, on `|z - z'| ≥ 1` use `2 ≤ 2|z - z'|^α ≤ 8|z - z'|^α`.

The constant `L = 8` therefore works for every `α ∈ (0,1]`.
-/




end Work.R1G
end
-- ===== merged: Submission.Work.R1G.van_gA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.SolutionDelivery.DatumCut.cutDatum_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.DatumCut


end Work.SolutionDelivery.DatumCut
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery.Scaling


end Work.SolutionDelivery.Scaling
end
end
