import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Computability.Reduce
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le
import Submission.Work.FTS.BSSwirl.NewtonPotentialAux
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.PhiStar.LinvI_solves
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.Regularity.profFullBounds
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-! ## The candidate partial derivatives of the spacetime Biot–Savart field

The reconstructed velocity of a spacetime vorticity `ω` is `(x,t) ↦ BS(ω(·,t)) x`
(`bsSTField`).  Its two partial derivatives are `bsXDeriv` (the Calderón–Zygmund derivative of the
slice `x ↦ BS(ω(·,t)) x`) and `bsTDeriv` (the time derivative `BS(∂ₜω(·,t)) x`, i.e. the linear map
`k ↦ k • BS(∂ₜω(·,t)) x`). -/

/-- The spacetime Biot–Savart field `(x,t) ↦ BS(ω(·,t)) x`, curried. -/
noncomputable def bsSTField (ω : Work.LWP.R3 → ℝ → Work.LWP.R3) (x : Work.LWP.R3) (t : ℝ) :
    Work.LWP.R3 :=
  Work.LWP.biotSavart (fun y => ω y t) x

/-- The candidate `x`-partial derivative of the spacetime Biot–Savart field, curried:
`(4π)⁻¹ • bsDerivCLM (ω(·,t)) ρ x`. -/
noncomputable def bsXDeriv (ω : Work.LWP.R3 → ℝ → Work.LWP.R3) (ρ : ℝ) (x : Work.LWP.R3)
    (t : ℝ) : Work.LWP.R3 →L[ℝ] Work.LWP.R3 :=
  (4 * Real.pi)⁻¹ • bsDerivCLM (fun y => ω y t) ρ x

/-- The candidate `t`-partial derivative of the spacetime Biot–Savart field, curried:
the one-dimensional derivative `BS(∂ₜω(·,t)) x`, as the linear map `k ↦ k • BS(∂ₜω(·,t)) x`. -/
noncomputable def bsTDeriv (ω : Work.LWP.R3 → ℝ → Work.LWP.R3) (x : Work.LWP.R3) (t : ℝ) :
    ℝ →L[ℝ] Work.LWP.R3 :=
  ContinuousLinearMap.toSpanSingleton ℝ
    (Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x)

/-! ## Elementary estimates -/

/-- A bound `‖v‖ ≤ N * |s|` may be replaced by `‖v‖ ≤ max N 0 * |s|` (for `N < 0` and `|s| > 0`
the original bound is impossible, so `v = 0`). -/
theorem norm_le_max_mul_abs {v : Work.LWP.R3} {N s : ℝ} (h : ‖v‖ ≤ N * |s|) :
    ‖v‖ ≤ max N 0 * |s| := by
  rcases le_or_gt 0 N with hN | hN
  · rwa [max_eq_left hN]
  · rw [max_eq_right (le_of_lt hN), zero_mul]
    by_contra hcon
    push_neg at hcon
    by_cases hs : |s| = 0
    · rw [hs, mul_zero] at h
      linarith [norm_nonneg v]
    · have hpos : 0 < |s| := lt_of_le_of_ne (abs_nonneg s) (Ne.symm hs)
      have : N * |s| < 0 := mul_neg_of_neg_of_pos hN hpos
      linarith [norm_nonneg v]

/-- A Hölder bound may be taken with the nonnegative constant `max C 0`: for `c > 0` a negative `C`
forces the two points to coincide. -/
theorem norm_sub_le_max_mul_rpow {v : Work.LWP.R3} {C c : ℝ} (hc : 0 < c)
    {a b : Work.LWP.R3} (h : ‖v‖ ≤ C * ‖a - b‖ ^ c) :
    ‖v‖ ≤ max C 0 * ‖a - b‖ ^ c := by
  rcases le_or_gt 0 C with hC | hC
  · rwa [max_eq_left hC]
  · rw [max_eq_right (le_of_lt hC), zero_mul]
    by_contra hcon
    push_neg at hcon
    rcases eq_or_ne a b with hab | hab
    · subst hab
      rw [sub_self, norm_zero, Real.zero_rpow (ne_of_gt hc), mul_zero] at h
      linarith [norm_nonneg v]
    · have hpos : 0 < ‖a - b‖ ^ c :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) c
      have : C * ‖a - b‖ ^ c < 0 := mul_neg_of_neg_of_pos hC hpos
      linarith [norm_nonneg v]

/-- If `f` obeys `‖f t - f t₀‖ ≤ N * |t - t₀|` on a neighbourhood `I` of `t₀`, then `f` is
continuous at `t₀`. -/
theorem continuousAt_of_norm_sub_le_mul_abs {f : ℝ → Work.LWP.R3} {I : Set ℝ} {N t₀ : ℝ}
    (hI : I ∈ 𝓝 t₀) (hlip : ∀ t ∈ I, ‖f t - f t₀‖ ≤ N * |t - t₀|) :
    ContinuousAt f t₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hI
  have hKpos : (0 : ℝ) < max N 0 + 1 := by positivity
  have hKnn : (0 : ℝ) ≤ max N 0 := le_max_right _ _
  refine ⟨min δ₁ (ε / (max N 0 + 1)), lt_min hδ₁ (by positivity), fun t ht => ?_⟩
  have ht₁ : dist t t₀ < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have htI : t ∈ I := hδ₁sub (by rwa [Metric.mem_ball, Real.dist_eq])
  have ht₂ : dist t t₀ < ε / (max N 0 + 1) := lt_of_lt_of_le ht (min_le_right _ _)
  rw [Real.dist_eq] at ht₂
  have hlt : max N 0 / (max N 0 + 1) < 1 := by rw [div_lt_one hKpos]; linarith
  calc dist (f t) (f t₀) = ‖f t - f t₀‖ := dist_eq_norm _ _
    _ ≤ max N 0 * |t - t₀| := norm_le_max_mul_abs (hlip t htI)
    _ ≤ max N 0 * (ε / (max N 0 + 1)) := mul_le_mul_of_nonneg_left ht₂.le hKnn
    _ = (max N 0 / (max N 0 + 1)) * ε := by ring
    _ < 1 * ε := mul_lt_mul_of_pos_right hlt hε
    _ = ε := one_mul ε

/-- **Joint continuity from a uniform `x`-Hölder bound and a uniform Lipschitz-in-time bound**:
`(x,t) ↦ ω x t` is continuous at `(x₀,t₀)`. -/
theorem continuousAt_uncurry_of_holder_lipschitz {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {I : Set ℝ} {c C M₁ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hM₁ : 0 ≤ M₁) (hI : I ∈ 𝓝 t₀) (ht₀ : t₀ ∈ I)
    (hhold : ∀ t ∈ I, ∀ a b : Work.LWP.R3, ‖ω a t - ω b t‖ ≤ C * ‖a - b‖ ^ c)
    (hlip : ∀ t ∈ I, ∀ s ∈ I, ∀ y : Work.LWP.R3, ‖ω y t - ω y s‖ ≤ M₁ * |t - s|) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω q.1 q.2) (x₀, t₀) := by
  obtain ⟨δI, hδI, hδIsub⟩ := Metric.mem_nhds_iff.mp hI
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hCpos : (0 : ℝ) < 2 * (C + 1) := by linarith
  have hMpos : (0 : ℝ) < 2 * (M₁ + 1) := by linarith
  have hεx : (0 : ℝ) < ε / (2 * (C + 1)) := div_pos hε hCpos
  have hεt : (0 : ℝ) < ε / (2 * (M₁ + 1)) := div_pos hε hMpos
  refine ⟨min (min 1 ((ε / (2 * (C + 1))) ^ (1 / c))) (min δI (ε / (2 * (M₁ + 1)))),
    lt_min (lt_min one_pos (Real.rpow_pos_of_pos hεx _)) (lt_min hδI hεt), fun q hq => ?_⟩
  have hdq : dist q (x₀, t₀) < min 1 ((ε / (2 * (C + 1))) ^ (1 / c)) :=
    lt_of_lt_of_le hq (min_le_left _ _)
  have hqt : dist q (x₀, t₀) < min δI (ε / (2 * (M₁ + 1))) :=
    lt_of_lt_of_le hq (min_le_right _ _)
  have hdx : dist q.1 x₀ ≤ dist q (x₀, t₀) := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hdt : dist q.2 t₀ ≤ dist q (x₀, t₀) := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hqx : ‖q.1 - x₀‖ < (ε / (2 * (C + 1))) ^ (1 / c) := by
    have h3 : dist q.1 x₀ < (ε / (2 * (C + 1))) ^ (1 / c) :=
      lt_of_lt_of_le (lt_of_le_of_lt hdx hdq) (min_le_right _ _)
    rwa [dist_eq_norm] at h3
  have hqtI : q.2 ∈ I := by
    have h3 : dist q.2 t₀ < δI := lt_of_lt_of_le (lt_of_le_of_lt hdt hqt) (min_le_left _ _)
    rw [Real.dist_eq] at h3
    exact hδIsub (by rwa [Metric.mem_ball, Real.dist_eq])
  have hqtε : |q.2 - t₀| < ε / (2 * (M₁ + 1)) := by
    have h3 : dist q.2 t₀ < ε / (2 * (M₁ + 1)) :=
      lt_of_lt_of_le (lt_of_le_of_lt hdt hqt) (min_le_right _ _)
    rwa [Real.dist_eq] at h3
  have hqpow : ‖q.1 - x₀‖ ^ c < ε / (2 * (C + 1)) := by
    have h2 := Real.rpow_lt_rpow (norm_nonneg _) hqx hc
    rwa [← Real.rpow_mul hεx.le, one_div, inv_mul_cancel₀ (ne_of_gt hc), Real.rpow_one] at h2
  have h1 : ‖ω q.1 q.2 - ω x₀ q.2‖ ≤ C * ‖q.1 - x₀‖ ^ c := hhold q.2 hqtI q.1 x₀
  have h2 : ‖ω x₀ q.2 - ω x₀ t₀‖ ≤ M₁ * |q.2 - t₀| := hlip q.2 hqtI t₀ ht₀ x₀
  have h3 : C * ‖q.1 - x₀‖ ^ c < ε / 2 := by
    calc C * ‖q.1 - x₀‖ ^ c ≤ (C + 1) * ‖q.1 - x₀‖ ^ c :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) c)
      _ < (C + 1) * (ε / (2 * (C + 1))) := mul_lt_mul_of_pos_left hqpow (by linarith)
      _ = ε / 2 := by field_simp
  have h4 : M₁ * |q.2 - t₀| < ε / 2 := by
    calc M₁ * |q.2 - t₀| ≤ (M₁ + 1) * |q.2 - t₀| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (M₁ + 1) * (ε / (2 * (M₁ + 1))) := mul_lt_mul_of_pos_left hqtε (by linarith)
      _ = ε / 2 := by field_simp
  calc dist (ω q.1 q.2) (ω x₀ t₀) = ‖ω q.1 q.2 - ω x₀ t₀‖ := dist_eq_norm _ _
    _ ≤ ‖ω q.1 q.2 - ω x₀ q.2‖ + ‖ω x₀ q.2 - ω x₀ t₀‖ := by
        have heq : ω q.1 q.2 - ω x₀ t₀
            = (ω q.1 q.2 - ω x₀ q.2) + (ω x₀ q.2 - ω x₀ t₀) := by abel
        rw [heq]; exact norm_add_le _ _
    _ ≤ C * ‖q.1 - x₀‖ ^ c + M₁ * |q.2 - t₀| := add_le_add h1 h2
    _ < ε / 2 + ε / 2 := add_lt_add h3 h4
    _ = ε := by ring

/-- **The `t`-derivative of the spacetime Biot–Savart field.**  Immediate from
`Work.StabilityFar.Decay.hasDerivAt_biotSavart`, together with the identification of a
one-dimensional derivative with a Fréchet derivative (`HasDerivAt.hasFDerivAt`). -/
theorem hasFDerivAt_bsSTField_time {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R M M₁ ε t : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hε : 0 < ε)
    (hbdd : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y, ‖ω y s‖ ≤ M)
    (hbdd' : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ M₁)
    (hdc : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      HasDerivAt (fun s' => ω y s') (FiniteTimeSingularity.timeDeriv ω y s) s)
    (hsupp : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y, ω y s ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      MeasureTheory.AEStronglyMeasurable (ω · s) MeasureTheory.volume)
    (x : Work.LWP.R3) :
    HasFDerivAt (fun s : ℝ => bsSTField ω x s) (bsTDeriv ω x t) t := by
  simpa [bsTDeriv, bsSTField] using
    (Work.StabilityFar.Decay.hasDerivAt_biotSavart hR hM hM₁ hε hbdd hbdd' hdc hsupp hmeas x).hasFDerivAt

/-! ## The main theorem -/


end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_fderiv_timeHolder_of_bundle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology
open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-! ### The mean-value/two-slice Hölder bound in the norm form -/

/-- `HolderWith` in the `dist` form, rewritten as a norm inequality. -/
theorem holder_norm_le {α : NNReal} {H : NNReal} {f : Work.LWP.R3 → Work.LWP.R3}
    (h : HolderWith H α f) (x y : Work.LWP.R3) :
    ‖f x - f y‖ ≤ (H : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
  have h1 := h.dist_le x y
  rw [dist_eq_norm, dist_eq_norm] at h1
  exact h1

/-- **The `t`-Hölder continuity of the spatial block of the derivative, for a bundled strip vorticity.**

Let `0 < α < 1` and let `ω` satisfy the full strip bundle `BSAdmissibleStripFull α ω R S`
(`BSAdmissibleStrip α ω R S`: support in `closedBall 0 R`, uniform bound `M`, uniform `x`-Hölder with
constant `H`, uniform `t`-Hölder with constant `N`, measurable slices; `TimeDerivStrip ω S`: slices
`t`-differentiable with uniformly bounded `∂ₜω`, bound `M₁`, measurable; `TimeDerivStripHolder α ω S`:
`∂ₜω` is `α`-Hölder in `t`, uniformly in `x`, constant `N₁`).

Claim: on any ball `‖x‖ ≤ R'` the spatial block `x ↦ fderiv ℝ (BS (ω · t)) x` is `α`-Hölder in `t`,
uniformly in `x`: `∃ C ≥ 0, ∀ x, ‖x‖ ≤ R' → ∀ t t' ∈ Icc 0 S,
‖fderiv ℝ (BS (ω·t)) x - fderiv ℝ (BS (ω·t')) x‖ ≤ C |t-t'|^α`.

This is the crux of the space-time Schauder statement.  **Suggested route** (reportedly it closes):
write `g := ω(·,t) - ω(·,t')`, `δ := |t-t'|`.  By linearity the quantity is `‖fderiv ℝ (BS g) x‖`, and
the bundle gives, *uniformly in `t,t'`*: `supp g ⊆ closedBall 0 R`, `[g]_{C^α} ≤ 2H`,
`A := ‖g‖_∞ ≤ min(Nδ^α, M₁δ)` (the second from the mean-value bound
`norm_sub_le_of_timeDerivBound` applied to the uniform `∂ₜω`-bound `M₁` — this is the ingredient that
makes the estimate true; without it the corresponding "order-`0` CZ is `L^∞`-bounded" claim is false).
For `R + ‖x‖ < ρ` we have `fderiv ℝ (BS g) x = (4π)⁻¹ bsDerivCLM g ρ x`, i.e. the peeled integral
`∫_{B(x,ρ)} crossL (g a - g x) ∘ kDerivCLM (x-a) da + (4π/3) crossL (g x)`, whose norm is at most
`(4π)⁻¹(16π ∫_0^ρ min(2A, 2H r^α) r⁻¹ dr + (4π/3) A)`.  Splitting the integral at `λ := (A/(2H))^{1/α}`
(so `2Hλ^α = A`) gives the bound `C(α) A (1 + log(ρ/λ)) = C(α) A (1 + log ρ + (1/α) log(2H/A))`.
Since `A ↦ A log(2H/A)` is increasing for small `A` and `A ≤ min(Nδ^α, M₁δ)`, there are two regimes:
`δ ≥ (N/M₁)^{1/(1-α)}` gives `C(α)N log(2H/(Nδ^α))·δ^α ≤ C(α,data) δ^α`, and
`δ < (N/M₁)^{1/(1-α)}` gives `C(α)M₁δ(1+log(ρ/(M₁δ)^{1/α})) ≤ C(α,data) δ^α` by the classical
`δ log(1/δ) ≤ C(α)δ^α` for `α < 1`.  Hence the claimed estimate with a constant depending only on
`α, R, R', M, H, N, M₁, N₁, S`.  (The `x`-direction, the whole `t`-block and the `C¹` clause are
separate; the far field `2R < ‖x‖` is handled by the decay estimates.)

**Actual route used** (avoids the logarithmic split entirely): the bound on the peeled integral is
obtained by interpolating the two pointwise bounds `‖g a - g x‖ ≤ 2A` and
`‖g a - g x‖ ≤ 2H‖a - x‖^α` as
`min(2A, 2H‖a-x‖^α) ≤ (2A)^α (2H‖a-x‖^α)^{1-α}`, which upgrades the singular weight `‖a-x‖^{-3}`
to the integrable `‖a-x‖^{α(1-α)-3}`; the ball integral is then
`4(2A)^α(2H)^{1-α}·4π(ρ+‖x‖)^{α(1-α)}/(α(1-α))` (`integral_ball_sub_norm_rpow`).  With `A = M₀·δ`
(`M₀ = max M₁ 0`) this is `O(δ^α)` directly.  The two ingredients are
`norm_bsDerivCLM_le_of_bdd_holder` and `bsDerivCLM_bound_arith` (delegated, in this directory). -/
theorem biotSavart_fderiv_timeHolder_of_bundle {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S R' : ℝ}
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Work.LWP.R3, ‖x‖ ≤ R' →
      ∀ t ∈ Set.Icc (0:ℝ) S, ∀ t' ∈ Set.Icc (0:ℝ) S,
        ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
          - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t')) x‖
          ≤ C * |t - t'| ^ (α : ℝ) := by
  obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩, ⟨hdc, ⟨M₁, hM₁⟩, hmeasd⟩, ⟨N₁, hN₁⟩⟩ :=
    hbun
  set M₀ : ℝ := max M₁ 0 with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact le_max_right M₁ 0
  set H₀ : ℝ := (H : ℝ) with hH₀def
  have hH₀nn : 0 ≤ H₀ := by rw [hH₀def]; positivity
  set P : ℝ := max 0 (R + 2 * R' + 1) with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; exact le_max_left 0 (R + 2 * R' + 1)
  set C₀ : ℝ := 4 * (2 * M₀) ^ (α : ℝ) * (2 * H₀) ^ (1 - (α : ℝ)) *
        (4 * Real.pi * P ^ ((α : ℝ) * (1 - (α : ℝ))) / ((α : ℝ) * (1 - (α : ℝ))))
      + (4 * Real.pi / 3) * (M₀ * max 1 S) with hC₀def
  refine ⟨(4 * Real.pi)⁻¹ * C₀, ?_, ?_⟩
  · have h4π : (0:ℝ) < 4 * Real.pi := by positivity
    have hnum : (0:ℝ) < (α : ℝ) * (1 - (α : ℝ)) := mul_pos hα (by linarith)
    have h2M : 0 ≤ 2 * M₀ := by linarith
    have h2H : 0 ≤ 2 * H₀ := by linarith
    have h1 : 0 ≤ (2 * M₀) ^ (α : ℝ) := Real.rpow_nonneg h2M _
    have h2 : 0 ≤ (2 * H₀) ^ (1 - (α : ℝ)) := Real.rpow_nonneg h2H _
    have h3 : 0 ≤ P ^ ((α : ℝ) * (1 - (α : ℝ))) := Real.rpow_nonneg hPnn _
    have h5 : 0 ≤ M₀ * max 1 S := by positivity
    have hC0 : 0 ≤ C₀ := by
      rw [hC₀def]
      have h6 : (0:ℝ) ≤ 4 * Real.pi * P ^ ((α:ℝ) * (1 - (α:ℝ))) / ((α:ℝ) * (1 - (α:ℝ))) :=
        div_nonneg (by positivity) hnum.le
      have h7 : (0:ℝ) ≤ 4 * (2 * M₀) ^ (α:ℝ) * (2 * H₀) ^ (1 - (α:ℝ)) :=
        mul_nonneg (by positivity) h2
      have h8 : (0:ℝ) ≤ 4 * (2 * M₀) ^ (α:ℝ) * (2 * H₀) ^ (1 - (α:ℝ)) *
          (4 * Real.pi * P ^ ((α:ℝ) * (1 - (α:ℝ))) / ((α:ℝ) * (1 - (α:ℝ)))) :=
        mul_nonneg h7 h6
      have h9 : (0:ℝ) ≤ 4 * Real.pi / 3 * (M₀ * max 1 S) := mul_nonneg (by positivity) h5
      linarith
    have : (0:ℝ) ≤ (4 * Real.pi)⁻¹ := by positivity
    exact mul_nonneg this hC0
  · intro x hx t ht t' ht'
    have ht0 : 0 ≤ t := ht.1
    have htS : t ≤ S := ht.2
    have ht'0 : 0 ≤ t' := ht'.1
    have ht'S : t' ≤ S := ht'.2
    set δ : ℝ := |t - t'| with hδdef
    have hδnn : 0 ≤ δ := by rw [hδdef]; exact abs_nonneg _
    have hδS : δ ≤ S := by
      rw [hδdef, abs_le]
      exact ⟨by linarith, by linarith⟩
    -- the vorticity bundle facts for the slices
    have hMnn : 0 ≤ M := le_trans (norm_nonneg (ω 0 t)) (hM t ht 0)
    have hslice : ∀ s ∈ Set.Icc (0:ℝ) S, ∀ a b : Work.LWP.R3,
        ‖ω a s - ω b s‖ ≤ H₀ * ‖a - b‖ ^ (α : ℝ) := by
      intro s hs a b
      rw [hH₀def]
      exact holder_norm_le (hH s hs) a b
    -- the difference field
    set g : Work.LWP.R3 → Work.LWP.R3 := fun a => ω a t - ω a t' with hgdef
    have hg_bdd : ∀ a, ‖g a‖ ≤ M₀ * δ := by
      intro a
      have h := norm_sub_le_of_timeDeriv_bound hM₀nn (convex_Icc (0:ℝ) S)
        (fun s hs y => hdc s hs y) (fun s hs y => le_trans (hM₁ s hs y) (le_max_left M₁ 0))
        t ht t' ht' a
      rw [hδdef]
      simpa only [hgdef] using h
    have hg_holder : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ 2 * H₀ * ‖a - b‖ ^ (α : ℝ) := by
      intro a b
      have h1 := hslice t ht a b
      have h2 := hslice t' ht' a b
      have hkey : g a - g b = (ω a t - ω b t) - (ω a t' - ω b t') := by
        simp only [hgdef]; abel
      rw [hkey]
      calc ‖(ω a t - ω b t) - (ω a t' - ω b t')‖
          ≤ ‖ω a t - ω b t‖ + ‖ω a t' - ω b t'‖ := norm_sub_le _ _
        _ ≤ H₀ * ‖a - b‖ ^ (α : ℝ) + H₀ * ‖a - b‖ ^ (α : ℝ) := add_le_add h1 h2
        _ = 2 * H₀ * ‖a - b‖ ^ (α : ℝ) := by ring
    have hg_supp : ∀ a, g a ≠ 0 → a ∈ Metric.closedBall 0 R := by
      intro a ha
      by_cases h1 : ω a t = 0
      · refine hsupp t' ht' a ?_
        intro hc
        exact ha (by simp only [hgdef, h1, hc, sub_zero])
      · exact hsupp t ht a h1
    have hg_meas : AEStronglyMeasurable g volume := by
      have h := (hmeas t ht).sub (hmeas t' ht')
      have h' : AEStronglyMeasurable (fun a : Work.LWP.R3 => ω a t - ω a t') volume := h
      rwa [hgdef]
    -- the ball radius
    set ρ : ℝ := R + ‖x‖ + 1 with hρdef
    have hρx : R + ‖x‖ < ρ := by rw [hρdef]; linarith
    have hρnn : 0 ≤ ρ := by rw [hρdef]; linarith [norm_nonneg x, hR]
    have hA : 0 ≤ M₀ * δ := mul_nonneg hM₀nn hδnn
    -- derivatives of the three fields
    have hfd_g : HasFDerivAt (Work.LWP.biotSavart g) ((4 * Real.pi)⁻¹ • bsDerivCLM g ρ x) x :=
      hasFDerivAt_biotSavart_slice (ω := g) (R := R) (M := M₀ * δ) (C := 2 * H₀)
        (c := (α : ℝ)) (ρ := ρ) hR hA hα hg_bdd hg_supp hg_meas hg_holder hρx
    have hfd_t : HasFDerivAt (Work.LWP.biotSavart (fun a => ω a t))
        ((4 * Real.pi)⁻¹ • bsDerivCLM (fun a => ω a t) ρ x) x :=
      hasFDerivAt_biotSavart_slice (ω := fun a => ω a t) (R := R) (M := M) (C := H₀)
        (c := (α : ℝ)) (ρ := ρ) hR hMnn hα (hM t ht) (hsupp t ht) (hmeas t ht)
        (hslice t ht) hρx
    have hfd_t' : HasFDerivAt (Work.LWP.biotSavart (fun a => ω a t'))
        ((4 * Real.pi)⁻¹ • bsDerivCLM (fun a => ω a t') ρ x) x :=
      hasFDerivAt_biotSavart_slice (ω := fun a => ω a t') (R := R) (M := M) (C := H₀)
        (c := (α : ℝ)) (ρ := ρ) hR hMnn hα (hM t' ht') (hsupp t' ht') (hmeas t' ht')
        (hslice t' ht') hρx
    -- linearity: `BS g = BS(ω·t) - BS(ω·t')`
    have hpt : ∀ y : Work.LWP.R3,
        Work.LWP.biotSavart (fun a => ω a t) y - Work.LWP.biotSavart (fun a => ω a t') y
          = Work.LWP.biotSavart g y := by
      intro y
      have h1 : Work.LWP.biotSavart (fun a => g a + ω a t') y
          = Work.LWP.biotSavart g y + Work.LWP.biotSavart (fun a => ω a t') y :=
        biotSavart_add hg_bdd (hM t' ht') hg_supp (hsupp t' ht') hg_meas (hmeas t' ht') y
      have h2 : (fun a => g a + ω a t') = fun a => ω a t := by
        funext a; simp only [hgdef]; abel
      rw [h2] at h1
      rw [h1]; abel
    have hfd_eq : fderiv ℝ (Work.LWP.biotSavart g) x
        = fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
          - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t')) x := by
      have heq : (fun y => Work.LWP.biotSavart (fun a => ω a t) y
            - Work.LWP.biotSavart (fun a => ω a t') y)
          =ᶠ[𝓝 x] Work.LWP.biotSavart g := Filter.Eventually.of_forall hpt
      have h1 : fderiv ℝ (fun y => Work.LWP.biotSavart (fun a => ω a t) y
            - Work.LWP.biotSavart (fun a => ω a t') y) x
          = fderiv ℝ (Work.LWP.biotSavart g) x := Filter.EventuallyEq.fderiv_eq heq
      rw [← h1]
      change fderiv ℝ ((Work.LWP.biotSavart (fun a => ω a t))
        - (Work.LWP.biotSavart (fun a => ω a t'))) x
          = fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
            - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t')) x
      rw [fderiv_sub hfd_t.differentiableAt hfd_t'.differentiableAt]
    -- the CLM bound for the difference field
    have hQnn : 0 ≤ ρ + ‖x‖ := by linarith [norm_nonneg x, hρnn]
    have hQP : ρ + ‖x‖ ≤ P := by
      rw [hρdef, hPdef]
      refine le_trans ?_ (le_max_right 0 (R + 2 * R' + 1))
      linarith [norm_nonneg x]
    have hbound : ‖bsDerivCLM g ρ x‖ ≤ C₀ * δ ^ (α : ℝ) := by
      have hL := norm_bsDerivCLM_le_of_bdd_holder hα hα1 hA hH₀nn hρnn hg_bdd hg_holder x
      have harith := bsDerivCLM_bound_arith hα hα1 hδnn hδS hM₀nn hH₀nn hQnn hQP hPnn
      rw [hC₀def]
      exact le_trans hL harith
    calc ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
            - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t')) x‖
        = ‖(4 * Real.pi)⁻¹ • bsDerivCLM g ρ x‖ := by
          rw [← hfd_eq, hfd_g.fderiv]
      _ = (4 * Real.pi)⁻¹ * ‖bsDerivCLM g ρ x‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ (4 * Real.pi)⁻¹ * (C₀ * δ ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ((4 * Real.pi)⁻¹ * C₀) * |t - t'| ^ (α : ℝ) := by
          rw [hδdef]; ring

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.bundleSliceFderiv_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Set Filter Topology
open scoped Topology
open Work.StabilityFar.Decay (kDerivCLM kf crossL)

/-! ## 1. The pointwise splitting of the peeled integrand -/

/-- **Pointwise algebra of the two peeled integrands.**  The difference of the two derivative
integrands is the sum of the "constant vector times kernel" term and the
"kernel difference times Hölder difference" term:
`Λ(ω a - ω x)∘K(x-a) - Λ(ω a - ω y)∘K(y-a)
   = Λ(ω y - ω x)∘K(x-a) + Λ(ω a - ω y)∘(K(x-a) - K(y-a))`. -/
theorem bsIntegrand_sub_eq (g : R3 → R3) (x y a : R3) :
    bsIntegrand g x a - bsIntegrand g y a
      = (crossL (g y - g x)).comp (kDerivCLM (x - a))
        + (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a)) := by
  have hcomp : ∀ (A B K K' : R3 →L[ℝ] R3),
      A.comp K - B.comp K' = (A - B).comp K + B.comp (K - K') := by
    intro A B K K'
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  have hAB : crossL (g a - g x) - crossL (g a - g y) = crossL (g y - g x) := by
    rw [← Work.StabilityFar.Decay.crossL_sub]
    congr 1
    abel
  simp only [bsIntegrand]
  rw [hcomp, hAB]

/-! ## 2. Integrability of the shifted kernel on a ball-minus-ball region -/

/-- The kernel `a ↦ kDerivCLM (x - a)` is Bochner integrable on
`B(0,ρ) \ B(y,2δ)` whenever `0 < δ` and `‖x - y‖ ≤ δ`: the region stays at distance at least
`δ` from `x`, so the integrand is bounded by `4/δ³` there, and the region has finite volume. -/
theorem integrableOn_kDerivCLM_sub_diff_ball {x y : R3} {ρ δ : ℝ} (hδ : 0 < δ)
    (hxy : ‖x - y‖ ≤ δ) :
    IntegrableOn (fun a : R3 => kDerivCLM (x - a))
      ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume := by
  have hmeas : MeasurableSet ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) :=
    measurableSet_ball.diff measurableSet_ball
  refine MeasureTheory.IntegrableOn.of_bound (f := fun a : R3 => kDerivCLM (x - a)) ?hfin ?hmeas
    (4 / δ ^ 3) ?hbd
  · refine lt_of_le_of_lt (measure_mono ?_) ((isCompact_closedBall (0 : R3) ρ).measure_lt_top)
    intro a ha
    have h1 : a ∈ Metric.ball (0 : R3) ρ := (Set.mem_sdiff a).mp ha |>.1
    rw [Metric.mem_ball, dist_zero_right] at h1
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt h1
  · exact ((Work.StabilityFar.Decay.measurable_kDerivCLM_sub x).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  · rw [MeasureTheory.ae_restrict_iff' hmeas]
    refine Filter.Eventually.of_forall fun a ha => ?_
    have h1 : 2 * δ ≤ ‖a - y‖ := by
      have h2 : a ∉ Metric.ball y (2 * δ) := (Set.mem_sdiff a).mp ha |>.2
      rw [Metric.mem_ball] at h2
      have h3 := not_lt.mp h2
      rwa [dist_eq_norm] at h3
    have h3 : ‖a - y‖ ≤ ‖a - x‖ + ‖x - y‖ := by
      have heq : a - y = (a - x) + (x - y) := by abel
      rw [heq]
      exact norm_add_le _ _
    have h2 : δ ≤ ‖x - a‖ := by
      rw [norm_sub_rev a x] at h3
      linarith
    exact Work.StabilityFar.Decay.norm_kDerivCLM_le (x - a) δ hδ h2

/-! ## 3. The uniform-in-the-field Calderón–Zygmund difference estimate -/

/-- **The Schauder difference estimate for `bsDerivCLM`, uniform in the field.**

For `0 < α < 1`, `R > 0`, `M, C ≥ 0` and fixed `R'`, there is `K ≥ 0` — depending only on
`R, M, C, α, R'` and *not* on the field — such that for every `α`-Hölder field `g` bounded by `M`,

`‖bsDerivCLM g (R+R'+1) x - bsDerivCLM g (R+R'+1) y‖ ≤ K ‖x-y‖^α` for `‖x‖, ‖y‖ ≤ R'`.

The proof is the Calderón–Zygmund argument: for `δ := ‖x-y‖ ≤ 1/4` split the peeled integral
over `B(0,ρ)` at the ball `B(y,2δ)`; the near part is bounded by
`4C(4π/α)((3δ)^α + (2δ)^α)`, the far part splits into the constant-vector term
`Λ(g y - g x)∘∫K(x-a)` (bounded uniformly by the mean-zero property of the kernel over centred
annuli) and the kernel-difference term (bounded by `1024 C δ (4π (2δ)^{α-1}/(1-α))`); the shape
term contributes `(4π/3) C δ^α`.  For `δ ≥ 1/4` both derivatives are bounded by the interpolation
bound `norm_bsDerivCLM_le_of_bdd_holder`. -/
theorem bsDerivCLM_sub_holder_uniform {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {R M C R' : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : R3 → R3),
      (∀ a, ‖g a‖ ≤ M) →
      (∀ a b : R3, ‖g a - g b‖ ≤ C * ‖a - b‖ ^ (α : ℝ)) →
      ∀ x y : R3, ‖x‖ ≤ R' → ‖y‖ ≤ R' →
        ‖bsDerivCLM g (R + R' + 1) x - bsDerivCLM g (R + R' + 1) y‖
          ≤ K * ‖x - y‖ ^ (α : ℝ) := by
  classical
  by_cases hR'neg : R' < 0
  · refine ⟨0, le_refl 0, fun g hbdd hhold x y hx hy => ?_⟩
    rw [zero_mul]
    exact absurd hx (not_le.mpr (by linarith [norm_nonneg x, hR'neg]))
  set ρ : ℝ := R + R' + 1 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hexp : 0 < (α : ℝ) * (1 - (α : ℝ)) := by nlinarith
  -- the uniform interpolation bound on each derivative
  set B : ℝ := 4 * (2 * M) ^ (α : ℝ) * (2 * C) ^ (1 - (α : ℝ)) *
      (4 * Real.pi * (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ))) / ((α : ℝ) * (1 - (α : ℝ))))
      + (4 * Real.pi / 3) * M with hBdef
  -- the constants of the near-field bound
  set Kv : ℝ := (16 * Real.pi / 3) * ((ρ + R') ^ 3 / (ρ - R') ^ 3)
      + (16 * Real.pi / 3) * 27 with hKvdef
  set smallK : ℝ := 4 * C * (4 * Real.pi / (α : ℝ)) * ((3 : ℝ) ^ (α : ℝ) + (2 : ℝ) ^ (α : ℝ))
      + 1024 * C * (4 * Real.pi * (2 : ℝ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ)))
      + (C * Kv + (4 * Real.pi / 3) * C) with hsmallKdef
  refine ⟨max 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))), le_max_left _ _, ?_⟩
  intro g hbdd hhold x y hx hy
  -- the uniform bound on `bsDerivCLM g ρ ·` on the ball `‖·‖ ≤ R'`
  have hBnd : ∀ z : R3, ‖z‖ ≤ R' → ‖bsDerivCLM g ρ z‖ ≤ B := by
    intro z hz
    have h1 := norm_bsDerivCLM_le_of_bdd_holder (α := (α : ℝ)) (A := M) (H := C) (ρ := ρ)
      hα hα1 hM hC hρpos.le hbdd (fun a b => by
        have h := hhold a b
        have h2 : 0 ≤ ‖a - b‖ ^ (α : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
        nlinarith [h, hC, h2]) z
    rw [hBdef]
    refine le_trans h1 (add_le_add ?_ le_rfl)
    have hnum : (ρ + ‖z‖) ^ ((α : ℝ) * (1 - (α : ℝ)))
        ≤ (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ))) :=
      Real.rpow_le_rpow (by linarith [norm_nonneg z]) (by linarith) hexp.le
    have hfrac : 4 * Real.pi * (ρ + ‖z‖) ^ ((α : ℝ) * (1 - (α : ℝ)))
          / ((α : ℝ) * (1 - (α : ℝ)))
        ≤ 4 * Real.pi * (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ)))
          / ((α : ℝ) * (1 - (α : ℝ))) := by
      calc 4 * Real.pi * (ρ + ‖z‖) ^ ((α : ℝ) * (1 - (α : ℝ)))
            / ((α : ℝ) * (1 - (α : ℝ)))
          = (4 * Real.pi / ((α : ℝ) * (1 - (α : ℝ))))
              * (ρ + ‖z‖) ^ ((α : ℝ) * (1 - (α : ℝ))) := by ring
        _ ≤ (4 * Real.pi / ((α : ℝ) * (1 - (α : ℝ))))
              * (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ))) :=
            mul_le_mul_of_nonneg_left hnum (by positivity)
        _ = 4 * Real.pi * (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ)))
            / ((α : ℝ) * (1 - (α : ℝ))) := by ring
    have hcoef : 0 ≤ 4 * (2 * M) ^ (α : ℝ) * (2 * C) ^ (1 - (α : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hfrac hcoef
  rcases eq_or_ne x y with hxyEq | hxyNe
  · subst hxyEq
    have h1 : ‖bsDerivCLM g ρ x - bsDerivCLM g ρ x‖ = 0 := by simp
    have h2 : ‖x - x‖ ^ (α : ℝ) = 0 := by simp [Real.zero_rpow, hα.ne']
    rw [h1, h2, mul_zero]
  have hδpos0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxyNe)
  set δ : ℝ := ‖x - y‖ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact hδpos0
  have hxyδ : ‖x - y‖ ≤ δ := le_of_eq hδdef.symm
  by_cases hδq : δ ≤ 1 / 4
  · -- near field: `δ ≤ 1/4`
    have hρδ : R' + 2 * δ < ρ := by rw [hρdef]; linarith
    have hIntx : IntegrableOn (bsIntegrand g x) (Metric.ball (0 : R3) ρ) volume :=
      integrableOn_bsIntegrand_ball hα hC hhold x ρ
    have hInty : IntegrableOn (bsIntegrand g y) (Metric.ball (0 : R3) ρ) volume :=
      integrableOn_bsIntegrand_ball hα hC hhold y ρ
    have hInt : IntegrableOn (fun a : R3 => bsIntegrand g x a - bsIntegrand g y a)
        (Metric.ball (0 : R3) ρ) volume := hIntx.sub hInty
    -- the peeled difference
    have hsm : (4 * Real.pi / 3) • (crossL (g x) - crossL (g y))
        = (4 * Real.pi / 3) • crossL (g x) - (4 * Real.pi / 3) • crossL (g y) := by
      have h := map_sub ((4 * Real.pi / 3) • ContinuousLinearMap.id ℝ (R3 →L[ℝ] R3))
        (crossL (g x)) (crossL (g y))
      simpa using h
    have hpeel : bsDerivCLM g ρ x - bsDerivCLM g ρ y
        = (∫ a in Metric.ball (0 : R3) ρ, (bsIntegrand g x a - bsIntegrand g y a))
          + (4 * Real.pi / 3) • crossL (g x - g y) := by
      have hx' : bsDerivCLM g ρ x
          = (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand g x a)
            + (4 * Real.pi / 3) • crossL (g x) := rfl
      have hy' : bsDerivCLM g ρ y
          = (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand g y a)
            + (4 * Real.pi / 3) • crossL (g y) := rfl
      rw [hx', hy', integral_sub hIntx hInty,
        Work.StabilityFar.Decay.crossL_sub (g x) (g y), hsm]
      abel
    -- split at the ball `B(y,2δ)`
    have hsplit : (∫ a in Metric.ball (0 : R3) ρ, (bsIntegrand g x a - bsIntegrand g y a))
        = (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball y (2 * δ)),
              (bsIntegrand g x a - bsIntegrand g y a))
          + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
              (bsIntegrand g x a - bsIntegrand g y a)) :=
      (MeasureTheory.integral_inter_add_sdiff measurableSet_ball hInt).symm
    have hInner : ‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball y (2 * δ)),
          (bsIntegrand g x a - bsIntegrand g y a)‖
        ≤ 4 * C * (4 * Real.pi / (α : ℝ)) * ((3 * δ) ^ (α : ℝ) + (2 * δ) ^ (α : ℝ)) :=
      Bundle.norm_setIntegral_bsIntegrand_diff_inter_ball_le hα hC hhold hδpos hxyδ
    -- the far-field split of the integrand
    have hKint : IntegrableOn (fun a : R3 => kDerivCLM (x - a))
        ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume :=
      integrableOn_kDerivCLM_sub_diff_ball (ρ := ρ) hδpos hxyδ
    have hAint : IntegrableOn
        (fun a : R3 => (crossL (g y - g x)).comp (kDerivCLM (x - a)))
        ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume := by
      have hmeasure : MeasurableSet
          ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) :=
        measurableSet_ball.diff measurableSet_ball
      have hmA : Measurable
          (fun a : R3 => (crossL (g y - g x)).comp (kDerivCLM (x - a))) :=
        Work.StabilityFar.Decay.continuous_compL.measurable.comp
          (measurable_const.prodMk (Work.StabilityFar.Decay.measurable_kDerivCLM_sub x))
      refine MeasureTheory.IntegrableOn.of_bound (f := fun a : R3 =>
        (crossL (g y - g x)).comp (kDerivCLM (x - a))) ?hfin ?hmeas
        (‖crossL (g y - g x)‖ * (4 / δ ^ 3)) ?hbd
      · refine lt_of_le_of_lt (measure_mono ?_) ((isCompact_closedBall (0 : R3) ρ).measure_lt_top)
        intro a ha
        have h1 : a ∈ Metric.ball (0 : R3) ρ := (Set.mem_sdiff a).mp ha |>.1
        rw [Metric.mem_ball, dist_zero_right] at h1
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_of_lt h1
      · exact hmA.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      · rw [MeasureTheory.ae_restrict_iff' hmeasure]
        refine Filter.Eventually.of_forall fun a ha => ?_
        have h1 : 2 * δ ≤ ‖a - y‖ := by
          have h2 : a ∉ Metric.ball y (2 * δ) := (Set.mem_sdiff a).mp ha |>.2
          rw [Metric.mem_ball] at h2
          have h3 := not_lt.mp h2
          rwa [dist_eq_norm] at h3
        have h3 : ‖a - y‖ ≤ ‖a - x‖ + ‖x - y‖ := by
          have heq : a - y = (a - x) + (x - y) := by abel
          rw [heq]
          exact norm_add_le _ _
        have h2 : δ ≤ ‖x - a‖ := by
          rw [norm_sub_rev a x] at h3
          linarith
        calc ‖(crossL (g y - g x)).comp (kDerivCLM (x - a))‖
            ≤ ‖crossL (g y - g x)‖ * ‖kDerivCLM (x - a)‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖crossL (g y - g x)‖ * (4 / δ ^ 3) :=
              mul_le_mul_of_nonneg_left
                (Work.StabilityFar.Decay.norm_kDerivCLM_le (x - a) δ hδpos h2) (norm_nonneg _)
    have hpt : ∀ a : R3, bsIntegrand g x a - bsIntegrand g y a
        = (crossL (g y - g x)).comp (kDerivCLM (x - a))
          + (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a)) :=
      fun a => bsIntegrand_sub_eq g x y a
    have hBint : IntegrableOn (fun a : R3 =>
        (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a)))
        ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume := by
      have h : IntegrableOn (fun a : R3 => (bsIntegrand g x a - bsIntegrand g y a)
          - (crossL (g y - g x)).comp (kDerivCLM (x - a)))
          ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume :=
        (hInt.mono_set Set.sdiff_subset).sub hAint
      refine h.congr_fun_ae ?_
      filter_upwards with a
      rw [hpt a]
      abel
    have hadd : (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
            (bsIntegrand g x a - bsIntegrand g y a))
        = (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
              (crossL (g y - g x)).comp (kDerivCLM (x - a)))
          + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
              (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a))) := by
      simp only [hpt]
      rw [MeasureTheory.integral_add hAint hBint]
    -- the constant-vector term
    have hAF : ‖∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
          (crossL (g y - g x)).comp (kDerivCLM (x - a))‖ ≤ C * Kv * δ ^ (α : ℝ) := by
      haveI : CompleteSpace (R3 →L[ℝ] R3) :=
        FiniteDimensional.complete ℝ (R3 →L[ℝ] R3)
      have hpull : (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
            (crossL (g y - g x)).comp (kDerivCLM (x - a)))
          = (crossL (g y - g x)).comp
              (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
                kDerivCLM (x - a)) := by
        have h := ContinuousLinearMap.integral_comp_comm
          (ContinuousLinearMap.compL ℝ R3 R3 R3 (crossL (g y - g x))) hKint
        simpa only [ContinuousLinearMap.compL_apply, Function.comp_apply] using h
      rw [hpull]
      have hD5 := Bundle.norm_setIntegral_kDerivCLM_ball_diff_ball_le (ρ := ρ) (R' := R') (δ := δ)
        hδpos hρδ hx hy hxyδ
      rw [← hKvdef] at hD5
      have hL : ‖crossL (g y - g x)‖ ≤ C * δ ^ (α : ℝ) := by
        have h1 : ‖g y - g x‖ ≤ C * ‖y - x‖ ^ (α : ℝ) := hhold y x
        have h2 : ‖y - x‖ = δ := by rw [norm_sub_rev y x, ← hδdef]
        rw [h2] at h1
        exact le_trans (Work.StabilityFar.Decay.norm_crossL_le _) h1
      calc ‖(crossL (g y - g x)).comp
              (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
                kDerivCLM (x - a))‖
          ≤ ‖crossL (g y - g x)‖ *
              ‖∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
                kDerivCLM (x - a)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (C * δ ^ (α : ℝ)) * Kv :=
            mul_le_mul hL hD5 (norm_nonneg _) (by positivity)
        _ = C * Kv * δ ^ (α : ℝ) := by ring
    -- the kernel-difference term
    have hBF : ‖∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
          (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a))‖
        ≤ 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ))) :=
      Bundle.norm_setIntegral_crossL_kDerivCLM_sub_le (ρ := ρ) hα hα1 hC hhold hδpos hxyδ
    have hOuter : ‖∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
          (bsIntegrand g x a - bsIntegrand g y a)‖
        ≤ C * Kv * δ ^ (α : ℝ)
          + 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ))) := by
      rw [hadd]
      exact le_trans (norm_add_le _ _) (add_le_add hAF hBF)
    -- the shape term
    have hShape : ‖(4 * Real.pi / 3) • crossL (g x - g y)‖
        ≤ (4 * Real.pi / 3) * C * δ ^ (α : ℝ) := by
      have h1 : ‖g x - g y‖ ≤ C * δ ^ (α : ℝ) := by
        have h := hhold x y
        rwa [← hδdef] at h
      have h2 : ‖(4 * Real.pi / 3) • crossL (g x - g y)‖
          ≤ (4 * Real.pi / 3) * ‖crossL (g x - g y)‖ := by
        refine le_trans (norm_smul_le (4 * Real.pi / 3) (crossL (g x - g y))) ?_
        rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi / 3)]
      calc ‖(4 * Real.pi / 3) • crossL (g x - g y)‖
          ≤ (4 * Real.pi / 3) * ‖crossL (g x - g y)‖ := h2
        _ ≤ (4 * Real.pi / 3) * ‖g x - g y‖ :=
            mul_le_mul_of_nonneg_left (Work.StabilityFar.Decay.norm_crossL_le _) (by positivity)
        _ ≤ (4 * Real.pi / 3) * (C * δ ^ (α : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (4 * Real.pi / 3) * C * δ ^ (α : ℝ) := by ring
    have htotal : ‖bsDerivCLM g ρ x - bsDerivCLM g ρ y‖
        ≤ 4 * C * (4 * Real.pi / (α : ℝ)) * ((3 * δ) ^ (α : ℝ) + (2 * δ) ^ (α : ℝ))
          + 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ)))
          + (C * Kv + (4 * Real.pi / 3) * C) * δ ^ (α : ℝ) := by
      rw [hpeel, hsplit]
      have hstep : ‖(∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball y (2 * δ)),
              (bsIntegrand g x a - bsIntegrand g y a))
            + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
              (bsIntegrand g x a - bsIntegrand g y a))
            + (4 * Real.pi / 3) • crossL (g x - g y)‖
          ≤ (4 * C * (4 * Real.pi / (α : ℝ)) * ((3 * δ) ^ (α : ℝ) + (2 * δ) ^ (α : ℝ)))
            + (C * Kv * δ ^ (α : ℝ)
              + 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ))))
            + (4 * Real.pi / 3) * C * δ ^ (α : ℝ) := by
        refine le_trans (norm_add_le _ _) (add_le_add ?_ hShape)
        exact le_trans (norm_add_le _ _) (add_le_add hInner hOuter)
      refine le_trans hstep (le_of_eq ?_)
      ring
    have harith := Bundle.sliceFderiv_holder_arith (α := (α : ℝ)) (C := C) (δ := δ) (Kv := Kv)
      hα hα1 hC hδpos.le
    rw [← hsmallKdef] at harith
    refine le_trans htotal (le_trans harith ?_)
    have hδpow : 0 ≤ δ ^ (α : ℝ) := Real.rpow_nonneg hδpos.le _
    have hle : smallK ≤ max 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))) :=
      le_trans (le_max_left smallK (2 * B * (4 : ℝ) ^ (α : ℝ)))
        (le_max_right 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))))
    exact mul_le_mul_of_nonneg_right hle hδpow
  · -- far field: `1/4 < δ`
    have hδq' : 1 / 4 < δ := not_le.mp hδq
    have h4δ : 1 ≤ 4 * δ := by linarith
    have hrpow : 1 ≤ (4 : ℝ) ^ (α : ℝ) * δ ^ (α : ℝ) := by
      have h := Real.one_le_rpow h4δ hα.le
      rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hδpos.le] at h
    have h2B : 0 ≤ 2 * B := by
      have h1 := hBnd x hx
      linarith [norm_nonneg (bsDerivCLM g ρ x)]
    calc ‖bsDerivCLM g ρ x - bsDerivCLM g ρ y‖
        ≤ ‖bsDerivCLM g ρ x‖ + ‖bsDerivCLM g ρ y‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hBnd x hx) (hBnd y hy)
      _ = 2 * B := by ring
      _ ≤ 2 * B * ((4 : ℝ) ^ (α : ℝ) * δ ^ (α : ℝ)) := by
          simpa using mul_le_mul_of_nonneg_left hrpow h2B
      _ = (2 * B * (4 : ℝ) ^ (α : ℝ)) * δ ^ (α : ℝ) := by ring
      _ ≤ (max 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ)))) * δ ^ (α : ℝ) := by
          have hδpow : 0 ≤ δ ^ (α : ℝ) := Real.rpow_nonneg hδpos.le _
          have hle : 2 * B * (4 : ℝ) ^ (α : ℝ)
              ≤ max 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))) :=
            le_trans (le_max_right smallK (2 * B * (4 : ℝ) ^ (α : ℝ)))
              (le_max_right 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))))
          exact mul_le_mul_of_nonneg_right hle hδpow

/-! ## 4. The uniform single-slice Schauder estimate -/

/-- **The uniform-in-the-slice Schauder estimate for one vorticity slice.**

For `0 < α < 1`, `R > 0`, `M, C ≥ 0` and fixed `R'` there is `K ≥ 0`, depending only on
`R, M, C, α, R'`, such that for every field `g` bounded by `M`, supported in `closedBall 0 R`,
ae-strongly-measurable and `α`-Hölder with constant `C`, the derivative
`x ↦ fderiv ℝ (biotSavart g) x` is `α`-Hölder on `‖x‖ ≤ R'` with constant `K`. -/
theorem sliceFderiv_holder_uniform {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {R M C R' : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : R3 → R3),
      (∀ a, ‖g a‖ ≤ M) →
      (∀ a, g a ≠ 0 → a ∈ Metric.closedBall 0 R) →
      MeasureTheory.AEStronglyMeasurable g volume →
      (∀ a b : R3, ‖g a - g b‖ ≤ C * ‖a - b‖ ^ (α : ℝ)) →
      ∀ x y : R3, ‖x‖ ≤ R' → ‖y‖ ≤ R' →
        ‖fderiv ℝ (Work.LWP.biotSavart g) x - fderiv ℝ (Work.LWP.biotSavart g) y‖
          ≤ K * ‖x - y‖ ^ (α : ℝ) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := bsDerivCLM_sub_holder_uniform (α := α) hα hα1 hR hM hC
  refine ⟨(4 * Real.pi)⁻¹ * K₀, by positivity, ?_⟩
  intro g hbdd hs hm hhold x y hx hy
  by_cases hR'neg : R' < 0
  · exact absurd hx (not_le.mpr (by linarith [norm_nonneg x, hR'neg]))
  have hxρ : R + ‖x‖ < R + R' + 1 := by linarith
  have hyρ : R + ‖y‖ < R + R' + 1 := by linarith
  have hfx : fderiv ℝ (Work.LWP.biotSavart g) x
      = (4 * Real.pi)⁻¹ • bsDerivCLM g (R + R' + 1) x :=
    (hasFDerivAt_biotSavart_slice (R := R) (M := M) (C := C) (c := (α : ℝ)) (ρ := R + R' + 1)
      hR hM hα hbdd hs hm hhold hxρ).fderiv
  have hfy : fderiv ℝ (Work.LWP.biotSavart g) y
      = (4 * Real.pi)⁻¹ • bsDerivCLM g (R + R' + 1) y :=
    (hasFDerivAt_biotSavart_slice (R := R) (M := M) (C := C) (c := (α : ℝ)) (ρ := R + R' + 1)
      hR hM hα hbdd hs hm hhold hyρ).fderiv
  have hsm : (4 * Real.pi)⁻¹ • bsDerivCLM g (R + R' + 1) x
        - (4 * Real.pi)⁻¹ • bsDerivCLM g (R + R' + 1) y
      = (4 * Real.pi)⁻¹ • (bsDerivCLM g (R + R' + 1) x - bsDerivCLM g (R + R' + 1) y) := by
    have h := map_sub ((4 * Real.pi)⁻¹ • ContinuousLinearMap.id ℝ (R3 →L[ℝ] R3))
      (bsDerivCLM g (R + R' + 1) x) (bsDerivCLM g (R + R' + 1) y)
    simpa using h.symm
  rw [hfx, hfy, hsm, norm_smul,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹)]
  have hmain := hK₀ g hbdd hhold x y hx hy
  calc (4 * Real.pi)⁻¹
        * ‖bsDerivCLM g (R + R' + 1) x - bsDerivCLM g (R + R' + 1) y‖
      ≤ (4 * Real.pi)⁻¹ * (K₀ * ‖x - y‖ ^ (α : ℝ)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (4 * Real.pi)⁻¹ * K₀ * ‖x - y‖ ^ (α : ℝ) := by ring

/-! ## 5. The bundle lemma -/

/-- **The uniform-in-`t` single-slice Schauder estimate for a strip-bundle vorticity.**

For `0 < α < 1`, let `ω` satisfy the full strip bundle `BSAdmissibleStripFull α ω R S`: supported in
`closedBall 0 R`, uniformly bounded by `M`, uniformly `α`-Hölder in `x` with constant `H`, uniformly
Hölder in `t`, with ae-strongly-measurable slices. Then the spatial Calderón–Zygmund derivative of
each slice, `x ↦ fderiv ℝ (BS (ω·t)) x`, is `α`-Hölder on the ball `‖x‖ ≤ R'`, with a constant `K`
*uniform in `t ∈ Icc 0 S`*.

This is the `x`-direction half of the space-time Schauder estimate: the bundle is exactly the
statement that all the constants of the classical Schauder estimate (`R`, the sup bound `M`, the
`x`-Hölder constant `H`) are uniform in `t`, which is what makes the resulting constant uniform.
The proof is `sliceFderiv_holder_uniform`, applied to each slice: the constants `R, max M 0, (H:ℝ)`
do not depend on `t`. -/
theorem bundleSliceFderiv_holder {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S R' : ℝ}
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0:ℝ) S, ∀ x y : Work.LWP.R3,
      ‖x‖ ≤ R' → ‖y‖ ≤ R' →
      ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
        - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) y‖
      ≤ K * ‖x - y‖ ^ (α : ℝ) := by
  obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, htime, hmeas⟩, -, -⟩ := hbun
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hH0 : 0 ≤ (H : ℝ) := H.coe_nonneg
  obtain ⟨K, hK0, hK⟩ := sliceFderiv_holder_uniform (α := α) hα hα1 (R := R) (M := max M 0)
    (C := (H : ℝ)) (R' := R') hR hM0 hH0
  refine ⟨K, hK0, ?_⟩
  intro t ht x y hx hy
  have hbdd : ∀ a : Work.LWP.R3, ‖ω a t‖ ≤ max M 0 :=
    fun a => le_trans (hM t ht a) (le_max_left _ _)
  have hhold : ∀ a b : Work.LWP.R3, ‖ω a t - ω b t‖ ≤ (H : ℝ) * ‖a - b‖ ^ (α : ℝ) :=
    fun a b => holderWith_norm_sub_le (hH t ht) a b
  exact hK (fun a => ω a t) hbdd (fun a ha => hsupp t ht a ha) (hmeas t ht) hhold x y hx hy

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.BSSwirl.div_biotSavart_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Set
open scoped Topology Matrix InnerProductSpace

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.FTS.BSSwirl

/-! ## Linearity of the trace on continuous linear maps -/

/-- The trace is additive on continuous linear maps. -/
theorem trace_add_clm (A B : R3 →L[ℝ] R3) :
    (A + B).trace ℝ R3 = A.trace ℝ R3 + B.trace ℝ R3 := by
  rw [show ((A + B).trace ℝ R3) = LinearMap.trace ℝ R3 ((A : R3 →ₗ[ℝ] R3) + B) from rfl, map_add]

/-- The trace is homogeneous on continuous linear maps. -/
theorem trace_smul_clm (c : ℝ) (A : R3 →L[ℝ] R3) :
    (c • A).trace ℝ R3 = c • A.trace ℝ R3 := by
  rw [show ((c • A).trace ℝ R3) = LinearMap.trace ℝ R3 (c • (A : R3 →ₗ[ℝ] R3)) from rfl, map_smul]

/-- The trace of a difference of continuous linear maps. -/
theorem trace_sub_clm (A B : R3 →L[ℝ] R3) :
    (A - B).trace ℝ R3 = A.trace ℝ R3 - B.trace ℝ R3 := by
  rw [show ((A - B).trace ℝ R3) = LinearMap.trace ℝ R3 ((A : R3 →ₗ[ℝ] R3) - B) from rfl, map_sub]

/-! ## Trace-freeness of the Biot–Savart kernels -/

/-- **The cross-product operator is orthogonal to its argument**: `⟪w, u × w⟫ = 0`.  This is the
componentwise form of `dot_cross_self`, transported to the Euclidean space `ℝ³`. -/
theorem inner_crossL_self (u w : R3) : ⟪w, Work.StabilityFar.Decay.crossL u w⟫_ℝ = 0 := by
  have h := dot_cross_self u.ofLp w.ofLp
  simp only [dotProduct] at h
  rw [Work.StabilityFar.Decay.crossL_apply, PiLp.inner_apply]
  have h2 : (∑ x, ⟪w.ofLp x, (crossProduct u.ofLp) w.ofLp x⟫_ℝ)
      = ∑ x, w.ofLp x * (crossProduct u.ofLp) w.ofLp x :=
    Finset.sum_congr rfl (fun x _ => by simp [mul_comm])
  rw [h2, h]

/-- **The cross-product operator is trace-free.**  In an orthonormal basis the trace of
`v ↦ u × v` is the sum of the diagonal entries `⟪eᵢ, u × eᵢ⟫`, all of which vanish
(`inner_crossL_self`). -/
theorem trace_crossL (u : R3) : (Work.StabilityFar.Decay.crossL u).trace ℝ R3 = 0 := by
  rw [show (Work.StabilityFar.Decay.crossL u).trace ℝ R3
      = LinearMap.trace ℝ R3 (Work.StabilityFar.Decay.crossL u).toLinearMap from rfl]
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  exact Finset.sum_eq_zero (fun i _ => inner_crossL_self u _)

/-- **The composite of the cross-product operator with a rank-one operator is trace-free.**
`(v ↦ u × v) ∘ (w ↦ ⟪z,w⟫ • z) = (w ↦ ⟪z,w⟫ • (u × z))` is the rank-one operator with symbol
`(u × z, z)`, whose trace is `⟪z, u × z⟫ = 0`. -/
theorem trace_crossL_rankOne (u z : R3) :
    ((Work.StabilityFar.Decay.crossL u).comp (InnerProductSpace.rankOne ℝ z z)).trace ℝ R3 = 0 := by
  rw [show ((Work.StabilityFar.Decay.crossL u).comp (InnerProductSpace.rankOne ℝ z z)).trace ℝ R3
      = LinearMap.trace ℝ R3
          (((Work.StabilityFar.Decay.crossL u).comp (InnerProductSpace.rankOne ℝ z z)).toLinearMap)
      from rfl]
  rw [InnerProductSpace.comp_rankOne]
  rw [show (InnerProductSpace.rankOne ℝ ((Work.StabilityFar.Decay.crossL u) z) z).trace ℝ R3
      = LinearMap.trace ℝ R3
          ((InnerProductSpace.rankOne ℝ ((Work.StabilityFar.Decay.crossL u) z) z).toLinearMap)
      from rfl]
  rw [InnerProductSpace.trace_rankOne]
  exact inner_crossL_self u z

/-- **The Jacobian of the Biot–Savart kernel composed with a cross product is trace-free.**  Since
`kDerivCLM z = ‖z‖⁻³ • id - 3‖z‖⁻⁵ • (w ↦ ⟪z,w⟫ • z)`, this reduces to the two previous lemmas
plus linearity of the trace. -/
theorem trace_crossL_kDerivCLM (u z : R3) :
    ((Work.StabilityFar.Decay.crossL u).comp (Work.StabilityFar.Decay.kDerivCLM z)).trace ℝ R3
      = 0 := by
  have hA : (Work.StabilityFar.Decay.crossL u).comp
        ((‖z‖ ^ (3:ℕ))⁻¹ • (ContinuousLinearMap.id ℝ R3)
          - (3 * (‖z‖ ^ (5:ℕ))⁻¹) • ((innerSL ℝ) z).smulRight z)
      = (‖z‖ ^ (3:ℕ))⁻¹ • Work.StabilityFar.Decay.crossL u
          - (3 * (‖z‖ ^ (5:ℕ))⁻¹) •
            ((Work.StabilityFar.Decay.crossL u).comp (InnerProductSpace.rankOne ℝ z z)) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id]
    rw [show ((innerSL ℝ) z).smulRight z = InnerProductSpace.rankOne ℝ z z from by
      rw [InnerProductSpace.rankOne_def]]
  rw [Work.StabilityFar.Decay.kDerivCLM, hA, trace_sub_clm, trace_smul_clm, trace_smul_clm,
    trace_crossL, trace_crossL_rankOne]
  simp

/-- **The integrand of the derivative of the Biot–Savart field is trace-free at every point.**
This is the pointwise algebraic heart of the divergence-free character of the Biot–Savart law. -/
theorem trace_bsIntegrand (ω : R3 → R3) (x a : R3) :
    (Work.CoreResiduals.BiotSavart.bsIntegrand ω x a).trace ℝ R3 = 0 := by
  rw [Work.CoreResiduals.BiotSavart.bsIntegrand]
  exact trace_crossL_kDerivCLM (ω a - ω x) (x - a)

/-! ## The trace as a continuous linear functional -/

/-- **The trace is bounded by three times the operator norm** — the dimension of `ℝ³`.  Obtained
by expanding the trace in the standard orthonormal basis. -/
theorem trace_bound (f : R3 →L[ℝ] R3) : ‖f.trace ℝ R3‖ ≤ 3 * ‖f‖ := by
  rw [show f.trace ℝ R3 = LinearMap.trace ℝ R3 f.toLinearMap from rfl]
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  have honb : ∀ i : Fin 3, ‖(EuclideanSpace.basisFun (Fin 3) ℝ) i‖ = 1 :=
    fun i => OrthonormalBasis.norm_eq_one _ i
  calc ‖∑ i, ⟪(EuclideanSpace.basisFun (Fin 3) ℝ) i,
        f ((EuclideanSpace.basisFun (Fin 3) ℝ) i)⟫_ℝ‖
      ≤ ∑ i, ‖⟪(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          f ((EuclideanSpace.basisFun (Fin 3) ℝ) i)⟫_ℝ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖f ((EuclideanSpace.basisFun (Fin 3) ℝ) i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h2 := norm_inner_le_norm (𝕜 := ℝ) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
          (f ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
        rwa [honb i, one_mul] at h2
    _ ≤ ∑ i, ‖f‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h1 := f.le_opNorm ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
        rwa [honb i, mul_one] at h1
    _ = 3 * ‖f‖ := by simp

/-- The trace, as a linear functional on the (finite-dimensional) space of continuous linear
endomorphisms of `ℝ³`. -/
noncomputable def traceLin : (R3 →L[ℝ] R3) →ₗ[ℝ] ℝ where
  toFun f := f.trace ℝ R3
  map_add' f g := trace_add_clm f g
  map_smul' c f := trace_smul_clm c f

/-- The trace, as a **continuous** linear functional on `ℝ³ →L[ℝ] ℝ³`. -/
noncomputable def traceCLM : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
  LinearMap.mkContinuous traceLin 3 (fun f => trace_bound f)

/-- The defining value of `traceCLM`. -/
theorem traceCLM_apply (f : R3 →L[ℝ] R3) : traceCLM f = f.trace ℝ R3 := rfl

/-- **The trace commutes with the Bochner integral of continuous linear maps.**  This is
`ContinuousLinearMap.integral_comp_comm` applied to the continuous linear functional `traceCLM`,
and needs the integrability of the `ℝ³ →L[ℝ] ℝ³`-valued integrand. -/
theorem trace_setIntegral {s : Set R3} {F : R3 → (R3 →L[ℝ] R3)}
    (hF : IntegrableOn F s volume) :
    ((∫ a in s, F a)).trace ℝ R3 = ∫ a in s, (F a).trace ℝ R3 := by
  have h := ContinuousLinearMap.integral_comp_comm traceCLM (φ := F) hF
  simpa only [traceCLM_apply] using h.symm

/-! ## Integrability of the derivative integrand and the trace of `bsDerivCLM` -/

/-- **The derivative integrand is integrable on any ball `B(0,ρ)`.**  The Hölder condition
`‖ω a - ω x‖ ≤ C‖a - x‖^α` with `α > 0` makes the singular kernel
`a ↦ ‖x - a‖^{α - 3}` integrable near `a = x`; the statement is
`integrableOn_bsIntegrand_inter` with the centre `x₀ := x` and a radius `Δ` so large that
`B(0,ρ) ⊆ B(x,Δ)`. -/
theorem integrableOn_bsIntegrand_ball (ω : R3 → R3) {C α : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α) (ρ : ℝ) (x : R3) :
    IntegrableOn (Work.CoreResiduals.BiotSavart.bsIntegrand ω x) (Metric.ball 0 ρ) volume := by
  have hΔpos : 0 < max (2 * ρ) 0 + 2 * ‖x‖ + 1 := by
    have := norm_nonneg x; linarith [le_max_right (2 * ρ) 0]
  have hsub : Metric.ball (0 : R3) ρ ⊆ Metric.ball x (max (2 * ρ) 0 + 2 * ‖x‖ + 1) := by
    intro a ha
    rw [Metric.mem_ball, dist_zero_right] at ha
    rw [Metric.mem_ball, dist_eq_norm]
    have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hmax : ρ ≤ max (2 * ρ) 0 := by
      by_cases h : ρ ≤ 0
      · exact le_trans h (le_max_right _ _)
      · exact le_trans (by linarith [not_le.mp h]) (le_max_left _ _)
    calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
      _ < ρ + ‖x‖ := by linarith
      _ ≤ max (2 * ρ) 0 + 2 * ‖x‖ + 1 := by linarith
  have hx : ‖x - x‖ ≤ (max (2 * ρ) 0 + 2 * ‖x‖ + 1) / 2 := by
    rw [sub_self, norm_zero]
    linarith [le_max_right (2 * ρ) 0, norm_nonneg x]
  have h1 := Work.CoreResiduals.BiotSavart.integrableOn_bsIntegrand_inter (ω := ω) hα hC hhold x
    (Δ := max (2 * ρ) 0 + 2 * ‖x‖ + 1) (ρ := ρ) hΔpos hx
  rwa [Set.inter_eq_left.mpr hsub] at h1

/-- **The candidate derivative of the Biot–Savart field is trace-free.**  This is the
divergence-free character of the Biot–Savart law in infinitesimal form: the trace of
`bsDerivCLM ω ρ x` — which is `4π • fderiv (biotSavart ω) x` — vanishes. -/
theorem trace_bsDerivCLM (ω : R3 → R3) {C α : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α) (ρ : ℝ) (x : R3) :
    (Work.CoreResiduals.BiotSavart.bsDerivCLM ω ρ x).trace ℝ R3 = 0 := by
  have hint : IntegrableOn (Work.CoreResiduals.BiotSavart.bsIntegrand ω x)
      (Metric.ball 0 ρ) volume := integrableOn_bsIntegrand_ball ω hα hC hhold ρ x
  have hint' : IntegrableOn (fun a : R3 => Work.StabilityFar.Decay.crossL (ω a - ω x)
      ∘SL Work.StabilityFar.Decay.kDerivCLM (x - a)) (Metric.ball 0 ρ) volume := hint
  have hb : ∀ a : R3, (Work.StabilityFar.Decay.crossL (ω a - ω x)
      ∘SL Work.StabilityFar.Decay.kDerivCLM (x - a)).trace ℝ R3 = 0 :=
    fun a => trace_bsIntegrand ω x a
  rw [Work.CoreResiduals.BiotSavart.bsDerivCLM.eq_def, trace_add_clm, trace_smul_clm,
    trace_crossL, trace_setIntegral hint']
  simp only [hb, integral_zero, zero_add, smul_zero]

/-! ## The divergence of the Biot–Savart field -/

theorem div_biotSavart_eq_zero {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R M α C : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hα : 0 < α) (hC : 0 ≤ C)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hholder : ∀ a b : Work.FTS.BSSwirl.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α) :
    ∀ x, FiniteTimeSingularity.div (Work.LWP.biotSavart ω) x = 0 := by
  intro x
  -- `biotSavart ω` is differentiable at `x`, with derivative `(4π)⁻¹ • bsDerivCLM ω ρ x` for any
  -- radius `ρ > R + ‖x‖`.
  have hρ : R + ‖x‖ < R + ‖x‖ + 1 := by linarith
  have hfd := Work.CoreResiduals.BiotSavart.hasFDerivAt_biotSavart_slice
    (ω := ω) (R := R) (M := M) (C := C) (c := α) (ρ := R + ‖x‖ + 1)
    hR hM hα hbdd hsupp hmeas hholder hρ
  -- The divergence is the trace of the derivative, which is therefore the trace of a multiple of
  -- the trace-free map `bsDerivCLM ω ρ x`.
  rw [FiniteTimeSingularity.div, hfd.fderiv, trace_smul_clm,
    trace_bsDerivCLM ω hα hC hholder (R + ‖x‖ + 1) x]
  simp

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.gsTools =====
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

set_option autoImplicit false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

/-- **The profile data of `c r = d·r/(1+r)`.**  On `r > 0` one has
`r⁻¹·c r = d/(1+r)`, so the profile factor of the `L₁₂`-weight is measurable,
square-integrable, and its square-integral is at most `2d²` (using `∫ (1+r)^{-2} ≤ 2`). -/
theorem profile_data {d : ℝ} (hd : 0 ≤ d) :
    AEMeasurable (fun r : ℝ => r⁻¹ * (d * r / (1 + r)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (d * r / (1 + r))) ^ 2)
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2) ≤ d ^ 2 * 2 ∧
      Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2)
        ≤ d * Real.sqrt 2 := by
  have hkey : ∀ r : ℝ, 0 < r → r⁻¹ * (d * r / (1 + r)) = d / (1 + r) := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hmeas : AEMeasurable (fun r : ℝ => r⁻¹ * (d * r / (1 + r)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hbase : AEMeasurable (fun r : ℝ => d * (1 + r)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_const.mul ((measurable_const.add measurable_id).inv)).aemeasurable
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have h := hkey r hr
    rw [h]
    rfl
  have hint : MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (d * r / (1 + r))) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    have hbase : MeasureTheory.IntegrableOn (fun r : ℝ => d ^ 2 * (1 / (1 + r)) ^ 2)
        (Set.Ioi (0 : ℝ)) := (integrableOn_inv_one_add_sq'.1).const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun hbase ?_ measurableSet_Ioi
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    change d ^ 2 * (1 / (1 + r)) ^ 2 = (r⁻¹ * (d * r / (1 + r))) ^ 2
    rw [hkey r hr']
    field_simp
  have hint2 : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2)
      = d ^ 2 * ∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2 := by
    have hcong : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2)
        = ∫ r in Set.Ioi (0 : ℝ), d ^ 2 * (1 / (1 + r)) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro r hr
      have hr' : (0 : ℝ) < r := hr
      have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
      change (r⁻¹ * (d * r / (1 + r))) ^ 2 = d ^ 2 * (1 / (1 + r)) ^ 2
      rw [hkey r hr']
      field_simp
    rw [hcong, MeasureTheory.integral_const_mul]
  have hle : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2) ≤ d ^ 2 * 2 := by
    rw [hint2]
    exact mul_le_mul_of_nonneg_left integrableOn_inv_one_add_sq'.2 (sq_nonneg _)
  refine ⟨hmeas, hint, hle, ?_⟩
  calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2)
      ≤ Real.sqrt (d ^ 2 * 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (d ^ 2) * Real.sqrt 2 := Real.sqrt_mul (sq_nonneg _) 2
    _ = d * Real.sqrt 2 := by rw [Real.sqrt_sq hd]

/-- `√(CA/(γ-1))·α = √(10CA)·α^{1/2}` (`γ - 1 = α/10`). -/
theorem sqrt_coef_mul_alpha {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α = Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) := by
  have hγ : Work.Spaces.gam α - 1 = α / 10 := by
    rw [Work.Spaces.gam]; ring
  have hCAα : CA / (Work.Spaces.gam α - 1) = 10 * CA / α := by
    rw [hγ]; field_simp
  have h10α : (0 : ℝ) ≤ 10 * CA / α := div_nonneg (by linarith) hα.le
  rw [hCAα]
  have hα2 : Real.sqrt (α ^ 2) = α := Real.sqrt_sq hα.le
  calc Real.sqrt (10 * CA / α) * α
      = Real.sqrt (10 * CA / α) * Real.sqrt (α ^ 2) := by rw [hα2]
    _ = Real.sqrt (10 * CA / α * α ^ 2) := (Real.sqrt_mul h10α (α ^ 2)).symm
    _ = Real.sqrt (10 * CA * α) := by
        congr 1
        field_simp
    _ = Real.sqrt (10 * CA) * Real.sqrt α := Real.sqrt_mul (by linarith) α
    _ = Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow α]

/-- `√(CA/(γ-1))·α² = √(10CA)·α^{3/2}` (`γ - 1 = α/10`). -/
theorem sqrt_coef_mul_alpha_sq {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2
      = Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) := by
  have h := sqrt_coef_mul_alpha hCA hα
  calc Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2
      = (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α) * α := by ring
    _ = (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ)) * α := by rw [h]
    _ = Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hα,
          Real.rpow_one]
        ring

/-- `α^{3/2} ≤ α^{1/2}` for `0 < α ≤ 1`. -/
theorem rpow_three_halves_le' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (3 / 2 : ℝ) ≤ α ^ (1 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hα, Real.rpow_one]
  have h1 : 0 < α ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hα _
  nlinarith

/-- `(π/2)·√2·120 ≤ 2000`: the numerical factor of the row constants. -/
theorem pi_div_two_mul_sqrt_two_mul : Real.pi / 2 * Real.sqrt 2 * 120 ≤ 2000 := by
  have h2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h2' := Real.sqrt_nonneg 2
    nlinarith
  have hp : Real.pi / 2 ≤ 2 := by
    have h := Real.pi_lt_four
    have h2' := Real.pi_pos
    linarith
  nlinarith [Real.sqrt_nonneg 2, Real.pi_pos]

/-- `√α·X ≤ Env α g` for `X = |g|_{ℋ⁴}`. -/
theorem sqrt_mul_le_Env {α : ℝ} {g : Fn} (hα : 0 < α) :
    α ^ (1 / 2 : ℝ) * Xn α g ≤ Env α g := by
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hsqrt : α ^ (1 / 2 : ℝ) = Real.sqrt α := (Real.sqrt_eq_rpow α).symm
  rw [hsqrt, Env]
  have h : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Xn α g) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  have h2 : 0 ≤ α ^ 2 := sq_nonneg α
  linarith

/-- **The row constants fit into `Env`.**  The common conclusion of the three `gs`-rows,
`Fa N ≤ ofReal (2000·√(10CA)·max Ce 0·α^{1/2}·|g|_{ℋ⁴})`, is dominated by
`ofReal (K·Env α g)` with `K = 1 + 2000·(max Ce 0·√(10CA))`, because `√α·|g|_{ℋ⁴} ≤ Env α g`. -/
theorem const_mul_le_K {CA Ce α : ℝ} {g : Fn} (_hCA : 0 ≤ CA) (hα : 0 < α)
    (hEnv : 0 ≤ Env α g) :
    2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g
      ≤ (1 + 2000 * (max Ce 0 * Real.sqrt (10 * CA))) * Env α g := by
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ 2000 * (max Ce 0 * Real.sqrt (10 * CA)) :=
    mul_nonneg (by norm_num) (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
  have h1 : α ^ (1 / 2 : ℝ) * Xn α g ≤ Env α g := sqrt_mul_le_Env hα
  have h2 : 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g
      = (2000 * (max Ce 0 * Real.sqrt (10 * CA))) * (α ^ (1 / 2 : ℝ) * Xn α g) := by ring
  rw [h2]
  have h3 : 2000 * (max Ce 0 * Real.sqrt (10 * CA))
      ≤ 1 + 2000 * (max Ce 0 * Real.sqrt (10 * CA)) := by linarith
  exact le_trans (mul_le_mul_of_nonneg_left h1 hA) (mul_le_mul_of_nonneg_right h3 hEnv)

end Work.FTS.NonlinRows.Rl1
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FamLopAux.TrigGegen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FamLopAux

/-
# The trigonometric form of the Gegenbauer polynomials

`famC k = (3/2)_k/k!` (extended by `0` to negative `k`) and
`famTrig n ψ = Σ_{j<n+1} famC j · famC (n-j) · cos ((2j-n) ψ)` are defined in
`Submission/Work/FTS/PhiStar/FamLopAux/Defs.lean`.  The claim is the classical trigonometric
form of the Gegenbauer polynomial `gC n = C_n^{(3/2)}`.

## Proof recipe (verified numerically to 40 digits)

Let `c k := famC k`, so that `c 0 = 1`, `c (k+1) = c k * ((k + 3/2)/(k+1))`, `c k ≠ 0` for
`k ≥ 0`, and `c k = 0` for `k < 0`.  Write `S n ψ := famTrig n ψ`.

1. **Base cases**: `S 0 ψ = 1`, `S 1 ψ = 3 * cos ψ`.
2. **Recurrence**: prove, for every `n : ℕ` and `ψ : ℝ`,
   `(n+2) * S (n+2) ψ = (2n+5) * cos ψ * S (n+1) ψ - (n+3) * S n ψ`.
   Ingredients (all with the convention `c (-1) = 0`, which is built into `famC`):
   * `cos ψ * cos ((2j-(n+1))ψ) = (cos ((2j-n)ψ) + cos ((2j-n-2)ψ))/2`
     (`Real.cos_add`/`Real.cos_sub`, and `cos` even);
   * reindexing: shifts of the summation range are handled by `Finset.sum_range_succ'`
     (`∑_{i<n+3} F i = ∑_{j<n+2} F (j+1) + F 0`) and `Finset.sum_range_succ`, with
     `F j := c (j-1) * c (n+2-j) * cos ((2j-n-2)ψ)` (write the indices as integers, e.g.
     `(n : ℤ) + 2 - (j : ℤ)`, so that no truncated natural subtraction appears); the only
     "boundary" terms that appear are multiples of `c (-1) = 0`;
   * the pointwise algebraic identity: for `j + l = n + 2` (in `ℕ`),
     `(n+2) * c j * c l = ((2n+5)/2) * (c (j-1) * c l + c j * c (l-1)) - (n+3) * c (j-1) * c (l-1)`.
     For `1 ≤ j ≤ n+1` divide by `c (j-1) * c (l-1) > 0` and use
     `c k / c (k-1) = (2k+1)/(2k) =: α_k`; the identity becomes
     `(j+l) * α_j * α_l - ((2j+2l+1)/2) * (α_j + α_l) + (j+l+1) = 0`, a rational identity
     (`field_simp; ring`).  The two remaining cases `j = 0` and `j = n+2` are handled directly
     (in both, one factor `c (-1)` vanishes and the identity reduces to
     `(k+2)c(k+2) = ((2k+5)/2)c(k+1)`, which is the defining ratio of `c`).
3. **Conclusion**: by induction on `n`, using the recurrence `gC_rec` of
   `Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode`
   (`((n:ℝ)+2) * gC (n+2) x = (2*(n:ℝ)+5) * x * gC (n+1) x - ((n:ℝ)+3) * gC n x`).
-/

set_option autoImplicit false

/-! ## Elementary properties of the coefficients `famC`

`famC k = (3/2)_k / k!` is the coefficient sequence of the binomial series
`(1 - z)^{-3/2}`; by definition it vanishes on the negative integers, which is exactly
what allows the summation ranges of `famTrig` to be shifted without boundary
corrections. -/

lemma famC_zero : famC (0 : ℤ) = 1 := by
  rw [famC]
  norm_num

lemma famC_eq_zero_of_neg {k : ℤ} (hk : k < 0) : famC k = 0 := by
  rw [famC]
  rw [if_neg]
  omega



/-- The defining ratio of the coefficients: `c (m+1) = c m · (m + 3/2)/(m+1)`. -/
lemma famC_succ_ratio (m : ℕ) :
    famC ((m : ℤ) + 1) = famC (m : ℤ) * (((m : ℝ) + 3 / 2) / ((m : ℝ) + 1)) := by
  have h1 : famC ((m : ℤ) + 1)
      = (∏ i ∈ Finset.range (m + 1), ((3 : ℝ) / 2 + i)) / ((Nat.factorial (m + 1) : ℕ) : ℝ) := by
    rw [famC, if_pos (by omega)]
    norm_num
  have h2 : famC ((m : ℤ))
      = (∏ i ∈ Finset.range m, ((3 : ℝ) / 2 + i)) / ((Nat.factorial m : ℕ) : ℝ) := by
    rw [famC, if_pos (by omega)]
    norm_num
  rw [h1, h2, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `c 1 = 3/2`. -/
lemma famC_one : famC (1 : ℤ) = 3 / 2 := by
  have h := famC_succ_ratio 0
  have hone : famC ((((0 : ℕ)) : ℤ) + 1) = famC (1 : ℤ) := congrArg famC (by norm_num)
  have hz : famC (((0 : ℕ)) : ℤ) = 1 := by simpa using famC_zero
  rw [hone, hz] at h
  have hval : ((((0 : ℕ)) : ℝ) + 3 / 2) / ((((0 : ℕ)) : ℝ) + 1) = 3 / 2 := by norm_num
  rw [hval, one_mul] at h
  exact h

/-- The boundary instance of the algebraic identity: `2(n+2)c(n+2) = (2n+5)c(n+1)`. -/
lemma famC_boundary (n : ℕ) :
    2 * ((n : ℝ) + 2) * famC ((n : ℤ) + 2) = (2 * (n : ℝ) + 5) * famC ((n : ℤ) + 1) := by
  have hA : (n : ℤ) + 2 = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [hA, famC_succ_ratio (n + 1)]
  push_cast
  field_simp
  ring

/--
**The pointwise algebraic identity driving the recurrence of `famTrig`.**

For integer `j`, `l` with `j + l = n + 2` (and the convention `c k = 0` for `k < 0`),

`2(n+2)·c j·c l = (2n+5)·(c (j-1)·c l + c j·c (l-1)) - 2(n+3)·c (j-1)·c (l-1)`.

Only the case `1 ≤ j`, `1 ≤ l` needs the defining ratio of `c`; the boundary cases
`j ≤ 0` or `l ≤ 0` are handled by `c (-1) = 0`, and `j = 0` / `l = 0` by
`famC_boundary`. -/
lemma famC_ident (n : ℕ) (j l : ℤ) (h : j + l = (n : ℤ) + 2) :
    2 * ((n : ℝ) + 2) * famC j * famC l
      = (2 * (n : ℝ) + 5) * (famC (j - 1) * famC l + famC j * famC (l - 1))
        - 2 * ((n : ℝ) + 3) * (famC (j - 1) * famC (l - 1)) := by
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have h1 : famC j = 0 := famC_eq_zero_of_neg hj
    have h2 : famC (j - 1) = 0 := famC_eq_zero_of_neg (by omega)
    rw [h1, h2]
    ring
  · -- `j = 0`: then `l = n + 2`
    subst hj
    have hl : l = (n : ℤ) + 2 := by omega
    rw [hl]
    have h0 : famC (0 : ℤ) = 1 := famC_zero
    have hm1 : famC ((0 : ℤ) - 1) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [h0, hm1]
    have hl1 : famC (((n : ℤ) + 2) - 1) = famC ((n : ℤ) + 1) := by congr 1; ring
    rw [hl1]
    linarith [famC_boundary n]
  · rcases lt_trichotomy l 0 with hl | hl | hl
    · have h1 : famC l = 0 := famC_eq_zero_of_neg hl
      have h2 : famC (l - 1) = 0 := famC_eq_zero_of_neg (by omega)
      rw [h1, h2]
      ring
    · -- `l = 0`: then `j = n + 2`
      subst hl
      have hj' : j = (n : ℤ) + 2 := by omega
      rw [hj']
      have h0 : famC (0 : ℤ) = 1 := famC_zero
      have hm1 : famC ((0 : ℤ) - 1) = 0 := famC_eq_zero_of_neg (by norm_num)
      rw [h0, hm1]
      have hl1 : famC (((n : ℤ) + 2) - 1) = famC ((n : ℤ) + 1) := by congr 1; ring
      rw [hl1]
      linarith [famC_boundary n]
    · -- `1 ≤ j` and `1 ≤ l`: the defining ratios
      obtain ⟨m, hm⟩ : ∃ m : ℕ, j = (m : ℤ) + 1 :=
        ⟨(j - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, l = (k : ℤ) + 1 :=
        ⟨(l - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
      have hjpred : famC (j - 1) = famC (m : ℤ) := by rw [hm]; congr 1; ring
      have hkpred : famC (l - 1) = famC (k : ℤ) := by rw [hk]; congr 1; ring
      rw [hjpred, hkpred]
      rw [hm, hk] at h ⊢
      have hn : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
        have hz : (n : ℤ) = (m : ℤ) + (k : ℤ) := by omega
        exact_mod_cast hz
      rw [hn, famC_succ_ratio m, famC_succ_ratio k]
      have key : 2 * ((m : ℝ) + (k : ℝ) + 2) * (((m : ℝ) + 3 / 2) / ((m : ℝ) + 1))
            * (((k : ℝ) + 3 / 2) / ((k : ℝ) + 1))
          = (2 * ((m : ℝ) + (k : ℝ)) + 5)
              * ((((m : ℝ) + 3 / 2) / ((m : ℝ) + 1)) + (((k : ℝ) + 3 / 2) / ((k : ℝ) + 1)))
            - 2 * ((m : ℝ) + (k : ℝ) + 3) := by
        field_simp
        ring
      linear_combination (famC (m : ℤ) * famC (k : ℤ)) * key

/-- The product-to-sum identity with an arbitrary prefactor. -/
lemma two_cos_mul_aux (A a b : ℝ) :
    2 * (Real.cos a * (A * Real.cos b)) = A * (Real.cos (a + b) + Real.cos (a - b)) := by
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- The base case `n = 0`: `famTrig 0 ψ = 1`. -/
lemma famTrig_zero (ψ : ℝ) : famTrig 0 ψ = 1 := by
  have h0 : famC (((0 : ℕ)) : ℤ) = 1 := by simpa using famC_zero
  rw [famTrig, Finset.sum_range_one]
  rw [show (((0 : ℕ)) : ℤ) - (((0 : ℕ)) : ℤ) = (((0 : ℕ)) : ℤ) from by norm_num,
      show (((2 : ℝ) * (((0 : ℕ)) : ℝ) - (((0 : ℕ)) : ℝ)) * ψ) = (0 : ℝ) from by ring,
      h0, Real.cos_zero]
  ring

/-- The base case `n = 1`: `famTrig 1 ψ = 3 cos ψ`. -/
lemma famTrig_one (ψ : ℝ) : famTrig 1 ψ = 3 * Real.cos ψ := by
  have h0 : famC (((0 : ℕ)) : ℤ) = 1 := by simpa using famC_zero
  have h1 : famC (((1 : ℕ)) : ℤ) = 3 / 2 := by simpa using famC_one
  rw [famTrig, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show (((1 : ℕ)) : ℤ) - (((0 : ℕ)) : ℤ) = (((1 : ℕ)) : ℤ) from by norm_num,
      show (((1 : ℕ)) : ℤ) - (((1 : ℕ)) : ℤ) = (((0 : ℕ)) : ℤ) from by norm_num,
      show (((2 : ℝ) * (((0 : ℕ)) : ℝ) - (((1 : ℕ)) : ℝ)) * ψ) = -ψ from by ring,
      show (((2 : ℝ) * (((1 : ℕ)) : ℝ) - (((1 : ℕ)) : ℝ)) * ψ) = ψ from by ring,
      h0, h1, Real.cos_neg]
  ring

/-! ## The three-term recurrence of `famTrig` -/

/--
**The three-term recurrence.**  With `S n ψ := famTrig n ψ`,

`(n+2)·S (n+2) ψ = (2n+5)·cos ψ·S (n+1) ψ - (n+3)·S n ψ`.

The proof writes every sum over the common index range `range (n+3)` (the shifts being
harmless because `famC` vanishes on the negative integers) with the common cosine
`cos ((2i - n - 2)ψ)`, and then applies the pointwise identity `famC_ident` termwise. -/
lemma famTrig_rec (n : ℕ) (ψ : ℝ) :
    ((n : ℝ) + 2) * famTrig (n + 2) ψ
      = (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
        - ((n : ℝ) + 3) * famTrig n ψ := by
  -- the four families of summands, all with the common cosine `cos ((2i - n - 2)ψ)`
  set P : ℕ → ℝ := fun i => famC ((i : ℤ) - 1) * famC ((n : ℤ) + 2 - (i : ℤ))
      * Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hP
  set Q : ℕ → ℝ := fun i => famC (i : ℤ) * famC ((n : ℤ) + 1 - (i : ℤ))
      * Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hQ
  set R : ℕ → ℝ := fun i => famC (i : ℤ) * famC ((n : ℤ) + 2 - (i : ℤ))
      * Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hR
  set U : ℕ → ℝ := fun i => famC ((i : ℤ) - 1) * famC ((n : ℤ) + 1 - (i : ℤ))
      * Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hU
  -- `S (n+2)` is the sum of `R`
  have hSn2 : famTrig (n + 2) ψ = ∑ i ∈ Finset.range (n + 3), R i := by
    simp only [famTrig, hR]
    refine Finset.sum_congr (by rfl) (fun i _ => ?_)
    rw [show (((n + 2 : ℕ)) : ℤ) = (n : ℤ) + 2 from by push_cast; ring,
        show (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 from by push_cast; ring]
  have hP0 : P 0 = 0 := by
    simp only [hP]
    have h1 : famC ((-1 : ℤ)) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [show ((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) from by norm_num, h1]
    ring
  have hQn : Q (n + 2) = 0 := by
    simp only [hQ]
    have h1 : famC ((-1 : ℤ)) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [show ((n : ℤ) + 1 - (((n + 2 : ℕ)) : ℤ)) = (-1 : ℤ) from by push_cast; ring, h1]
    ring
  have hU0 : U 0 = 0 := by
    simp only [hU]
    have h1 : famC ((-1 : ℤ)) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [show ((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) from by norm_num, h1]
    ring
  have hUn : U (n + 2) = 0 := by
    simp only [hU]
    have h1 : famC ((-1 : ℤ)) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [show ((n : ℤ) + 1 - (((n + 2 : ℕ)) : ℤ)) = (-1 : ℤ) from by push_cast; ring, h1]
    ring
  -- `S n` is the sum of `U`
  have hSn : famTrig n ψ = ∑ i ∈ Finset.range (n + 3), U i := by
    rw [show n + 3 = (n + 2) + 1 from by ring, Finset.sum_range_succ, hUn]
    rw [add_zero]
    rw [show n + 2 = (n + 1) + 1 from by ring, Finset.sum_range_succ', hU0]
    rw [add_zero]
    simp only [famTrig]
    refine Finset.sum_congr (by rfl) (fun j _ => ?_)
    simp only [hU]
    rw [show (((j + 1 : ℕ)) : ℤ) - 1 = (j : ℤ) from by push_cast; ring,
        show ((n : ℤ) + 1 - (((j + 1 : ℕ)) : ℤ)) = ((n : ℤ) - (j : ℤ)) from by push_cast; ring,
        show (((2 : ℝ) * (((j + 1 : ℕ)) : ℝ) - ((n : ℝ) + 2)) * ψ)
            = (((2 : ℝ) * (j : ℝ) - (n : ℝ)) * ψ) from by push_cast; ring]
  -- the shifted sums
  have hshiftP : (∑ j ∈ Finset.range (n + 2), P (j + 1)) = ∑ i ∈ Finset.range (n + 3), P i := by
    have h : (∑ i ∈ Finset.range (n + 3), P i)
        = (∑ j ∈ Finset.range (n + 2), P (j + 1)) + P 0 := Finset.sum_range_succ' P (n + 2)
    rw [hP0, add_zero] at h
    exact h.symm
  have hshiftQ : (∑ j ∈ Finset.range (n + 2), Q j) = ∑ i ∈ Finset.range (n + 3), Q i := by
    have h : (∑ i ∈ Finset.range (n + 3), Q i)
        = (∑ j ∈ Finset.range (n + 2), Q j) + Q (n + 2) := Finset.sum_range_succ Q (n + 2)
    rw [hQn, add_zero] at h
    exact h.symm
  -- the doubled cosine expansion of `2 cos ψ · S (n+1)`
  have hstep : ∀ j : ℕ,
      2 * (Real.cos ψ * (famC (j : ℤ) * famC ((((n + 1 : ℕ)) : ℤ) - (j : ℤ))
        * Real.cos (((2 : ℝ) * (j : ℝ) - (((n + 1 : ℕ)) : ℝ)) * ψ))) = P (j + 1) + Q j := by
    intro j
    simp only [hP, hQ]
    rw [two_cos_mul_aux]
    rw [show ψ + ((2 : ℝ) * (j : ℝ) - (((n + 1 : ℕ)) : ℝ)) * ψ
            = ((2 : ℝ) * (((j + 1 : ℕ)) : ℝ) - ((n : ℝ) + 2)) * ψ from by push_cast; ring,
        show ψ - ((2 : ℝ) * (j : ℝ) - (((n + 1 : ℕ)) : ℝ)) * ψ
            = -(((2 : ℝ) * (j : ℝ) - ((n : ℝ) + 2)) * ψ) from by push_cast; ring,
        show famC ((((j + 1 : ℕ)) : ℤ) - 1) = famC ((j : ℤ)) from by congr 1; push_cast; ring,
        show famC ((n : ℤ) + 2 - (((j + 1 : ℕ)) : ℤ)) = famC ((n : ℤ) + 1 - (j : ℤ)) from by
          congr 1; push_cast; ring,
        Real.cos_neg]
    push_cast
    ring
  have hcos : 2 * (Real.cos ψ * famTrig (n + 1) ψ)
      = (∑ i ∈ Finset.range (n + 3), P i) + (∑ i ∈ Finset.range (n + 3), Q i) := by
    simp only [famTrig]
    rw [show (n + 1) + 1 = n + 2 from by ring]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    rw [Finset.sum_add_distrib, hshiftP, hshiftQ]
  -- the termwise identity
  have hterm : ∀ i ∈ Finset.range (n + 3), (2 * ((n : ℝ) + 2)) * R i
      = (2 * (n : ℝ) + 5) * (P i + Q i) - 2 * ((n : ℝ) + 3) * U i := by
    intro i _
    have h := famC_ident n (i : ℤ) ((n : ℤ) + 2 - (i : ℤ)) (by ring)
    have hpred : famC (((n : ℤ) + 2 - (i : ℤ)) - 1) = famC ((n : ℤ) + 1 - (i : ℤ)) := by
      congr 1; ring
    rw [hpred] at h
    simp only [hP, hQ, hR, hU]
    linear_combination (Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ)) * h
  -- the doubled recurrence
  have hdouble : (2 * ((n : ℝ) + 2)) * famTrig (n + 2) ψ
      = (2 * (n : ℝ) + 5)
          * ((∑ i ∈ Finset.range (n + 3), P i) + (∑ i ∈ Finset.range (n + 3), Q i))
        - 2 * ((n : ℝ) + 3) * famTrig n ψ := by
    rw [hSn2, Finset.mul_sum]
    rw [Finset.sum_congr rfl hterm]
    rw [hSn]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmain : 2 * (((n : ℝ) + 2) * famTrig (n + 2) ψ)
      = 2 * ((2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
          - ((n : ℝ) + 3) * famTrig n ψ) := by
    have h1 : 2 * (((n : ℝ) + 2) * famTrig (n + 2) ψ)
        = (2 * ((n : ℝ) + 2)) * famTrig (n + 2) ψ := by ring
    have h2 : (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
        = (2 * (n : ℝ) + 5)
            * (((∑ i ∈ Finset.range (n + 3), P i) + (∑ i ∈ Finset.range (n + 3), Q i)) / 2) := by
      rw [show (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
            = (2 * (n : ℝ) + 5) * (Real.cos ψ * famTrig (n + 1) ψ) from by ring,
          show Real.cos ψ * famTrig (n + 1) ψ
            = (2 * (Real.cos ψ * famTrig (n + 1) ψ)) / 2 from by ring,
          hcos]
    rw [h1, hdouble, h2]
    ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hmain

theorem TrigGegen (n : ℕ) (ψ : ℝ) : Work.FTS.PhiStar.Gegenbauer.gC n (Real.cos ψ) = Work.FTS.PhiStar.famTrig n ψ := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [famTrig_zero]
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
  | one =>
      rw [famTrig_one]
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
  | more n ih1 ih2 =>
      have h2 : ((n : ℝ) + 2) * Work.FTS.PhiStar.Gegenbauer.gC (n + 2) (Real.cos ψ)
          = ((n : ℝ) + 2) * famTrig (n + 2) ψ := by
        rw [Work.FTS.PhiStar.Gegenbauer.gC_rec n (Real.cos ψ), ih1, ih2, famTrig_rec n ψ]
      exact mul_left_cancel₀ (by positivity : ((n : ℝ) + 2) ≠ 0) h2

end Work.FTS.PhiStar.FamLopAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Kernels.phiKernelWeightedLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.FlatWAux.Kernels.phiKernelWeightedLe`

The weighted bound for the inner (`Φ`-) rescaled Green kernel.  Writing the inner piece of the
radial Green function in the form

  `Φ z = ∫ u in (0)..1, h (z * u) * u ^ (Q - 1)`

(the substitution `t = z u` in `∫_0^z h(t) t^{Q-1} dt`), the `j`-th `z`-derivative is the same
integral with `h` replaced by `iteratedDeriv j h`.  If that derivative decays like
`B / (1 + t ^ (j + 2))`, then the `j`-th kernel moment obeys

  `(z+1)^{j+1} |∫₀¹ h^{(j)}(z u) u^{j+Q-1} du|  ≤  2^{j+1} B (1/(j+Q) + 1/(Q-2))`

for every `z > 0` and every `j ≤ 10`, `Q > 2`.

The proof is elementary and uses nothing but the pointwise bound on `h^{(j)}` (the smoothness
hypothesis `hh` is not needed):

* for `u ∈ (0,1)` and `t = z u > 0` one has `|h^{(j)}(t)| ≤ B`, hence the integrand is
  dominated by `B u^{j+Q-1}`, and `(z+1)^{j+1} ≤ 2^{j+1}` for `z ≤ 1`;
* for `z ≥ 1` the sharper comparison `u^{j+Q-1}/(1+(zu)^{j+2}) ≤ z^{-(j+2)} u^{Q-3}`, obtained
  from `(zu)^{j+2}/(1+(zu)^{j+2}) ≤ 1`, gives the second summand, and
  `(z+1)^{j+1} z^{-(j+2)} ≤ 2^{j+1}` for `z ≥ 1`.

The elementary integrals are Mathlib's `integral_rpow`; the domination is
`norm_integral_le_integral_norm` together with `integral_mono_of_nonneg` on the set `Ioc 0 1`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false

namespace Work.FTS.PhiStar.FlatWAux.Kernels

/-- Pointwise comparison used in the large-`z` regime: on `(0,1]` the decaying kernel
`u^{j+Q-1}/(1+(z u)^{j+2})` is dominated by `z^{-(j+2)} u^{Q-3}`. -/
private lemma phiKernel_pointwise {j : ℕ} {Q B : ℝ} (hB : 0 ≤ B) {H : ℝ → ℝ}
    (hb : ∀ t : ℝ, 0 < t → |H t| ≤ B / (1 + t ^ (j + 2))) {z u : ℝ} (hz : 0 < z) (hu : 0 < u) :
    |H (z * u)| * u ^ ((j : ℝ) + Q - 1)
      ≤ B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3) := by
  have hzu : 0 < z * u := mul_pos hz hu
  have hup : (0 : ℝ) ≤ u ^ ((j : ℝ) + Q - 1) := Real.rpow_nonneg hu.le _
  have huz : (0 : ℝ) ≤ u ^ (Q - 3) := Real.rpow_nonneg hu.le _
  -- `u^p = u^{Q-3} * u^{j+2}`
  have hsplit : u ^ ((j : ℝ) + Q - 1) = u ^ (Q - 3) * u ^ (((j + 2 : ℕ)) : ℝ) := by
    rw [← Real.rpow_add hu]
    congr 1
    push_cast
    ring
  -- `u^{j+2} = (z^{j+2})⁻¹ * (z*u)^{j+2}`
  have huz_nat : u ^ (j + 2) = (z ^ (j + 2))⁻¹ * (z * u) ^ (j + 2) := by
    rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt hz)), one_mul]
  have huz' : u ^ (((j + 2 : ℕ)) : ℝ) = (z ^ (j + 2))⁻¹ * (z * u) ^ (j + 2) := by
    rw [Real.rpow_natCast]
    exact huz_nat
  -- the quotient is at most `1`
  have hfrac : (z * u) ^ (j + 2) / (1 + (z * u) ^ (j + 2)) ≤ 1 := by
    have hp1 : (0 : ℝ) < 1 + (z * u) ^ (j + 2) := by
      have h := pow_nonneg hzu.le (j + 2)
      linarith
    rw [div_le_one hp1]
    have h := pow_nonneg hzu.le (j + 2)
    linarith
  have hkey : u ^ (((j + 2 : ℕ)) : ℝ) / (1 + (z * u) ^ (j + 2))
      ≤ z ^ (-(((j + 2 : ℕ)) : ℝ)) := by
    calc u ^ (((j + 2 : ℕ)) : ℝ) / (1 + (z * u) ^ (j + 2))
        = ((z ^ (j + 2))⁻¹ * (z * u) ^ (j + 2)) / (1 + (z * u) ^ (j + 2)) := by rw [huz']
      _ = (z ^ (j + 2))⁻¹ * ((z * u) ^ (j + 2) / (1 + (z * u) ^ (j + 2))) := by ring
      _ ≤ (z ^ (j + 2))⁻¹ * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = z ^ (-(((j + 2 : ℕ)) : ℝ)) := by
          rw [mul_one, ← Real.rpow_natCast z (j + 2), ← Real.rpow_neg hz.le]
  calc |H (z * u)| * u ^ ((j : ℝ) + Q - 1)
      ≤ (B / (1 + (z * u) ^ (j + 2))) * u ^ ((j : ℝ) + Q - 1) :=
        mul_le_mul_of_nonneg_right (hb (z * u) hzu) hup
    _ = B * (u ^ (Q - 3) * (u ^ (((j + 2 : ℕ)) : ℝ) / (1 + (z * u) ^ (j + 2)))) := by
        rw [hsplit]
        ring
    _ ≤ B * (u ^ (Q - 3) * z ^ (-(((j + 2 : ℕ)) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey huz) hB
    _ = B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3) := by ring

/-- The `z ≤ 1` regime: the crude bound `|h^{(j)}| ≤ B` suffices. -/
private lemma phiKernel_le_small {j : ℕ} {Q B z : ℝ} (hQ : 2 < Q) (hB : 0 ≤ B) (hz : 0 < z)
    {H : ℝ → ℝ} (hb : ∀ t : ℝ, 0 < t → |H t| ≤ B / (1 + t ^ (j + 2))) :
    |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)| ≤ B / ((j : ℝ) + Q) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hp : (-1 : ℝ) < (j : ℝ) + Q - 1 := by
    have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hInt : Integrable (fun u : ℝ => B * u ^ ((j : ℝ) + Q - 1))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h1 := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
      (r := (j : ℝ) + Q - 1) hp
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01] at h1
    exact h1.const_mul B
  have habs : |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)| := by
    rw [intervalIntegral.integral_of_le h01]
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (fun u : ℝ => H (z * u) * u ^ ((j : ℝ) + Q - 1))
  have hmono : ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, B * u ^ ((j : ℝ) + Q - 1) := by
    refine integral_mono_of_nonneg ?_ hInt ?_
    · filter_upwards with u
      exact abs_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 < u := hu.1
      have hup : (0 : ℝ) ≤ u ^ ((j : ℝ) + Q - 1) := Real.rpow_nonneg hu0.le _
      rw [abs_mul, abs_of_nonneg hup]
      refine mul_le_mul_of_nonneg_right ?_ hup
      have hzu : 0 < z * u := mul_pos hz hu0
      have h1 := hb (z * u) hzu
      have htnn : (0 : ℝ) ≤ (z * u) ^ (j + 2) := pow_nonneg hzu.le _
      have hpos : (0 : ℝ) < 1 + (z * u) ^ (j + 2) := by linarith
      refine le_trans h1 ?_
      rw [div_le_iff₀ hpos]
      nlinarith [hB, htnn]
  have hval : ∫ u in Ioc (0 : ℝ) 1, B * u ^ ((j : ℝ) + Q - 1) = B / ((j : ℝ) + Q) := by
    rw [← intervalIntegral.integral_of_le h01, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl hp), Real.one_rpow,
      Real.zero_rpow (by linarith : (j : ℝ) + Q - 1 + 1 ≠ 0), sub_zero,
      show (j : ℝ) + Q - 1 + 1 = (j : ℝ) + Q from by ring]
    ring
  calc |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)| := habs
    _ ≤ ∫ u in Ioc (0 : ℝ) 1, B * u ^ ((j : ℝ) + Q - 1) := hmono
    _ = B / ((j : ℝ) + Q) := hval

/-- The `z ≥ 1` regime: the decay `|h^{(j)}(t)| ≤ B/(1+t^{j+2})` gives the `z^{-(j+2)}` rate. -/
private lemma phiKernel_le_large {j : ℕ} {Q B z : ℝ} (hQ : 2 < Q) (hB : 0 ≤ B) (hz : 1 ≤ z)
    {H : ℝ → ℝ} (hb : ∀ t : ℝ, 0 < t → |H t| ≤ B / (1 + t ^ (j + 2))) :
    |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ B * z ^ (-(((j + 2 : ℕ)) : ℝ)) / (Q - 2) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hexp : (-1 : ℝ) < Q - 3 := by linarith
  have hInt : Integrable (fun u : ℝ => B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h1 := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) (r := Q - 3) hexp
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01] at h1
    exact h1.const_mul (B * z ^ (-(((j + 2 : ℕ)) : ℝ)))
  have habs : |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)| := by
    rw [intervalIntegral.integral_of_le h01]
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (fun u : ℝ => H (z * u) * u ^ ((j : ℝ) + Q - 1))
  have hmono : ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3) := by
    refine integral_mono_of_nonneg ?_ hInt ?_
    · filter_upwards with u
      exact abs_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 < u := hu.1
      have hup : (0 : ℝ) ≤ u ^ ((j : ℝ) + Q - 1) := Real.rpow_nonneg hu0.le _
      rw [abs_mul, abs_of_nonneg hup]
      exact phiKernel_pointwise hB hb hz0 hu0
  have hval : ∫ u in Ioc (0 : ℝ) 1, B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3)
      = B * z ^ (-(((j + 2 : ℕ)) : ℝ)) / (Q - 2) := by
    rw [← intervalIntegral.integral_of_le h01, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl hexp), Real.one_rpow,
      Real.zero_rpow (by linarith : Q - 3 + 1 ≠ 0), sub_zero,
      show Q - 3 + 1 = Q - 2 from by ring]
    ring
  calc |∫ u in (0 : ℝ)..1, H (z * u) * u ^ ((j : ℝ) + Q - 1)|
      ≤ ∫ u in Ioc (0 : ℝ) 1, |H (z * u) * u ^ ((j : ℝ) + Q - 1)| := habs
    _ ≤ ∫ u in Ioc (0 : ℝ) 1, B * z ^ (-(((j + 2 : ℕ)) : ℝ)) * u ^ (Q - 3) := hmono
    _ = B * z ^ (-(((j + 2 : ℕ)) : ℝ)) / (Q - 2) := hval

/-- `(z+1)^{j+1} z^{-(j+2)} ≤ 2^{j+1}` for `z ≥ 1`. -/
private lemma phiKernel_ratio {j : ℕ} {z : ℝ} (hz : 1 ≤ z) :
    (z + 1) ^ (j + 1) * z ^ (-(((j + 2 : ℕ)) : ℝ)) ≤ (2 : ℝ) ^ (j + 1) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hq : (z + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) * z ^ (j + 1) := by
    have h1 : z + 1 ≤ 2 * z := by linarith
    have h0 : (0 : ℝ) ≤ z + 1 := by linarith
    calc (z + 1) ^ (j + 1) ≤ (2 * z) ^ (j + 1) := pow_le_pow_left₀ h0 h1 (j + 1)
      _ = (2 : ℝ) ^ (j + 1) * z ^ (j + 1) := by rw [mul_pow]
  have hzpow : z ^ (((j + 1 : ℕ)) : ℝ) * z ^ (-(((j + 2 : ℕ)) : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add hz0]
    have hexp : (((j + 1 : ℕ)) : ℝ) + (-(((j + 2 : ℕ)) : ℝ)) = -1 := by
      push_cast
      ring
    rw [hexp]
    exact Real.rpow_le_one_of_one_le_of_nonpos hz (by norm_num)
  calc (z + 1) ^ (j + 1) * z ^ (-(((j + 2 : ℕ)) : ℝ))
      ≤ ((2 : ℝ) ^ (j + 1) * z ^ (j + 1)) * z ^ (-(((j + 2 : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hz0.le _)
    _ = (2 : ℝ) ^ (j + 1) * (z ^ (((j + 1 : ℕ)) : ℝ) * z ^ (-(((j + 2 : ℕ)) : ℝ))) := by
        rw [show z ^ (j + 1) = z ^ (((j + 1 : ℕ)) : ℝ) from
          (Real.rpow_natCast z (j + 1)).symm]
        ring
    _ ≤ (2 : ℝ) ^ (j + 1) * 1 :=
        mul_le_mul_of_nonneg_left hzpow (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (j + 1) := by ring

theorem phiKernelWeightedLe {Q B : ℝ} (hQ : 2 < Q) (hB : 0 ≤ B) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 14 h (Set.Ioi 0))
    (hb : ∀ j : ℕ, j ≤ 10 → ∀ t : ℝ, 0 < t → |iteratedDeriv j h t| ≤ B / (1 + t ^ (j + 2))) :
    ∀ j : ℕ, j ≤ 10 → ∀ z : ℝ, 0 < z →
      (z + 1) ^ (j + 1) *
          |∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + Q - 1)|
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / ((j : ℝ) + Q) + 1 / (Q - 2)) := by
  intro j hj z hz
  have hQ2 : (0 : ℝ) < Q - 2 := by linarith
  have hjQ : (0 : ℝ) < (j : ℝ) + Q := by
    have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hden1 : (0 : ℝ) ≤ 1 / ((j : ℝ) + Q) := div_nonneg zero_le_one hjQ.le
  have hden2 : (0 : ℝ) ≤ 1 / (Q - 2) := div_nonneg zero_le_one hQ2.le
  have hpow : (0 : ℝ) ≤ (z + 1) ^ (j + 1) := pow_nonneg (by linarith) _
  have hb' : ∀ t : ℝ, 0 < t → |iteratedDeriv j h t| ≤ B / (1 + t ^ (j + 2)) :=
    fun t ht => hb j hj t ht
  rcases le_or_gt z 1 with hzle | hzlt
  · have hI := phiKernel_le_small (j := j) (Q := Q) (B := B) (z := z) hQ hB hz hb'
    have h2 : (z + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ z + 1) (by linarith) (j + 1)
    have hBQ : (0 : ℝ) ≤ B / ((j : ℝ) + Q) := div_nonneg hB hjQ.le
    calc (z + 1) ^ (j + 1)
          * |∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + Q - 1)|
        ≤ (z + 1) ^ (j + 1) * (B / ((j : ℝ) + Q)) := mul_le_mul_of_nonneg_left hI hpow
      _ ≤ (2 : ℝ) ^ (j + 1) * (B / ((j : ℝ) + Q)) := mul_le_mul_of_nonneg_right h2 hBQ
      _ = (2 : ℝ) ^ (j + 1) * B * (1 / ((j : ℝ) + Q)) := by ring
      _ ≤ (2 : ℝ) ^ (j + 1) * B * (1 / ((j : ℝ) + Q) + 1 / (Q - 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_right hden2
  · have hz1 : 1 ≤ z := le_of_lt hzlt
    have hI := phiKernel_le_large (j := j) (Q := Q) (B := B) (z := z) hQ hB hz1 hb'
    have hratio := phiKernel_ratio (j := j) hz1
    calc (z + 1) ^ (j + 1)
          * |∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + Q - 1)|
        ≤ (z + 1) ^ (j + 1) * (B * z ^ (-(((j + 2 : ℕ)) : ℝ)) / (Q - 2)) :=
          mul_le_mul_of_nonneg_left hI hpow
      _ = ((z + 1) ^ (j + 1) * z ^ (-(((j + 2 : ℕ)) : ℝ))) * B * (1 / (Q - 2)) := by ring
      _ ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (Q - 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hB) hden2
      _ ≤ (2 : ℝ) ^ (j + 1) * B * (1 / ((j : ℝ) + Q) + 1 / (Q - 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_left hden1

end Work.FTS.PhiStar.FlatWAux.Kernels
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Kernels.psiKernelWeightedLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Real

namespace Work.FTS.PhiStar.FlatWAux.Kernels

/-- Comparison of a set integral over `Ioi 1` of a function dominated by an integrable one. -/
private lemma abs_integral_Ioi_le {F G : ℝ → ℝ} (hG : IntegrableOn G (Set.Ioi 1))
    (h : ∀ u ∈ Set.Ioi 1, |F u| ≤ G u) :
    |∫ u in Set.Ioi 1, F u| ≤ ∫ u in Set.Ioi 1, G u := by
  refine (abs_integral_le_integral_abs (f := F)).trans ?_
  exact setIntegral_mono_of_nonneg (fun u _ => abs_nonneg _) h hG

/-- `∫_1^∞ u^a du = 1/(-(a+1))` for `a < -1`. -/
private lemma integral_Ioi_rpow (a : ℝ) (ha : a < -1) :
    ∫ u in Set.Ioi 1, u ^ a = 1 / (-(a + 1)) := by
  rw [integral_Ioi_rpow_of_lt (a := a) ha (c := 1) (by norm_num)]
  rw [Real.one_rpow, div_eq_mul_inv, div_eq_mul_inv, inv_neg]
  ring

/-- `u ↦ c u^a` is integrable on `(1,∞)` for `a < -1`. -/
private lemma integrableOn_Ioi_const_mul_rpow (c a : ℝ) (ha : a < -1) :
    IntegrableOn (fun u : ℝ => c * u ^ a) (Set.Ioi 1) := by
  have h : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (t := 1) (by norm_num)).mpr ha
  exact h.const_mul c

theorem psiKernelWeightedLe {P B : ℝ} (hP : 9 ≤ P) (hB : 0 ≤ B) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 14 h (Set.Ioi 0))
    (hb : ∀ j : ℕ, j ≤ 10 → ∀ t : ℝ, 0 < t → |iteratedDeriv j h t| ≤ B / (1 + t ^ (j + 2))) :
    ∀ j : ℕ, j ≤ 10 → (j : ℝ) < P → ∀ z : ℝ, 0 < z →
      (z + 1) ^ (j + 1) *
          |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ)) + 1 / (P + 2)) := by
  intro j hj hjP z hz
  have _ := hh
  have hqpos : 0 < P - (j : ℝ) := by linarith
  have hElt : (j : ℝ) - P - 1 < -1 := by linarith
  have hP3lt : -P - 3 < -1 := by linarith
  have hP2pos : 0 < P + 2 := by linarith
  -- ### pointwise bound, first (crude) form
  have key1 : ∀ u ∈ Set.Ioi 1,
      |iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)| ≤ B * u ^ ((j : ℝ) - P - 1) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hzu : (0 : ℝ) < z * u := mul_pos hz hu0
    have h1 : |iteratedDeriv j h (z * u)| ≤ B / (1 + (z * u) ^ (j + 2)) := hb j hj (z * u) hzu
    have h2 : B / (1 + (z * u) ^ (j + 2)) ≤ B := by
      rw [div_le_iff₀ (by positivity)]
      refine le_mul_of_one_le_right hB ?_
      have hnn : (0 : ℝ) ≤ (z * u) ^ (j + 2) := pow_nonneg hzu.le _
      linarith
    calc |iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        = |iteratedDeriv j h (z * u)| * u ^ ((j : ℝ) - P - 1) := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      _ ≤ B * u ^ ((j : ℝ) - P - 1) :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (Real.rpow_nonneg hu0.le _)
  -- ### pointwise bound, sharp form with the `j+2` decay
  have key2 : ∀ u ∈ Set.Ioi 1,
      |iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hzu : (0 : ℝ) < z * u := mul_pos hz hu0
    have h1 : |iteratedDeriv j h (z * u)| ≤ B / (1 + (z * u) ^ (j + 2)) := hb j hj (z * u) hzu
    have hpow : (z * u) ^ (j + 2) = (z * u) ^ ((j : ℝ) + 2) := by
      have hc : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
      rw [← Real.rpow_natCast (z * u) (j + 2), hc]
    have hp : (0 : ℝ) < (z * u) ^ (j + 2) := pow_pos hzu _
    have h2 : B / (1 + (z * u) ^ (j + 2)) ≤ B / ((z * u) ^ (j + 2)) := by
      refine div_le_div_of_nonneg_left hB hp ?_
      have hnn : (0 : ℝ) ≤ (z * u) ^ (j + 2) := hp.le
      linarith
    have h3 : B / ((z * u) ^ (j + 2)) = B * (z * u) ^ (-((j : ℝ) + 2)) := by
      rw [hpow, div_eq_mul_inv, ← Real.rpow_neg hzu.le]
    have h4 : B * (z * u) ^ (-((j : ℝ) + 2))
        = B * z ^ (-((j : ℝ) + 2)) * u ^ (-((j : ℝ) + 2)) := by
      rw [Real.mul_rpow hz.le hu0.le]; ring
    have h5 : |iteratedDeriv j h (z * u)| ≤ B * z ^ (-((j : ℝ) + 2)) * u ^ (-((j : ℝ) + 2)) :=
      h1.trans (h2.trans (le_of_eq (h3.trans h4)))
    calc |iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        = |iteratedDeriv j h (z * u)| * u ^ ((j : ℝ) - P - 1) := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      _ ≤ (B * z ^ (-((j : ℝ) + 2)) * u ^ (-((j : ℝ) + 2))) * u ^ ((j : ℝ) - P - 1) :=
          mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hu0.le _)
      _ = B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3) := by
          have hcomb : u ^ (-((j : ℝ) + 2)) * u ^ ((j : ℝ) - P - 1) = u ^ (-P - 3) := by
            rw [← Real.rpow_add hu0]
            congr 1
            ring
          rw [mul_assoc, hcomb]
  -- ### the two integral values
  have hInt1 : ∫ u in Set.Ioi 1, u ^ ((j : ℝ) - P - 1) = 1 / (P - (j : ℝ)) := by
    rw [integral_Ioi_rpow ((j : ℝ) - P - 1) hElt]
    rw [show -(((j : ℝ) - P - 1) + 1) = P - (j : ℝ) by ring]
  have hInt2 : ∫ u in Set.Ioi 1, u ^ (-P - 3) = 1 / (P + 2) := by
    rw [integral_Ioi_rpow (-P - 3) hP3lt]
    rw [show -(-P - 3 + 1) = P + 2 by ring]
  -- ### integrability of the dominants
  have hintG1 : IntegrableOn (fun u : ℝ => B * u ^ ((j : ℝ) - P - 1)) (Set.Ioi 1) :=
    integrableOn_Ioi_const_mul_rpow B ((j : ℝ) - P - 1) hElt
  have hintG2 : IntegrableOn (fun u : ℝ => B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3))
      (Set.Ioi 1) :=
    integrableOn_Ioi_const_mul_rpow (B * z ^ (-((j : ℝ) + 2))) (-P - 3) hP3lt
  rcases lt_or_ge z 1 with hz1 | hz1
  · -- ### case `z < 1`
    have hA : |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ B * (1 / (P - (j : ℝ))) := by
      have hmain := abs_integral_Ioi_le
        (F := fun u => iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1))
        (G := fun u => B * u ^ ((j : ℝ) - P - 1)) hintG1 key1
      have hG : ∫ u in Set.Ioi 1, B * u ^ ((j : ℝ) - P - 1) = B * (1 / (P - (j : ℝ))) := by
        rw [MeasureTheory.integral_const_mul, hInt1]
      rwa [hG] at hmain
    have hW : (z + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) (j + 1)
    have hstep1 : (z + 1) ^ (j + 1) *
          |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ (z + 1) ^ (j + 1) * (B * (1 / (P - (j : ℝ)))) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have hstep2 : (z + 1) ^ (j + 1) * (B * (1 / (P - (j : ℝ))))
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ))) := by
      calc (z + 1) ^ (j + 1) * (B * (1 / (P - (j : ℝ))))
          = ((z + 1) ^ (j + 1) * B) * (1 / (P - (j : ℝ))) := by ring
        _ ≤ ((2 : ℝ) ^ (j + 1) * B) * (1 / (P - (j : ℝ))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW hB) (by positivity)
        _ = (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ))) := by ring
    have hstep3 : (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ)))
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ)) + 1 / (P + 2)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (mul_nonneg (pow_nonneg (by norm_num) _) hB)
    linarith
  · -- ### case `1 ≤ z`
    have hA : |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2)) := by
      have hmain := abs_integral_Ioi_le
        (F := fun u => iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1))
        (G := fun u => B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3)) hintG2 key2
      have hG : ∫ u in Set.Ioi 1, B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3)
          = B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2)) := by
        rw [MeasureTheory.integral_const_mul, hInt2]
      rwa [hG] at hmain
    have hW : (z + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) * z ^ (j + 1) := by
      have h1 : (z + 1) ^ (j + 1) ≤ (2 * z) ^ (j + 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith) (j + 1)
      rwa [mul_pow] at h1
    have hzpow : z ^ (j + 1) * z ^ (-((j : ℝ) + 2)) = z ^ (-1 : ℝ) := by
      have hc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [← Real.rpow_natCast z (j + 1), hc, ← Real.rpow_add hz]
      congr 1
      ring
    have hzle : z ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one]
      exact inv_le_one_of_one_le₀ hz1
    have hnonneg : 0 ≤ B * (1 / (P + 2)) := mul_nonneg hB (by positivity)
    have hstep1 : (z + 1) ^ (j + 1) *
          |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ (z + 1) ^ (j + 1) * (B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2))) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have hstep2 : (z + 1) ^ (j + 1) * (B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2)))
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P + 2)) := by
      calc (z + 1) ^ (j + 1) * (B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2)))
          = ((z + 1) ^ (j + 1) * z ^ (-((j : ℝ) + 2))) * (B * (1 / (P + 2))) := by ring
        _ ≤ ((2 : ℝ) ^ (j + 1) * z ^ (j + 1) * z ^ (-((j : ℝ) + 2)))
              * (B * (1 / (P + 2))) := by
            refine mul_le_mul_of_nonneg_right ?_ hnonneg
            exact mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg hz.le _)
        _ = (2 : ℝ) ^ (j + 1) * (z ^ (j + 1) * z ^ (-((j : ℝ) + 2)))
              * (B * (1 / (P + 2))) := by ring
        _ = (2 : ℝ) ^ (j + 1) * z ^ (-1 : ℝ) * (B * (1 / (P + 2))) := by rw [hzpow]
        _ ≤ (2 : ℝ) ^ (j + 1) * 1 * (B * (1 / (P + 2))) := by
            refine mul_le_mul_of_nonneg_right ?_ hnonneg
            exact mul_le_mul_of_nonneg_left hzle (pow_nonneg (by norm_num) _)
        _ = (2 : ℝ) ^ (j + 1) * B * (1 / (P + 2)) := by ring
    have hstep3 : (2 : ℝ) ^ (j + 1) * B * (1 / (P + 2))
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ)) + 1 / (P + 2)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity))
        (mul_nonneg (pow_nonneg (by norm_num) _) hB)
    linarith

end Work.FTS.PhiStar.FlatWAux.Kernels
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.LinvTsumEFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- The summability majorant of the `m`-th summand of the `Linv`-series: `(2m+1)·(m+1)^{-5/2}`,
which is of order `m^{-3/2}` and hence summable. -/
def linvMaj (m : ℕ) : ℝ := (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))

theorem linvMaj_def (m : ℕ) :
    linvMaj m = (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := rfl

theorem linvMaj_nonneg (m : ℕ) : 0 ≤ linvMaj m := by
  rw [linvMaj_def]
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)

/-- The majorant `Σ_m (2m+1)(m+1)^{-5/2}` is summable (comparison with `Σ_m (m+1)^{-3/2}`). -/
theorem linvMaj_summable : Summable linvMaj := by
  have h3 : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    have h : Summable (fun m : ℕ => ((m : ℝ)) ^ (-(3 / 2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun m : ℕ => ((m : ℝ)) ^ (-(3 / 2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hmaj : Summable (fun m : ℕ => 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := h3.mul_left 2
  refine Summable.of_nonneg_of_le (fun m => linvMaj_nonneg m) (fun m => ?_) hmaj
  rw [linvMaj_def]
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hpow : ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
      = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    calc ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
        = ((m : ℝ) + 1) ^ (1 : ℝ) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
          rw [Real.rpow_one]
      _ = ((m : ℝ) + 1) ^ ((1 : ℝ) + (-(5 / 2 : ℝ))) := by rw [Real.rpow_add hm1]
      _ = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
          rw [show (1 : ℝ) + (-(5 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num]
  calc (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
      ≤ (2 * ((m : ℝ) + 1)) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hm1) _)
        linarith
    _ = 2 * (((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) := by ring
    _ = 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by rw [hpow]

theorem LinvTsumEFam (c : ℕ → ℝ) (Cd Ce : ℝ) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce)
    (hsup : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * (2 * (m : ℝ) + 1))
    (hc : ∀ m : ℕ, |c m| ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.FTS.PhiStar.Linv
          (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        = ∑' m : ℕ, c m * Work.FTS.PhiStar.Linv
            (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ := by
  intro θ hθ
  obtain ⟨hθ0, hθπ⟩ := hθ
  have hθle : (0 : ℝ) ≤ θ := le_of_lt hθ0
  -- every point of `[0, θ]` lies in `Iθ = [0, π/2]`
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) θ, t ∈ Work.Spaces.Iθ := by
    intro t ht
    have h2 : t ≤ Real.pi / 2 := le_of_lt (lt_of_le_of_lt ht.2 hθπ)
    change t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
    exact Set.mem_Icc.mpr ⟨ht.1, h2⟩
  -- the pointwise bound on the regularised integrand of a single mode
  have hLip : ∀ m t, t ∈ Set.Icc (0 : ℝ) θ →
      |Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t|
        ≤ Ce * (2 * (m : ℝ) + 1) / 2 := by
    intro m t ht
    have hfac : |Real.sin t * Real.cos t ^ 2 / 2| ≤ 1 / 2 := by
      rw [abs_div, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 : |Real.sin t| * |Real.cos t| ^ 2 ≤ 1 :=
        calc |Real.sin t| * |Real.cos t| ^ 2 ≤ 1 * 1 :=
              mul_le_mul (Real.abs_sin_le_one t)
                (by nlinarith [Real.abs_cos_le_one t, abs_nonneg (Real.cos t)])
                (by positivity) zero_le_one
          _ = 1 := by norm_num
      linarith
    calc |Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t|
        = |Real.sin t * Real.cos t ^ 2 / 2|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m t| := by
          simp only [Work.FTS.PhiStar.LinvPhiInt, abs_mul]
      _ ≤ (1 / 2) * (Ce * (2 * (m : ℝ) + 1)) :=
          mul_le_mul hfac (hsup m t (hmem t ht)) (abs_nonneg _) (by norm_num)
      _ = Ce * (2 * (m : ℝ) + 1) / 2 := by ring
  -- the same bound against the summable majorant
  have hGb : ∀ m t, t ∈ Set.Icc (0 : ℝ) θ →
      ‖c m * Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖
        ≤ Cd * Ce / 2 * linvMaj m := by
    intro m t ht
    rw [Real.norm_eq_abs, abs_mul]
    calc |c m| * |Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t|
        ≤ (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) * (Ce * (2 * (m : ℝ) + 1) / 2) :=
          mul_le_mul (hc m) (hLip m t ht) (abs_nonneg _)
            (mul_nonneg hCd (Real.rpow_nonneg (by positivity) _))
      _ = Cd * Ce / 2 * linvMaj m := by
          rw [linvMaj_def]; ring
  -- continuity, hence integrability of every summand on `(0, θ]`
  have hcontG : ∀ m : ℕ, Continuous (fun t : ℝ =>
      c m * Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t) := by
    intro m
    have hli : Continuous (fun t : ℝ =>
        Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t) := by
      change Continuous (fun t : ℝ => Real.sin t * Real.cos t ^ 2 / 2
        * Work.FTS.PhiStar.Gegenbauer.eFam m t)
      exact ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).div_const 2).mul
        (Work.FTS.PhiStar.Series.continuous_eFam m)
    exact continuous_const.mul hli
  have hGint : ∀ m : ℕ, Integrable
      (fun t : ℝ => c m * Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t)
      (volume.restrict (Set.Ioc (0 : ℝ) θ)) := by
    intro m
    exact ((hcontG m).intervalIntegrable (0 : ℝ) θ).1
  -- the integral of the norm of a summand is bounded by the summable majorant
  have hle : ∀ m : ℕ, ∫ t, ‖c m * Work.FTS.PhiStar.LinvPhiInt
        (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) θ))
      ≤ θ * (Cd * Ce / 2 * linvMaj m) := by
    intro m
    have h1 : IntervalIntegrable (fun t : ℝ => ‖c m * Work.FTS.PhiStar.LinvPhiInt
        (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖) volume (0 : ℝ) θ :=
      (hcontG m).norm.intervalIntegrable 0 θ
    have h2 : IntervalIntegrable (fun _ : ℝ => Cd * Ce / 2 * linvMaj m) volume (0 : ℝ) θ :=
      continuous_const.intervalIntegrable 0 θ
    rw [← intervalIntegral.integral_of_le hθle]
    have hmono := intervalIntegral.integral_mono_on hθle h1 h2 (fun x hx => hGb m x hx)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
    exact hmono
  have hGsum : Summable (fun m : ℕ => ∫ t, ‖c m * Work.FTS.PhiStar.LinvPhiInt
      (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) θ))) := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => θ * (Cd * Ce / 2 * linvMaj m))
      ((linvMaj_summable.mul_left (Cd * Ce / 2)).mul_left θ) (fun m => ?_)
    calc ‖∫ t, ‖c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) θ))‖
        ≤ ∫ t, ‖‖c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) θ)) :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ t, ‖c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) θ)) := by simp
      _ ≤ θ * (Cd * Ce / 2 * linvMaj m) := hle m
  -- the interchange of the integral with the series
  have hkey : (∑' m : ℕ, ∫ t, c m * Work.FTS.PhiStar.LinvPhiInt
        (Work.FTS.PhiStar.Gegenbauer.eFam m) t ∂(volume.restrict (Set.Ioc (0 : ℝ) θ)))
      = ∫ t in Set.Ioc (0 : ℝ) θ, ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhiInt
          (Work.FTS.PhiStar.Gegenbauer.eFam m) t :=
    MeasureTheory.integral_tsum_of_summable_integral_norm
      (μ := volume.restrict (Set.Ioc (0 : ℝ) θ))
      (F := fun m t => c m * Work.FTS.PhiStar.LinvPhiInt
        (Work.FTS.PhiStar.Gegenbauer.eFam m) t) hGint hGsum
  -- the pointwise identity for the regularised integrand of the series
  have hpt : ∀ t : ℝ, Work.FTS.PhiStar.LinvPhiInt
      (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) t
      = ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhiInt
          (Work.FTS.PhiStar.Gegenbauer.eFam m) t := by
    intro t
    simp only [Work.FTS.PhiStar.LinvPhiInt]
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    rw [← mul_assoc, mul_comm (Real.sin t * Real.cos t ^ 2 / 2) (c m), mul_assoc]
  -- hence `LinvPhi` of the series is the series of the `LinvPhi`
  have hPhi : Work.FTS.PhiStar.LinvPhi
      (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
      = ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhi
          (Work.FTS.PhiStar.Gegenbauer.eFam m) θ := by
    calc Work.FTS.PhiStar.LinvPhi
          (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        = ∫ t in (0 : ℝ)..θ, Work.FTS.PhiStar.LinvPhiInt
            (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) t := rfl
      _ = ∫ t in (0 : ℝ)..θ, ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t :=
          intervalIntegral.integral_congr (fun t _ => hpt t)
      _ = ∫ t in Set.Ioc (0 : ℝ) θ, ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t := intervalIntegral.integral_of_le hθle
      _ = ∑' m : ℕ, ∫ t in Set.Ioc (0 : ℝ) θ, c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t := hkey.symm
      _ = ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhi
            (Work.FTS.PhiStar.Gegenbauer.eFam m) θ := by
          refine tsum_congr (fun m => ?_)
          rw [← intervalIntegral.integral_of_le hθle, intervalIntegral.integral_const_mul]
          rfl
  -- the pulled-out form of `Linv`
  have hLinv_eq : ∀ h : ℝ → ℝ, Work.FTS.PhiStar.Linv h θ
      = (-(Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹) * Work.FTS.PhiStar.LinvPhi h θ := by
    intro h
    rw [Work.FTS.PhiStar.Linv_eq_phi]
    rw [neg_mul]
  have hstep : ∀ m : ℕ, c m * Work.FTS.PhiStar.Linv
      (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
      = (-(Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹) * (c m * Work.FTS.PhiStar.LinvPhi
          (Work.FTS.PhiStar.Gegenbauer.eFam m) θ) := by
    intro m
    rw [hLinv_eq]
    rw [← mul_assoc, mul_comm (c m) (-(Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹), mul_assoc]
  -- the final assembly
  calc Work.FTS.PhiStar.Linv
        (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
      = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * Work.FTS.PhiStar.LinvPhi
          (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ) :=
        Work.FTS.PhiStar.Linv_eq_phi _ _
    _ = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhi
          (Work.FTS.PhiStar.Gegenbauer.eFam m) θ)) := by rw [hPhi]
    _ = ∑' m : ℕ, c m * Work.FTS.PhiStar.Linv
          (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ := by
        rw [tsum_congr hstep, tsum_mul_left, neg_mul]

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Linv_lop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- `Lop (Linv h) = (6 - 10 cos²θ)·Linv h - h` on `(0, π/2)`, for `h` continuous and bounded
there with vanishing `sin θ cos²θ`-moment.

This is the first-order form of `LinvI_solves`: writing `v = LinvI h` (so that
`Lzero1 (sin 2θ · v) = h`), the substitution identity
`Lzero1 (sin 2θ · v) = -sin 2θ · v'' + (6 - 10 cos²θ) · v'`
together with `v' = Linv h` gives `-sin 2θ ·(Linv h)' + (6-10cos²θ)·Linv h = h`, i.e. the
claim, since `Lop u θ = sin(2θ)·u'(θ)`. -/
theorem Linv_lop {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ M)
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.Lop (Work.FTS.PhiStar.Linv h) θ
        = (6 - 10 * Real.cos θ ^ 2) * Work.FTS.PhiStar.Linv h θ - h θ := by
  intro θ hθ
  -- `v := LinvI h` is twice differentiable on the interval
  have hd1 : DifferentiableOn ℝ (Work.FTS.PhiStar.LinvI h) (Set.Ioo 0 (Real.pi / 2)) := fun t ht =>
    (Work.FTS.PhiStar.hasDerivAt_LinvI hcont hbdd ht).differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℝ (deriv (Work.FTS.PhiStar.LinvI h))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have heq : deriv (Work.FTS.PhiStar.LinvI h) =ᶠ[𝓝 t] Work.FTS.PhiStar.Linv h := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (Work.FTS.PhiStar.hasDerivAt_LinvI hcont hbdd hs).deriv
    exact (DifferentiableAt.congr_of_eventuallyEq
      (Work.FTS.PhiStar.hasDerivAt_Linv hcont hbdd ht).differentiableAt heq).differentiableWithinAt
  -- the equation `Lzero1 (sin 2θ · v) = h`
  have hsolve : Work.FTS.EllipticEst.Lzero1
      (fun θ' => Real.sin (2 * θ') * Work.FTS.PhiStar.LinvI h θ') θ = h θ := by
    simpa only [Work.Construction.s2_eq] using
      Work.FTS.PhiStar.LinvI_solves hcont hbdd hint hmom θ hθ
  -- the substitution identity
  have hsub := Work.FTS.PhiStar.Lzero1_sin2_mul (v := Work.FTS.PhiStar.LinvI h) hθ hd1 hd2
  rw [hsub] at hsolve
  -- the two derivative evaluations at `θ`
  have hD1 : deriv (Work.FTS.PhiStar.LinvI h) θ = Work.FTS.PhiStar.Linv h θ :=
    (Work.FTS.PhiStar.hasDerivAt_LinvI hcont hbdd hθ).deriv
  have hD2 : deriv (deriv (Work.FTS.PhiStar.LinvI h)) θ
      = deriv (Work.FTS.PhiStar.Linv h) θ := by
    have heq : deriv (Work.FTS.PhiStar.LinvI h) =ᶠ[𝓝 θ] Work.FTS.PhiStar.Linv h := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
      exact (Work.FTS.PhiStar.hasDerivAt_LinvI hcont hbdd hs).deriv
    exact heq.deriv_eq
  rw [hD2, hD1] at hsolve
  show Real.sin (2 * θ) * deriv (Work.FTS.PhiStar.Linv h) θ
    = (6 - 10 * Real.cos θ ^ 2) * Work.FTS.PhiStar.Linv h θ - h θ
  linarith [hsolve]

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.ModeRescaledSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open MeasureTheory Set Filter
open scoped Real Topology ContDiff

set_option autoImplicit false

/-!
# `ModeRescaledSmooth`

`radGreen α m c` is the explicit mode-`m` radial Green function

`radGreen α m c z = 1/(α(4m+5))·( z^{s⁻}∫₀^z c t t^{s⁺-1} dt + z^{s⁺}∫_{Ioi z} c t t^{-s⁺-1} dt )`

with `s⁺ = 2m/α`, `s⁻ = -(2m+5)/α`.  For the source `c = φ_α = phiA α` (a rational function,
smooth on `(0,∞)` away from `-1`) we show that `(z+1)/z · radGreen α m φ_α` is `C^n` on `(0,∞)`
for **every** `n` and **every** real `α` — no positivity of `α` is needed, because the two pieces
are smooth in all regimes:

* the `0..z` piece is a primitive of the `C^n` function `t ↦ c t · t^{s⁺-1}` on `(0,∞)`
  (`EllExist.Honesty.Pieces.primitive_contDiffOn`, which handles the case where that function is
  not integrable near `0`: then Lean's interval integral is the junk constant `0`);
* the `Ioi z` piece is the tail integral of the `C^n` function `t ↦ c t · t^{-s⁺-1}`; the same
  dichotomy occurs at `∞` and is handled by `tailIntegral_contDiffOn_all` below
  (integrability on one tail is equivalent to integrability on every tail, by continuity of the
  integrand on `(0,∞)` and compactness of the difference of two tails);
* the prefactors `z^{s^±}` and the outer factor `(z+1)/z` are `C^∞` on `(0,∞)`.

Nothing about the analytic content of `radGreen` (that it solves the mode equation) is used here.
-/

/-- **Dichotomy for tails.**  For a function continuous on `(0,∞)`, either every tail `Ioi z`
(`z > 0`) carries an integrable function, or none does.  (Two tails differ by a compact set on
which the function is bounded.) -/
theorem integrableOn_Ioi_dichotomy_of_continuousOn {k : ℝ → ℝ}
    (hk : ContinuousOn k (Set.Ioi 0)) :
    (∀ z : ℝ, 0 < z → IntegrableOn k (Set.Ioi z)) ∨
      (∀ z : ℝ, 0 < z → ¬ IntegrableOn k (Set.Ioi z)) := by
  by_cases h1 : IntegrableOn k (Set.Ioi (1 : ℝ))
  · left
    intro z hz
    rcases le_or_gt 1 z with hle | hlt
    · exact h1.mono_set (Ioi_subset_Ioi hle)
    · rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
      refine (IntegrableOn.mono_set ?_ Ioc_subset_Icc_self).union h1
      exact ContinuousOn.integrableOn_Icc (hk.mono fun x hx => lt_of_lt_of_le hz hx.1)
  · right
    intro z hz hzint
    refine h1 ?_
    rcases le_or_gt z 1 with hle | hlt
    · exact hzint.mono_set (Ioi_subset_Ioi hle)
    · rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
      refine (IntegrableOn.mono_set ?_ Ioc_subset_Icc_self).union hzint
      exact ContinuousOn.integrableOn_Icc (hk.mono fun x hx => lt_of_lt_of_le zero_lt_one hx.1)

/-- **Smoothness of a tail integral, junk case included.**  The tail integral
`z ↦ ∫ t in Ioi z, f t` of a function of class `C^n` on `(0,∞)` is again of class `C^n` on
`(0,∞)`; if `f` is integrable on no tail then each integral is the junk constant `0`. -/
theorem tailIntegral_contDiffOn_all (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ n f (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) := by
  rcases integrableOn_Ioi_dichotomy_of_continuousOn hf.continuousOn with hall | hnone
  · exact Work.FTS.EllExist.Honesty.Pieces.tailIntegral_contDiffOn n hf (hall 1 zero_lt_one)
  · refine (contDiffOn_const (c := (0 : ℝ)) (s := Set.Ioi 0)).congr (fun z hz => ?_)
    exact MeasureTheory.integral_undef (hnone z hz)

/-- **Smoothness of the radial Green function.**  For every real `α`, every `m : ℕ` and every
`n : ℕ`, `radGreen α m c` is `C^n` on `(0,∞)` as soon as `c` is. -/
theorem contDiffOn_radGreen (α : ℝ) (m : ℕ) (n : ℕ) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ n c (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0) := by
  have hf1 : ContDiffOn ℝ n (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) :=
    hc.mul (contDiffOn_id.rpow_const_of_ne (p := (2 * (m : ℝ) + 5) / α - 1)
      (fun x hx => ne_of_gt hx))
  have hf2 : ContDiffOn ℝ n (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 0) :=
    hc.mul (contDiffOn_id.rpow_const_of_ne (p := -(2 * (m : ℝ) / α) - 1)
      (fun x hx => ne_of_gt hx))
  have hA : ContDiffOn ℝ n
      (fun z => ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) := Work.FTS.EllExist.Honesty.Pieces.primitive_contDiffOn n hf1
  have hB : ContDiffOn ℝ n
      (fun z => ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 0) :=
    tailIntegral_contDiffOn_all n hf2
  have hza : ContDiffOn ℝ n (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α)) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (p := -(2 * (m : ℝ) + 5) / α) (fun x hx => ne_of_gt hx)
  have hzb : ContDiffOn ℝ n (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (p := 2 * (m : ℝ) / α) (fun x hx => ne_of_gt hx)
  have hmain : ContDiffOn ℝ n (fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5)) *
      (z ^ (-(2 * (m : ℝ) + 5) / α)
          * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        + z ^ (2 * (m : ℝ) / α)
          * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)))) (Set.Ioi 0) :=
    contDiffOn_const.mul ((hza.mul hA).add (hzb.mul hB))
  exact hmain.congr (fun z _ => rfl)


end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.PhiAjFlatDecayU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped Real Topology
open Set Polynomial

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Unif

/-! ## 1. The coefficient norm `cl1` and its calculus -/

/-- `cl1 P` is the sum of the absolute values of the coefficients of the real polynomial `P`. -/
noncomputable def cl1 (P : Polynomial ℝ) : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|

lemma cl1_nonneg (P : Polynomial ℝ) : 0 ≤ cl1 P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Summing the absolute values of the coefficients over any range containing the degree gives
`cl1`. -/
lemma sum_range_coeff_eq_cl1 {P : Polynomial ℝ} {D : ℕ} (h : P.natDegree ≤ D) :
    ∑ i ∈ Finset.range (D + 1), |P.coeff i| = cl1 P := by
  rw [cl1]
  refine (Finset.sum_subset ?_ ?_).symm
  · rw [Finset.range_subset_range]; omega
  · intro i hi hni
    have hi' : P.natDegree < i := by
      simp only [Finset.mem_range] at hi hni
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi', abs_zero]


lemma cl1_add_le (P Q : Polynomial ℝ) : cl1 (P + Q) ≤ cl1 P + cl1 Q := by
  have hPQ : (P + Q).natDegree ≤ max P.natDegree Q.natDegree := Polynomial.natDegree_add_le P Q
  calc cl1 (P + Q)
      = ∑ i ∈ Finset.range (max P.natDegree Q.natDegree + 1), |(P + Q).coeff i| :=
        (sum_range_coeff_eq_cl1 hPQ).symm
    _ ≤ ∑ i ∈ Finset.range (max P.natDegree Q.natDegree + 1),
          (|P.coeff i| + |Q.coeff i|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Polynomial.coeff_add]
        exact abs_add_le _ _
    _ = (∑ i ∈ Finset.range (max P.natDegree Q.natDegree + 1), |P.coeff i|)
        + ∑ i ∈ Finset.range (max P.natDegree Q.natDegree + 1), |Q.coeff i| :=
        Finset.sum_add_distrib
    _ = cl1 P + cl1 Q := by
        rw [sum_range_coeff_eq_cl1 (le_max_left P.natDegree Q.natDegree),
          sum_range_coeff_eq_cl1 (le_max_right P.natDegree Q.natDegree)]

lemma cl1_neg (P : Polynomial ℝ) : cl1 (-P) = cl1 P := by
  rw [cl1, cl1, Polynomial.natDegree_neg]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_neg, abs_neg]

lemma cl1_sub_le (P Q : Polynomial ℝ) : cl1 (P - Q) ≤ cl1 P + cl1 Q := by
  calc cl1 (P - Q) = cl1 (P + -Q) := by rw [sub_eq_add_neg]
    _ ≤ cl1 P + cl1 (-Q) := cl1_add_le P (-Q)
    _ = cl1 P + cl1 Q := by rw [cl1_neg]

lemma cl1_C_mul (a : ℝ) (P : Polynomial ℝ) : cl1 (C a * P) = |a| * cl1 P := by
  have h : (C a * P).natDegree ≤ P.natDegree := Polynomial.natDegree_C_mul_le a P
  calc cl1 (C a * P) = ∑ i ∈ Finset.range (P.natDegree + 1), |(C a * P).coeff i| :=
        (sum_range_coeff_eq_cl1 h).symm
    _ = ∑ i ∈ Finset.range (P.natDegree + 1), |a| * |P.coeff i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.coeff_C_mul, abs_mul]
    _ = |a| * ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| := by rw [Finset.mul_sum]
    _ = |a| * cl1 P := by rw [cl1]

/-- Multiplying by a monomial does not increase the coefficient norm. -/
lemma cl1_mul_X_pow_le (P : Polynomial ℝ) (k : ℕ) : cl1 (P * X ^ k) ≤ cl1 P := by
  have hdeg : (P * X ^ k).natDegree ≤ P.natDegree + k := by
    have h := Polynomial.natDegree_mul_le (p := P) (q := X ^ k)
    have hX := Polynomial.natDegree_X_pow_le (R := ℝ) k
    omega
  have hmain : cl1 (P * X ^ k) = cl1 P := by
    calc cl1 (P * X ^ k)
        = ∑ i ∈ Finset.range (P.natDegree + k + 1), |(P * X ^ k).coeff i| :=
          (sum_range_coeff_eq_cl1 hdeg).symm
      _ = ∑ i ∈ Finset.range k, |(P * X ^ k).coeff i|
          + ∑ i ∈ Finset.range (P.natDegree + 1), |(P * X ^ k).coeff (k + i)| := by
          rw [show P.natDegree + k + 1 = k + (P.natDegree + 1) from by omega,
            Finset.sum_range_add]
      _ = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| := by
          have h0 : ∑ i ∈ Finset.range k, |(P * X ^ k).coeff i| = 0 := by
            refine Finset.sum_eq_zero fun i hi => ?_
            rw [Polynomial.coeff_mul_X_pow']
            have hik : ¬ (k ≤ i) := by simpa using Finset.mem_range.mp hi
            rw [if_neg hik, abs_zero]
          have h1 : ∑ i ∈ Finset.range (P.natDegree + 1), |(P * X ^ k).coeff (k + i)|
              = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [show k + i = i + k from by omega, Polynomial.coeff_mul_X_pow]
          rw [h0, zero_add, h1]
      _ = cl1 P := sum_range_coeff_eq_cl1 (le_refl P.natDegree)
  exact hmain.le

/-- `X^k` on the left does not increase the coefficient norm. -/
lemma cl1_X_pow_mul_le (P : Polynomial ℝ) (k : ℕ) : cl1 (X ^ k * P) ≤ cl1 P := by
  rw [mul_comm]
  exact cl1_mul_X_pow_le P k

/-- The `X²`-multiple of a polynomial has no larger coefficient norm. -/
lemma cl1_X_sq_mul_le (P : Polynomial ℝ) : cl1 (X ^ 2 * P) ≤ cl1 P :=
  cl1_X_pow_mul_le P 2

/-- The `X(1+X)`-multiple has coefficient norm at most twice that of the polynomial. -/
lemma cl1_mul_one_add_X_le (P : Polynomial ℝ) : cl1 (P * (1 + X)) ≤ 2 * cl1 P := by
  have h : P * (1 + X) = P + P * X := by rw [mul_add, mul_one]
  calc cl1 (P * (1 + X)) = cl1 (P + P * X) := by rw [h]
    _ ≤ cl1 P + cl1 (P * X) := cl1_add_le P (P * X)
    _ ≤ cl1 P + cl1 P :=
        add_le_add le_rfl (by simpa [pow_one] using cl1_mul_X_pow_le P 1)
    _ = 2 * cl1 P := by ring

lemma cl1_X_mul_one_add_X_le (P : Polynomial ℝ) : cl1 (X * ((1 + X) * P)) ≤ 2 * cl1 P := by
  calc cl1 (X * ((1 + X) * P)) = cl1 ((X ^ 1) * ((1 + X) * P)) := by rw [pow_one]
    _ ≤ cl1 ((1 + X) * P) := cl1_X_pow_mul_le ((1 + X) * P) 1
    _ = cl1 (P * (1 + X)) := by rw [mul_comm]
    _ ≤ 2 * cl1 P := cl1_mul_one_add_X_le P

/-- The first `phiAjNum` summand stays bounded by `|a| · cl1` of the numerator. -/
lemma cl1_C_X_sq_mul_le (a : ℝ) (Q : Polynomial ℝ) :
    cl1 (C a * X ^ 2 * Q) ≤ |a| * cl1 Q := by
  have h1 : C a * X ^ 2 * Q = C a * (X ^ 2 * Q) := by rw [mul_assoc]
  rw [h1, cl1_C_mul]
  exact mul_le_mul_of_nonneg_left (cl1_X_sq_mul_le Q) (abs_nonneg a)

/-- The second `phiAjNum` summand stays bounded by `2|a| · cl1` of the numerator. -/
lemma cl1_C_X_one_add_X_mul_le (a : ℝ) (Q : Polynomial ℝ) :
    cl1 (C a * X * (1 + X) * Q) ≤ 2 * |a| * cl1 Q := by
  have h1 : C a * X * (1 + X) * Q = C a * (X * ((1 + X) * Q)) := by
    rw [mul_assoc, mul_assoc]
  rw [h1, cl1_C_mul]
  calc |a| * cl1 (X * ((1 + X) * Q)) ≤ |a| * (2 * cl1 Q) :=
        mul_le_mul_of_nonneg_left (cl1_X_mul_one_add_X_le Q) (abs_nonneg a)
    _ = 2 * |a| * cl1 Q := by ring

/-- Differentiating multiplies the coefficient norm by at most the degree. -/
lemma cl1_derivative_le (P : Polynomial ℝ) :
    cl1 (derivative P) ≤ (P.natDegree : ℝ) * cl1 P := by
  have hdeg : (derivative P).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le _ _)
  calc cl1 (derivative P)
      = ∑ i ∈ Finset.range (P.natDegree + 1), |(derivative P).coeff i| :=
        (sum_range_coeff_eq_cl1 hdeg).symm
    _ = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff (i + 1)| * ((i : ℝ) + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.coeff_derivative, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)]
    _ = ∑ i ∈ Finset.range P.natDegree, |P.coeff (i + 1)| * ((i : ℝ) + 1) := by
        rw [Finset.sum_range_succ, Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _),
          abs_zero, zero_mul, add_zero]
    _ ≤ ∑ i ∈ Finset.range P.natDegree, |P.coeff (i + 1)| * (P.natDegree : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i + 1 ≤ P.natDegree := by simpa using Finset.mem_range.mp hi
        have h1 : ((i : ℝ) + 1) ≤ (P.natDegree : ℝ) := by exact_mod_cast hi'
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (∑ i ∈ Finset.range P.natDegree, |P.coeff (i + 1)|) * (P.natDegree : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|) * (P.natDegree : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [Finset.sum_range_succ' (f := fun i => |P.coeff i|) (n := P.natDegree)]
        linarith [abs_nonneg (P.coeff 0)]
    _ = cl1 P * (P.natDegree : ℝ) := by rw [sum_range_coeff_eq_cl1 (le_refl P.natDegree)]
    _ = (P.natDegree : ℝ) * cl1 P := by ring

/-- The one-step estimate for the derivative numerator of a rational function with a single pole
at `-1`. -/
lemma cl1_numStep_le (n d : ℕ) {P : Polynomial ℝ} (hP : P.natDegree ≤ d) :
    cl1 (numStep n P) ≤ ((2 * d + 2 + n : ℕ) : ℝ) * cl1 P := by
  have hder : cl1 (derivative P) ≤ (d : ℝ) * cl1 P :=
    (cl1_derivative_le P).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hP) (cl1_nonneg P))
  have hA : cl1 (derivative P * (1 + X)) ≤ 2 * ((d : ℝ) * cl1 P) :=
    (cl1_mul_one_add_X_le (derivative P)).trans
      (mul_le_mul_of_nonneg_left hder (by norm_num))
  have hB : cl1 (C (n : ℝ) * P) ≤ (n : ℝ) * cl1 P := by
    rw [cl1_C_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hsum : 2 * ((d : ℝ) * cl1 P) + (n : ℝ) * cl1 P
      ≤ ((2 * d + 2 + n : ℕ) : ℝ) * cl1 P := by
    push_cast
    nlinarith [cl1_nonneg P]
  calc cl1 (numStep n P) = cl1 (derivative P * (1 + X) - C (n : ℝ) * P) := by rw [numStep]
    _ ≤ cl1 (derivative P * (1 + X)) + cl1 (C (n : ℝ) * P) := cl1_sub_le _ _
    _ ≤ 2 * ((d : ℝ) * cl1 P) + (n : ℝ) * cl1 P := add_le_add hA hB
    _ ≤ ((2 * d + 2 + n : ℕ) : ℝ) * cl1 P := hsum

/-- The `k`-fold recursion constant for `cl1 (numIter n P k)` under the degree bound `deg P ≤ d`. -/
def cit (d n : ℕ) : ℕ → ℝ
  | 0 => 1
  | (k + 1) => ((2 * d + 2 + n + k : ℕ) : ℝ) * cit d n k

lemma cit_nonneg (d n k : ℕ) : 0 ≤ cit d n k := by
  induction k with
  | zero => simp [cit]
  | succ k ih =>
      have h : cit d n (k + 1) = ((2 * d + 2 + n + k : ℕ) : ℝ) * cit d n k := rfl
      rw [h]
      positivity

lemma cl1_numIter_le (n d k : ℕ) {P : Polynomial ℝ} (hP : P.natDegree ≤ d) :
    cl1 (numIter n P k) ≤ cit d n k * cl1 P := by
  induction k with
  | zero => simp [numIter, cit]
  | succ k ih =>
      have hdeg : (numIter n P k).natDegree ≤ d := (numIter_natDegree_le n P k).trans hP
      have hstep : cl1 (numStep (n + k) (numIter n P k))
          ≤ ((2 * d + 2 + (n + k) : ℕ) : ℝ) * cl1 (numIter n P k) :=
        cl1_numStep_le (n + k) d hdeg
      calc cl1 (numIter n P (k + 1)) = cl1 (numStep (n + k) (numIter n P k)) := by
            rw [numIter_succ]
        _ ≤ ((2 * d + 2 + (n + k) : ℕ) : ℝ) * cl1 (numIter n P k) := hstep
        _ ≤ ((2 * d + 2 + (n + k) : ℕ) : ℝ) * (cit d n k * cl1 P) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = cit d n (k + 1) * cl1 P := by
            rw [show cit d n (k + 1) = ((2 * d + 2 + n + k : ℕ) : ℝ) * cit d n k from rfl,
              show 2 * d + 2 + (n + k) = 2 * d + 2 + n + k from by omega]
            ring

lemma cl1_divX_le (P : Polynomial ℝ) : cl1 (P.divX) ≤ cl1 P := by
  have hdeg : P.divX.natDegree ≤ P.natDegree := Polynomial.natDegree_divX_le
  calc cl1 P.divX = ∑ i ∈ Finset.range (P.natDegree + 1), |P.divX.coeff i| :=
        (sum_range_coeff_eq_cl1 hdeg).symm
    _ = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff (i + 1)| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.coeff_divX]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 2), |P.coeff i| := by
        rw [show P.natDegree + 2 = (P.natDegree + 1) + 1 from by omega,
          Finset.sum_range_succ' (f := fun i => |P.coeff i|) (n := P.natDegree + 1)]
        linarith [abs_nonneg (P.coeff 0)]
    _ = cl1 P := by
        rw [show P.natDegree + 2 = (P.natDegree + 1) + 1 from by omega,
          Finset.sum_range_succ, sum_range_coeff_eq_cl1 (le_refl P.natDegree),
          Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), abs_zero, add_zero]

lemma cl1_X : cl1 (Polynomial.X : Polynomial ℝ) = 1 := by
  rw [cl1, Polynomial.natDegree_X, Finset.sum_range_succ, Finset.sum_range_one,
    Polynomial.coeff_X_zero, Polynomial.coeff_X_one]
  norm_num

/-! ## 2. The `α`-free recursive bounds -/

/-- The `α`-free factor by which `cl1` grows in one `phiAjNum` step
(`|α| ≤ 1/5`, `|5+α| ≤ 6`). -/
noncomputable def fac (j : ℕ) : ℝ :=
  (1 / 5 : ℝ) * ((6 * j + 6 : ℕ) : ℝ) * ((6 * j + 7 : ℕ) : ℝ)
    + 12 * ((6 * j + 6 : ℕ) : ℝ)

lemma fac_nonneg (j : ℕ) : 0 ≤ fac j := by
  rw [fac]; positivity

/-- An `α`-free bound on `cl1 (phiAjNum α j)`, uniform in `α ∈ (0, 1/5]`. -/
noncomputable def nb : ℕ → ℝ
  | 0 => 2
  | (j + 1) => fac j * nb j

lemma nb_nonneg (j : ℕ) : 0 ≤ nb j := by
  induction j with
  | zero => norm_num [nb]
  | succ j ih =>
      have h : nb (j + 1) = fac j * nb j := rfl
      rw [h]
      exact mul_nonneg (fac_nonneg j) ih

/-- One `numStep` of the `phiAjNum` recursion. -/
lemma cl1_numStep_one_le (α : ℝ) (j : ℕ) :
    cl1 (numStep (2 * j + 2) (phiAjNum α j))
      ≤ ((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j) := by
  have hP : (phiAjNum α j).natDegree ≤ 2 * j + 1 := phiAjNum_natDegree_le α j
  have h := cl1_numStep_le (2 * j + 2) (2 * j + 1) hP
  rwa [show (2 * (2 * j + 1) + 2 + (2 * j + 2) : ℕ) = 6 * j + 6 from by omega] at h

/-- Two `numStep`s of the `phiAjNum` recursion. -/
lemma cl1_numStep_pair_le (α : ℝ) (j : ℕ) :
    cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ ((6 * j + 7 : ℕ) : ℝ) * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j)) := by
  have hP : (phiAjNum α j).natDegree ≤ 2 * j + 1 := phiAjNum_natDegree_le α j
  have hQ1 : (numStep (2 * j + 2) (phiAjNum α j)).natDegree ≤ 2 * j + 1 :=
    numStep_natDegree_le (by omega) hP
  have h2 : cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ ((6 * j + 7 : ℕ) : ℝ) * cl1 (numStep (2 * j + 2) (phiAjNum α j)) := by
    have h := cl1_numStep_le (2 * j + 3) (2 * j + 1) hQ1
    rwa [show (2 * (2 * j + 1) + 2 + (2 * j + 3) : ℕ) = 6 * j + 7 from by omega] at h
  exact h2.trans (mul_le_mul_of_nonneg_left (cl1_numStep_one_le α j) (Nat.cast_nonneg _))

/-- The algebraic splitting of one `phiAjNum` step. -/
lemma cl1_phiAjNum_split (α : ℝ) (j : ℕ) :
    cl1 (phiAjNum α (j + 1))
      ≤ |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
        + |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j))) := by
  rw [phiAjNum]
  refine (cl1_add_le _ _).trans (add_le_add ?_ ?_)
  · exact cl1_C_X_sq_mul_le α (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
  · refine (cl1_C_X_one_add_X_mul_le (5 + α)
      (numStep (2 * j + 2) (phiAjNum α j))).trans (le_of_eq ?_)
    ring

/-- The numeric step: `|α| ≤ 1/5`, `|5 + α| ≤ 6` bound the two coefficients. -/
lemma cl1_pair_step (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (j : ℕ) :
    |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
      + |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ fac j * cl1 (phiAjNum α j) := by
  have hαabs : |α| ≤ 1 / 5 := by rw [abs_of_pos hα]; exact hα5
  have h5abs : |5 + α| ≤ 6 := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < 5 + α)]
    linarith
  have hpair := cl1_numStep_pair_le α j
  have hone := cl1_numStep_one_le α j
  have h4 : |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ (1 / 5) * (((6 * j + 7 : ℕ) : ℝ)
          * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j))) :=
    mul_le_mul hαabs hpair (cl1_nonneg _) (by norm_num)
  have h5 : |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ 6 * (2 * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j))) := by
    refine mul_le_mul h5abs ?_ ?_ (by norm_num)
    · exact mul_le_mul_of_nonneg_left hone (by norm_num)
    · exact mul_nonneg (by norm_num) (cl1_nonneg _)
  calc |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
        + |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ (1 / 5) * (((6 * j + 7 : ℕ) : ℝ)
            * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j)))
        + 6 * (2 * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j))) := add_le_add h4 h5
    _ = fac j * cl1 (phiAjNum α j) := by rw [fac]; ring

/-- **The uniform coefficient bound.**  For `α ∈ (0, 1/5]` the numerator polynomial of
`phiAj j α` has coefficient norm at most `nb j`, independently of `α`. -/
lemma cl1_phiAjNum_le (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (j : ℕ) :
    cl1 (phiAjNum α j) ≤ nb j := by
  induction j with
  | zero =>
      have h : phiAjNum α 0 = C 2 * X := rfl
      rw [h, cl1_C_mul, cl1_X, mul_one]
      norm_num [nb]
  | succ j ih =>
      calc cl1 (phiAjNum α (j + 1))
          ≤ |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
            + |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j))) :=
            cl1_phiAjNum_split α j
        _ ≤ fac j * cl1 (phiAjNum α j) := cl1_pair_step α hα hα5 j
        _ ≤ fac j * nb j := mul_le_mul_of_nonneg_left ih (fac_nonneg j)
        _ = nb (j + 1) := rfl

/-! ## 3. The uniform slot bounds and the constant `AU` -/

/-- The uniform bound on `2 · slotC1 α j k`. -/
noncomputable def B1 (j k : ℕ) : ℝ := 2 * (cit (2 * j + 1) (2 * j + 2) k * nb j)

/-- The uniform bound on `2 · slotC2 α j k`. -/
noncomputable def B2 (j k : ℕ) : ℝ := 2 * (cit (2 * j) (2 * j + 2) k * nb j)

lemma B1_nonneg (j k : ℕ) : 0 ≤ B1 j k := by
  rw [B1]
  exact mul_nonneg (by norm_num) (mul_nonneg (cit_nonneg _ _ _) (nb_nonneg j))

lemma B2_nonneg (j k : ℕ) : 0 ≤ B2 j k := by
  rw [B2]
  exact mul_nonneg (by norm_num) (mul_nonneg (cit_nonneg _ _ _) (nb_nonneg j))

/-- The constant of the statement. -/
noncomputable def AU : ℝ :=
  1 + ∑ j ∈ Finset.range 10, ∑ k ∈ Finset.range 15, (B1 j k + B2 j k)

lemma AU_pos : 0 < AU := by
  rw [AU]
  have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range 10, ∑ k ∈ Finset.range 15, (B1 j k + B2 j k) :=
    Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => add_nonneg (B1_nonneg j k) (B2_nonneg j k)
  linarith

lemma B1_le_AU {j k : ℕ} (hj : j ≤ 9) (hk : k ≤ 14) : B1 j k ≤ AU := by
  have hj10 : j ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have hk15 : k ∈ Finset.range 15 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ j' ∈ Finset.range 10,
      0 ≤ ∑ k' ∈ Finset.range 15, (B1 j' k' + B2 j' k') := fun j' _ =>
    Finset.sum_nonneg fun k' _ => add_nonneg (B1_nonneg j' k') (B2_nonneg j' k')
  have h1 : B1 j k ≤ ∑ k' ∈ Finset.range 15, (B1 j k' + B2 j k') :=
    (le_add_of_nonneg_right (B2_nonneg j k)).trans
      (Finset.single_le_sum (fun k' _ => add_nonneg (B1_nonneg j k') (B2_nonneg j k')) hk15)
  have h2 : (∑ k' ∈ Finset.range 15, (B1 j k' + B2 j k'))
      ≤ ∑ j' ∈ Finset.range 10, ∑ k' ∈ Finset.range 15, (B1 j' k' + B2 j' k') :=
    Finset.single_le_sum hinner hj10
  rw [AU]
  linarith

lemma B2_le_AU {j k : ℕ} (hj : j ≤ 9) (hk : k ≤ 14) : B2 j k ≤ AU := by
  have hj10 : j ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have hk15 : k ∈ Finset.range 15 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ j' ∈ Finset.range 10,
      0 ≤ ∑ k' ∈ Finset.range 15, (B1 j' k' + B2 j' k') := fun j' _ =>
    Finset.sum_nonneg fun k' _ => add_nonneg (B1_nonneg j' k') (B2_nonneg j' k')
  have h1 : B2 j k ≤ ∑ k' ∈ Finset.range 15, (B1 j k' + B2 j k') :=
    (le_add_of_nonneg_left (B1_nonneg j k)).trans
      (Finset.single_le_sum (fun k' _ => add_nonneg (B1_nonneg j k') (B2_nonneg j k')) hk15)
  have h2 : (∑ k' ∈ Finset.range 15, (B1 j k' + B2 j k'))
      ≤ ∑ j' ∈ Finset.range 10, ∑ k' ∈ Finset.range 15, (B1 j' k' + B2 j' k') :=
    Finset.single_le_sum hinner hj10
  rw [AU]
  linarith

lemma slotC1_le_B1 (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (j k : ℕ) :
    2 * slotC1 α j k ≤ B1 j k := by
  have hP : (phiAjNum α j).natDegree ≤ 2 * j + 1 := phiAjNum_natDegree_le α j
  have hdeg : (numIter (2 * j + 2) (phiAjNum α j) k).natDegree ≤ 2 * j + 1 :=
    (numIter_natDegree_le (2 * j + 2) (phiAjNum α j) k).trans hP
  have hslot : slotC1 α j k = cl1 (numIter (2 * j + 2) (phiAjNum α j) k) := by
    have hcongr : Finset.range (2 * j + 2) = Finset.range ((2 * j + 1) + 1) := by
      rw [show 2 * j + 2 = (2 * j + 1) + 1 from by omega]
    rw [slotC1]
    exact (Finset.sum_congr hcongr (fun _ _ => rfl)).trans (sum_range_coeff_eq_cl1 hdeg)
  rw [hslot, B1]
  have hiter := cl1_numIter_le (2 * j + 2) (2 * j + 1) k hP
  have hnb := cl1_phiAjNum_le α hα hα5 j
  calc 2 * cl1 (numIter (2 * j + 2) (phiAjNum α j) k)
      ≤ 2 * (cit (2 * j + 1) (2 * j + 2) k * cl1 (phiAjNum α j)) :=
        mul_le_mul_of_nonneg_left hiter (by norm_num)
    _ ≤ 2 * (cit (2 * j + 1) (2 * j + 2) k * nb j) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnb (cit_nonneg _ _ _)) (by norm_num)

lemma slotC2_le_B2 (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (j k : ℕ) :
    2 * slotC2 α j k ≤ B2 j k := by
  have hP : (phiAjNumDiv α j).natDegree ≤ 2 * j := phiAjNumDiv_natDegree_le α j
  have hdeg : (numIter (2 * j + 2) (phiAjNumDiv α j) k).natDegree ≤ 2 * j :=
    (numIter_natDegree_le (2 * j + 2) (phiAjNumDiv α j) k).trans hP
  have hslot : slotC2 α j k = cl1 (numIter (2 * j + 2) (phiAjNumDiv α j) k) := by
    rw [slotC2]
    exact sum_range_coeff_eq_cl1 hdeg
  have hdiv : cl1 (phiAjNumDiv α j) ≤ nb j := by
    have h : phiAjNumDiv α j = (phiAjNum α j).divX := rfl
    rw [h]
    exact (cl1_divX_le (phiAjNum α j)).trans (cl1_phiAjNum_le α hα hα5 j)
  rw [hslot, B2]
  have hiter := cl1_numIter_le (2 * j + 2) (2 * j) k hP
  calc 2 * cl1 (numIter (2 * j + 2) (phiAjNumDiv α j) k)
      ≤ 2 * (cit (2 * j) (2 * j + 2) k * cl1 (phiAjNumDiv α j)) :=
        mul_le_mul_of_nonneg_left hiter (by norm_num)
    _ ≤ 2 * (cit (2 * j) (2 * j + 2) k * nb j) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdiv (cit_nonneg _ _ _)) (by norm_num)

end Unif

open Unif

theorem PhiAjFlatDecayU : ∃ A : ℝ, 0 < A ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ j : ℕ, j ≤ 9 →
    (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (Work.FTS.PhiStar.phiAj j α) t| ≤ A / (1 + t ^ (k + 1))) ∧
    (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (fun t => Work.FTS.PhiStar.phiAj j α t / t) t| ≤ A / (1 + t ^ (k + 2))) := by
  refine ⟨AU, AU_pos, fun α hα hα5 j hj => ⟨?_, ?_⟩⟩
  · intro k hk t ht
    have hC1 : 2 * slotC1 α j k ≤ AU := (slotC1_le_B1 α hα hα5 j k).trans (B1_le_AU hj hk)
    have hC1nn : 0 ≤ slotC1 α j k := slotC1_nonneg α j k
    have ht1 : (-1 : ℝ) < t := by linarith
    have heq : iteratedDeriv k (Work.FTS.PhiStar.phiAj j α) t
        = iteratedDeriv k (fun z : ℝ => (phiAjNum α j).eval z / (1 + z) ^ (2 * j + 2)) t :=
      iteratedDeriv_congr_of_eqOn_isOpen isOpen_Ioi (phiAj_eqOn_num α j) k ht1
    have hb : |iteratedDeriv k (fun z : ℝ => (phiAjNum α j).eval z / (1 + z) ^ (2 * j + 2)) t|
        ≤ slotC1 α j k / (1 + t) ^ (k + 1) := by
      have h := rat_iteratedDeriv_bound (phiAjNum α j) (2 * j + 1) 1 k (by norm_num)
        (phiAjNum_natDegree_le α j) t ht
      rw [show (2 * j + 1 + 1 : ℕ) = 2 * j + 2 from by omega,
        show (1 + k : ℕ) = k + 1 from by omega] at h
      exact h
    rw [heq]
    exact bound_of_le (k + 1) hC1nn hC1 ht hb
  · intro k hk t ht
    have hC2 : 2 * slotC2 α j k ≤ AU := (slotC2_le_B2 α hα hα5 j k).trans (B2_le_AU hj hk)
    have hC2nn : 0 ≤ slotC2 α j k := slotC2_nonneg α j k
    have heq : iteratedDeriv k (fun t : ℝ => Work.FTS.PhiStar.phiAj j α t / t) t
        = iteratedDeriv k (fun z : ℝ => (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)) t :=
      iteratedDeriv_congr_of_eqOn_isOpen isOpen_Ioi (phiAj_div_eqOn_num α j) k ht
    have hb : |iteratedDeriv k (fun z : ℝ => (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)) t|
        ≤ slotC2 α j k / (1 + t) ^ (k + 2) := by
      have h := rat_iteratedDeriv_bound (phiAjNumDiv α j) (2 * j) 2 k (by norm_num)
        (phiAjNumDiv_natDegree_le α j) t ht
      rw [show (2 + k : ℕ) = k + 2 from by omega] at h
      exact h
    rw [heq]
    exact bound_of_le (k + 2) hC2nn hC2 ht hb

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.famC_coeff_int =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-
# The three-term coefficient identity for `famC`

`famC k = (3/2)_k / k!` is the coefficient sequence of `(1 - z)^{-3/2}`, defined in
`Submission/Work/FTS/PhiStar/FamLopAux/Defs.lean` as

`famC k = (∏_{i<k} (3/2 + i)) / k!`  for `k ≥ 0`  (and `0` for `k < 0`).

The present lemma is the **pairwise** coefficient identity: for integers `u, v ≥ 0` with
`u + v = n + 2`,

`(n+2)·c u·c v - ((2n+5)/2)·(c u·c (v-1) + c (u-1)·c v) + (n+3)·c (u-1)·c (v-1) = 0`,

equivalently (writing `s = u + v = n + 2`)

`(u+v)·c u·c v = ((2(u+v)+1)/2)·(c (u-1)·c v + c u·c (v-1)) - (u+v+1)·c (u-1)·c (v-1)`.

This is the pointwise algebraic input to the three-term recurrence of the trigonometric
Gegenbauer sums `famTrig`; it is exactly the statement that the product of the generating
series `Σ c u·z^u` with itself satisfies the degree-`s` ODE inherited from
`2(1-z)f' = 3f` on each bidegree `(u,v)`.

## Proof

Everything is derived here from the definition of `famC`, so the module is self-contained
(it only imports the definitions).

* `famC_ratio_nat`: the defining ratio `c (m+1) = c m · (m + 3/2)/(m + 1)`, from
  `Finset.prod_range_succ` and `Nat.factorial_succ`.
* `key_boundary`: the degenerate instance `(n+2)·c (n+2) = ((2n+5)/2)·c (n+1)`, an immediate
  consequence of the ratio at `m = n+1`.
* `key_core`: the genuinely two-variable case: after `field_simp` it is the polynomial
  identity (in `m, k : ℕ`, `s := m + k + 2`, `r_m := (m + 3/2)/(m + 1)`,
  `r_k := (k + 3/2)/(k + 1)`)

  `s·r_m·r_k - ((2s+1)/2)·(r_m + r_k) + (s+1) = 0`,

  which is the "room" computation `-¼(1/u + 1/v) + (u+v)/(4uv) = 0` with `u = m+1`,
  `v = k + 1` (here `r_j = 1 + 1/(2(j+1))`).
* The main theorem distinguishes `u = 0`, `v = 0`, and `u, v ≥ 1`; in the last case we write
  `u = m+1`, `v = k+1` and substitute the defining ratio twice.

An equivalent form of the identity (multiplied by `2` and rearranged) is available in
`Work.FTS.PhiStar.FamLopAux.famC_ident` (`FamLopAux/TrigGegen.lean`), proved for arbitrary
integers `j`, `l`; the proof below does not use it, so that this module needs neither that
file nor its (larger) import cone.
-/

/-! ## Elementary facts about `famC`, from the definition -/

private lemma famC_one_zero : famC (0 : ℤ) = 1 := by
  rw [famC]
  norm_num

private lemma famC_eq_zero_of_neg {k : ℤ} (hk : k < 0) : famC k = 0 := by
  rw [famC, if_neg (by omega)]

/-- The defining ratio of the coefficients: `c (m+1) = c m · (m + 3/2)/(m + 1)`. -/
private lemma famC_ratio_nat (m : ℕ) :
    famC ((m : ℤ) + 1) = famC (m : ℤ) * (((m : ℝ) + 3 / 2) / ((m : ℝ) + 1)) := by
  have h1 : (((m : ℤ) + 1).toNat) = m + 1 := by simp
  have h2 : ((m : ℤ).toNat) = m := by simp
  rw [famC, famC,
    if_pos (by omega : (0 : ℤ) ≤ (m : ℤ) + 1), if_pos (by omega : (0 : ℤ) ≤ (m : ℤ)),
    h1, h2, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-! ## The two algebraic keys -/

/-- Degenerate instance (one index `0`): `(n+2)·c (n+2) = ((2n+5)/2)·c (n+1)`. -/
private lemma key_boundary (n : ℕ) :
    ((n : ℝ) + 2) * famC ((n : ℤ) + 2) - ((2 * (n : ℝ) + 5) / 2) * famC ((n : ℤ) + 1) = 0 := by
  have h := famC_ratio_nat (n + 1)
  have h1 : (((n + 1 : ℕ) : ℤ) + 1) = (n : ℤ) + 2 := by push_cast; ring
  have h2 : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
  rw [h1, h2] at h
  rw [h]
  push_cast
  field_simp
  ring

/-- The two-variable rational identity, with `r_j := (j + 3/2)/(j + 1) = 1 + 1/(2(j+1))`:
`(m+k+2)·r_m·r_k - ((2(m+k)+5)/2)·(r_m + r_k) + (m+k+3) = 0`. -/
private lemma key_core (m k : ℕ) :
    ((m : ℝ) + (k : ℝ) + 2) * (((m : ℝ) + 3 / 2) / ((m : ℝ) + 1))
        * (((k : ℝ) + 3 / 2) / ((k : ℝ) + 1))
      - ((2 * ((m : ℝ) + (k : ℝ)) + 5) / 2)
        * ((((m : ℝ) + 3 / 2) / ((m : ℝ) + 1)) + (((k : ℝ) + 3 / 2) / ((k : ℝ) + 1)))
      + ((m : ℝ) + (k : ℝ) + 3) = 0 := by
  field_simp
  ring

/-! ## The theorem -/

theorem famC_coeff_int (n : ℕ) (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u + v = (n : ℤ) + 2) :
    ((n : ℝ) + 2) * Work.FTS.PhiStar.famC u * Work.FTS.PhiStar.famC v
      - ((2 * (n : ℝ) + 5) / 2) * (Work.FTS.PhiStar.famC u * Work.FTS.PhiStar.famC (v - 1)
          + Work.FTS.PhiStar.famC (u - 1) * Work.FTS.PhiStar.famC v)
      + ((n : ℝ) + 3) * Work.FTS.PhiStar.famC (u - 1) * Work.FTS.PhiStar.famC (v - 1) = 0 := by
  rcases lt_or_eq_of_le hu with hu | hu
  · rcases lt_or_eq_of_le hv with hv | hv
    · -- `1 ≤ u` and `1 ≤ v`: write `u = m+1`, `v = k+1` and use the defining ratio
      obtain ⟨m, hm⟩ : ∃ m : ℕ, u = (m : ℤ) + 1 :=
        ⟨(u - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, v = (k : ℤ) + 1 :=
        ⟨(v - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
      have hn : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
        have hz : (n : ℤ) = (m : ℤ) + (k : ℤ) := by omega
        exact_mod_cast hz
      rw [hm, hk, hn,
        show ((m : ℤ) + 1) - 1 = (m : ℤ) by ring,
        show ((k : ℤ) + 1) - 1 = (k : ℤ) by ring,
        famC_ratio_nat m, famC_ratio_nat k]
      linear_combination (famC (m : ℤ) * famC (k : ℤ)) * key_core m k
    · -- `v = 0`: only the boundary term survives
      have hv0 : v = 0 := hv.symm
      subst hv0
      have hu_eq : u = (n : ℤ) + 2 := by omega
      subst hu_eq
      rw [famC_one_zero, famC_eq_zero_of_neg (by norm_num : ((0 : ℤ) - 1) < 0),
        show ((n : ℤ) + 2) - 1 = (n : ℤ) + 1 by ring]
      simpa using key_boundary n
  · -- `u = 0`: symmetric
    have hu0 : u = 0 := hu.symm
    subst hu0
    have hv_eq : v = (n : ℤ) + 2 := by omega
    subst hv_eq
    rw [famC_one_zero, famC_eq_zero_of_neg (by norm_num : ((0 : ℤ) - 1) < 0),
      show ((n : ℤ) + 2) - 1 = (n : ℤ) + 1 by ring]
    simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using key_boundary n

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.Deleg.truncated_kernel_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `truncated_kernel_facts` — derivatives and bounds of the truncated kernel

For a source `c : ℝ → ℝ` that is `C^N` on `(0,∞)` with `|c^{(k)}| ≤ K` there (`k ≤ N`), the
parametric integral

  `x ↦ ∫ u in (1)..U, c (x * u) * u ^ s`     (`1 ≤ U`, `s ≤ 0`)

has `k`-th iterated derivative `x ↦ ∫ u in (1)..U, c^{(k)} (x * u) * u ^ (k + s)` for every
`k ≤ N` and `x > 0`, and that derivative is bounded by `K * (max 1 U) ^ (N + 1)`.

The proof is the truncated-interval analogue of `Series.SmoothAux.Deleg.radPhi_general`: the
integration variable runs over `[1, U]` with `1 ≤ U`, so no endpoint singularity is present
and integrability/measurability is plain continuity, while the exponent `k + s` is bounded by
`k ≤ N` on the interval (as `u ≥ 1` and `s ≤ 0`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptQSmooth.Deleg

set_option autoImplicit false

/-- The `k`-th differentiated truncated kernel, i.e. the parametric integral
`x ↦ ∫ u in (1)..U, c^{(k)} (x * u) * u ^ (k + s)`. -/
private def truncKernel (c : ℝ → ℝ) (U s : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun x => ∫ u in (1 : ℝ)..U, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)

/-- On `Ioi 0`, where `c` is `C^N`, the `k`-th iterated derivative of `c` is differentiable as
soon as `k < N`. -/
private lemma differentiableAt_iteratedDeriv_trunc {N : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) {k : ℕ} (hk : k < N) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (iteratedDeriv k c) y := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_of_lt hk)) ht).symm
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)

/-- On `Ioi 0` the `k`-th iterated derivative of a `C^N` function is continuous, `k ≤ N`. -/
private lemma continuousOn_iteratedDeriv_trunc {N : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) {k : ℕ} (hk : k ≤ N) :
    ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast hk)) ht).symm
  exact (hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk)
    (uniqueDiffOn_Ioi 0)).congr hEq

/-- The truncated kernel integrand `u ↦ c^{(k)}(x u) u^{k+s}` is continuous on `Ici a` whenever
`x > 0` and `a > 0` — in particular no endpoint singularity is present. -/
private lemma continuousOn_trunc_integrand {N : ℕ} {c : ℝ → ℝ} {s : ℝ} {k : ℕ}
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hk : k ≤ N) {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)) (Set.Ici a) := by
  have h1 : ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ici a) :=
    (continuousOn_iteratedDeriv_trunc hc hk).comp
      ((continuous_const.mul continuous_id).continuousOn)
      (fun u hu => mul_pos hx (lt_of_lt_of_le ha hu))
  have h2 : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) + s)) (Set.Ici a) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le ha hu)))
  exact h1.mul h2

/-- On `Ici a` with `a > 0` the function `u ↦ u ^ t` is continuous, for every real `t`. -/
private lemma continuousOn_rpow_Ici {t : ℝ} {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => u ^ t) (Set.Ici a) :=
  ContinuousOn.rpow_const continuousOn_id
    (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le ha hu)))

/-- The truncated kernel integrand is a.e. strongly measurable on `Ι 1 U` for `x > 0`. -/
private lemma aestronglyMeasurable_trunc {N : ℕ} {c : ℝ → ℝ} {U s : ℝ} (hU : 1 ≤ U)
    {k : ℕ} (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    AEStronglyMeasurable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s))
      (volume.restrict (Set.uIoc (1 : ℝ) U)) := by
  rw [Set.uIoc_of_le hU]
  exact ((continuousOn_trunc_integrand hc hk hx zero_lt_one).mono
    (fun u hu => le_of_lt hu.1)).aestronglyMeasurable measurableSet_Ioc

/-- The truncated kernel integrand is interval integrable on `1..U` for `x > 0`, `1 ≤ U`. -/
private lemma intervalIntegrable_trunc {N : ℕ} {c : ℝ → ℝ} {U s : ℝ} (hU : 1 ≤ U)
    {k : ℕ} (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s))
      volume (1 : ℝ) U := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hU]
  exact (continuousOn_trunc_integrand hc hk hx zero_lt_one).mono (fun u hu => hu.1)

/-- Differentiation under the integral sign for the truncated kernel: passing from the `k`-th
to the `(k+1)`-st kernel multiplies the `u`-weight by `u`. -/
private lemma hasDerivAt_truncKernel {N : ℕ} {c : ℝ → ℝ} {K U s : ℝ} (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K)
    {k : ℕ} (hk : k + 1 ≤ N) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (truncKernel c U s k) (truncKernel c U s (k + 1) z) z := by
  have hkle : k ≤ N := by omega
  have hklt : k < N := by omega
  have hneigh : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s))
      (volume.restrict (Set.uIoc (1 : ℝ) U)) := by
    filter_upwards [hneigh] with x hx
    exact aestronglyMeasurable_trunc hU hc hkle hx
  have hF_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + s)) volume (1 : ℝ) U :=
    intervalIntegrable_trunc hU hc hkle hz
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (k + 1) c (z * u) * u ^ (((k + 1 : ℕ) : ℝ) + s))
      (volume.restrict (Set.uIoc (1 : ℝ) U)) :=
    aestronglyMeasurable_trunc hU hc hk hz
  have hbound_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + s)) volume (1 : ℝ) U := by
    have hr : IntervalIntegrable (fun u : ℝ => u ^ (((k + 1 : ℕ) : ℝ) + s)) volume (1 : ℝ) U := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hU]
      exact (continuousOn_rpow_Ici (t := (((k + 1 : ℕ) : ℝ) + s)) zero_lt_one).mono
        (fun u hu => hu.1)
    exact hr.const_mul K
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (1 : ℝ) U → ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + s)‖
        ≤ K * t ^ (((k + 1 : ℕ) : ℝ) + s) := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le hU] at ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) hk (x * t) (mul_pos hx ht0))
      (Real.rpow_nonneg ht0.le _)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (1 : ℝ) U → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t) * t ^ ((k : ℝ) + s))
        (iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + s)) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le hU] at ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    have hxt : 0 < x * t := mul_pos hx ht0
    have hgd : HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c (x * t)) (x * t) := by
      simpa only [iteratedDeriv_succ] using
        (differentiableAt_iteratedDeriv_trunc hc hklt hxt).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t))
        (iteratedDeriv (k + 1) c (x * t) * t) x := by
      simpa only [Function.comp_def] using hgd.comp x hlin
    have hmul := hcomp.mul_const (t ^ ((k : ℝ) + s))
    refine hmul.congr_deriv ?_
    have hcast : (((k + 1 : ℕ)) : ℝ) + s = ((k : ℝ) + s) + 1 := by push_cast; ring
    have hrpow : t ^ (((k : ℝ) + s) + 1) = t ^ ((k : ℝ) + s) * t := by
      rw [Real.rpow_add ht0, Real.rpow_one]
    rw [hcast, hrpow]
    ring
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s))
    (F' := fun x u => iteratedDeriv (k + 1) c (x * u) * u ^ (((k + 1 : ℕ) : ℝ) + s))
    (x₀ := z) (s := Set.Ioi 0) (a := (1 : ℝ)) (b := U) (μ := volume)
    (bound := fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + s))
    hneigh hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  exact hmain

/-- `iteratedDeriv k` of the truncated kernel is the `k`-th truncated kernel, for every `k ≤ N`. -/
private lemma iteratedDeriv_trunc_eq {N : ℕ} {c : ℝ → ℝ} {K U s : ℝ} (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K) :
    ∀ k : ℕ, k ≤ N → ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun x : ℝ => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ s) x
        = truncKernel c U s k x := by
  intro k
  induction k with
  | zero =>
    intro _ x _
    simp only [truncKernel, iteratedDeriv_zero, Nat.cast_zero, zero_add]
  | succ n ih =>
    intro hn x hx
    have hnle : n ≤ N := by omega
    have h1 : deriv (iteratedDeriv n (fun x : ℝ => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ s)) x
        = deriv (truncKernel c U s n) x := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ih hnle y hy
    have h2 : deriv (truncKernel c U s n) x = truncKernel c U s (n + 1) x :=
      (hasDerivAt_truncKernel hK hU hc hb hn (z := x) hx).deriv
    rw [iteratedDeriv_succ, h1, h2]

/-- The bound on the truncated kernel: `|∫_1^U c^{(k)}(x u) u^{k+s} du| ≤ K (max 1 U)^{N+1}`. -/
private lemma truncKernel_bound {N : ℕ} {c : ℝ → ℝ} {K U s : ℝ} (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hs : s ≤ 0) (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K)
    {k : ℕ} (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    |truncKernel c U s k x| ≤ K * (max 1 U) ^ (N + 1) := by
  have hmax : max 1 U = U := max_eq_right hU
  have hU0 : (0 : ℝ) < U := lt_of_lt_of_le zero_lt_one hU
  have hf_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)) volume (1 : ℝ) U :=
    intervalIntegrable_trunc hU hc hk hx
  have h1 : |∫ u in (1 : ℝ)..U, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)|
      ≤ ∫ u in (1 : ℝ)..U, |iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)| :=
    intervalIntegral.abs_integral_le_integral_abs hU
  have hr : IntervalIntegrable (fun u : ℝ => u ^ ((k : ℝ) + s)) volume (1 : ℝ) U := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hU]
    exact (continuousOn_rpow_Ici (t := (k : ℝ) + s) zero_lt_one).mono (fun u hu => hu.1)
  have hdom_int : IntervalIntegrable (fun u : ℝ => K * u ^ ((k : ℝ) + s)) volume (1 : ℝ) U :=
    hr.const_mul K
  have hae : (fun u : ℝ => |iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)|)
      ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) U)] (fun u : ℝ => K * u ^ ((k : ℝ) + s)) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards with u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
    exact mul_le_mul_of_nonneg_right (hb k hk (x * u) (mul_pos hx hu0))
      (Real.rpow_nonneg hu0.le _)
  have h2 : (∫ u in (1 : ℝ)..U, |iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)|)
      ≤ ∫ u in (1 : ℝ)..U, K * u ^ ((k : ℝ) + s) :=
    intervalIntegral.integral_mono_ae_restrict hU hf_int.abs hdom_int hae
  have hrN : (k : ℝ) + s ≤ (N : ℝ) := by
    have h : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    linarith
  have h4 : (∫ u in (1 : ℝ)..U, u ^ ((k : ℝ) + s))
      ≤ ∫ u in (1 : ℝ)..U, (U : ℝ) ^ N := by
    refine intervalIntegral.integral_mono_on hU hr intervalIntegrable_const (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    calc u ^ ((k : ℝ) + s) ≤ u ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hu.1 hrN
      _ = (u : ℝ) ^ N := Real.rpow_natCast u N
      _ ≤ (U : ℝ) ^ N := pow_le_pow_left₀ hu0.le hu.2 N
  calc |truncKernel c U s k x|
      = |∫ u in (1 : ℝ)..U, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)| := by
        simp only [truncKernel]
    _ ≤ ∫ u in (1 : ℝ)..U, |iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)| := h1
    _ ≤ ∫ u in (1 : ℝ)..U, K * u ^ ((k : ℝ) + s) := h2
    _ = K * ∫ u in (1 : ℝ)..U, u ^ ((k : ℝ) + s) :=
        intervalIntegral.integral_const_mul K _
    _ ≤ K * ∫ u in (1 : ℝ)..U, (U : ℝ) ^ N := mul_le_mul_of_nonneg_left h4 hK
    _ = K * ((U - 1) * (U : ℝ) ^ N) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ K * ((U : ℝ) ^ N * U) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        calc (U - 1) * (U : ℝ) ^ N ≤ U * (U : ℝ) ^ N := by
              refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hU0.le N)
              linarith
          _ = (U : ℝ) ^ N * U := by ring
    _ = K * (U : ℝ) ^ (N + 1) := by rw [pow_succ]
    _ = K * (max 1 U) ^ (N + 1) := by rw [hmax]

theorem truncated_kernel_facts {N : ℕ} {c : ℝ → ℝ} {K U s : ℝ} (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hs : s ≤ 0) (hc : ContDiffOn ℝ (↑N) c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) :
    ∀ k : ℕ, k ≤ N → ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun x : ℝ => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ s) x
          = ∫ u in (1 : ℝ)..U, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + s)
        ∧ |iteratedDeriv k (fun x : ℝ => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ s) x|
            ≤ K * (max 1 U) ^ (N + 1) := by
  intro k hk x hx
  refine ⟨?_, ?_⟩
  · rw [iteratedDeriv_trunc_eq hK hU hc hb k hk x hx]
    simp only [truncKernel]
  · rw [iteratedDeriv_trunc_eq hK hU hc hb k hk x hx]
    exact truncKernel_bound hK hU hs hc hb hk hx

end Work.FTS.PhiStar.Honesty.CptQSmooth.Deleg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_mul_self_atTop_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-! ### elementary real-power and square estimates -/

/-- `(z^a)² = z^{2a}` for `z > 0`. -/
private lemma rpow_sq {z : ℝ} (hz : 0 < z) (a : ℝ) : (z ^ a) ^ 2 = z ^ (2 * a) := by
  rw [sq, ← Real.rpow_add hz]
  congr 1
  ring









/-- `(a+b+c)² ≤ 3(a²+b²+c²)`. -/
private lemma sq_add_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]




/-! ### the three constants of the estimate -/


/-- `P = ∫_{Ioi 1} c²`. -/
private def rgP (c : ℝ → ℝ) : ℝ := ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2







/-! ### the two halves of the pointwise bound -/



/-! ### the pointwise bound and the main theorem -/



end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Linv23Aux.Fallback =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Linv23Aux.Fallback

set_option autoImplicit false






end Work.FTS.PhiStar.Linv23Aux.Fallback
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Linv23Aux.linvI_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Linv23Aux

set_option autoImplicit false



end Work.FTS.PhiStar.Linv23Aux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Linv23Aux.linv_smooth_of_phi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Linv23Aux

set_option autoImplicit false



end Work.FTS.PhiStar.Linv23Aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real ContDiff Topology

namespace Work.FTS.PhiStar.LinvFlat

open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-!
# `Linv_contDiffOn_hasDerivAt`

`Linv h θ = -(sin²θ cos³θ)⁻¹ · ∫_0^θ sin²t cos³t h t / sin 2t dt` is the `σ`-normalised
zero-moment Dirichlet inverse of `L₀` (`Work.FTS.PhiStar.Linv`).  This file shows that it
inherits the smoothness of the source and computes its derivative: `Linv h` is `C^n` on
`(0, π/2)` whenever `h` is, and

`(Linv h)'(θ) = -(1/sin 2θ)·(h θ + 2(2cos²θ - 3sin²θ)·Linv h θ)`.

The integrability hypothesis `hint` is exactly what makes the primitive `LinvPrim h` a
genuine (non-junk) integral: `LinvInt h = h·sin θcos²θ/2` identically, so `hint` says that
`LinvInt h` is integrable on `[0, π/2]`, hence on every `[0, θ]` with `θ < π/2`.
-/

/-- The integrand of `Linv`'s primitive, in the regularised form `sin t cos²t h t / 2`. -/
private lemma linvInt_eq_factor (h : ℝ → ℝ) :
    LinvInt h = fun t => (Real.sin t * Real.cos t ^ 2 / 2) * h t := by
  funext t; exact LinvInt_eq h t

/-- The integrand of `Linv`'s primitive, in the form `h t · sinCos2 t / 2`. -/
private lemma linvInt_eq_sinCos2 (h : ℝ → ℝ) :
    LinvInt h = fun t => (h t * Work.Elliptic.sinCos2 t) / 2 := by
  funext t; rw [LinvInt_eq]; simp only [Work.Elliptic.sinCos2]; ring

/-- `LinvInt h` is interval-integrable on `[0, θ]` for `θ ∈ (0, π/2)`: it is a multiple of
`h · sinCos2`, which is integrable on all of `[0, π/2]` by hypothesis. -/
private lemma intervalIntegrable_linvInt {h : ℝ → ℝ}
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    IntervalIntegrable (LinvInt h) volume 0 θ := by
  rw [linvInt_eq_sinCos2, intervalIntegrable_iff, Set.uIoc_of_le (le_of_lt hθ.1)]
  have hsub : Set.Ioc 0 θ ⊆ Work.Spaces.Iθ :=
    fun t ht => ⟨le_of_lt ht.1, le_of_lt (lt_of_le_of_lt ht.2 hθ.2)⟩
  exact (hint.mono_set hsub).div_const 2

/-- `LinvInt h` is continuous at every point of `(0, π/2)`. -/
private lemma continuousAt_linvInt {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (π/2)))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (π/2)) : ContinuousAt (LinvInt h) t := by
  rw [linvInt_eq_factor]
  exact ((by fun_prop : ContinuousAt (fun t : ℝ => Real.sin t * Real.cos t ^ 2 / 2) t)).mul
    (hcont.continuousAt (isOpen_Ioo.mem_nhds ht))

/-- Fundamental theorem of calculus for `LinvPrim`: on `(0, π/2)` its derivative is
`LinvInt h`. -/
private lemma hasDerivAt_LinvPrim_of {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (π/2)))
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    HasDerivAt (LinvPrim h) (LinvInt h θ) θ := by
  have hInt := intervalIntegrable_linvInt hint hθ
  have hcontAt := continuousAt_linvInt hcont hθ
  have hsm : StronglyMeasurableAtFilter (LinvInt h) (𝓝 θ) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun x hx => continuousAt_linvInt hcont hx) θ hθ
  exact intervalIntegral.integral_hasDerivAt_right hInt hsm hcontAt

/-- `LinvInt h` is `C^n` on `(0, π/2)` whenever `h` is. -/
private lemma contDiffOn_linvInt {n : ℕ} {h : ℝ → ℝ}
    (hcd : ContDiffOn ℝ (n : ℕ∞ω) h (Set.Ioo 0 (π/2))) :
    ContDiffOn ℝ (n : ℕ∞ω) (LinvInt h) (Set.Ioo 0 (π/2)) := by
  rw [linvInt_eq_factor]
  exact (by fun_prop : ContDiffOn ℝ (n : ℕ∞ω)
    (fun t : ℝ => Real.sin t * Real.cos t ^ 2 / 2) (Set.Ioo 0 (π/2))).mul hcd

/-- `LinvPrim h = ∫_0^θ LinvInt h` is `C^n` on `(0, π/2)` whenever `h` is: it is actually
`C^(n+1)`, since its derivative is `LinvInt h`, which is `C^n`. -/
private lemma contDiffOn_LinvPrim {n : ℕ} {h : ℝ → ℝ}
    (hcd : ContDiffOn ℝ (n : ℕ∞ω) h (Set.Ioo 0 (π/2)))
    (hcont : ContinuousOn h (Set.Ioo 0 (π/2)))
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    ContDiffOn ℝ (n : ℕ∞ω) (LinvPrim h) (Set.Ioo 0 (π/2)) := by
  have hP1 : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (LinvPrim h) (Set.Ioo 0 (π/2)) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (hasDerivAt_LinvPrim_of hcont hint hx).differentiableAt.differentiableWithinAt
    · intro hcon
      exact absurd hcon (by simp)
    · refine (contDiffOn_linvInt hcd).congr ?_
      intro x hx
      exact (hasDerivAt_LinvPrim_of hcont hint hx).deriv
  exact hP1.of_le (by simp)

/-- The reciprocal weight `θ ↦ (sin²θ cos³θ)⁻¹` is smooth on `(0, π/2)`. -/
private lemma contDiffOn_inv_LinvMu {n : ℕ} :
    ContDiffOn ℝ (n : ℕ∞ω) (fun θ => (LinvMu θ)⁻¹) (Set.Ioo 0 (π/2)) := by
  refine ContDiffOn.inv ?_ ?_
  · show ContDiffOn ℝ (n : ℕ∞ω) (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3)
      (Set.Ioo 0 (π/2))
    fun_prop
  · intro x hx
    have hs : Real.sin x ≠ 0 := ne_of_gt (linv_sin_pos hx)
    have hc : Real.cos x ≠ 0 := ne_of_gt (linv_cos_pos hx)
    exact mul_ne_zero (pow_ne_zero 2 hs) (pow_ne_zero 3 hc)

theorem Linv_contDiffOn_hasDerivAt {h : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcd : ContDiffOn ℝ n h (Set.Ioo 0 (π/2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    ContDiffOn ℝ n (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (π/2)) ∧
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) →
        HasDerivAt (Work.FTS.PhiStar.Linv h)
          (-(1 / Real.sin (2 * θ)) * (h θ + 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2)
            * Work.FTS.PhiStar.Linv h θ)) θ := by
  have hcont : ContinuousOn h (Set.Ioo 0 (π/2)) := hcd.continuousOn
  have hLP : ContDiffOn ℝ (n : ℕ∞ω) (LinvPrim h) (Set.Ioo 0 (π/2)) :=
    contDiffOn_LinvPrim hcd hcont hint
  have hμinv : ContDiffOn ℝ (n : ℕ∞ω) (fun θ => (LinvMu θ)⁻¹) (Set.Ioo 0 (π/2)) :=
    contDiffOn_inv_LinvMu
  have hmain : ContDiffOn ℝ (n : ℕ∞ω) (Linv h) (Set.Ioo 0 (π/2)) := by
    rw [Linv_eq]
    exact (hμinv.mul hLP).neg
  refine ⟨hmain, ?_⟩
  intro θ hθ
  have hS : Real.sin θ ≠ 0 := ne_of_gt (linv_sin_pos hθ)
  have hC : Real.cos θ ≠ 0 := ne_of_gt (linv_cos_pos hθ)
  have h3 : HasDerivAt (fun θ => -((LinvMu θ)⁻¹ * LinvPrim h θ))
      (-(1 / Real.sin (2 * θ)) * (h θ + 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2)
        * Linv h θ)) θ := by
    have hbase := ((hasDerivAt_LinvMu θ).inv (LinvMu_ne_zero_of_mem_Ioo hθ)).mul
      (hasDerivAt_LinvPrim_of hcont hint hθ)
    refine (hbase.neg).congr_deriv ?_
    rw [Linv_apply, LinvInt_eq, Real.sin_two_mul]
    simp only [LinvMu, Pi.inv_apply]
    field_simp
    ring
  rw [Linv_eq]
  exact h3

end Work.FTS.PhiStar.LinvFlat
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.PhiPsiDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-- `PhiQ Q c z = ∫₀¹ c (z u) u^{Q-1} du`, the inner rescaled Green piece with exponent `Q > 0`. -/
def PhiQ (Q : ℝ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, c (z * u) * u ^ (Q - 1)

/-- `PsiP P c z = ∫_{u>1} c (z u) u^{-P-1} du`, the outer rescaled Green piece. -/
def PsiP (P : ℝ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ u in Set.Ioi 1, c (z * u) * u ^ (-P - 1)



end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The three analytic facts about `𝒜φ = VocabO.phiA α` -/

/-- `𝒜φ` is continuous on the positive half-line: it is a rational function whose only pole
is at `z = −1`. -/
theorem psiSeriesIntegrability_phiACont (α : ℝ) :
    ContinuousOn (Work.FTS.VocabO.phiA α) (Set.Ioi 0) := by
  refine ContinuousOn.congr (f := fun z : ℝ =>
    4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4
      + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3) ?_ ?_
  · have hne4 : ∀ x ∈ Set.Ioi (0 : ℝ), (1 + x) ^ 4 ≠ 0 := by
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      have h1x : (0 : ℝ) < 1 + x := by linarith
      positivity
    have hne3 : ∀ x ∈ Set.Ioi (0 : ℝ), (1 + x) ^ 3 ≠ 0 := by
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      have h1x : (0 : ℝ) < 1 + x := by linarith
      positivity
    fun_prop
  · intro z hz
    exact Work.FTS.PhiStar.phiA_eq α z (by
      intro h
      rw [h] at hz
      norm_num at hz)

/-- **Small-`z` domination**: `|𝒜φ(t)| ≤ (10α+10)·t` on `(0,1)`. -/
theorem psiSeriesIntegrability_phiA_bound_small {α : ℝ} (hα : 0 < α) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |Work.FTS.VocabO.phiA α t| ≤ (10 * α + 10) * t := by
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : t < 1 := ht.2
  have htne : t ≠ -1 := by linarith
  have ht4 : (0 : ℝ) < (1 + t) ^ 4 := by positivity
  have ht3 : (0 : ℝ) < (1 + t) ^ 3 := by positivity
  have h1 : |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4| ≤ 8 * α * t := by
    rw [abs_div, abs_of_pos ht4, div_le_iff₀ ht4]
    have habs : |4 * α * t ^ 2 * (t - 2)| = 4 * α * t ^ 2 * (2 - t) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg (sq_nonneg t), abs_of_nonpos (by linarith : t - 2 ≤ 0)]
      ring
    rw [habs]
    have hA : 4 * α * t ^ 2 * (2 - t) ≤ 8 * α * t ^ 2 := by
      have h2t : 2 - t ≤ 2 := by linarith
      have hnn : (0 : ℝ) ≤ 4 * α * t ^ 2 := by positivity
      calc 4 * α * t ^ 2 * (2 - t) ≤ 4 * α * t ^ 2 * 2 :=
            mul_le_mul_of_nonneg_left h2t hnn
        _ = 8 * α * t ^ 2 := by ring
    have hB : 8 * α * t ^ 2 ≤ 8 * α * t * (1 + t) ^ 4 := by
      have h4 : t ≤ (1 + t) ^ 4 := by
        have h5 : (1 : ℝ) ≤ (1 + t) ^ 4 := one_le_pow₀ (by linarith)
        linarith
      have hnn : (0 : ℝ) ≤ 8 * α * t := by positivity
      calc 8 * α * t ^ 2 = 8 * α * t * t := by ring
        _ ≤ 8 * α * t * (1 + t) ^ 4 := mul_le_mul_of_nonneg_left h4 hnn
    linarith
  have h2 : |2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3| ≤ 2 * (5 + α) * t := by
    rw [abs_div, abs_of_pos ht3, div_le_iff₀ ht3]
    have habs : |2 * (5 + α) * t * (1 - t)| = 2 * (5 + α) * t * (1 - t) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg ht0.le,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
    rw [habs]
    have hA : 1 - t ≤ (1 + t) ^ 3 := by
      have h3 : (1 : ℝ) ≤ (1 + t) ^ 3 := one_le_pow₀ (by linarith)
      linarith
    have hnn : (0 : ℝ) ≤ 2 * (5 + α) * t := by positivity
    exact mul_le_mul_of_nonneg_left hA hnn
  rw [Work.FTS.PhiStar.phiA_eq α t htne]
  calc |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4
        + 2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3|
      ≤ |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4|
        + |2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3| := abs_add_le _ _
    _ ≤ 8 * α * t + 2 * (5 + α) * t := by linarith
    _ = (10 * α + 10) * t := by ring

/-- **Large-`z` domination**: `|𝒜φ(t)| ≤ (14α+10)/t` on `(1,∞)`. -/
theorem psiSeriesIntegrability_phiA_bound_large {α : ℝ} (hα : 0 < α) {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    |Work.FTS.VocabO.phiA α t| ≤ (14 * α + 10) / t := by
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
  have htne : t ≠ -1 := by linarith
  have ht4 : (0 : ℝ) < (1 + t) ^ 4 := by positivity
  have ht3 : (0 : ℝ) < (1 + t) ^ 3 := by positivity
  have h1 : |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4| ≤ 12 * α / t := by
    rw [abs_div, abs_of_pos ht4, div_le_div_iff₀ ht4 ht0]
    have habs : |4 * α * t ^ 2 * (t - 2)| = 4 * α * t ^ 2 * |t - 2| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg (sq_nonneg t)]
    rw [habs]
    have hle : |t - 2| ≤ 3 * t := by
      rw [abs_le]
      constructor <;> linarith
    have h44 : t ^ 4 ≤ (1 + t) ^ 4 := pow_le_pow_left₀ ht0.le (by linarith) 4
    have hA : 4 * α * t ^ 2 * |t - 2| * t ≤ 4 * α * t ^ 2 * (3 * t) * t := by
      have hnn : (0 : ℝ) ≤ 4 * α * t ^ 2 * t := by positivity
      calc 4 * α * t ^ 2 * |t - 2| * t = (4 * α * t ^ 2 * t) * |t - 2| := by ring
        _ ≤ (4 * α * t ^ 2 * t) * (3 * t) := mul_le_mul_of_nonneg_left hle hnn
        _ = 4 * α * t ^ 2 * (3 * t) * t := by ring
    have hB : 4 * α * t ^ 2 * (3 * t) * t ≤ 12 * α * (1 + t) ^ 4 := by
      have h12 : 4 * α * t ^ 2 * (3 * t) * t = 12 * α * t ^ 4 := by ring
      rw [h12]
      exact mul_le_mul_of_nonneg_left h44 (by positivity)
    linarith
  have h2 : |2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3| ≤ 2 * (5 + α) / t := by
    rw [abs_div, abs_of_pos ht3, div_le_div_iff₀ ht3 ht0]
    have habs : |2 * (5 + α) * t * (1 - t)| = 2 * (5 + α) * t * |1 - t| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg ht0.le]
    rw [habs]
    have hle : |1 - t| ≤ t := by
      rw [abs_le]
      constructor <;> linarith
    have h33 : t ^ 3 ≤ (1 + t) ^ 3 := pow_le_pow_left₀ ht0.le (by linarith) 3
    have hA : 2 * (5 + α) * t * |1 - t| * t ≤ 2 * (5 + α) * t * t * t := by
      have hnn : (0 : ℝ) ≤ 2 * (5 + α) * t * t := by positivity
      calc 2 * (5 + α) * t * |1 - t| * t = (2 * (5 + α) * t * t) * |1 - t| := by ring
        _ ≤ (2 * (5 + α) * t * t) * t := mul_le_mul_of_nonneg_left hle hnn
        _ = 2 * (5 + α) * t * t * t := by ring
    have hB : 2 * (5 + α) * t * t * t ≤ 2 * (5 + α) * (1 + t) ^ 3 := by
      have h13 : 2 * (5 + α) * t * t * t = 2 * (5 + α) * t ^ 3 := by ring
      rw [h13]
      exact mul_le_mul_of_nonneg_left h33 (by positivity)
    linarith
  rw [Work.FTS.PhiStar.phiA_eq α t htne]
  calc |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4
        + 2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3|
      ≤ |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4|
        + |2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3| := abs_add_le _ _
    _ ≤ 12 * α / t + 2 * (5 + α) / t := by linarith
    _ = (14 * α + 10) / t := by ring

/-- **Integrability near `0`**: `𝒜φ(t)·t^{(2m+5)/α−1}` is integrable on `(0,1)`.

The integrand is `O(t^{(2m+5)/α})` and `(2m+5)/α > 0`, so `t^{(2m+5)/α−1}` is even locally
bounded there. -/
theorem psiSeriesIntegrability_phiAIntSmall (α : ℝ) (hα : 0 < α) (m : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1) := by
  set β : ℝ := (2 * (m : ℝ) + 5) / α - 1 with hβ
  have hunit : (1 : ℝ) + β = (2 * (m : ℝ) + 5) / α := by
    rw [hβ]; ring
  have hexp : -1 < (2 * (m : ℝ) + 5) / α := by
    have h2m : (0 : ℝ) < 2 * (m : ℝ) + 5 := by positivity
    have hd : (0 : ℝ) < (2 * (m : ℝ) + 5) / α := div_pos h2m hα
    linarith
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => (10 * α + 10) * t ^ ((2 * (m : ℝ) + 5) / α)) (Set.Ioo 0 1) :=
    MeasureTheory.Integrable.const_mul
      ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := (2 * (m : ℝ) + 5) / α)
        (t := (1 : ℝ)) one_pos).2 hexp) (10 * α + 10)
  have hpow : ContinuousOn (fun x : ℝ => x ^ β) (Set.Ioi 0) :=
    fun x hx => (Real.continuousAt_rpow_const x β (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ β)
      (Set.Ioo 0 1) :=
    ((psiSeriesIntegrability_phiACont α).mul hpow).mono (fun x hx => hx.1)
  refine MeasureTheory.Integrable.mono' hmaj
    (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  have hb := psiSeriesIntegrability_phiA_bound_small hα ht
  have hβpos : (0 : ℝ) < t ^ β := Real.rpow_pos_of_pos ht0 β
  have hmul : (t : ℝ) * t ^ β = t ^ (1 + β) := by
    rw [Real.rpow_add ht0 1 β, Real.rpow_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hβpos]
  calc |Work.FTS.VocabO.phiA α t| * t ^ β
      ≤ ((10 * α + 10) * t) * t ^ β := mul_le_mul_of_nonneg_right hb hβpos.le
    _ = (10 * α + 10) * (t * t ^ β) := by ring
    _ = (10 * α + 10) * t ^ (1 + β) := by rw [hmul]
    _ = (10 * α + 10) * t ^ ((2 * (m : ℝ) + 5) / α) := by rw [hunit]

/-- **Integrability at `∞`**: `𝒜φ(t)·t^{−2m/α−1}` is integrable on `(1,∞)`.

The integrand is `O(t^{−2m/α−2})` and `−2m/α − 2 < −1`. -/
theorem psiSeriesIntegrability_phiAIntLarge (α : ℝ) (hα : 0 < α) (m : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1) := by
  set γ : ℝ := -(2 * (m : ℝ) / α) - 1 with hγ
  have hexp : γ - 1 < -1 := by
    rw [hγ]
    have : (0 : ℝ) ≤ 2 * (m : ℝ) / α := by positivity
    linarith
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => (14 * α + 10) * t ^ (γ - 1)) (Set.Ioi 1) :=
    MeasureTheory.Integrable.const_mul
      ((integrableOn_Ioi_rpow_iff (s := γ - 1) (t := (1 : ℝ)) one_pos).2 hexp) (14 * α + 10)
  have hpow : ContinuousOn (fun x : ℝ => x ^ γ) (Set.Ioi 0) :=
    fun x hx => (Real.continuousAt_rpow_const x γ (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (by norm_num)
  have hcont : ContinuousOn (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ γ)
      (Set.Ioi 1) :=
    ((psiSeriesIntegrability_phiACont α).mul hpow).mono hsub
  refine MeasureTheory.Integrable.mono' hmaj
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hb := psiSeriesIntegrability_phiA_bound_large hα ht
  have hγpos : (0 : ℝ) < t ^ γ := Real.rpow_pos_of_pos ht0 γ
  have hmul : (t : ℝ)⁻¹ * t ^ γ = t ^ (γ - 1) := by
    rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0 (-1) γ]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hγpos]
  calc |Work.FTS.VocabO.phiA α t| * t ^ γ
      ≤ ((14 * α + 10) / t) * t ^ γ := mul_le_mul_of_nonneg_right hb hγpos.le
    _ = (14 * α + 10) * (t⁻¹ * t ^ γ) := by ring
    _ = (14 * α + 10) * t ^ (γ - 1) := by rw [hmul]

/-! ## The target -/

theorem psiSeriesIntegrability (α : ℝ) (hα : 0 < α) (ψ : ℝ → ℝ) :
    (∀ m : ℕ, ContinuousOn (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t) (Set.Ioi 0)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) ∧
    ContinuousOn (Work.FTS.VocabO.phiA α) (Set.Ioi 0) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) := by
  refine ⟨?_, ?_, ?_, psiSeriesIntegrability_phiACont α,
    fun m => psiSeriesIntegrability_phiAIntSmall α hα m,
    fun m => psiSeriesIntegrability_phiAIntLarge α hα m⟩
  · -- continuity of the `cmode`-slices, from `cmode m (RemSource α ψ) = α²·bmode m ψ·𝒜φ`
    intro m
    refine ContinuousOn.congr (f := fun t : ℝ =>
      (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) * Work.FTS.VocabO.phiA α t) ?_ ?_
    · exact (psiSeriesIntegrability_phiACont α).const_mul _
    · intro t ht
      simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
      ring
  · intro m
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
          * (Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)))
        (Set.Ioo 0 1) :=
      MeasureTheory.Integrable.const_mul (psiSeriesIntegrability_phiAIntSmall α hα m) _
    refine h1.congr_fun ?_ measurableSet_Ioo
    intro t ht
    simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
    ring
  · intro m
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
          * (Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)))
        (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul (psiSeriesIntegrability_phiAIntLarge α hα m) _
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
    ring

end Work.FTS.PhiStar.Series.Deleg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Weil.remSourceFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false

/-! ## The closure of `SmoothOpen` under separable products with open-interval factors -/

/-- The separable product `(z,θ) ↦ A z * B θ` of a radial factor which is `C^n` on `(0,∞)` for
every `n` and an angular factor which is `C^n` on `(0,π/2)` for every `n` is `C^∞` on the open
quadrant. -/
private theorem sep_mul_smoothOpen_quad {A B : ℝ → ℝ}
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A (Set.Ioi 0))
    (hB : ∀ m : ℕ, ContDiffOn ℝ m B (Set.Ioo 0 (π / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z * B θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => A z * B θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => A p.1 * B p.2) Work.FTS.EllipticEst.Q0
  rw [show (fun p : ℝ × ℝ => A p.1 * B p.2)
      = (fun p : ℝ × ℝ => A p.1) * (fun p : ℝ × ℝ => B p.2) from rfl]
  have hAinfty : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Ioi 0) :=
    contDiffOn_infty.mpr hA
  have hBinfty : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B (Set.Ioo 0 (π / 2)) :=
    contDiffOn_infty.mpr hB
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A p.1)
      Work.FTS.EllipticEst.Q0 :=
    hAinfty.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => B p.2)
      Work.FTS.EllipticEst.Q0 :=
    hBinfty.comp contDiffOn_snd fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2
  exact h1.mul h2

/-! ## The size and the `L²`-integrability of the radial factor `𝒜φ` -/

/-- **`𝒜φ = phiA α` is `O(1/z)` at infinity and `O(z)` at the origin**: for `z > 0`,
`|𝒜φ(z)| ≤ K/(1+z)` with the explicit `α`-dependent constant
`K = |2α - 10| + 8|α| + |10 + 2α|`. -/
private theorem phiA_abs_le_inv_one_add (α : ℝ) {z : ℝ} (hz : 0 < z) :
    |Work.FTS.VocabO.phiA α z|
      ≤ (|2 * α - 10| + 8 * |α| + |10 + 2 * α|) / (1 + z) := by
  set K : ℝ := |2 * α - 10| + 8 * |α| + |10 + 2 * α| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _)))
      (abs_nonneg _)
  have hz0 : (0 : ℝ) ≤ z := hz.le
  have hz1 : z ≠ -1 := by linarith
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  have hz3 : (0 : ℝ) ≤ z ^ 3 := pow_nonneg hz0 3
  have hs1 : (0 : ℝ) < 1 + z := by linarith
  have h4 : (0 : ℝ) < (1 + z) ^ 4 := pow_pos hs1 4
  -- coefficient bounds splitting the numerator `M z = (2α-10)z³ - 8αz² + (10+2α)z` into the
  -- three nonnegative pieces `A = |2α-10|z³`, `B = 8|α|z²`, `C = |10+2α|z`
  have hA1 : (2 * α - 10) ≤ |2 * α - 10| := le_abs_self _
  have hA2 : -(2 * α - 10) ≤ |2 * α - 10| := neg_le_abs _
  have hB1 : 8 * α ≤ 8 * |α| := by linarith [le_abs_self α]
  have hB2 : -(8 * α) ≤ 8 * |α| := by linarith [neg_le_abs α]
  have hC1 : (10 + 2 * α) ≤ |10 + 2 * α| := le_abs_self _
  have hC2 : -(10 + 2 * α) ≤ |10 + 2 * α| := neg_le_abs _
  have hnum : |(2 * α - 10) * z ^ 3 - 8 * α * z ^ 2 + (10 + 2 * α) * z|
      ≤ |2 * α - 10| * z ^ 3 + 8 * |α| * z ^ 2 + |10 + 2 * α| * z := by
    rw [abs_le]
    constructor
    · have e1 : -(2 * α - 10) * z ^ 3 ≤ |2 * α - 10| * z ^ 3 :=
        mul_le_mul_of_nonneg_right hA2 hz3
      have e2 : 8 * α * z ^ 2 ≤ 8 * |α| * z ^ 2 :=
        mul_le_mul_of_nonneg_right hB1 hz2
      have e3 : -(10 + 2 * α) * z ≤ |10 + 2 * α| * z :=
        mul_le_mul_of_nonneg_right hC2 hz0
      nlinarith [e1, e2, e3]
    · have e1 : (2 * α - 10) * z ^ 3 ≤ |2 * α - 10| * z ^ 3 :=
        mul_le_mul_of_nonneg_right hA1 hz3
      have e2 : -(8 * α) * z ^ 2 ≤ 8 * |α| * z ^ 2 :=
        mul_le_mul_of_nonneg_right hB2 hz2
      have e3 : (10 + 2 * α) * z ≤ |10 + 2 * α| * z :=
        mul_le_mul_of_nonneg_right hC1 hz0
      nlinarith [e1, e2, e3]
  have hsum : |2 * α - 10| * z ^ 3 + 8 * |α| * z ^ 2 + |10 + 2 * α| * z
      ≤ K * (z ^ 3 + z ^ 2 + z) := by
    rw [hK]
    have hz2z : (0 : ℝ) ≤ z ^ 2 + z := by linarith
    have hz3z : (0 : ℝ) ≤ z ^ 3 + z := by linarith
    have hz3z2 : (0 : ℝ) ≤ z ^ 3 + z ^ 2 := by linarith
    nlinarith [mul_nonneg (abs_nonneg (2 * α - 10)) hz2z,
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (abs_nonneg α)) hz3z,
      mul_nonneg (abs_nonneg (10 + 2 * α)) hz3z2]
  have hMM : |(2 * α - 10) * z ^ 3 - 8 * α * z ^ 2 + (10 + 2 * α) * z|
      ≤ K * (z ^ 3 + z ^ 2 + z) := le_trans hnum hsum
  have h3 : z ^ 3 + z ^ 2 + z ≤ (1 + z) ^ 3 := by nlinarith [hz0, sq_nonneg z]
  have hstep : |Work.FTS.VocabO.phiA α z| ≤ K * (1 + z) ^ 3 / (1 + z) ^ 4 := by
    rw [Work.FTS.PhiStar.Series.phiA_combined α z hz1, abs_div, abs_of_pos h4]
    exact div_le_div_of_nonneg_right
      (le_trans hMM (mul_le_mul_of_nonneg_left h3 hK0)) h4.le
  have hfinal : K * (1 + z) ^ 3 / (1 + z) ^ 4 = K / (1 + z) := by
    have hs1n : (1 + z) ≠ 0 := ne_of_gt hs1
    have hs4n : (1 + z) ^ 4 ≠ 0 := pow_ne_zero 4 hs1n
    field_simp
  rw [hfinal] at hstep
  exact hstep

/-- **`(𝒜φ)²` is integrable on `(0,∞)`** for every real `α`: `𝒜φ = phiA α` is a rational
function with its only pole at `z = -1` (outside `(0,∞)`), vanishing like `z` at `0` and like
`1/z` at `∞`, so it is dominated by `K/(1+z)`, whose square is integrable on `Iz = [0,∞)`
(`Work.Elliptic.WtoH_IntZ`). -/
private theorem phiA_sq_integrableOn' (α : ℝ) :
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.FTS.VocabO.phiA α z ^ 2) (Set.Ioi 0) := by
  set K : ℝ := |2 * α - 10| + 8 * |α| + |10 + 2 * α| with hK
  have hbase : MeasureTheory.IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi 0) := by
    refine Work.Elliptic.WtoH_IntZ.1.mono_set ?_
    intro z hz
    rw [Work.Spaces.Iz]
    exact Set.mem_Ici.mpr hz.le
  have hmaj : MeasureTheory.IntegrableOn (fun z : ℝ => K ^ 2 * (1 / (1 + z) ^ 2))
      (Set.Ioi 0) := hbase.const_mul (K ^ 2)
  have hsqu : ∀ z : ℝ, (K / (1 + z)) ^ 2 = K ^ 2 * (1 / (1 + z) ^ 2) := by
    intro z
    rw [div_pow, div_eq_mul_inv]
    ring
  refine hmaj.mono' ?_ ?_
  · have hcont : ContinuousOn (fun z : ℝ => Work.FTS.VocabO.phiA α z ^ 2) (Set.Ioi 0) :=
      fun z hz =>
        (((Work.FTS.PhiStar.contDiffAt_phiA_of α 0 hz).continuousAt).pow 2).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    change ‖Work.FTS.VocabO.phiA α z ^ 2‖ ≤ K ^ 2 * (1 / (1 + z) ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hbdd : |Work.FTS.VocabO.phiA α z| ≤ K / (1 + z) := phiA_abs_le_inv_one_add α hz
    have hsq : (Work.FTS.VocabO.phiA α z) ^ 2 ≤ (K / (1 + z)) ^ 2 := by
      have h2 : |Work.FTS.VocabO.phiA α z| ^ 2 ≤ (K / (1 + z)) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (abs_nonneg (Work.FTS.VocabO.phiA α z)) hbdd
      rwa [sq_abs] at h2
    rw [← hsqu z]
    exact hsq

/-! ## The three facts about the source -/

theorem remSourceFacts (α : ℝ) (ψ : ℝ → ℝ) (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.RemSource α ψ) ∧
    Work.Elliptic.OrthCond (Work.FTS.PhiStar.RemSource α ψ) ∧
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.RemSource α ψ p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ## 1. the source is `C^∞` on the open quadrant: it is a separable product
    refine sep_mul_smoothOpen_quad (A := fun z : ℝ => α ^ 2 * Work.FTS.VocabO.phiA α z)
      (B := ψ) ?_ ?_
    · -- the `z`-factor `α^2 · 𝒜φ` is `C^n` on `(0,∞)` for every `n`
      intro m z hz
      exact ((contDiffAt_const (c := α ^ 2)).mul
        (Work.FTS.PhiStar.contDiffAt_phiA_of α m hz)).contDiffWithinAt
    · -- the `θ`-factor `ψ` is `C^n` on `(0,π/2)` for every `n`
      intro m
      exact contDiffOn_iff_forall_nat_le.mp hψ.smooth m le_top
  · -- ## 2. the angular moment of the source vanishes
    intro z
    have hF : Work.Elliptic.Fstar (Work.FTS.PhiStar.RemSource α ψ) z
        = (α ^ 2 * Work.FTS.VocabO.phiA α z)
          * (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) := by
      simp only [Work.Elliptic.Fstar, Work.FTS.PhiStar.RemSource]
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hF, hψ.moment, mul_zero]
  · -- ## 3. the source is square integrable on the quadrant: both factors are `L²`
    have hpsi2 : MeasureTheory.IntegrableOn (fun θ : ℝ => ψ θ ^ 2) (Set.Ioo 0 (π / 2)) :=
      continuousOn_sq_integrableOn_Ioo (a := 0) (b := π / 2)
        (by linarith [Real.pi_pos]) hψ.cont
    have hphi2 : MeasureTheory.IntegrableOn
        (fun z : ℝ => (α ^ 2 * Work.FTS.VocabO.phiA α z) ^ 2) (Set.Ioi 0) := by
      have hscaled : MeasureTheory.IntegrableOn
          (fun z : ℝ => α ^ 4 * Work.FTS.VocabO.phiA α z ^ 2) (Set.Ioi 0) :=
        MeasureTheory.Integrable.const_mul (phiA_sq_integrableOn' α) (α ^ 4)
      exact hscaled.congr_fun (fun z _ => by ring) measurableSet_Ioi
    have hprod : MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => (α ^ 2 * Work.FTS.VocabO.phiA α p.1) ^ 2 * ψ p.2 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      integrableOn_prod_mul hphi2 hpsi2
    refine hprod.congr_fun (fun p _ => ?_) (measurableSet_Ioi.prod measurableSet_Ioo)
    simp only [Work.FTS.PhiStar.RemSource]
    ring

end Work.FTS.PhiStar.Series.Weil
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.Defs =====
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

/-- **THE SECOND-ORDER `z`-CLASS DATA AT THE ORIGIN.**  The boundedness of the second `z`-derivative
of `g` on `(0,2] × Iθ × [0,S]` — the Taylor class condition `g = c(τ)z²Γ(θ)(1 + O(z))` of the
construction, in the form in which the `z`-modulus of `∂_zg̃` consumes it.  See the module
docstring for why it is *not* a consequence of `ℋ⁴`-membership. -/
structure StData2 (α S : ℝ) (g : Fam) : Prop where
  /-- `|∂_z²g| ≤ Q₂` for `0 < z ≤ 2`, uniformly in `(θ,τ) ∈ Iθ × [0,S]` -/
  quad2 : ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → z ≤ 2 →
    |Work.Spaces.pz (Work.Spaces.pz (gSlice g τ)) z θ| ≤ Q₂


/-! ## The joint regularity class used by the R5 constituents

The R5 constituents (`𝓛_Γ^T(g)(τ)`, `N₀`, `N`, `N_*`) need, for their `z`-differentiability, both the
*joint* regularity (the `Jet` of `FTS.Regularity`: a uniform bound **and** an α-Hölder modulus) and
the `z`-differentiability with a uniform bound — the value bounds are *not* implied by
differentiability alone (the review of `Der.zderiv_LGammaT` produced the witness
`g z θ τ = φ(τ)u(θ)` with `φ` unbounded).  `C1Jet` bundles exactly those two things. -/
def C1Jet (α S N : ℝ) (h : Fam) : Prop :=
  Jet α S N h ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
    ∃ d : ℝ, HasDerivAt (fun z' => h z' θ τ) d z ∧ |d| ≤ N

theorem C1Jet.jet {α S N : ℝ} {h : Fam} (H : C1Jet α S N h) : Jet α S N h := H.1

theorem C1Jet.zderiv {α S N : ℝ} {h : Fam} (H : C1Jet α S N h) :
    ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => h z' θ τ) d z ∧ |d| ≤ N := H.2

end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.L12fDensContInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-- **Continuity of the density in the radial variable.** -/
theorem continuousOn_L12dens_gSlice {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hJ : Work.FTS.Regularity.Jet α S N F) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.Regularity.gSlice F τ) s) (Set.Ioi 0) := by
  -- the numerator is `α`-Hölder (with the sharp constant `N·∫|K|`), hence continuous
  have hNc : (0 : ℝ) ≤ N * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|) :=
    mul_nonneg hJ.nonneg
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ => abs_nonneg _)
  have hT : ContinuousOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.K θ * F s θ τ) (Set.Ioi 0) :=
    continuousOn_of_holder hNc hα ((L12densAngIntegralHolder hα hJ.nonneg hJ) τ hτ)
  -- and the density is the numerator divided by `s ≠ 0`
  have hdiv : ContinuousOn (fun s : ℝ => (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.K θ * F s θ τ) / s) (Set.Ioi 0) :=
    hT.div continuousOn_id fun s hs => ne_of_gt hs
  refine hdiv.congr fun s hs => ?_
  rw [Work.FM.L12dens_eq (ne_of_gt hs)]
  simp only [Work.Spaces.Iθ, Work.FTS.Regularity.gSlice_apply]

theorem L12fDensContInt {α S N Kl Lf : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      |F z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → F z θ τ = 0) :
    ∀ τ ∈ Set.Icc 0 S,
      ContinuousOn (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
          (Work.FTS.Regularity.gSlice F τ) s) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
          (Work.FTS.Regularity.gSlice F τ) s) (Set.Ioi 0) := by
  intro τ hτ
  refine ⟨continuousOn_L12dens_gSlice hα hJ hτ, ?_⟩
  -- the two facts supplied by the sibling module `L12fDensBound`
  have hbd : ∀ s : ℝ, 0 < s → |Work.FM.L12dens Work.Spaces.K
      (Work.FTS.Regularity.gSlice F τ) s| ≤ 6 * max Kl N :=
    (L12fDensBound hJ hlin hsupp).1 τ hτ
  have hzv : ∀ s : ℝ, Lf ≤ s → Work.FM.L12dens Work.Spaces.K
      (Work.FTS.Regularity.gSlice F τ) s = 0 :=
    (L12fDensBound hJ hlin hsupp).2 τ hτ
  -- a continuous function on `(0,∞)` which is bounded there and vanishes past `Lf > 0` is `L¹`
  exact integrableOn_Ioi_of_bound_of_eventually_zero hsupp.1
    (continuousOn_L12dens_gSlice hα hJ hτ) hbd hzv

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.endpoint_cont =====
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

/-! ## Elementary `θ`-facts at the two endpoints -/




/-! ## Vanishing of a slice at both angular endpoints, from the boundary traces -/


/-! ## The target -/


end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.GalHyp =====
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

/-- **THE INPUT BUNDLE OF THE ASSEMBLY.**  See the module docstring for the provenance of each
group of fields. -/
structure GalHyp (α S : ℝ) (g : Fam) (m : ℝ → ℝ) (Vz Vθ cs : ℝ → ℝ → ℝ → ℝ)
    (a b c Lz7 M Lz Lθ Lt Nz Nθ Nt : ℝ) : Prop where
  /-- the Hölder exponent is positive -/
  hα : 0 < α
  /-- the paper's regime -/
  hα13 : α ≤ 1 / 3
  /-- the fake-time strip is nonempty -/
  hS : 0 < S
  /-- the lead's minimal Galerkin input (design `FTS_STRONG_ROUTE.md` §1/§4) -/
  hmin : RegPkgMin (pExp α) g
  /-- the modulation rate of design §2 is continuous near the strip -/
  hm : ContinuousOn m (Set.Ioo (-1 : ℝ) (S + 1))
  /-- `|m| ≤ 1/2` on the strip (design §2) -/
  hmb : ∀ τ : ℝ, τ ∈ Set.Ioo (-1 : ℝ) (S + 1) → |m τ| ≤ 1 / 2
  /-- `m` is `α`-Hölder on the strip (design §2, `muDyn_holderOn`) -/
  hmh : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |m τ - m τ'| ≤ L * |τ - τ'| ^ α
  /-- the `St1`-class data of `g̃` (the `Γ`-vanishing of `D_θg̃` with its `z²` factor, and the
  quadratic/linear vanishing at `z = 0`); *not* implied by `ℋ⁴`-membership, see
  `NOTES_RegPkgGal.md` §2 -/
  hSt : StData α S (extG g)
  /-- `C¹` on the open quadrant for every strip time (this is `RegPkgMin.c4` read as `C¹`) -/
  hsm1 : ∀ τ ∈ Set.Icc 0 S,
    ContDiffOn ℝ 1 (Function.uncurry (fun z θ => extG g z θ τ))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2)))
  /-- continuity of the angular slices at `θ = 0` -/
  hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
    Filter.Tendsto (fun θ => extG g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ)))
      (nhds (extG g z 0 τ))
  /-- continuity of the angular slices at `θ = π/2` -/
  hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
    Filter.Tendsto (fun θ => extG g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds (extG g z (Real.pi / 2) τ))
  /-- the far-field `Γ`-bound (`g̃ = -F_*` for `z ≥ L`); supplied by the compact support of the
  localised profile together with the explicit bound `F_* ≤ (2 pExp α/c)Γ` -/
  hfar : ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Cf ≤ z →
    θ ∈ Work.Spaces.Iθ → |extG g z θ τ| ≤ Cf * Gamma α θ
  /-- sup bounds for the profile and its `z`-derivative (the data `R3c.jet_g` consumes).
  **There is deliberately no bound on `pth (·) = ∂_θg`**: together with the compact support it
  would be unsatisfiable (`g = -F_*` at `z = L` has `∂_θg ~ θ^{α-1}`; machine-checked as
  `R5c.no_data`).  The bounded angular quantity is `D_θg` — see `NOTES_RegPkgGal.md` §6. -/
  hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
    |extG g z θ τ| ≤ M ∧ |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ| ≤ M
  /-- the `z`-modulus of `g̃` (`α`-Hölder, `R3d`) -/
  hhz : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ,
    |extG g z θ τ - extG g z' θ τ| ≤ Lz * |z - z'| ^ α
  /-- the `θ`-modulus of `g̃` (`α`-Hölder, `R3d`; *not* Lipschitz: the profile is `Γ`-shaped, so
  a uniform Lipschitz modulus in `θ` is unsatisfiable — see `NOTES_RegPkgGal.md` §8) -/
  hhθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
    ∀ θ' ∈ Work.Spaces.Iθ, |extG g z θ τ - extG g z θ' τ| ≤ Lθ * |θ - θ'| ^ α
  /-- the `τ`-modulus of `g̃` (`α`-Hölder, `R3d`) -/
  hhτ : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
    ∀ θ ∈ Work.Spaces.Iθ, |extG g z θ τ - extG g z θ τ'| ≤ Lt * |τ - τ'| ^ α
  /-- the `z`-modulus of `∂_zg̃` (`α`-Hölder, `R3d`) -/
  hhzp : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => extG g z θ τ) z' θ| ≤ Nz * |z - z'| ^ α
  /-- the `θ`-modulus of `∂_zg̃` (`α`-Hölder, `R3d`) -/
  hhθp : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
    ∀ θ' ∈ Work.Spaces.Iθ,
    |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => extG g z θ τ) z θ'| ≤ Nθ * |θ - θ'| ^ α
  /-- the `τ`-modulus of `∂_zg̃` (`α`-Hölder, `R3d`) -/
  hhτp : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
    ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => extG g z θ τ') z θ| ≤ Nt * |τ - τ'| ^ α
  /-- R1's joint `C¹` hypothesis on `{z > 0}` -/
  hbase : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)))
  /-- R1: the joint limit `(z,τ) → (0,τ₀)` of `g` -/
  hj0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => g p.1 θ p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `z⁻¹g` -/
  hjz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * g p.1 θ p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `∂_zg` -/
  hjdz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => g z θ p.2) p.1)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `∂_τg` -/
  hjdt : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => g p.1 θ s) p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: `C¹` of `z ↦ ∂_τg(z,θ,0)` on `{z > 0}` -/
  hd1 : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => deriv (fun s => g q.1 θ s) 0)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)))
  /-- R1: the joint limit of `∂_z(∂_τg(·,θ,0))` -/
  hd1z : ∀ θ ∈ Work.Spaces.Iθ,
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => g z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `z⁻¹∂_τg(z,θ,0)` -/
  hd1z2 : ∀ θ ∈ Work.Spaces.Iθ,
    Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: right continuity of `τ ↦ ∂_τg` at `τ = 0` -/
  ht0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
    Filter.Tendsto (fun τ => deriv (fun s => g z θ s) τ)
      (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => g z θ s) 0))
  /-- R7: joint `C¹` of the full profile `F = F_* + g̃` on the slab -/
  hFjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => profFull α (extG g) p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: joint continuity of the transport velocity on the closed angular box -/
  hVjoint : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: a `τ`-uniform Lipschitz constant for the velocity, required only on `z > Lz7` (design
  item R-a: the backward characteristics stay above `Lz7`, so the Lipschitz control is needed only
  there; `R7e.support_strip_zL`) -/
  hVlipU : ∃ K : NNReal, ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
    (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
    (Set.prod (Set.Ioi Lz7) (Set.Ioo (0:ℝ) (Real.pi / 2)))
  /-- R7: continuity of the source coefficient -/
  hcscont : ContinuousOn (fun p : ℝ × ℝ × ℝ => cs p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: the transport equation `(E)` in the characteristic form `∂_τF = -(Vz·D_zF + Vθ·∂_θF + cs·F)` -/
  hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
    HasDerivAt (fun s => profFull α (extG g) z θ s)
      (-(Vz z θ τ * Work.Spaces.Dz (fun z θ => profFull α (extG g) z θ τ) z θ
        + Vθ z θ τ * Work.Spaces.pth (fun z θ => profFull α (extG g) z θ τ) z θ
        + cs z θ τ * profFull α (extG g) z θ τ)) τ
  /-- R7: non-negativity of the `z`-speed -/
  hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ
  /-- R7: the `z`-speed bound -/
  hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a
  /-- R7: the `θ`-speed bound -/
  hVθb : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ b
  /-- R7: the `θ`-speed vanishes at `θ = 0` -/
  hVθ0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0
  /-- R7: the `θ`-speed vanishes at `θ = π/2` -/
  hVθπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0
  /-- R7: the source coefficient is bounded -/
  hcsc : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |cs z θ τ| ≤ c
  /-- R7: the initial support of the profile (the localised datum) -/
  hInit : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < Real.pi / 2 →
    profFull α (extG g) z θ 0 = 0
  /-- the profile vanishes for `z ≥ L` at the angles *outside* `Iθ` — the field `RegPkg'.hsupp`
  quantifies over all `θ`, and only `θ ∈ Iθ` is seen by the physical reconstruction; outside that
  range the profile is not constrained by the localised construction -/
  hsuppOut : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z →
    θ ∉ Work.Spaces.Iθ → profFull α (extG g) z θ τ = 0
  /-- R7: the support threshold is non-negative -/
  hLz7 : 0 ≤ Lz7
  /-- R7: the `z`-speed bound is non-negative -/
  ha : 0 ≤ a
  /-- R7: the `θ`-speed bound is non-negative -/
  hb : 0 ≤ b
  /-- R7: the source bound is non-negative -/
  hc : 0 ≤ c
  /-- R3b: the sup constant is non-negative -/
  hMn : 0 ≤ M
  /-- R3b: the `z`-modulus constant of `g̃` -/
  hLzn : 0 ≤ Lz
  /-- R3b: the `θ`-modulus constant of `g̃` -/
  hLθn : 0 ≤ Lθ
  /-- R3b: the `τ`-modulus constant of `g̃` -/
  hLtn : 0 ≤ Lt
  /-- R3b: the `z`-modulus constant of `∂_zg̃` -/
  hNzn : 0 ≤ Nz
  /-- R3b: the `θ`-modulus constant of `∂_zg̃` -/
  hNθn : 0 ≤ Nθ
  /-- R3b: the `τ`-modulus constant of `∂_zg̃` -/
  hNtn : 0 ≤ Nt
end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R1 =====
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

/-- A function that vanishes on `(-∞,0]` has derivative `0` at `0`: if it is differentiable there
the two-sided derivative is the left one (which is `0`), and otherwise `deriv` is the junk value
`0`. -/
lemma deriv_zero_of_eq_zero_on_nonpos {f : ℝ → ℝ} (h : ∀ z : ℝ, z ≤ 0 → f z = 0) :
    deriv f 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ f 0
  · have h1 : HasDerivWithinAt f (deriv f 0) (Set.Iic 0) 0 := hd.hasDerivAt.hasDerivWithinAt
    have h2 : HasDerivWithinAt f 0 (Set.Iic 0) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Set.Iic 0) 0).congr (fun y hy => h y hy) (h 0 le_rfl)
    exact UniqueDiffWithinAt.eq_deriv (Set.Iic 0) (uniqueDiffWithinAt_Iic 0) h1 h2
  · exact deriv_zero_of_not_differentiableAt hd

/-- **R1 (axis clauses).**  The extension vanishes at `z = 0`, for every `θ`, `τ`: this is the
`z ≤ 0` branch of `extG`, and it needs nothing about `g`. -/
theorem extG_hquad0 (g : Fam) (τ θ : ℝ) : extG g 0 θ τ = 0 := extG_of_nonpos (le_refl 0)

/-- **R1 (axis clauses).**  The `z`-derivative of the extended slice vanishes at `z = 0`: the
slice of the extension is `0` on `(-∞,0]`, so its derivative at `0` is `0`. -/
theorem extG_hquad (g : Fam) (τ θ : ℝ) :
    Work.Spaces.pz (fun z θ => extG g z θ τ) 0 θ = 0 := by
  refine deriv_zero_of_eq_zero_on_nonpos (fun z hz => ?_)
  exact extG_of_nonpos hz

/-- **R1 (`hvt`).**  The extended slice vanishes on the two angular boundary lines as soon as the
original one does: on the left half-plane it is `0` by definition, and at `z > 0` and `τ ≥ 0` it
is `g`. -/
theorem extG_hvt {S : ℝ} {g : Fam}
    (hvan : ∀ τ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (fun z θ => extG g z θ τ) := by
  intro τ hτ
  constructor
  · intro z
    show extG g z 0 τ = 0
    by_cases hz : z ≤ 0
    · exact extG_of_nonpos hz
    · rw [extG_of_pos (lt_of_not_ge hz) hτ.1]
      exact (hvan τ hτ.1 z (le_of_lt (lt_of_not_ge hz))).1
  · intro z
    show extG g z (π / 2) τ = 0
    by_cases hz : z ≤ 0
    · exact extG_of_nonpos hz
    · rw [extG_of_pos (lt_of_not_ge hz) hτ.1]
      exact (hvan τ hτ.1 z (le_of_lt (lt_of_not_ge hz))).2

end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R2c.tay_clauses =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R2c

/-!
# `R2c`: the Taylor clauses with the two angular endpoint *limits* as hypotheses

This file proves `tay_clauses` in the `R2c` shape: instead of the (too strong) smoothness
hypothesis on a neighbourhood of the closed angular range (`R2b`), or the (too strong)
hypothesis that the angular slices are *continuous* on `Iθ` (`R2.tay_clauses_of_continuous`),
the two endpoint conditions are supplied as one-sided *limits*:

* `hcont0`  : `θ ↦ g z θ τ → g z 0 τ` as `θ → 0⁺`,
* `hcontπ` : `θ ↦ g z θ τ → g z (π/2) τ` as `θ → (π/2)⁻`.

Together with the joint `C¹` hypothesis `hsm` on the *open* quadrant these say exactly that
every angular slice `θ ↦ g z θ τ` is continuous on the closed interval `Iθ = [0, π/2]`
(for `z > 0`), which is the minimal repair identified by the counterexample
`Work.FTS.RegPkgGal.R2.tay_clauses_refuted` (a jump of the slice at an angular endpoint is
invisible to `D_θ` and to `VanishTheta`).  The conclusion is then the proved
`Work.FTS.RegPkgGal.R2.tay_clauses_of_continuous`.
-/

/-- **Continuity of an angular slice on the closed interval.**

From the joint `C¹` hypothesis on the open quadrant (which gives continuity at every interior
point of the slice) and the two one-sided endpoint limits, the slice is continuous on
`Iθ = [0, π/2]`. -/
private lemma slice_continuousOn {g : ℝ → ℝ → ℝ → ℝ} {τ z : ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g z 0 τ)))
    (hπ : Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds (g z (Real.pi / 2) τ))) :
    ContinuousOn (fun θ => g z θ τ) Work.Spaces.Iθ := by
  have hIoo : ContinuousOn (fun θ : ℝ => g z θ τ) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h2 := hsm.continuousOn.comp h1 (fun θ hθ => ⟨hz, hθ⟩)
    simpa [Function.comp_def, Function.uncurry] using h2
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | rfl
  · rcases lt_or_eq_of_le hx.2 with hxπ | rfl
    · exact (hIoo.continuousAt (isOpen_Ioo.mem_nhds ⟨hx0, hxπ⟩)).continuousWithinAt
    · refine ContinuousWithinAt.mono (ContinuousWithinAt.insert hπ) (fun y hy => ?_)
      rcases lt_or_eq_of_le hy.2 with h | h
      · exact Or.inr h
      · exact Or.inl h
  · refine ContinuousWithinAt.mono (ContinuousWithinAt.insert h0) (fun y hy => ?_)
    rcases lt_or_eq_of_le hy.1 with h | h
    · exact Or.inr h
    · exact Or.inl h.symm

theorem tay_clauses {α S Cθ K Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hCθ : 0 ≤ Cθ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g z 0 τ)))
    (hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (g z (Real.pi / 2) τ)))
    (hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0)
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |g z θ τ| ≤ K * z ^ 2)
    (hlinz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K' * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K' * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K' * z ^ 2 * |θ - θ'| ^ α) := by
  refine Work.FTS.RegPkgGal.R2.tay_clauses_of_continuous hα hα1 hS hCθ hK hQ hsm hd hvt
    hquad hlinz ?_
  intro τ hτ z hz hz2
  exact slice_continuousOn (hsm τ hτ) hz (hcont0 τ hτ z (le_of_lt hz))
    (hcontπ τ hτ z (le_of_lt hz))

end Work.FTS.RegPkgGal.R2c
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R3d.jet_g =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R3d

/-! ## The `α`-Hölder upgrade to a `Jet`

`Work.FTS.Regularity.Jet α S N h` bundles a *uniform bound* by `N` on the domain
`z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` together with a *joint* `α`-Hölder modulus for the metric
`|Δz| + |Δθ| + |Δτ|`, again with the constant `N`.  The data available in the `R3d` hypotheses are
*one-variable* `α`-Hölder bounds in `z`, `θ`, `τ` (with constants `Lz`, `Lθ`, `Lt`) plus
pointwise bounds by `M`.  The two lemmas below perform the (elementary) upgrade.  Since all three
moduli carry the **same** exponent `α`, the passage to the sum metric is a direct application of
`Real.rpow_le_rpow` (`|Δz| ≤ d` and `0 ≤ α` give `|Δz|^α ≤ d^α`): no `d ≤ 1` / `d ≥ 1`
dichotomy is needed, unlike in the Lipschitz-to-Hölder upgrade `R3b.jet_of_bounded_lipschitz`
(where `Lz * |Δz|` has to be compared with `d^α`, forcing a case split and paying `2M`). -/

/-- `|a + b + c| ≤ |a| + |b| + |c|`. -/
theorem abs_add_three_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := by linarith [abs_add_le a b]
    _ = |a| + |b| + |c| := by ring

/-- **The `α`-Hölder-to-`Jet` upgrade.**  A family `h` bounded by `M` on
`[0,∞) × Iθ × [0,S]`, `α`-Hölder in each of the three variables at fixed values of the other
variables (same exponent `α`, constants `Lz, Lθ, Lt`), is a `Jet` with the constant
`Lz + Lθ + Lt + M`. -/
theorem jet_of_bounded_holder {α S M Lz Lθ Lt : ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (hLz : 0 ≤ Lz) (hLθ : 0 ≤ Lθ) (hLt : 0 ≤ Lt)
    {h : ℝ → ℝ → ℝ → ℝ}
    (hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |h z θ τ| ≤ M)
    (hhz : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ,
      |h z θ τ - h z' θ τ| ≤ Lz * |z - z'| ^ α)
    (hhθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      ∀ θ' ∈ Work.Spaces.Iθ, |h z θ τ - h z θ' τ| ≤ Lθ * |θ - θ'| ^ α)
    (hhτ : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, |h z θ τ - h z θ τ'| ≤ Lt * |τ - τ'| ^ α) :
    ∃ N : ℝ, Work.FTS.Regularity.Jet α S N h := by
  refine ⟨Lz + Lθ + Lt + M, by linarith, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    have h1 := hsup τ hτ z θ hz hθ
    linarith
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := hhz τ hτ z z' hz hz' θ hθ
    have h2 := hhθ τ hτ z' hz' θ hθ θ' hθ'
    have h3 := hhτ τ hτ τ' hτ' z' hz' θ' hθ'
    have htri : |h z θ τ - h z' θ' τ'|
        ≤ |h z θ τ - h z' θ τ| + |h z' θ τ - h z' θ' τ| + |h z' θ' τ - h z' θ' τ'| := by
      have e : h z θ τ - h z' θ' τ'
          = (h z θ τ - h z' θ τ) + (h z' θ τ - h z' θ' τ)
            + (h z' θ' τ - h z' θ' τ') := by ring
      rw [e]
      exact abs_add_three_le _ _ _
    have hkey : |h z θ τ - h z' θ' τ'|
        ≤ Lz * |z - z'| ^ α + Lθ * |θ - θ'| ^ α + Lt * |τ - τ'| ^ α := by linarith
    have hd0 : (0 : ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by
      linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]
    have hrp : (0 : ℝ) ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := Real.rpow_nonneg hd0 α
    have hAz : |z - z'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by linarith [abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]) hα.le
    have hAθ : |θ - θ'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by linarith [abs_nonneg (z - z'), abs_nonneg (τ - τ')]) hα.le
    have hAτ : |τ - τ'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ')]) hα.le
    have hstep : Lz * |z - z'| ^ α + Lθ * |θ - θ'| ^ α + Lt * |τ - τ'| ^ α
        ≤ (Lz + Lθ + Lt + M) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
      have hz' := mul_le_mul_of_nonneg_left hAz hLz
      have hθ' := mul_le_mul_of_nonneg_left hAθ hLθ
      have hτ' := mul_le_mul_of_nonneg_left hAτ hLt
      nlinarith [mul_nonneg hM hrp]
    linarith

theorem jet_g {α S M Lz Lθ Lt Nz Nθ Nt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hM : 0 ≤ M) (hLz : 0 ≤ Lz) (hLθ : 0 ≤ Lθ) (hLt : 0 ≤ Lt)
    (hNz : 0 ≤ Nz) (hNθ : 0 ≤ Nθ) (hNt : 0 ≤ Nt)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ M ∧ |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M)
    (hhz : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      ∀ θ ∈ Work.Spaces.Iθ, |g z θ τ - g z' θ τ| ≤ Lz * |z - z'| ^ α)
    (hhθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      ∀ θ' ∈ Work.Spaces.Iθ, |g z θ τ - g z θ' τ| ≤ Lθ * |θ - θ'| ^ α)
    (hhτ : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, |g z θ τ - g z θ τ'| ≤ Lt * |τ - τ'| ^ α)
    (hhzp : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ
        - Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z' θ| ≤ Nz * |z - z'| ^ α)
    (hhθp : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ
        - Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ'| ≤ Nθ * |θ - θ'| ^ α)
    (hhτp : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ
        - Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Nt * |τ - τ'| ^ α) :
    (∃ N : ℝ, Work.FTS.Regularity.Jet α S N g) ∧
    (∃ N : ℝ, Work.FTS.Regularity.Jet α S N
      (fun z θ τ => Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ)) := by
  refine ⟨?_, ?_⟩
  · exact jet_of_bounded_holder hα hM hLz hLθ hLt
      (fun τ hτ z θ hz hθ => (hsup τ hτ z θ hz hθ).1) hhz hhθ hhτ
  · exact jet_of_bounded_holder hα hM hNz hNθ hNt
      (fun τ hτ z θ hz hθ => (hsup τ hτ z θ hz hθ).2) hhzp hhθp hhτp

end Work.FTS.RegPkgGal.R3d
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R4b.van_of_dthvan =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R4b

set_option autoImplicit false

/-! ## The slice calculus -/

/-- **The `θ`-derivative of a slice.**  If `G` is `C¹` on a product `s ×ˢ t` of open sets, then at
every point `(z,θ) ∈ s ×ˢ t` the angular slice `fun θ' => G z θ'` has derivative
`Work.Spaces.pth G z θ` at `θ` (which is how `pth` is defined, but here the differentiability
comes from the *uncurried* smoothness hypothesis). -/
theorem hasDerivAt_sliceTh {G : ℝ → ℝ → ℝ} {s t : Set ℝ} (hs : IsOpen s) (ht : IsOpen t)
    (h : ContDiffOn ℝ 1 (Function.uncurry G) (s ×ˢ t)) {z θ : ℝ} (hz : z ∈ s) (hθ : θ ∈ t) :
    HasDerivAt (fun θ' => G z θ') (Work.Spaces.pth G z θ) θ := by
  have hp : (z, θ) ∈ s ×ˢ t := ⟨hz, hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
    ((h.differentiableOn (by norm_num)).differentiableAt ((hs.prod ht).mem_nhds hp))
  have hcurve : HasDerivAt (fun x : ℝ => (z, x)) (0, 1) θ := by
    simpa using (hasDerivAt_const (x := θ) z).prodMk (hasDerivAt_id θ)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt θ hcurve
  rw [Work.Spaces.pth_eq_fderiv hd]
  simpa [Function.comp_def] using hcomp

/-- **FTC for a slice, with a majorant.**  If `G` is `C¹` on the product `s ×ˢ t` of open sets,
`z ∈ s`, `a ≤ b`, `[a,b] ⊆ t`, and `maj` is interval integrable on `[a,b]` and dominates the
norm of the slice derivative almost everywhere on `(a,b]`, then

  `|G z b - G z a| ≤ ∫_a^b maj`.

The derivative is only evaluated on the *open* interval (which is why the a.e. hypothesis
suffices), so this lemma is insensitive to the singularities of `maj` at the endpoints. -/
lemma slice_ftc_abs_le {G : ℝ → ℝ → ℝ} {s t : Set ℝ} (hs : IsOpen s) (ht : IsOpen t)
    (h : ContDiffOn ℝ 1 (Function.uncurry G) (s ×ˢ t))
    {z a b : ℝ} (hz : z ∈ s) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ t)
    {maj : ℝ → ℝ} (hmaj_int : IntervalIntegrable maj volume a b)
    (hmaj : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), ‖deriv (fun θ => G z θ) x‖ ≤ maj x) :
    |G z b - G z a| ≤ ∫ x in a..b, maj x := by
  have hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ (fun θ => G z θ) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hasDerivAt_sliceTh hs ht h hz (hsub hx)).differentiableAt
  have hint : IntervalIntegrable (deriv (fun θ => G z θ)) volume a b := by
    refine IntervalIntegrable.mono_fun' hmaj_int ?_ ?_
    · exact (measurable_deriv _).aestronglyMeasurable
    · change ∀ᵐ x ∂(volume.restrict (Set.uIoc a b)), ‖deriv (fun θ => G z θ) x‖ ≤ maj x
      rw [Set.uIoc_of_le hab]
      exact hmaj
  have hftc : ∫ x in a..b, deriv (fun θ => G z θ) x = G z b - G z a :=
    intervalIntegral.integral_deriv_eq_sub hdiff hint
  have hle : ∫ x in a..b, ‖deriv (fun θ => G z θ) x‖ ≤ ∫ x in a..b, maj x := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint).norm
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hmaj_int
    · exact hmaj
  have hnorm : |∫ x in a..b, deriv (fun θ => G z θ) x| ≤ ∫ x in a..b, ‖deriv (fun θ => G z θ) x‖ := by
    simpa [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (f := fun x => deriv (fun θ => G z θ) x) hab
  calc |G z b - G z a| = |∫ x in a..b, deriv (fun θ => G z θ) x| := by rw [hftc]
    _ ≤ ∫ x in a..b, ‖deriv (fun θ => G z θ) x‖ := hnorm
    _ ≤ ∫ x in a..b, maj x := hle

/-! ## The pointwise majorants of the derivative -/

/-- The left majorant: `|∂_θg| ≤ Cθ·z²·Γ/sin(2·) ≤ Cθ·z²·M·t^{α-1}` on `(0,π/4]`. -/
lemma pth_le_majorant {α Cθ M : ℝ} (hCθ : 0 ≤ Cθ) {g : ℝ → ℝ → ℝ → ℝ} {τ : ℝ}
    (hdτ : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hM : ∀ t : ℝ, 0 < t → t ≤ Real.pi / 4 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ M * t ^ (α - 1))
    {z x : ℝ} (hz : 0 ≤ z) (hx : 0 < x) (hxle : x ≤ Real.pi / 4) :
    |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| ≤ Cθ * z ^ 2 * M * x ^ (α - 1) := by
  have hxI : x ∈ Work.Spaces.Iθ := ⟨le_of_lt hx, by linarith [Real.pi_pos]⟩
  have hsin : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have h1 := hdτ z x hz hxI
  rw [Work.Spaces.Dth, abs_mul, abs_of_pos hsin] at h1
  have hMs : Work.FTS.Regularity.Gamma α x ≤ M * x ^ (α - 1) * Real.sin (2 * x) := by
    have h := hM x hx hxle
    rw [div_le_iff₀ hsin] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hkey : |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| * Real.sin (2 * x)
      ≤ (Cθ * z ^ 2 * M * x ^ (α - 1)) * Real.sin (2 * x) := by
    calc |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| * Real.sin (2 * x)
        = Real.sin (2 * x) * |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| := by ring
      _ ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α x := h1
      _ ≤ Cθ * z ^ 2 * (M * x ^ (α - 1) * Real.sin (2 * x)) :=
            mul_le_mul_of_nonneg_left hMs (by positivity)
      _ = (Cθ * z ^ 2 * M * x ^ (α - 1)) * Real.sin (2 * x) := by ring
  exact le_of_mul_le_mul_right hkey hsin

/-- The right majorant: `|∂_θg| ≤ Cθ·z²·N·(π/2-t)^{2α-1}` on `[π/4,π/2)`. -/
lemma pth_le_majorant_right {α Cθ N : ℝ} (hCθ : 0 ≤ Cθ) {g : ℝ → ℝ → ℝ → ℝ} {τ : ℝ}
    (hdτ : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hN : ∀ t : ℝ, Real.pi / 4 ≤ t → t < Real.pi / 2 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ N * (Real.pi / 2 - t) ^ (2 * α - 1))
    {z x : ℝ} (hz : 0 ≤ z) (hx : Real.pi / 4 ≤ x) (hxlt : x < Real.pi / 2) :
    |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x|
      ≤ Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
  have hx0 : 0 < x := by linarith [Real.pi_pos]
  have hxI : x ∈ Work.Spaces.Iθ := ⟨le_of_lt hx0, le_of_lt hxlt⟩
  have hsin : 0 < Real.sin (2 * x) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h1 := hdτ z x hz hxI
  rw [Work.Spaces.Dth, abs_mul, abs_of_pos hsin] at h1
  have hNs : Work.FTS.Regularity.Gamma α x
      ≤ N * (Real.pi / 2 - x) ^ (2 * α - 1) * Real.sin (2 * x) := by
    have h := hN x hx hxlt
    rw [div_le_iff₀ hsin] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hkey : |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| * Real.sin (2 * x)
      ≤ (Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)) * Real.sin (2 * x) := by
    calc |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| * Real.sin (2 * x)
        = Real.sin (2 * x) * |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| := by ring
      _ ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α x := h1
      _ ≤ Cθ * z ^ 2 * (N * (Real.pi / 2 - x) ^ (2 * α - 1) * Real.sin (2 * x)) :=
            mul_le_mul_of_nonneg_left hNs (by positivity)
      _ = (Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)) * Real.sin (2 * x) := by ring
  exact le_of_mul_le_mul_right hkey hsin

/-! ## The two lower bounds for `Γ` -/

/-- `Γ(θ) ≥ (1/π)^α θ^α` on `[0,π/4]`: `Γ = sin^α·cos^{2α}` with `sinθ ≥ (2/π)θ` and
`cosθ ≥ √2/2`. -/
lemma Gamma_left_lb {α θ : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθle : θ ≤ Real.pi / 4) :
    (1 / Real.pi) ^ α * θ ^ α ≤ Work.FTS.Regularity.Gamma α θ := by
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
  have hcos2 : (0:ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hθ0
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hθle
    rwa [Real.cos_pi_div_four] at h
  have hcossq : (1/2 : ℝ) ≤ Real.cos θ ^ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hcos]
  have e1 : ((2 / Real.pi) * θ) ^ α ≤ Real.sin θ ^ α :=
    Real.rpow_le_rpow (by positivity) (Real.mul_le_sin hθ0 (by linarith [Real.pi_pos]))
      (le_of_lt hα)
  have e2 : ((1/2 : ℝ)) ^ α ≤ (Real.cos θ ^ 2) ^ α :=
    Real.rpow_le_rpow (by norm_num) hcossq (le_of_lt hα)
  have hmul := mul_le_mul e1 e2 (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg hsin0 α)
  have hEq : (1 / Real.pi) ^ α * θ ^ α = (2 / Real.pi * θ) ^ α * (1/2 : ℝ) ^ α := by
    have A : (1 / Real.pi) ^ α * θ ^ α = ((1 / Real.pi) * θ) ^ α :=
      (Real.mul_rpow (by positivity) hθ0).symm
    have B : (2 / Real.pi * θ) ^ α * (1/2 : ℝ) ^ α = ((2 / Real.pi * θ) * (1/2)) ^ α :=
      (Real.mul_rpow (by positivity) (by norm_num)).symm
    rw [A, B]
    congr 1
    ring
  rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, Real.mul_rpow hsin0 hcos2, hEq]
  exact hmul

/-- `Γ(θ) ≥ c₂·(π/2-θ)^{2α}` on `[π/4,π/2]`, `c₂ = (√2/2·(2/π)²)^α`: with `σ = π/2-θ` one has
`Γ(π/2-σ) = (cosσ·sin²σ)^α` and `cosσ ≥ √2/2`, `sinσ ≥ (2/π)σ`. -/
lemma Gamma_right_lb {α σ : ℝ} (hα : 0 < α) (hσ0 : 0 ≤ σ) (hσle : σ ≤ Real.pi / 4) :
    ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α * σ ^ (2 * α)
      ≤ Work.FTS.Regularity.Gamma α (Real.pi / 2 - σ) := by
  have hsinσ0 : 0 ≤ Real.sin σ := Real.sin_nonneg_of_mem_Icc ⟨hσ0, by linarith [Real.pi_pos]⟩
  have hb0 : 0 ≤ (2 / Real.pi) * σ := by positivity
  have hc : (2 / Real.pi) * σ ≤ Real.sin σ := Real.mul_le_sin hσ0 (by linarith [Real.pi_pos])
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos σ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hσ0
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hσle
    rwa [Real.cos_pi_div_four] at h
  have hcos0 : (0:ℝ) ≤ Real.cos σ :=
    le_trans (div_nonneg (Real.sqrt_nonneg 2) (by norm_num)) hcos
  have hsq : ((2 / Real.pi) * σ) ^ 2 ≤ Real.sin σ ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hb0 hc
  have hc3 : (0:ℝ) ≤ (Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2 :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg 2) (by norm_num)) (sq_nonneg _)
  have hbase : ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) * σ ^ 2
      ≤ Real.cos σ * Real.sin σ ^ 2 := by
    have h1 : ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) * σ ^ 2
        = (Real.sqrt 2 / 2) * ((2 / Real.pi) * σ) ^ 2 := by ring
    rw [h1]
    exact mul_le_mul hcos hsq (sq_nonneg _) hcos0
  have hEq : (((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) * σ ^ 2) ^ α
      = ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α * σ ^ (2 * α) := by
    rw [Real.mul_rpow hc3 (sq_nonneg σ), ← Real.rpow_natCast σ 2, ← Real.rpow_mul hσ0]
    norm_num
  have h := Real.rpow_le_rpow (mul_nonneg hc3 (sq_nonneg σ)) hbase (le_of_lt hα)
  rw [show (Real.cos σ * Real.sin σ ^ 2) ^ α = Work.FTS.Regularity.Gamma α (Real.pi / 2 - σ) from by
      rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, Real.sin_pi_div_two_sub,
          Real.cos_pi_div_two_sub]] at h
  rwa [hEq] at h

/-! ## The target lemma -/


end Work.FTS.RegPkgGal.R4b
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R5.dtg_eq_rhs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.R5.dtg_eq_rhs` — the pointwise identification `∂_τ g̃ = dynLin + dynRHS`

`extG g` extends the family `g` to negative fake time by the *first-order Taylor jet* of
`s ↦ g z θ s` at `s = 0`:

`extG g z θ s = 0` for `z ≤ 0`; `= g z θ 0 + s·∂_τg(z,θ,0)` for `s < 0`; `= g z θ s` otherwise.

For `z > 0` and `τ ≥ 0` we therefore have `extG g z θ τ = g z θ τ`, and the derivative of
`s ↦ extG g z θ s` is the derivative of `s ↦ g z θ s`:

* at `τ > 0` this is immediate, because `Ioi 0` is a neighbourhood of `τ` (the two functions
  agree there), and the equation is only needed on `Ici 0` (its `HasDerivWithinAt` form, which
  converts to `HasDerivAt` at any `τ > 0`);
* at `τ = 0` the negative branch of `extG` is *exactly* the linearisation of `g` at `0`, so the
  left difference quotients of `g̃` and those of `g` agree, and the two one-sided derivatives glue
  (`HasDerivWithinAt.union` on `Iic 0 ∪ Ici 0 = univ`).  This is where the hypothesis
  `h0` — the *two-sided* derivative of `τ ↦ g z θ τ` at `0` — is consumed.

Notably no use is made of the regularity package `hmin`: the two ingredients that carry the
derivative are the equation `hsol.2` (on `Ici 0`) and `h0` (the two-sided derivative at `0`).
-/

namespace Work.FTS.RegPkgGal.R5

open Set Filter Topology

/-- **The derivative of `g̃` at `τ = 0`.**  If `G = s ↦ g z θ s` has a two-sided derivative `c` at
`0` and `0 < z`, then so does `s ↦ extG g z θ s`: on `Iic 0` the extension is *identically* the
affine function `s ↦ g z θ 0 + s·c` (the negative branch being the Taylor jet, and at `s = 0` the
branch test `s < 0` fails with the same value), while on `Ici 0` it *is* `G`; the two one-sided
derivatives therefore coincide and glue over `Iic 0 ∪ Ici 0 = univ`. -/
theorem hasDerivAt_extG_of_zero {g : ℝ → ℝ → ℝ → ℝ} {z θ c : ℝ} (hz : 0 < z)
    (h : HasDerivAt (fun s => g z θ s) c 0) :
    HasDerivAt (fun s => extG g z θ s) c 0 := by
  have hderiv : deriv (fun s => g z θ s) 0 = c := h.deriv
  -- pointwise description of the extension at `z > 0`
  have hpt : ∀ s : ℝ, extG g z θ s = if s < 0 then g z θ 0 + s * c else g z θ s := by
    intro s
    by_cases hs : s < 0
    · rw [extG_of_neg hz hs, hderiv, if_pos hs]
    · rw [extG_of_pos hz (not_lt.mp hs), if_neg hs]
  -- the right piece: `extG` agrees with `g` on `Ici 0`
  have hR : HasDerivWithinAt (fun s => extG g z θ s) c (Set.Ici 0) 0 :=
    (h.hasDerivWithinAt (s := Set.Ici 0)).congr
      (fun y hy => extG_of_pos hz hy)
      (extG_of_pos hz le_rfl)
  -- the left piece: `extG` is the affine jet on `Iic 0`
  have hA : HasDerivAt (fun s : ℝ => g z θ 0 + s * c) c 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s * c) (1 * c) 0 := (hasDerivAt_id (0 : ℝ)).mul_const c
    have h2 : HasDerivAt (fun s : ℝ => s * c) c 0 := by simpa using h1
    simpa using h2.const_add (g z θ 0)
  have hL : HasDerivWithinAt (fun s => extG g z θ s) c (Set.Iic 0) 0 :=
    hA.hasDerivWithinAt.congr
      (fun y hy => by
        rw [hpt y]
        by_cases hy' : y < 0
        · rw [if_pos hy']
        · rw [if_neg hy']
          have hy0 : y = 0 := le_antisymm hy (not_lt.mp hy')
          subst hy0
          simp)
      (by rw [hpt 0, if_neg (not_lt.mpr le_rfl)]; simp)
  have hU : HasDerivWithinAt (fun s => extG g z θ s) c (Set.Iic 0 ∪ Set.Ici 0) 0 := hL.union hR
  rw [Set.Iic_union_Ici] at hU
  exact hasDerivWithinAt_univ.mp hU

/-- **The derivative of `g̃` at `τ > 0`.**  For `z > 0` and `τ > 0` the extension agrees with `g`
on the neighbourhood `Ioi 0` of `τ`, so the two functions have the same derivative there. -/
theorem hasDerivAt_extG_of_pos {g : ℝ → ℝ → ℝ → ℝ} {z θ τ c : ℝ} (hz : 0 < z) (hτ : 0 < τ)
    (h : HasDerivAt (fun s => g z θ s) c τ) :
    HasDerivAt (fun s => extG g z θ s) c τ :=
  h.congr_of_eventuallyEq <| by
    filter_upwards [Ioi_mem_nhds hτ] with s hs
    exact extG_of_pos hz hs.le


end Work.FTS.RegPkgGal.R5
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R5Slot =====
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

/-- **THE R5 INPUT**: the a-priori regularity of the right-hand side of the fake-time equation,
together with its boundary values. -/
structure R5Slot (α S : ℝ) (g Φ : Fam) (N0 : ℝ) : Prop where
  /-- the dynamic equation (`IsDynEqOn`, the one-sided-in-`τ` form produced by Open2) -/
  hsol : Work.FTS.Galerkin.IsDynEqOn (pExp α) Φ g
  /-- the two-sided `τ = 0` equation, which glues the extension at `τ = 0` -/
  h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
    HasDerivAt (fun s => g z θ s)
      (Work.FTS.Galerkin.dynLin (pExp α) g 0 z θ
        + Work.FTS.Galerkin.dynRHS (pExp α) Φ g 0 z θ) 0
  /-- the right-hand side is a `Jet` on the closed quadrant -/
  hRHS : Jet α S N0
    (fun z θ τ => Work.FTS.Galerkin.dynLin (pExp α) g τ z θ
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z θ)
  /-- **the right-hand side is `C¹` in `z` with a uniformly bounded derivative** on the open
  quadrant: at every point of `(0,∞) × Iθ × [0,S]` the map `z ↦ dynLin + dynRHS` is differentiable
  with derivative bounded by `N1`, uniformly in `τ` (and in `θ`).  This is the *only* extra piece of
  the right-hand side's regularity that the fake-time `z`-modulus of `∂_zg̃` needs: since
  `∂_τg̃ = dynLin + dynRHS` (`R5f.deriv_extG_eq_rhs_of_jet`), it gives `∂_z∂_τg̃ = ∂_z(dynLin+dynRHS)`
  and hence, by differentiating under the `τ`-integral, the `τ`-Lipschitz continuity of `z ↦ ∂_zg̃`
  (`Der.htaumodp`). -/
  hRHz : ∃ N1 : ℝ, 0 ≤ N1 ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    ∀ z ∈ Set.Ioi (0 : ℝ),
    ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS.Galerkin.dynLin (pExp α) g τ z' θ
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z' θ) d z ∧ |d| ≤ N1
  /-- the right-hand side vanishes at `z = 0` -/
  hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ 0 θ
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ 0 θ = 0
  /-- the right-hand side vanishes at `θ = 0` -/
  hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ z 0
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z 0 = 0
  /-- the right-hand side vanishes at `θ = π/2` -/
  hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ z (Real.pi / 2)
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z (Real.pi / 2) = 0

end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R6.clock_fields =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter MeasureTheory intervalIntegral
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R6

set_option autoImplicit false

/-- `gpow m c τ = exp(-∫_0^τ (1 + c·m))`.  `Avort m` is `c = 1` and `Bdyn m` is `c = -1`. -/
def gpow (m : ℝ → ℝ) (c τ : ℝ) : ℝ :=
  Real.exp (-∫ s in (0 : ℝ)..τ, (1 + c * m s))

theorem Avort_eq_gpow (m : ℝ → ℝ) : Work.FTS.RegPkgGal.Avort m = gpow m 1 := by
  funext τ
  simp [Work.FTS.RegPkgGal.Avort, gpow]

theorem Bdyn_eq_gpow (m : ℝ → ℝ) : Work.FTS.RegPkgGal.Bdyn m = gpow m (-1) := by
  funext τ
  simp [Work.FTS.RegPkgGal.Bdyn, gpow, sub_eq_add_neg]

theorem contOn_uIcc {m : ℝ → ℝ} {S τ : ℝ} (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := by
  refine hm.mono ?_
  intro x hx
  rw [Set.uIcc_of_le hτ.1] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2, hτ.2]⟩

/-- `1 + c·x ∈ [1/2, 3/2]` for `|c| = 1`, `|x| ≤ 1/2`. -/
theorem abs_one_add {c x : ℝ} (hc : |c| = 1) (hx : |x| ≤ 1 / 2) : |1 + c * x| ≤ 3 / 2 := by
  have habs : |c * x| ≤ 1 / 2 := by rw [abs_mul, hc, one_mul]; exact hx
  have h := abs_le.mp habs
  rw [abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The fundamental theorem of calculus for the clock: on `[0,S]` the derivative of `gpow` is
`-(1 + c·m τ)` times its value. -/
theorem gpow_hasDerivAt {m : ℝ → ℝ} {c S τ : ℝ}
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    HasDerivAt (gpow m c) (-(1 + c * m τ) * gpow m c τ) τ := by
  have hmem : τ ∈ Set.Ioo (-1 : ℝ) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmτ : ContinuousAt m τ := hm.continuousAt (isOpen_Ioo.mem_nhds hmem)
  have hfτ : ContinuousAt (fun s : ℝ => 1 + c * m s) τ := (hmτ.const_mul c).const_add 1
  have hmono : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := contOn_uIcc hm hτ
  have hcOnIoo : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.Ioo (-1) (S + 1)) :=
    (hm.const_mul c).const_add 1
  have hcOn : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.uIcc (0 : ℝ) τ) :=
    (hmono.const_mul c).const_add 1
  have hint : IntervalIntegrable (fun s : ℝ => 1 + c * m s) volume (0 : ℝ) τ :=
    hcOn.intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => 1 + c * m s) (𝓝 τ) volume :=
    hcOnIoo.stronglyMeasurableAtFilter isOpen_Ioo τ hmem
  have hderiv : HasDerivAt (fun u : ℝ => ∫ x in (0 : ℝ)..u, (1 + c * m x)) (1 + c * m τ) τ :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hfτ
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (-∫ x in (0 : ℝ)..u, (1 + c * m x)))
      (Real.exp (-∫ x in (0 : ℝ)..τ, (1 + c * m x)) * (-(1 + c * m τ))) τ := hderiv.neg.exp
  have h3 : HasDerivAt (gpow m c)
      (Real.exp (-∫ x in (0 : ℝ)..τ, (1 + c * m x)) * (-(1 + c * m τ))) τ := by
    rw [show gpow m c = fun u : ℝ => Real.exp (-∫ x in (0 : ℝ)..u, (1 + c * m x)) from rfl]
    exact h2
  exact h3.congr_deriv (by rw [gpow]; ring)

theorem gpow_deriv_eq {m : ℝ → ℝ} {c S τ : ℝ}
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    deriv (gpow m c) τ = -(1 + c * m τ) * gpow m c τ :=
  (gpow_hasDerivAt hm hτ).deriv

/-- `|gpow m c τ| ≤ 1` on `[0,S]` (the exponent of the exponential is nonpositive). -/
theorem gpow_abs_le_one {m : ℝ → ℝ} {c S τ : ℝ} (hc : |c| = 1)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2)
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) : |gpow m c τ| ≤ 1 := by
  have hmono : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := contOn_uIcc hm hτ
  have hcOn : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.uIcc (0 : ℝ) τ) :=
    (hmono.const_mul c).const_add 1
  have hInt : IntervalIntegrable (fun s : ℝ => 1 + c * m s) volume (0 : ℝ) τ :=
    hcOn.intervalIntegrable
  have hInt1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume (0 : ℝ) τ :=
    continuous_const.intervalIntegrable _ _
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) τ, (1 : ℝ) / 2 ≤ 1 + c * m x := by
    intro x hx
    have hxS : x ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_trans hx.2 hτ.2⟩
    have habs : |c * m x| ≤ 1 / 2 := by rw [abs_mul, hc, one_mul]; exact hmb x hxS
    have := abs_le.mp habs
    linarith [this.1]
  have h1 : (∫ s in (0 : ℝ)..τ, ((1 : ℝ) / 2)) ≤ ∫ s in (0 : ℝ)..τ, (1 + c * m s) :=
    intervalIntegral.integral_mono_on hτ.1 hInt1 hInt hpt
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
  rw [abs_of_pos (show (0 : ℝ) < gpow m c τ from Real.exp_pos _)]
  have hI : -(∫ s in (0 : ℝ)..τ, (1 + c * m s)) ≤ 0 := by linarith [h1, hτ.1]
  calc gpow m c τ = Real.exp (-(∫ s in (0 : ℝ)..τ, (1 + c * m s))) := rfl
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hI
    _ = 1 := Real.exp_zero

/-- `|deriv (gpow m c) τ| ≤ 3/2` on `[0,S]`. -/
theorem gpow_deriv_bound {m : ℝ → ℝ} {c S τ : ℝ} (hc : |c| = 1)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2)
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) : |deriv (gpow m c) τ| ≤ 3 / 2 := by
  rw [gpow_deriv_eq hm hτ, abs_mul, abs_neg]
  calc |1 + c * m τ| * |gpow m c τ| ≤ (3 / 2) * 1 :=
        mul_le_mul (abs_one_add hc (hmb τ hτ)) (gpow_abs_le_one hc hm hmb hτ)
          (abs_nonneg _) (by norm_num)
    _ = 3 / 2 := by norm_num

/-- `gpow` is bounded above and below by positive constants on `[0,S]`. -/
theorem gpow_bounds {m : ℝ → ℝ} {c S : ℝ} (hc : |c| = 1)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2) :
    ∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, a₀ ≤ gpow m c τ ∧ gpow m c τ ≤ a₁ := by
  refine ⟨Real.exp (-(3 * S / 2)), 1, Real.exp_pos _, fun τ hτ => ⟨?_, ?_⟩⟩
  · have hmono : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := contOn_uIcc hm hτ
    have hcOn : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.uIcc (0 : ℝ) τ) :=
      (hmono.const_mul c).const_add 1
    have hInt : IntervalIntegrable (fun s : ℝ => 1 + c * m s) volume (0 : ℝ) τ :=
      hcOn.intervalIntegrable
    have hInt3 : IntervalIntegrable (fun _ : ℝ => (3 : ℝ) / 2) volume (0 : ℝ) τ :=
      continuous_const.intervalIntegrable _ _
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) τ, 1 + c * m x ≤ (3 : ℝ) / 2 := by
      intro x hx
      have hxS : x ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_trans hx.2 hτ.2⟩
      have habs : |c * m x| ≤ 1 / 2 := by rw [abs_mul, hc, one_mul]; exact hmb x hxS
      have := abs_le.mp habs
      linarith [this.2]
    have h2 : (∫ s in (0 : ℝ)..τ, (1 + c * m s)) ≤ ∫ s in (0 : ℝ)..τ, ((3 : ℝ) / 2) :=
      intervalIntegral.integral_mono_on hτ.1 hInt hInt3 hpt
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h2
    have hI : -(3 * S / 2) ≤ -(∫ s in (0 : ℝ)..τ, (1 + c * m s)) := by linarith [h2, hτ.2]
    calc Real.exp (-(3 * S / 2)) ≤ Real.exp (-(∫ s in (0 : ℝ)..τ, (1 + c * m s))) :=
          Real.exp_le_exp.mpr hI
      _ = gpow m c τ := rfl
  · have hmono : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := contOn_uIcc hm hτ
    have hcOn : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.uIcc (0 : ℝ) τ) :=
      (hmono.const_mul c).const_add 1
    have hInt : IntervalIntegrable (fun s : ℝ => 1 + c * m s) volume (0 : ℝ) τ :=
      hcOn.intervalIntegrable
    have hInt1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume (0 : ℝ) τ :=
      continuous_const.intervalIntegrable _ _
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) τ, (1 : ℝ) / 2 ≤ 1 + c * m x := by
      intro x hx
      have hxS : x ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_trans hx.2 hτ.2⟩
      have habs : |c * m x| ≤ 1 / 2 := by rw [abs_mul, hc, one_mul]; exact hmb x hxS
      have := abs_le.mp habs
      linarith [this.1]
    have h1 : (∫ s in (0 : ℝ)..τ, ((1 : ℝ) / 2)) ≤ ∫ s in (0 : ℝ)..τ, (1 + c * m s) :=
      intervalIntegral.integral_mono_on hτ.1 hInt1 hInt hpt
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
    have hI : -(∫ s in (0 : ℝ)..τ, (1 + c * m s)) ≤ 0 := by linarith [h1, hτ.1]
    calc gpow m c τ = Real.exp (-(∫ s in (0 : ℝ)..τ, (1 + c * m s))) := rfl
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hI
      _ = 1 := Real.exp_zero

/-- `gpow` is `3/2`-Lipschitz on `[0,S]`. -/
theorem gpow_lipschitz {m : ℝ → ℝ} {c S : ℝ} (hc : |c| = 1)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2) :
    ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |gpow m c τ - gpow m c τ'| ≤ (3 / 2) * |τ - τ'| := by
  intro τ hτ τ' hτ'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := gpow m c)
    (s := Set.Icc (0 : ℝ) S) (C := 3 / 2) (x := τ') (y := τ)
    (fun x hx => (gpow_hasDerivAt hm hx).differentiableAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact gpow_deriv_bound hc hm hmb hx)
    (convex_Icc _ _) hτ' hτ
  simpa only [Real.norm_eq_abs] using h

/-- The derivative of `gpow` is `α`-Hölder on `[0,S]`. -/
theorem gpow_deriv_holder {m : ℝ → ℝ} {c α L S : ℝ} (hc : |c| = 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (hL : 0 ≤ L)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2)
    (hmh : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |m τ - m τ'| ≤ L * |τ - τ'| ^ α) :
    ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |deriv (gpow m c) τ - deriv (gpow m c) τ'| ≤
        (L + 9 / 4 * S ^ (1 - α)) * |τ - τ'| ^ α := by
  intro τ hτ τ' hτ'
  rw [gpow_deriv_eq hm hτ, gpow_deriv_eq hm hτ']
  have hE : -(1 + c * m τ) * gpow m c τ - (-(1 + c * m τ') * gpow m c τ')
      = (1 + c * m τ') * (gpow m c τ' - gpow m c τ) + c * (m τ' - m τ) * gpow m c τ := by
    ring
  rw [hE]
  have hA : |1 + c * m τ'| ≤ 3 / 2 := abs_one_add hc (hmb τ' hτ')
  have hB : |gpow m c τ' - gpow m c τ| ≤ 3 / 2 * |τ - τ'| := by
    simpa only [abs_sub_comm τ' τ] using gpow_lipschitz hc hm hmb τ' hτ' τ hτ
  have hC : |c * (m τ' - m τ)| ≤ L * |τ - τ'| ^ α := by
    rw [abs_mul, hc, one_mul]
    simpa only [abs_sub_comm τ' τ] using hmh τ' hτ' τ hτ
  have hD : |gpow m c τ| ≤ 1 := gpow_abs_le_one hc hm hmb hτ
  have h1 : |(1 + c * m τ') * (gpow m c τ' - gpow m c τ)| ≤ (3 / 2) * (3 / 2) * |τ - τ'| := by
    rw [abs_mul]
    calc |1 + c * m τ'| * |gpow m c τ' - gpow m c τ|
          ≤ (3 / 2) * ((3 / 2) * |τ - τ'|) :=
          mul_le_mul hA hB (abs_nonneg _) (by positivity)
      _ = (3 / 2) * (3 / 2) * |τ - τ'| := by ring
  have h2 : |c * (m τ' - m τ) * gpow m c τ| ≤ L * |τ - τ'| ^ α := by
    rw [abs_mul]
    calc |c * (m τ' - m τ)| * |gpow m c τ| ≤ (L * |τ - τ'| ^ α) * 1 :=
          mul_le_mul hC hD (abs_nonneg _) (mul_nonneg hL (Real.rpow_nonneg (abs_nonneg _) α))
      _ = L * |τ - τ'| ^ α := by ring
  have h3 : |(1 + c * m τ') * (gpow m c τ' - gpow m c τ) + c * (m τ' - m τ) * gpow m c τ|
      ≤ (3 / 2) * (3 / 2) * |τ - τ'| + L * |τ - τ'| ^ α :=
    (abs_add_le _ _).trans (add_le_add h1 h2)
  have ht0 : 0 ≤ |τ - τ'| := abs_nonneg _
  have htS : |τ - τ'| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hτ.2, hτ'.1], by linarith [hτ'.2, hτ.1]⟩
  have hlt : |τ - τ'| ≤ S ^ (1 - α) * |τ - τ'| ^ α := by
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (ne_of_gt hα), mul_zero]
    · have hr1 : |τ - τ'| ^ (1 - α) ≤ S ^ (1 - α) :=
        Real.rpow_le_rpow (le_of_lt hpos) htS (by linarith)
      have hr2 : |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α = |τ - τ'| := by
        rw [← Real.rpow_add hpos, show (1 - α) + α = 1 by ring, Real.rpow_one]
      calc |τ - τ'| = |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α := hr2.symm
        _ ≤ S ^ (1 - α) * |τ - τ'| ^ α :=
            mul_le_mul_of_nonneg_right hr1 (Real.rpow_nonneg (le_of_lt hpos) α)
  calc |(1 + c * m τ') * (gpow m c τ' - gpow m c τ) + c * (m τ' - m τ) * gpow m c τ|
        ≤ (3 / 2) * (3 / 2) * |τ - τ'| + L * |τ - τ'| ^ α := h3
    _ ≤ (3 / 2) * (3 / 2) * (S ^ (1 - α) * |τ - τ'| ^ α) + L * |τ - τ'| ^ α := by
        have h := mul_le_mul_of_nonneg_left hlt (by norm_num : (0 : ℝ) ≤ (3 / 2) * (3 / 2))
        linarith
    _ = (L + 9 / 4 * S ^ (1 - α)) * |τ - τ'| ^ α := by ring

theorem clock_fields {m : ℝ → ℝ} {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hm : ContinuousOn m (Set.Ioo (-1 : ℝ) (S + 1)))
    (hmb : ∀ τ : ℝ, τ ∈ Set.Ioo (-1 : ℝ) (S + 1) → |m τ| ≤ 1 / 2)
    (hmh : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |m τ - m τ'| ≤ L * |τ - τ'| ^ α) :
    (∀ τ ∈ Set.Icc 0 S, 0 < Work.FTS.RegPkgGal.Avort m τ) ∧
    (∀ τ ∈ Set.Icc 0 S, 0 < Work.FTS.RegPkgGal.Bdyn m τ) ∧
    (∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc 0 S,
      a₀ ≤ Work.FTS.RegPkgGal.Avort m τ ∧ Work.FTS.RegPkgGal.Avort m τ ≤ a₁) ∧
    (∃ b₀ b₁ : ℝ, 0 < b₀ ∧ ∀ τ ∈ Set.Icc 0 S,
      b₀ ≤ Work.FTS.RegPkgGal.Bdyn m τ ∧ Work.FTS.RegPkgGal.Bdyn m τ ≤ b₁) ∧
    (∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (Work.FTS.RegPkgGal.Avort m) (deriv (Work.FTS.RegPkgGal.Avort m) τ) τ) ∧
    (∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (Work.FTS.RegPkgGal.Bdyn m) (deriv (Work.FTS.RegPkgGal.Bdyn m) τ) τ) ∧
    (∃ a₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv (Work.FTS.RegPkgGal.Avort m) τ| ≤ a₂) ∧
    (∃ b₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv (Work.FTS.RegPkgGal.Bdyn m) τ| ≤ b₂) ∧
    (∃ a₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |deriv (Work.FTS.RegPkgGal.Avort m) τ - deriv (Work.FTS.RegPkgGal.Avort m) τ'|
        ≤ a₃ * |τ - τ'| ^ α) ∧
    (∃ b₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |deriv (Work.FTS.RegPkgGal.Bdyn m) τ - deriv (Work.FTS.RegPkgGal.Bdyn m) τ'|
        ≤ b₃ * |τ - τ'| ^ α) := by
  have hmb' : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2 := by
    intro s hs
    exact hmb s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨L, hL, hmhL⟩ := hmh
  have hc1 : |(1 : ℝ)| = 1 := by norm_num
  have hcm1 : |(-1 : ℝ)| = 1 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ _
    rw [Avort_eq_gpow]
    exact Real.exp_pos _
  · intro τ _
    rw [Bdyn_eq_gpow]
    exact Real.exp_pos _
  · obtain ⟨a₀, a₁, ha₀, ha⟩ := gpow_bounds (m := m) (c := 1) (S := S) hc1 hm hmb'
    exact ⟨a₀, a₁, ha₀, fun τ hτ => by rw [Avort_eq_gpow]; exact ha τ hτ⟩
  · obtain ⟨b₀, b₁, hb₀, hb⟩ := gpow_bounds (m := m) (c := -1) (S := S) hcm1 hm hmb'
    exact ⟨b₀, b₁, hb₀, fun τ hτ => by rw [Bdyn_eq_gpow]; exact hb τ hτ⟩
  · intro τ hτ
    rw [Avort_eq_gpow]
    have h := gpow_hasDerivAt (m := m) (c := 1) (S := S) hm hτ
    rw [h.deriv]
    exact h
  · intro τ hτ
    rw [Bdyn_eq_gpow]
    have h := gpow_hasDerivAt (m := m) (c := -1) (S := S) hm hτ
    rw [h.deriv]
    exact h
  · exact ⟨3 / 2, fun τ hτ => by
      rw [Avort_eq_gpow]; exact gpow_deriv_bound hc1 hm hmb' hτ⟩
  · exact ⟨3 / 2, fun τ hτ => by
      rw [Bdyn_eq_gpow]; exact gpow_deriv_bound hcm1 hm hmb' hτ⟩
  · exact ⟨L + 9 / 4 * S ^ (1 - α), fun τ hτ τ' hτ' => by
      rw [Avort_eq_gpow]
      exact gpow_deriv_holder hc1 hα hα1 hL hm hmb' hmhL τ hτ τ' hτ'⟩
  · exact ⟨L + 9 / 4 * S ^ (1 - α), fun τ hτ τ' hτ' => by
      rw [Bdyn_eq_gpow]
      exact gpow_deriv_holder hcm1 hα hα1 hL hm hmb' hmhL τ hτ τ' hτ'⟩

end Work.FTS.RegPkgGal.R6
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7e.curve_box_zL =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter
open scoped Topology Real

set_option maxHeartbeats 1600000

namespace Work.FTS.RegPkgGal.R7e

/-- **Existence of the backward characteristic with an a priori box**, for a velocity field that is
Lipschitz only on `z > L`.

Given `z > L·e^{aS}`, `0 < θ < π/2` and `0 < τ ≤ S`, there is a solution `α` of

  `ż = -z·Vz(z,θ,τ-t)`,  `θ̇ = -Vθ(z,θ,τ-t)`,  `α 0 = (z,θ)`

on `[0,τ]`, and it stays in the box

  `z·e^{-aτ} ≤ z(t) ≤ z`,   `θ·e^{-Kτ} ≤ θ(t) ≤ π/2 - (π/2-θ)·e^{-Kτ}`.

The lower bound `z(t) ≥ z·e^{-aτ} > L` is what makes the shrunk Lipschitz domain `z > L` usable:
the trajectory never leaves it.  (The proof bootstraps on the maximal time up to which the
trajectory is strictly inside the region `z > L`, `0 < θ < π/2`.) -/
theorem curve_box_zL {S a b L : ℝ} (hS : 0 < S) (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 ≤ L)
    {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {K : NNReal}
    (hVlipL : ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
      (Set.prod (Set.Ioi L) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hVjoint : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S))))
    (hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ)
    (hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a)
    (hVθb : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ b)
    (hVθ0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0)
    (hVθπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0)
    {τ z θ : ℝ} (hτ : 0 < τ) (hτS : τ ≤ S) (hz : L * Real.exp (a * S) < z)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = (z, θ) ∧
      (∀ t ∈ Set.Icc (0:ℝ) τ, HasDerivWithinAt α
        (-((α t).1 * Vz (α t).1 (α t).2 (τ - t)), -(Vθ (α t).1 (α t).2 (τ - t)))
        (Set.Icc (0:ℝ) τ) t) ∧
      (∀ t ∈ Set.Icc (0:ℝ) τ,
        (α t).1 ∈ Set.Icc (z * Real.exp (-(a * τ))) z ∧
        (α t).2 ∈ Set.Icc (θ * Real.exp (-((K:ℝ) * τ)))
          (Real.pi / 2 - (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)))) := by
  have hK0 : (0:ℝ) ≤ (K:ℝ) := K.2
  have hexp1 : (1:ℝ) ≤ Real.exp (a * S) := Real.one_le_exp (by positivity)
  have hzL : L < z := by nlinarith [hL, hexp1, hz]
  have hzpos : 0 < z := lt_of_le_of_lt (by nlinarith [hL, hexp1]) hz
  -- barrier bound for the angular field, now only for `z' > L`
  have hbar : ∀ z' θ' τ' : ℝ, L < z' → 0 < θ' → θ' < Real.pi / 2 → 0 ≤ τ' → τ' ≤ S →
      |Vθ z' θ' τ'| ≤ (K:ℝ) * θ' ∧ |Vθ z' θ' τ'| ≤ (K:ℝ) * (Real.pi / 2 - θ') :=
    Vth_barrier_L hS hK0 hL hVlipL hVjoint hVθ0 hVθπ
  -- the a priori box of the trajectory
  set zm : ℝ := z * Real.exp (-(a * τ)) with hzm
  set θm : ℝ := θ * Real.exp (-((K:ℝ) * τ)) with hθm
  set θM : ℝ := Real.pi / 2 - (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)) with hθM
  have hexpa : Real.exp (-(a * τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [ha, le_of_lt hτ]
  have hexpK : Real.exp (-((K:ℝ) * τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [hK0, le_of_lt hτ]
  have hzm_pos : 0 < zm := by rw [hzm]; positivity
  have hθm_pos : 0 < θm := by rw [hθm]; positivity
  have hθM_lt : θM < Real.pi / 2 := by
    rw [hθM]
    have h1 : 0 < (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)) :=
      mul_pos (by linarith) (Real.exp_pos _)
    linarith
  have hzm_le_z : zm ≤ z := by
    rw [hzm]
    calc z * Real.exp (-(a * τ)) ≤ z * 1 :=
          mul_le_mul_of_nonneg_left hexpa (le_of_lt hzpos)
      _ = z := by ring
  have hθm_le_θ : θm ≤ θ := by
    rw [hθm]
    calc θ * Real.exp (-((K:ℝ) * τ)) ≤ θ * 1 :=
          mul_le_mul_of_nonneg_left hexpK (le_of_lt hθ0)
      _ = θ := by ring
  have hθ_le_θM : θ ≤ θM := by
    rw [hθM]
    have h1 : (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)) ≤ (Real.pi / 2 - θ) * 1 :=
      mul_le_mul_of_nonneg_left hexpK (by linarith)
    linarith
  have hθm_le_θM : θm ≤ θM := le_trans hθm_le_θ hθ_le_θM
  -- the a priori lower bound for `z` is strictly above `L`: this is what makes the shrunk
  -- Lipschitz domain `z > L` usable
  have hzm_gt_L : L < zm := by
    rw [hzm]
    have hexp3 : Real.exp (a * S) * Real.exp (-(a * τ)) = Real.exp (a * (S - τ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h1 : L * Real.exp (a * S) * Real.exp (-(a * τ)) < z * Real.exp (-(a * τ)) :=
      mul_lt_mul_of_pos_right hz (Real.exp_pos _)
    have h2 : L ≤ L * Real.exp (a * S) * Real.exp (-(a * τ)) := by
      rw [mul_assoc, hexp3]
      have h5 : (1:ℝ) ≤ Real.exp (a * (S - τ)) := Real.one_le_exp (by nlinarith [ha, hτS])
      nlinarith [hL, h5]
    linarith
  -- the outer box, chosen strictly inside `z > L` and `0 < θ < π/2`
  have hzl_gt_L : L < (L + zm) / 2 := by linarith [hzm_gt_L]
  have hzl_lt_zm : (L + zm) / 2 < zm := by linarith [hzm_gt_L]
  have hzl_pos : 0 < (L + zm) / 2 := by linarith [hL, hzm_gt_L]
  have hθm2 : 0 < θm / 2 := by linarith [hθm_pos]
  have hθhi_lt : (θM + Real.pi / 2) / 2 < Real.pi / 2 := by linarith [hθM_lt]
  have hbox_nonempty : (L + zm) / 2 ≤ z + 1 := by linarith [hzm_le_z, hzL]
  have hθbox_nonempty : θm / 2 ≤ (θM + Real.pi / 2) / 2 := by
    linarith [hθm_le_θM, hθM_lt]
  have houter_sub : Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2) ⊆
      Set.Ioi L ×ˢ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    exact Set.mem_prod.mpr
      ⟨lt_of_lt_of_le hzl_gt_L hp1.1, lt_of_lt_of_le hθm2 hp2.1, lt_of_le_of_lt hp2.2 hθhi_lt⟩
  -- bound at fake time `0`
  have hcont0 : ContinuousOn (fun x : ℝ × ℝ => (Vz x.1 x.2 0, Vθ x.1 x.2 0))
      (Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2)) := by
    have hψ : ContinuousOn (fun x : ℝ × ℝ => (x.1, x.2, (0:ℝ)))
        (Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2)) := by fun_prop
    have hmap : MapsTo (fun x : ℝ × ℝ => (x.1, x.2, (0:ℝ)))
        (Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2))
        (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi/2) ×ˢ Set.Icc (0:ℝ) S)) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
      exact Set.mem_prod.mpr
        ⟨lt_of_lt_of_le hzl_pos hx1.1,
          ⟨le_of_lt (lt_of_lt_of_le hθm2 hx2.1), le_of_lt (lt_of_le_of_lt hx2.2 hθhi_lt)⟩,
          ⟨le_rfl, le_of_lt hS⟩⟩
    simpa [Function.comp_def] using hVjoint.comp hψ hmap
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont0
  have hC0 : 0 ≤ C := by
    have hm : ((L + zm)/2, θm/2) ∈
        Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2) :=
      Set.mem_prod.mpr ⟨⟨le_rfl, hbox_nonempty⟩, ⟨le_rfl, hθbox_nonempty⟩⟩
    exact le_trans (norm_nonneg _) (hC _ hm)
  -- the constants for the existence theorem
  set Mvz : ℝ := C + a with hMvz
  set Mvθ : ℝ := C + b with hMvθ
  set Zb : ℝ := (L + zm)/2 + (z+1) with hZb
  set Lb : ℝ := Zb * Mvz + Mvθ + 1 with hLb
  set Klip : ℝ := Mvz + Zb * (K:ℝ) + (K:ℝ) + 1 with hKlip
  have hMvz0 : 0 ≤ Mvz := by rw [hMvz]; linarith
  have hMvθ0 : 0 ≤ Mvθ := by rw [hMvθ]; linarith
  have hZb0 : 0 ≤ Zb := by rw [hZb]; linarith [hzl_pos]
  have hLb0 : 0 < Lb := by rw [hLb]; nlinarith
  have hKlip0 : 0 ≤ Klip := by rw [hKlip]; nlinarith
  -- bounds on the two fields over the outer box
  have hVzb : ∀ σ ∈ Set.Icc (0:ℝ) S,
      ∀ x ∈ Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      |Vz x.1 x.2 σ| ≤ Mvz := by
    intro σ hσ x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    have hx1' : 0 < x.1 := lt_of_lt_of_le hzl_pos hx1.1
    have hx2a : 0 < x.2 := lt_of_lt_of_le hθm2 hx2.1
    have hx2b : x.2 < Real.pi / 2 := lt_of_le_of_lt hx2.2 hθhi_lt
    rcases eq_or_lt_of_le hσ.1 with hs | hs
    · rw [← hs, hMvz]
      have h2 := hC x (Set.mem_prod.mpr ⟨hx1, hx2⟩)
      rw [Prod.norm_def] at h2
      have h3 : |Vz x.1 x.2 0| ≤ max |Vz x.1 x.2 0| |Vθ x.1 x.2 0| := le_max_left _ _
      have h4 : max |Vz x.1 x.2 0| |Vθ x.1 x.2 0| ≤ C := by simpa [Real.norm_eq_abs] using h2
      linarith
    · have h1 : Vz x.1 x.2 σ ≤ a := hVza _ _ _ hx1' hx2a hx2b hs hσ.2
      have h2 : 0 ≤ Vz x.1 x.2 σ := hVz0 _ _ _ hx1' hx2a hx2b hs hσ.2
      rw [hMvz]
      rw [abs_le]
      constructor <;> linarith
  have hVθb' : ∀ σ ∈ Set.Icc (0:ℝ) S,
      ∀ x ∈ Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      |Vθ x.1 x.2 σ| ≤ Mvθ := by
    intro σ hσ x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    have hx1' : 0 < x.1 := lt_of_lt_of_le hzl_pos hx1.1
    have hx2a : 0 < x.2 := lt_of_lt_of_le hθm2 hx2.1
    have hx2b : x.2 < Real.pi / 2 := lt_of_le_of_lt hx2.2 hθhi_lt
    rcases eq_or_lt_of_le hσ.1 with hs | hs
    · rw [← hs, hMvθ]
      have h2 := hC x (Set.mem_prod.mpr ⟨hx1, hx2⟩)
      rw [Prod.norm_def] at h2
      have h3 : |Vθ x.1 x.2 0| ≤ max |Vz x.1 x.2 0| |Vθ x.1 x.2 0| := le_max_right _ _
      have h4 : max |Vz x.1 x.2 0| |Vθ x.1 x.2 0| ≤ C := by simpa [Real.norm_eq_abs] using h2
      linarith
    · have h1 : |Vθ x.1 x.2 σ| ≤ b := hVθb _ _ _ hx1' hx2a hx2b hs hσ.2
      rw [hMvθ]
      linarith
  -- the data of the existence theorem
  have hx1_le_Zb : ∀ x ∈ Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      |x.1| ≤ Zb := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    rw [hZb, abs_le]
    constructor <;> linarith [hx1.1, hx1.2]
  have hlipbox : ∀ t ∈ Set.Icc (0:ℝ) τ, LipschitzOnWith ⟨Klip, hKlip0⟩
      (fun x : ℝ × ℝ => (-(x.1 * Vz x.1 x.2 (τ - t)), -(Vθ x.1 x.2 (τ - t))))
      (Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2)) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    obtain ⟨hy1, hy2⟩ := Set.mem_prod.mp hy
    have hσ : τ - t ∈ Set.Icc (0:ℝ) S := ⟨by linarith [ht.2], by linarith [ht.1, hτS]⟩
    have hxmem : (x.1, x.2) ∈ Set.prod (Set.Ioi L) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      Set.mem_prod.mpr ⟨lt_of_lt_of_le hzl_gt_L hx1.1, lt_of_lt_of_le hθm2 hx2.1,
        lt_of_le_of_lt hx2.2 hθhi_lt⟩
    have hymem : (y.1, y.2) ∈ Set.prod (Set.Ioi L) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      Set.mem_prod.mpr ⟨lt_of_lt_of_le hzl_gt_L hy1.1, lt_of_lt_of_le hθm2 hy2.1,
        lt_of_le_of_lt hy2.2 hθhi_lt⟩
    have hLip := hVlipL (τ - t) hσ
    have hVθdiff : |Vθ x.1 x.2 (τ - t) - Vθ y.1 y.2 (τ - t)| ≤ (K:ℝ) * dist x y := by
      have h2 := hLip.dist_le_mul _ hxmem _ hymem
      rw [Prod.dist_eq] at h2
      have h3 : dist (Vθ x.1 x.2 (τ - t)) (Vθ y.1 y.2 (τ - t)) ≤ (K:ℝ) * dist x y :=
        le_trans (le_max_right _ _) h2
      simpa [Real.dist_eq] using h3
    have hVzdiff : |Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t)| ≤ (K:ℝ) * dist x y := by
      have h2 := hLip.dist_le_mul _ hxmem _ hymem
      rw [Prod.dist_eq] at h2
      have h3 : dist (Vz x.1 x.2 (τ - t)) (Vz y.1 y.2 (τ - t)) ≤ (K:ℝ) * dist x y :=
        le_trans (le_max_left _ _) h2
      simpa [Real.dist_eq] using h3
    have hdist : |x.1 - y.1| ≤ dist x y := by
      rw [Prod.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hsecond : dist (-(x.1 * Vz x.1 x.2 (τ - t))) (-(y.1 * Vz y.1 y.2 (τ - t)))
        ≤ Klip * dist x y := by
      have hdecomp : x.1 * Vz x.1 x.2 (τ - t) - y.1 * Vz y.1 y.2 (τ - t)
          = x.1 * (Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t))
            + (x.1 - y.1) * Vz y.1 y.2 (τ - t) := by ring
      have h1 : |x.1 * Vz x.1 x.2 (τ - t) - y.1 * Vz y.1 y.2 (τ - t)|
          ≤ Zb * ((K:ℝ) * dist x y) + dist x y * Mvz := by
        calc |x.1 * Vz x.1 x.2 (τ - t) - y.1 * Vz y.1 y.2 (τ - t)|
            = |x.1 * (Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t))
                + (x.1 - y.1) * Vz y.1 y.2 (τ - t)| := by rw [hdecomp]
          _ ≤ |x.1 * (Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t))|
                + |(x.1 - y.1) * Vz y.1 y.2 (τ - t)| := abs_add_le _ _
          _ = |x.1| * |Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t)|
                + |x.1 - y.1| * |Vz y.1 y.2 (τ - t)| := by rw [abs_mul, abs_mul]
          _ ≤ Zb * ((K:ℝ) * dist x y) + dist x y * Mvz := by
              have hA : |x.1| * |Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t)|
                  ≤ Zb * ((K:ℝ) * dist x y) := by
                exact mul_le_mul (hx1_le_Zb x (Set.mem_prod.mpr ⟨hx1, hx2⟩)) hVzdiff
                  (abs_nonneg _) hZb0
              have hB : |x.1 - y.1| * |Vz y.1 y.2 (τ - t)| ≤ dist x y * Mvz := by
                exact mul_le_mul hdist (hVzb _ hσ y (Set.mem_prod.mpr ⟨hy1, hy2⟩))
                  (abs_nonneg _) dist_nonneg
              linarith
      have h2 : dist (-(x.1 * Vz x.1 x.2 (τ - t))) (-(y.1 * Vz y.1 y.2 (τ - t)))
          = |x.1 * Vz x.1 x.2 (τ - t) - y.1 * Vz y.1 y.2 (τ - t)| := by
        rw [Real.dist_eq, abs_sub_comm]
        congr 1
        ring
      rw [h2]
      have h3 : Zb * ((K:ℝ) * dist x y) + dist x y * Mvz
          = (Zb * (K:ℝ) + Mvz) * dist x y := by ring
      rw [h3] at h1
      refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      rw [hKlip]
      linarith [hMvz0, mul_nonneg hZb0 hK0]
    have hfirst : dist (-(Vθ x.1 x.2 (τ - t))) (-(Vθ y.1 y.2 (τ - t))) ≤ Klip * dist x y := by
      have h2 : dist (-(Vθ x.1 x.2 (τ - t))) (-(Vθ y.1 y.2 (τ - t)))
          = |Vθ x.1 x.2 (τ - t) - Vθ y.1 y.2 (τ - t)| := by
        rw [Real.dist_eq, abs_sub_comm]
        congr 1
        ring
      rw [h2]
      refine le_trans hVθdiff (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      rw [hKlip]
      linarith [hMvz0, mul_nonneg hZb0 hK0]
    rw [Prod.dist_eq]
    exact max_le hsecond hfirst
  have hbddbox : ∀ t ∈ Set.Icc (0:ℝ) τ,
      ∀ x ∈ Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      ‖(-(x.1 * Vz x.1 x.2 (τ - t)), -(Vθ x.1 x.2 (τ - t)))‖ ≤ Lb := by
    intro t ht x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    have hσ : τ - t ∈ Set.Icc (0:ℝ) S := ⟨by linarith [ht.2], by linarith [ht.1, hτS]⟩
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs, abs_neg, abs_mul]
      calc |x.1| * |Vz x.1 x.2 (τ - t)| ≤ Zb * Mvz :=
            mul_le_mul (hx1_le_Zb x (Set.mem_prod.mpr ⟨hx1, hx2⟩))
              (hVzb _ hσ x (Set.mem_prod.mpr ⟨hx1, hx2⟩)) (abs_nonneg _) hZb0
        _ ≤ Lb := by rw [hLb]; linarith [hMvθ0]
    · rw [Real.norm_eq_abs, abs_neg]
      calc |Vθ x.1 x.2 (τ - t)| ≤ Mvθ := hVθb' _ hσ x (Set.mem_prod.mpr ⟨hx1, hx2⟩)
        _ ≤ Lb := by rw [hLb]; nlinarith [hZb0, hMvz0]
  have htcontbox : ∀ x ∈ Set.Icc ((L + zm)/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      ContinuousOn (fun t : ℝ => (-(x.1 * Vz x.1 x.2 (τ - t)), -(Vθ x.1 x.2 (τ - t))))
        (Set.Icc (0:ℝ) τ) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    have hx1' : 0 < x.1 := lt_of_lt_of_le hzl_pos hx1.1
    have hx2' : 0 < x.2 := lt_of_lt_of_le hθm2 hx2.1
    have hx2'' : x.2 < Real.pi / 2 := lt_of_le_of_lt hx2.2 hθhi_lt
    have hslice : ContinuousOn (fun s : ℝ => (Vz x.1 x.2 s, Vθ x.1 x.2 s)) (Set.Icc (0:ℝ) S) := by
      have hψ : ContinuousOn (fun s : ℝ => (x.1, x.2, s)) (Set.Icc (0:ℝ) S) := by fun_prop
      have hmap : MapsTo (fun s : ℝ => (x.1, x.2, s)) (Set.Icc (0:ℝ) S)
          (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi/2) ×ˢ Set.Icc (0:ℝ) S)) := by
        intro s hs
        exact Set.mem_prod.mpr ⟨hx1', ⟨le_of_lt hx2', le_of_lt hx2''⟩, hs⟩
      simpa [Function.comp_def] using hVjoint.comp hψ hmap
    have hsub : ContinuousOn (fun t : ℝ => τ - t) (Set.Icc (0:ℝ) τ) := by fun_prop
    have hmap2 : MapsTo (fun t : ℝ => τ - t) (Set.Icc (0:ℝ) τ) (Set.Icc (0:ℝ) S) := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1, hτS]⟩
    have hcomp : ContinuousOn (fun t : ℝ => (Vz x.1 x.2 (τ - t), Vθ x.1 x.2 (τ - t)))
        (Set.Icc (0:ℝ) τ) := hslice.comp hsub hmap2
    have h1 : ContinuousOn (fun t : ℝ => Vz x.1 x.2 (τ - t)) (Set.Icc (0:ℝ) τ) :=
      continuous_fst.comp_continuousOn hcomp
    have h2 : ContinuousOn (fun t : ℝ => Vθ x.1 x.2 (τ - t)) (Set.Icc (0:ℝ) τ) :=
      continuous_snd.comp_continuousOn hcomp
    have h3 : ContinuousOn (fun t : ℝ => x.1 * Vz x.1 x.2 (τ - t)) (Set.Icc (0:ℝ) τ) :=
      continuousOn_const.mul h1
    exact h3.neg.prodMk h2.neg
  -- the a priori estimate
  have htrajg : ∀ T' ∈ Set.Icc (0:ℝ) τ, ∀ α : ℝ → ℝ × ℝ, α 0 = (z, θ) →
      (∀ t ∈ Set.Icc (0:ℝ) T', HasDerivWithinAt α
        (-((α t).1 * Vz (α t).1 (α t).2 (τ - t)), -(Vθ (α t).1 (α t).2 (τ - t)))
        (Set.Icc (0:ℝ) T') t) →
      ∀ t ∈ Set.Icc (0:ℝ) T', (α t).1 ∈ Set.Icc zm z ∧ (α t).2 ∈ Set.Icc θm θM := by
    intro T' hT' α hα0' hode t ht
    have hVθl : ∀ z' θ' τ' : ℝ, L < z' → 0 < θ' → θ' < Real.pi / 2 → 0 < τ' → τ' ≤ S →
        |Vθ z' θ' τ'| ≤ (K:ℝ) * θ' := fun z' θ' τ' h1 h2 h3 h4 h5 =>
      (hbar z' θ' τ' h1 h2 h3 (le_of_lt h4) h5).1
    have hVθu : ∀ z' θ' τ' : ℝ, L < z' → 0 < θ' → θ' < Real.pi / 2 → 0 < τ' → τ' ≤ S →
        |Vθ z' θ' τ'| ≤ (K:ℝ) * (Real.pi / 2 - θ') := fun z' θ' τ' h1 h2 h3 h4 h5 =>
      (hbar z' θ' τ' h1 h2 h3 (le_of_lt h4) h5).2
    have hzT' : L < z * Real.exp (-(a * T')) := by
      have h1 : z * Real.exp (-(a * τ)) ≤ z * Real.exp (-(a * T')) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hzpos)
        rw [Real.exp_le_exp]
        have : a * T' ≤ a * τ := mul_le_mul_of_nonneg_left hT'.2 ha
        linarith
      have h2 : L < z * Real.exp (-(a * τ)) := by
        rw [← hzm]
        exact hzm_gt_L
      linarith
    have hb : z * Real.exp (-(a * t)) ≤ (α t).1 ∧ (α t).1 ≤ z ∧
        θ * Real.exp (-((K:ℝ) * t)) ≤ (α t).2 ∧
        (α t).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * t)) :=
      trajectory_bounds_L (Vz := Vz) (Vθ := Vθ) (a := a) (K := (K:ℝ)) (S := S) (τ₀ := τ)
        (T := T') (z₀ := z) (θ₀ := θ) (L := L) (α := α) hL hT'.1 hT'.2 hτS hzT' hθ0 hθπ ha hK0
        hα0' hode hVz0 hVza hVθl hVθu t ht
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    refine ⟨⟨?_, hb2⟩, ?_, ?_⟩
    · rw [hzm]
      calc z * Real.exp (-(a * τ)) ≤ z * Real.exp (-(a * t)) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hzpos)
            have hle : a * t ≤ a * τ :=
              mul_le_mul_of_nonneg_left (le_trans ht.2 hT'.2) ha
            exact Real.exp_le_exp.mpr (neg_le_neg hle)
        _ ≤ (α t).1 := hb1
    · rw [hθm]
      calc θ * Real.exp (-((K:ℝ) * τ)) ≤ θ * Real.exp (-((K:ℝ) * t)) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hθ0)
            have hle : (K:ℝ) * t ≤ (K:ℝ) * τ :=
              mul_le_mul_of_nonneg_left (le_trans ht.2 hT'.2) hK0
            exact Real.exp_le_exp.mpr (neg_le_neg hle)
        _ ≤ (α t).2 := hb3
    · rw [hθM]
      have hle : (K:ℝ) * t ≤ (K:ℝ) * τ :=
        mul_le_mul_of_nonneg_left (le_trans ht.2 hT'.2) hK0
      have h5 : Real.exp (-((K:ℝ) * τ)) ≤ Real.exp (-((K:ℝ) * t)) :=
        Real.exp_le_exp.mpr (neg_le_neg hle)
      have h6 : (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ))
          ≤ (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * t)) :=
        mul_le_mul_of_nonneg_left h5 (by linarith [hθπ])
      have h7 := sub_le_sub_left h6 (Real.pi / 2)
      linarith [hb4, h7]
  -- existence of the trajectory
  have hexists : ∃ α : ℝ → ℝ × ℝ, α 0 = (z, θ) ∧
      ∀ t ∈ Set.Icc (0:ℝ) τ, HasDerivWithinAt α
        (-((α t).1 * Vz (α t).1 (α t).2 (τ - t)), -(Vθ (α t).1 (α t).2 (τ - t)))
        (Set.Icc (0:ℝ) τ) t :=
    Work.FTS.RegPkgGal.R7d.ode_box_existence (fun (t : ℝ) (x : ℝ × ℝ) =>
        (-(x.1 * Vz x.1 x.2 (τ - t)), -(Vθ x.1 x.2 (τ - t))))
      (z, θ) (T := τ) (L := Lb) (Klip := Klip)
      (zlo := zm) (zhi := z) (θlo := θm) (θhi := θM)
      (zlo' := (L + zm)/2) (zhi' := z+1) (θlo' := θm/2) (θhi' := (θM + Real.pi/2)/2)
      (le_of_lt hτ) hLb0 hKlip0
      ⟨⟨hzm_le_z, le_rfl⟩, hθm_le_θ, hθ_le_θM⟩
      hzl_lt_zm (by linarith) (by linarith) (by linarith)
      hlipbox hbddbox htcontbox htrajg
  obtain ⟨α, hα0', hαode⟩ := hexists
  have hbox : ∀ t ∈ Set.Icc (0:ℝ) τ, (α t).1 ∈ Set.Icc zm z ∧ (α t).2 ∈ Set.Icc θm θM :=
    htrajg τ ⟨le_of_lt hτ, le_rfl⟩ α hα0' hαode
  refine ⟨α, hα0', hαode, ?_⟩
  -- the endpoints are the *values* of the local definitions `zm`, `θm`, `θM`
  intro t ht
  exact hbox t ht

end Work.FTS.RegPkgGal.R7e
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.FstarSlotPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FstarSlotPt`: the pointwise slot bound for `F_*`, `D_θF_*` and `D_zF_*`

For every `0 < α ≤ 1`, every `r > 0` and every `θ ∈ Iθ`,

  `F_*(r,θ)² + (D_θF_*)(r,θ)² + (D_zF_*)(r,θ)² ≤ C α² (1+r)^{-2}`

with a universal constant `C`.

## Mathematics

Everything follows from the *separation of variables* of the fundamental profile
(paper tex 1334)

  `F_*(z,θ) = (2α/c(α)) · Γ(θ) · h(z)`,   `h(z) = z/(1+z)²`,   `Γ(θ) = (sinθ cos²θ)^{α/3}`,

and from its two associates

* `D_θF_*(z,θ) = (2α/c) · D_θΓ(θ) · h(z)` — the angular operator `D_θ` acts on `Γ` only
  (`FstarPkg.pzIter_DthIter_Fstar_eq` at `j = 1`, `k = 0`);
* `D_zF_*(z,θ) = (α/c) · Γ(θ) · H(z)`, `H(z) = 2z(1-z)/(1+z)³` — the radial operator acts on
  the radial factor only (`FstarPkg.Dz_Fstar_eq_Hz`).

The elementary inputs are

* the radial bounds `|h(z)| ≤ 1/(1+z)` and `|H(z)| ≤ 2/(1+z)` for `z ≥ 0` (proved here by
  elementary algebra);
* the angular bounds `0 ≤ Γ ≤ 1` (`Spaces.Gam_bounds`) and `|D_θΓ| ≤ α · tBound 0 0`
  (`Spaces.dthU_Gam_le`, since `D_θΓ = α · (cos 2θ - 1/3) · Γ`);
* the normalisation `1/10 ≤ c(α) ≤ 10` (`Spaces.c_bounds`).

Two powers of `α` are then available in every slot: one from the prefactor `2α/c`, and a
second in the `D_θ`-slot because the angular derivative costs a factor `α`; in the `F_*`- and
`D_zF_*`-slots the second power comes from `α ≤ 1` (`α² ≤ α`).  The decay `(1+r)^{-2}` is
paid by the radial factors, which contribute `(1+r)^{-1}` in every slot; squaring turns this
into the required `(1+r)^{-2}`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux

open scoped Real Topology

/-! ## Elementary bounds for the two radial factors -/

/-- `|h(z)| ≤ 1/(1+z)` for `h(z) = z/(1+z)²`, `z ≥ 0`. -/
lemma hKer_abs_le {z : ℝ} (hz : 0 ≤ z) : |Work.Spaces.hKer z| ≤ 1 / (1 + z) := by
  have h1z : 0 < 1 + z := by linarith
  rw [Work.Spaces.hKer_apply, abs_of_nonneg (div_nonneg hz (by positivity))]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2) (by positivity : (0:ℝ) < 1 + z)]
  nlinarith

/-- `|H(z)| ≤ 2/(1+z)` for `H(z) = 2z(1-z)/(1+z)³`, `z ≥ 0`. -/
lemma Hz_abs_le {z : ℝ} (hz : 0 ≤ z) : |Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ 2 / (1 + z) := by
  have h1z : 0 < 1 + z := by linarith
  rw [Work.FTS.Nonlinear.FstarPkg.Hz, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + z) ^ 3)]
  have hnum : |2 * z * (1 - z)| ≤ 2 * (1 + z) ^ 2 := by
    have h1 : |2 * z * (1 - z)| = 2 * z * |1 - z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hz, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [h1]
    have h2 : |1 - z| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
    calc 2 * z * |1 - z| ≤ 2 * z * (1 + z) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 * (1 + z) ^ 2 := by nlinarith
  calc |2 * z * (1 - z)| / (1 + z) ^ 3 ≤ (2 * (1 + z) ^ 2) / (1 + z) ^ 3 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 / (1 + z) := by
        rw [div_eq_div_iff (by positivity : (1 + z) ^ 3 ≠ 0) (by positivity : (1 + z) ≠ 0)]
        ring

/-! ## The three slot bounds -/

/-- `|F_*(z,θ)| ≤ 20 α /(1+z)`: the prefactor `2α/c ≤ 20α`, the angular factor `Γ ≤ 1` and
the radial factor `|h(z)| ≤ 1/(1+z)`. -/
lemma Fstar_abs_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α z θ| ≤ 20 * α * (1 / (1 + z)) := by
  simp only [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored]
  have hc : (1:ℝ)/10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α := by
    rw [abs_of_nonneg (div_nonneg (by linarith) hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hker := hKer_abs_le hz
  rw [abs_mul, abs_mul, abs_of_nonneg hGam.1]
  have hstep : |2 * α / Work.Spaces.c α| * Work.Spaces.Gam α θ * |Work.Spaces.hKer z|
      ≤ (20 * α) * 1 * (1 / (1 + z)) :=
    mul_le_mul (mul_le_mul hcoef hGam.2 hGam.1 (mul_nonneg (by norm_num) hα.le)) hker
      (abs_nonneg _) (by positivity)
  linarith

/-- `|D_zF_*(z,θ)| ≤ 20 α /(1+z)`: `D_z` only sees the radial factor `H`, and
`|H(z)| ≤ 2/(1+z)`. -/
lemma DzFstar_abs_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 20 * α * (1 / (1 + z)) := by
  rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith : (-1:ℝ) < z)]
  have hc : (1:ℝ)/10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hHz := Hz_abs_le hz
  rw [abs_mul, abs_mul, abs_of_nonneg hGam.1]
  have hstep : |α / Work.Spaces.c α| * (Work.Spaces.Gam α θ * |Work.FTS.Nonlinear.FstarPkg.Hz z|)
      ≤ (10 * α) * (1 * (2 / (1 + z))) :=
    mul_le_mul hcoef (mul_le_mul hGam.2 hHz (abs_nonneg _) (by norm_num))
      (mul_nonneg hGam.1 (abs_nonneg _)) (mul_nonneg (by norm_num) hα.le)
  calc |α / Work.Spaces.c α| * (Work.Spaces.Gam α θ * |Work.FTS.Nonlinear.FstarPkg.Hz z|)
      ≤ (10 * α) * (1 * (2 / (1 + z))) := hstep
    _ = 20 * α * (1 / (1 + z)) := by ring


/-! ## The slot bound -/


end Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_N_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux



end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstar_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fstar_slots` --- the pointwise slot bounds for the profile `F_*` and its family

For `α ∈ (0,1]`, `z > 0`, `θ ∈ (0,π/2)` and all `j + i ≤ 6`,

  `|D_z^jD_θ^i F_*| ≤ Cα·z/(1+z)²`

and likewise for `D_θF_*`, `D_zF_*` and `z ↦ FK(F_*)`, while for `i ≥ 1` the same slots
gain a factor `sin(2θ)^{α/3}` (the factor `Γ(θ) = (sinθcos²θ)^{α/3} ≤ sin(2θ)^{α/3}`).

## Route

`F_* = c₀·(Γ ⊗ φ)` with `c₀ = 2α/c(α) ≤ 20α`, `Γ(θ) = (sinθcos²θ)^{α/3}` and
`φ(z) = z/(1+z)²` (`Work.Spaces.hKer`), so every slot is a product of an angular
`D_θ`-iterate of `Γ` (bounded by `dthU_Gam_le` and `Γ ≤ sin(2θ)^{α/3}`) and a radial
`D_z`-iterate of `φ`.  The radial factor is the crux: `D_z = z·d/dz` in the Möbius chart
`x = (z-1)/(z+1)` becomes `Tmul P = ½(1-X²)P'` (`Work.FTS.CoercivityFix.E2Bound`), and
`Zop^[b] φ = φ·(R_b ∘ x)` where `R_b` is the polynomial recursion
`R_{b+1} = -X R_b + ½(1-X²)R_b'`; since `|x| ≤ 1` on `z > 0`, the coefficient sum of `R_b`
bounds the ratio.  Everything is then combined by the two master lemmas `FS.slot_le` /
`FS.slot_le_sin` and the arithmetic of `FS.Cst`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

namespace FS

open Work.FTS.CoercivityFix.E2Bound

/-! ## §1 The radial chart bound -/

/-- The polynomial recursion whose chart-side evaluation is the ratio
`Zop^[b] φ / φ` for `φ = z/(1+z)²`. -/
noncomputable def R : ℕ → Polynomial ℝ
  | 0 => 1
  | (b + 1) => -(Polynomial.X * R b)
      + Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative (R b)

lemma R_succ (b : ℕ) :
    R (b + 1) = -(Polynomial.X * R b)
      + Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative (R b) := rfl

lemma R_zero : R 0 = 1 := rfl

lemma deriv_Pphi : Polynomial.derivative Pphi = Polynomial.C (-(1 / 2)) * Polynomial.X := by
  simp only [Pphi_eq, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_one, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X]
  simp only [zero_mul, zero_sub, mul_one, Nat.reduceSub, pow_one]
  rw [zero_add, mul_neg, ← mul_assoc, ← Polynomial.C_mul]
  norm_num

lemma hC : Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative Pphi
    = -(Polynomial.X * Pphi) := by
  rw [deriv_Pphi, Pphi_eq]
  apply Polynomial.funext
  intro y
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
  ring

lemma Tmul_Pphi_mul (Q : Polynomial ℝ) :
    Tmul (Pphi * Q) = Pphi * (-(Polynomial.X * Q)
      + Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative Q) := by
  rw [Tmul_apply, Polynomial.derivative_mul]
  rw [show Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2)
        * (Polynomial.derivative Pphi * Q + Pphi * Polynomial.derivative Q)
      = (Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative Pphi) * Q
        + Pphi * (Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2)
            * Polynomial.derivative Q) from by ring]
  rw [hC]
  ring

lemma Tmul_iter_R (b : ℕ) : Tmul^[b] Pphi = Pphi * R b := by
  induction b with
  | zero => rw [Function.iterate_zero_apply, R_zero, mul_one]
  | succ b ih =>
      rw [Function.iterate_succ_apply', ih, Tmul_Pphi_mul, R_succ]

/-- The `Zop`-iterates of the profile `φ = z/(1+z)²` are the chart evaluations of
`Tmul^[b] Pphi`. -/
lemma Zop_iter_hKer_gpoly (b : ℕ) {z : ℝ} (hz : 0 < z) :
    Work.Spaces.Zop^[b] Work.Spaces.hKer z = gpoly (Tmul^[b] Pphi) z := by
  have hz1 : z ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; linarith
  have hEqOn : Set.EqOn Work.Spaces.hKer (gpoly Pphi) (Set.Ioi (-1)) := by
    intro w hw
    rw [Set.mem_Ioi] at hw
    rw [Work.Spaces.hKer_apply]
    exact (Work.FTS.CoercivityFix.E2Bound.SlotMul.phiZ_gpoly_eq
      (show 1 + w ≠ 0 by intro h; linarith)).symm
  rw [Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi hEqOn hz1]
  exact Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate Pphi b z hz

/-- The coefficient-sum constant bounding the `b`-th iterate of the chart variable. -/
noncomputable def RadK (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range ((R b).natDegree + 1), |(R b).coeff k|

lemma RadK_nonneg (b : ℕ) : 0 ≤ RadK b :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma hKer_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.hKer z := by
  rw [Work.Spaces.hKer_apply]
  positivity

/-- **The radial slot bound.**  For `z > 0` every `Zop`-iterate of the profile
`φ(z) = z/(1+z)²` is bounded by its own value. -/
lemma Zop_iter_hKer_le (b : ℕ) {z : ℝ} (hz : 0 < z) :
    |Work.Spaces.Zop^[b] Work.Spaces.hKer z| ≤ RadK b * Work.Spaces.hKer z := by
  rw [Zop_iter_hKer_gpoly b hz, Tmul_iter_R b]
  have hz1 : 1 + z ≠ 0 := by positivity
  have hp : gpoly (Pphi * R b) z = gpoly Pphi z * gpoly (R b) z := by
    simp only [gpoly_apply, Polynomial.eval_mul]
  rw [hp, Work.FTS.CoercivityFix.E2Bound.SlotMul.phiZ_gpoly_eq hz1,
    Work.Spaces.hKer_apply]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z / (1 + z) ^ 2)]
  have hx : |zchart z| ≤ 1 := Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hz
  have hb := Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff
    (R b) hx
  calc z / (1 + z) ^ 2 * |(R b).eval (zchart z)| ≤ z / (1 + z) ^ 2 * RadK b :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = RadK b * (z / (1 + z) ^ 2) := by ring

/-! ## §2 The constants -/

/-- The common radial constant: dominates `RadK j` for all `j ≤ 7`. -/
noncomputable def CK : ℝ := 1 + ∑ j ∈ Finset.range 8, RadK j

/-- The common angular constant: dominates `tBound i 0` for all `i ≤ 7`. -/
noncomputable def CT : ℝ := 1 + ∑ i ∈ Finset.range 8, Work.Spaces.tBound i 0

/-- The final constant of the slot estimate. -/
noncomputable def Cst : ℝ := 10000 * CK * CT

lemma CK_pos : 0 < CK := by
  have h0 : 0 ≤ ∑ j ∈ Finset.range 8, RadK j :=
    Finset.sum_nonneg (fun j _ => RadK_nonneg j)
  rw [CK]; linarith

lemma CT_pos : 0 < CT := by
  have h0 : 0 ≤ ∑ i ∈ Finset.range 8, Work.Spaces.tBound i 0 :=
    Finset.sum_nonneg (fun i _ => Work.Spaces.tBound_nonneg i 0)
  rw [CT]; linarith



lemma RadK_le_CK {j : ℕ} (hj : j ≤ 7) : RadK j ≤ CK := by
  have hmem : j ∈ Finset.range 8 := Finset.mem_range.mpr (by omega)
  have hsum : RadK j ≤ ∑ i ∈ Finset.range 8, RadK i :=
    Finset.single_le_sum (fun i _ => RadK_nonneg i) hmem
  rw [CK]
  have h0 : 0 ≤ ∑ i ∈ Finset.range 8, RadK i :=
    Finset.sum_nonneg fun i _ => RadK_nonneg i
  linarith

lemma tBound_le_CT {i : ℕ} (hi : i ≤ 7) : Work.Spaces.tBound i 0 ≤ CT := by
  have hmem : i ∈ Finset.range 8 := Finset.mem_range.mpr (by omega)
  have hsum : Work.Spaces.tBound i 0
      ≤ ∑ k ∈ Finset.range 8, Work.Spaces.tBound k 0 :=
    Finset.single_le_sum (fun k _ => Work.Spaces.tBound_nonneg k 0) hmem
  rw [CT]
  have h0 : 0 ≤ ∑ k ∈ Finset.range 8, Work.Spaces.tBound k 0 :=
    Finset.sum_nonneg fun k _ => Work.Spaces.tBound_nonneg k 0
  linarith

/-! ## §3 Angular bounds for the profile `Γ` -/

/-- The angular constant `max 1 (tBound (i-1) 0)`. -/
noncomputable def Amax (i : ℕ) : ℝ := max 1 (Work.Spaces.tBound (i - 1) 0)

lemma Amax_nonneg (i : ℕ) : 0 ≤ Amax i := by
  rw [Amax]; exact le_trans zero_le_one (le_max_left _ _)

lemma Amax_le_CT {i : ℕ} (hi : i ≤ 7) : Amax i ≤ CT := by
  rw [Amax]
  refine max_le ?_ ?_
  · rw [CT]
    have h0 : 0 ≤ ∑ k ∈ Finset.range 8, Work.Spaces.tBound k 0 :=
      Finset.sum_nonneg fun k _ => Work.Spaces.tBound_nonneg k 0
    linarith
  · exact tBound_le_CT (by omega)

/-- **The angular `i`-th `D_θ`-iterate of `Γ` is bounded by `Amax i`.** -/
lemma Lop_Gam_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ| ≤ Amax i := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp only [Function.iterate_zero, id_eq]
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_of_nonneg hG.1]
    calc Work.Spaces.Gam α θ ≤ 1 := hG.2
      _ ≤ Amax 0 := by
          rw [Amax]; exact le_max_left _ _
  · have h := Work.Spaces.dthU_Gam_le i hpos α hα hα1 θ hθ
    rw [Amax]
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have hT := Work.Spaces.tBound_nonneg (i - 1) 0
    have hαΓ : α * Work.Spaces.Gam α θ ≤ 1 := by nlinarith [hG.1, hG.2, hα.le, hα1]
    have h1 : α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ
        ≤ Work.Spaces.tBound (i - 1) 0 := by nlinarith [hT, hαΓ, hG.1]
    exact le_trans (le_trans h h1) (le_max_right _ _)

/-- **The angular `i`-th `D_θ`-iterate of `Γ` with the `sin(2θ)^{α/3}` weight.** -/
lemma Lop_Gam_le_sin (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {i : ℕ} (hi : 1 ≤ i) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound (i - 1) 0 * (Real.sin (2 * θ)) ^ (α / 3) := by
  refine le_trans (Work.Spaces.dthU_Gam_le i hi α hα hα1 θ hθ) ?_
  have hG := Work.Construction.Gam_le_sin_two_rpow hα hθ
  calc α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ
      ≤ α * Work.Spaces.tBound (i - 1) 0 * (Real.sin (2 * θ)) ^ (α / 3) :=
        mul_le_mul_of_nonneg_left hG
          (mul_nonneg hα.le (Work.Spaces.tBound_nonneg (i - 1) 0))

/-- Nonnegativity of the angular weight `sin(2θ)^{α/3}` on `Iθ`. -/
lemma sin_rpow_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (α / 3) :=
  Real.rpow_nonneg (Work.Construction.sin_two_nonneg_of_mem_Iθ hθ) _


/-! ## §4 The slot arithmetic -/

lemma slot_arith {α M φ CK' CT' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M)
    (hMle : M ≤ CT') (hφ : 0 ≤ φ) (hCK : 0 ≤ CK') (hCT : 0 ≤ CT') :
    20 * α * M * (CK' * φ) ≤ 10000 * CK' * CT' * α * φ := by
  have hX : 0 ≤ CK' * CT' * φ := by positivity
  have hY : 0 ≤ 20 * α * (CK' * φ) := by positivity
  have step1 : 20 * α * M * (CK' * φ) ≤ 20 * α * CT' * (CK' * φ) := by
    nlinarith [hMle, hY]
  have step4 : 20 * α * CT' * (CK' * φ) = 20 * (CK' * CT' * φ) * α := by ring
  have step5 : 10000 * CK' * CT' * α * φ = 10000 * (CK' * CT' * φ) * α := by ring
  have step6 : 20 * α * CT' * (CK' * φ) ≤ 10000 * (CK' * CT' * φ) * α := by
    rw [step4]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hX) hα.le
  rw [step5]
  exact le_trans step1 step6

lemma slot_arith_sin {α TB s φ CK' CT' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hTB : 0 ≤ TB)
    (hTBle : TB ≤ CT') (hs : 0 ≤ s) (hφ : 0 ≤ φ) (hCK : 0 ≤ CK') (hCT : 0 ≤ CT') :
    20 * α * (α * TB * s) * (CK' * φ) ≤ 10000 * CK' * CT' * α * s * φ := by
  have hα2 : α * α ≤ α := by nlinarith [hα1, hα.le]
  have hX : 0 ≤ CK' * CT' * φ := by positivity
  have hY : 0 ≤ 20 * TB * s * (CK' * φ) := by positivity
  have hY3 : 0 ≤ 20 * α * s * (CK' * φ) := by positivity
  have hY4 : 0 ≤ α * s := by positivity
  have step1 : 20 * α * (α * TB * s) * (CK' * φ) = 20 * (α * α) * TB * s * (CK' * φ) := by ring
  rw [step1]
  have step2 : 20 * (α * α) * TB * s * (CK' * φ) ≤ 20 * α * TB * s * (CK' * φ) := by
    nlinarith [hα.le, hα2, hY]
  have step3 : 20 * α * TB * s * (CK' * φ) ≤ 20 * α * CT' * s * (CK' * φ) := by
    nlinarith [hTBle, hY3]
  have step4 : 20 * α * CT' * s * (CK' * φ) = 20 * (CK' * CT' * φ) * (α * s) := by ring
  have step5 : 10000 * CK' * CT' * α * s * φ = 10000 * (CK' * CT' * φ) * (α * s) := by ring
  have step6 : 20 * (α * α) * TB * s * (CK' * φ) ≤ 20 * (CK' * CT' * φ) * (α * s) := by
    rw [← step4]
    exact le_trans step2 step3
  have hfin : 20 * (CK' * CT' * φ) * (α * s) ≤ 10000 * (CK' * CT' * φ) * (α * s) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hX) hY4
  rw [step5]
  exact le_trans step6 hfin

/-! ## §5 The master slot bounds -/

open Work.Construction in
/-- **The master slot bound.** -/
lemma slot_le {α c₀ MA K z θ : ℝ} {A ψ : ℝ → ℝ} {m : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc₀ : |c₀| ≤ 20 * α)
    (hA : |A θ| ≤ MA) (hMA : 0 ≤ MA) (hMAle : MA ≤ CT)
    (hrad : |Work.Spaces.Zop^[m] ψ z| ≤ K * Work.Spaces.hKer z)
    (hK : 0 ≤ K) (hKle : K ≤ CK) (hφ : 0 ≤ Work.Spaces.hKer z) :
    |(Work.Spaces.Zop^[m] (fun z => c₀ * ψ z) z) * A θ|
      ≤ Cst * α * Work.Spaces.hKer z := by
  rw [Work.Construction.Zop_iter_const_mul m c₀ ψ]
  have hrad' : |Work.Spaces.Zop^[m] ψ z| ≤ CK * Work.Spaces.hKer z :=
    le_trans hrad (mul_le_mul_of_nonneg_right hKle hφ)
  have h20 : 0 ≤ 20 * α * (CK * Work.Spaces.hKer z) :=
    mul_nonneg (by positivity) (mul_nonneg (le_of_lt CK_pos) hφ)
  have h2 : |c₀ * Work.Spaces.Zop^[m] ψ z| ≤ 20 * α * (CK * Work.Spaces.hKer z) := by
    rw [abs_mul]
    exact le_trans (mul_le_mul hc₀ hrad' (abs_nonneg _) (mul_nonneg (by norm_num) hα.le))
      (le_of_eq (by ring))
  calc |c₀ * Work.Spaces.Zop^[m] ψ z * A θ|
      = |c₀ * Work.Spaces.Zop^[m] ψ z| * |A θ| := by rw [abs_mul]
    _ ≤ (20 * α * (CK * Work.Spaces.hKer z)) * MA :=
        mul_le_mul h2 hA (abs_nonneg _) h20
    _ = 20 * α * MA * (CK * Work.Spaces.hKer z) := by ring
    _ ≤ 10000 * CK * CT * α * Work.Spaces.hKer z :=
        slot_arith hα hα1 hMA hMAle hφ (le_of_lt CK_pos) (le_of_lt CT_pos)
    _ = Cst * α * Work.Spaces.hKer z := by rw [Cst]

open Work.Construction in
/-- **The master slot bound, with the angular `sin(2θ)^{α/3}` weight.** -/
lemma slot_le_sin {α c₀ TB s K z θ : ℝ} {A ψ : ℝ → ℝ} {m : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc₀ : |c₀| ≤ 20 * α)
    (hA : |A θ| ≤ α * TB * s) (hTB : 0 ≤ TB) (hTBle : TB ≤ CT) (hs : 0 ≤ s)
    (hrad : |Work.Spaces.Zop^[m] ψ z| ≤ K * Work.Spaces.hKer z)
    (hK : 0 ≤ K) (hKle : K ≤ CK) (hφ : 0 ≤ Work.Spaces.hKer z) :
    |(Work.Spaces.Zop^[m] (fun z => c₀ * ψ z) z) * A θ|
      ≤ Cst * α * s * Work.Spaces.hKer z := by
  rw [Work.Construction.Zop_iter_const_mul m c₀ ψ]
  have hrad' : |Work.Spaces.Zop^[m] ψ z| ≤ CK * Work.Spaces.hKer z :=
    le_trans hrad (mul_le_mul_of_nonneg_right hKle hφ)
  have h20 : 0 ≤ 20 * α * (CK * Work.Spaces.hKer z) :=
    mul_nonneg (by positivity) (mul_nonneg (le_of_lt CK_pos) hφ)
  have h2 : |c₀ * Work.Spaces.Zop^[m] ψ z| ≤ 20 * α * (CK * Work.Spaces.hKer z) := by
    rw [abs_mul]
    exact le_trans (mul_le_mul hc₀ hrad' (abs_nonneg _) (mul_nonneg (by norm_num) hα.le))
      (le_of_eq (by ring))
  calc |c₀ * Work.Spaces.Zop^[m] ψ z * A θ|
      = |c₀ * Work.Spaces.Zop^[m] ψ z| * |A θ| := by rw [abs_mul]
    _ ≤ (20 * α * (CK * Work.Spaces.hKer z)) * (α * TB * s) :=
        mul_le_mul h2 hA (abs_nonneg _) h20
    _ = 20 * α * (α * TB * s) * (CK * Work.Spaces.hKer z) := by ring
    _ ≤ 10000 * CK * CT * α * s * Work.Spaces.hKer z :=
        slot_arith_sin hα hα1 hTB hTBle hs hφ (le_of_lt CK_pos) (le_of_lt CT_pos)
    _ = Cst * α * s * Work.Spaces.hKer z := by rw [Cst]

/-! ## §6 The four profiles in separated form -/

open Work.Construction in
/-- `F_* = c₀·(Γ ⊗ φ)` with `c₀ = 2α/c(α)` and `φ = z/(1+z)²`. -/
lemma fstar_sep (α : ℝ) :
    Work.Construction.Fstar α
      = Work.Construction.sepF (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z)
          (fun θ => Work.Spaces.Gam α θ) := by
  funext z θ
  simp only [Work.Construction.sepF, Work.Construction.Fstar, Work.FM.Fstar,
    Work.Spaces.hKer_apply]
  ring

open Work.Construction in
/-- `D_θ F_* = c₀·(D_θΓ ⊗ φ)`. -/
lemma dth_fstar_sep (α : ℝ) :
    Work.Spaces.Dth (Work.Construction.Fstar α)
      = Work.Construction.sepF (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z)
          (Work.Spaces.Lop (fun θ => Work.Spaces.Gam α θ)) := by
  have h := Work.Construction.sepF_DthIter 1
    (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) (fun θ => Work.Spaces.Gam α θ)
  rw [← fstar_sep α] at h
  simpa using h

open Work.Construction in
/-- `D_z F_* = c₀·(Γ ⊗ D_zφ)`. -/
lemma dz_fstar_sep (α : ℝ) :
    Work.Spaces.Dz (Work.Construction.Fstar α)
      = Work.Construction.sepF
          (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.Zop Work.Spaces.hKer z)
          (fun θ => Work.Spaces.Gam α θ) := by
  have h := Work.Construction.sepF_DzIter 1
    (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) (fun θ => Work.Spaces.Gam α θ)
  rw [← fstar_sep α] at h
  rw [show Work.Spaces.Zop^[1] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z)
      = fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.Zop^[1] Work.Spaces.hKer z from
        Work.Construction.Zop_iter_const_mul 1 (2 * α / Work.Spaces.c α) Work.Spaces.hKer]
    at h
  simpa using h


/-! ## §7 The six slot lemmas -/

lemma coef_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    |2 * α / Work.Spaces.c α| ≤ 20 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hc0)), div_le_iff₀ hc0]
  nlinarith


/-- The `D_θ`-iterate of `Γ` of index `i`, seen as the angular factor of `D_θ F_*`. -/
lemma Lop_succ_eq (i : ℕ) (Γ : ℝ → ℝ) :
    Work.Spaces.Lop^[i] (Work.Spaces.Lop Γ) = Work.Spaces.Lop^[i + 1] Γ :=
  (Function.iterate_succ_apply Work.Spaces.Lop i Γ).symm

lemma Zop_comp_hKer (j : ℕ) :
    Work.Spaces.Zop^[j] (Work.Spaces.Zop Work.Spaces.hKer)
      = Work.Spaces.Zop^[j + 1] Work.Spaces.hKer := by
  have h1 : Work.Spaces.Zop Work.Spaces.hKer
      = Work.Spaces.Zop^[1] Work.Spaces.hKer := (Function.iterate_one _).symm
  rw [h1]
  exact (Function.iterate_succ_apply Work.Spaces.Zop j Work.Spaces.hKer).symm

open Work.Construction in
lemma G0_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hji : j + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ|
      ≤ FS.Cst * α * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [fstar_sep α, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  exact slot_le hα hα1 (coef_le α hα hα1) (Lop_Gam_le α hα hα1 i hθ) (Amax_nonneg i)
    (Amax_le_CT (by omega)) (Zop_iter_hKer_le j hz) (RadK_nonneg j)
    (RadK_le_CK (by omega)) (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G0_le_sin {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hi : 1 ≤ i)
    (hji : j + i ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ|
      ≤ FS.Cst * α * (Real.sin (2 * θ)) ^ (α / 3) * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [fstar_sep α, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  exact slot_le_sin hα hα1 (coef_le α hα hα1) (Lop_Gam_le_sin α hα hα1 hi hθ)
    (Work.Spaces.tBound_nonneg _ _) (tBound_le_CT (by omega)) (sin_rpow_nonneg hθ)
    (Zop_iter_hKer_le j hz) (RadK_nonneg j) (RadK_le_CK (by omega))
    (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G1_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hji : j + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ|
      ≤ FS.Cst * α * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i + 1] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [dth_fstar_sep α, Work.Construction.sepF_mixed,
      Lop_succ_eq i (fun t => Work.Spaces.Gam α t)]
    rfl
  rw [hmix]
  refine slot_le hα hα1 (coef_le α hα hα1) ?_ (Amax_nonneg (i + 1))
    (Amax_le_CT (by omega)) (Zop_iter_hKer_le j hz) (RadK_nonneg j)
    (RadK_le_CK (by omega)) (le_of_lt (hKer_pos hz))
  exact Lop_Gam_le α hα hα1 (i + 1) hθ

open Work.Construction in
lemma G1_le_sin {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hi : 1 ≤ i)
    (hji : j + i ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ|
      ≤ FS.Cst * α * (Real.sin (2 * θ)) ^ (α / 3) * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i + 1] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [dth_fstar_sep α, Work.Construction.sepF_mixed,
      Lop_succ_eq i (fun t => Work.Spaces.Gam α t)]
    rfl
  rw [hmix]
  have hA : |Work.Spaces.Lop^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound i 0 * (Real.sin (2 * θ)) ^ (α / 3) := by
    simpa using Lop_Gam_le_sin α hα hα1 (i := i + 1) (by omega) hθ
  exact slot_le_sin hα hα1 (coef_le α hα hα1) hA
    (Work.Spaces.tBound_nonneg i 0) (tBound_le_CT (by omega)) (sin_rpow_nonneg hθ)
    (Zop_iter_hKer_le j hz) (RadK_nonneg j) (RadK_le_CK (by omega))
    (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G2_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hji : j + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ|
      ≤ FS.Cst * α * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ
      = (Work.Spaces.Zop^[j]
          (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.Zop Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [dz_fstar_sep α, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  have hrad : |Work.Spaces.Zop^[j] (Work.Spaces.Zop Work.Spaces.hKer) z|
      ≤ RadK (j + 1) * Work.Spaces.hKer z := by
    rw [Zop_comp_hKer j]
    exact Zop_iter_hKer_le (j + 1) hz
  exact slot_le hα hα1 (coef_le α hα hα1) (Lop_Gam_le α hα hα1 i hθ) (Amax_nonneg i)
    (Amax_le_CT (by omega)) hrad (RadK_nonneg (j + 1))
    (RadK_le_CK (by omega)) (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G2_le_sin {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hi : 1 ≤ i)
    (hji : j + i ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ|
      ≤ FS.Cst * α * (Real.sin (2 * θ)) ^ (α / 3) * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ
      = (Work.Spaces.Zop^[j]
          (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.Zop Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [dz_fstar_sep α, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  have hrad : |Work.Spaces.Zop^[j] (Work.Spaces.Zop Work.Spaces.hKer) z|
      ≤ RadK (j + 1) * Work.Spaces.hKer z := by
    rw [Zop_comp_hKer j]
    exact Zop_iter_hKer_le (j + 1) hz
  exact slot_le_sin hα hα1 (coef_le α hα hα1) (Lop_Gam_le_sin α hα hα1 hi hθ)
    (Work.Spaces.tBound_nonneg _ _) (tBound_le_CT (by omega)) (sin_rpow_nonneg hθ)
    hrad (RadK_nonneg (j + 1)) (RadK_le_CK (by omega))
    (le_of_lt (hKer_pos hz))



end FS

/-! ## The target -/


end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Star6 =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

variable {α Cs : ℝ} {Φs : Fn}

/-! ## The five fields, split into membership and bound -/

/-- The `ℛ`-field `((z+1)/z)·ℛ(Φ̃_*)` lies in `𝒲^{6,∞}`. -/
theorem StarPkg6.RW6_mem (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) :=
  h.RW6.1

/-- Its `𝒲^{6,∞}`-norm is bounded by `Cs·α`. -/
theorem StarPkg6.RW6_bd (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ)
      ≤ Cs * α :=
  h.RW6.2



/-- The weighted `V`-field `((z+1)/z)·V(Φ̃_*)` lies in `𝒲^{6,∞}`. -/
theorem StarPkg6.VzW6_mem (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) :=
  h.VzW6.1

/-- Its `𝒲^{6,∞}`-norm is bounded by `Cs·α`. -/
theorem StarPkg6.VzW6_bd (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
      ≤ Cs * α :=
  h.VzW6.2



/-- The weighted `U/ sin 2θ`-field `((z+1)/z)·U(Φ̃_*)/sin 2θ` lies in `𝒲^{6,∞}`. -/
theorem StarPkg6.UszW6_mem (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)) :=
  h.UszW6.1

/-- Its `𝒲^{6,∞}`-norm is bounded by `Cs·α`. -/
theorem StarPkg6.UszW6_bd (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)) ≤ Cs * α :=
  h.UszW6.2

end Work.FTS.StrongPersist
end
end
