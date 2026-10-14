import ChallengeDeps
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.Vth_barrier =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.RegPkgGal.R7d


end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.trajectory_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

open Set Filter
open scoped Topology

/-- The first coordinate of a curve with values in `ℝ × ℝ` is differentiable, with the first
coordinate of the derivative. -/
theorem hasDerivAt_fst {α : ℝ → ℝ × ℝ} {x : ℝ} {v : ℝ × ℝ} (h : HasDerivAt α v x) :
    HasDerivAt (fun y => (α y).1) v.1 x := by
  rw [hasDerivAt_iff_hasFDerivAt] at h
  have h2 : HasFDerivAt (fun y => (α y).1)
      (ContinuousLinearMap.toSpanSingleton ℝ v.1) x := by
    have hh := h.fst
    convert hh using 1
    ext w
    simp [ContinuousLinearMap.comp_apply]
  simpa using h2.hasDerivAt

/-- The second coordinate of a curve with values in `ℝ × ℝ` is differentiable, with the second
coordinate of the derivative. -/
theorem hasDerivAt_snd {α : ℝ → ℝ × ℝ} {x : ℝ} {v : ℝ × ℝ} (h : HasDerivAt α v x) :
    HasDerivAt (fun y => (α y).2) v.2 x := by
  rw [hasDerivAt_iff_hasFDerivAt] at h
  have h2 : HasFDerivAt (fun y => (α y).2)
      (ContinuousLinearMap.toSpanSingleton ℝ v.2) x := by
    have hh := h.snd
    convert hh using 1
    ext w
    simp [ContinuousLinearMap.comp_apply]
  simpa using h2.hasDerivAt


end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.Top.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-- `ℝ³`, definitionally `Work.LWP.R3`, `Work.StabilityFar.R3`, `Work.Cyl.R3` and
`Work.FTS.Physical.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **A finite-time blow-up of the incompressible Euler equation at time `T > 0`.**

This is the audit's `N0` interface: a pair `(p, u)` defined on `ℝ³ × [0,T)` such that

* `(p,u)` solves the incompressible Euler equation (`IsLocalEulerEquationSolution`, the *fixed*
  `ChallengeDeps` structure) with initial datum `u(·,0)`;
* the datum `u(·,0)` is divergence-free, odd, of class `C^{1,α}(ℝ³)`, and its vorticity decays
  like `‖x‖^{-α}` — the four datum clauses of the challenge statement;
* the solution is odd at every time `t ∈ [0,T)`;
* `u.uncurry` is jointly `C^{1,α}` on every strip `ℝ³ × [0,S]` with `S < T` — the strict part of
  the challenge's statement (it includes `∂ₜu`; see the audit §1 and §4-N7);
* the vorticity sup-norm dominates `c/(T-t)` on `[0,T)`, which is the quantitative form of the
  blow-up and the input of the Beale–Kato–Majda divergence.

Nothing is assumed *at* or *past* `T`. -/
structure BlowupAt (α : ℝ≥0) (T : ℝ) where
  /-- the velocity field -/
  u : R3 → ℝ → R3
  /-- the pressure field -/
  p : R3 → ℝ → ℝ
  /-- the blow-up time is positive -/
  hT : 0 < T
  /-- `(p,u)` solves the incompressible Euler equation on `[0,T)` with initial datum `u(·,0)` -/
  sol : IsLocalEulerEquationSolution p (u · 0) T u
  /-- the initial datum is divergence-free -/
  div0 : div (u · 0) = 0
  /-- the solution is odd at every time -/
  odd : ∀ t ∈ Set.Ico 0 T, IsOdd (u · t)
  /-- the initial datum is of class `C^{1,α}(ℝ³)` -/
  cdh0 : IsContDiffHolder ℝ α (u · 0)
  /-- the vorticity of the initial datum decays like `‖x‖^{-α}` -/
  decay0 : ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity (u · 0) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)
  /-- joint `C^{1,α}` regularity of `u.uncurry` on every strip `ℝ³ × [0,S]`, `S < T` -/
  strip : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)
  /-- the vorticity sup-norm blows up at least like `c/(T-t)` -/
  lower : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf u t

namespace BlowupAt

variable {α : ℝ≥0} {T : ℝ}






end BlowupAt

end Work.FTS.Top
end
-- ===== merged: Submission.Work.FTS.TransportS.T2SupB2.TvSub.tv_bound_subinterval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.T2SupB2.TvSub

open MeasureTheory

/-- On a subinterval `[a,b]` of `(0, π/2)` the profile weight is positive. -/
theorem sin_two_pos_of_mem_Icc {a b t : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2)
    (ht : t ∈ Set.Icc a b) : 0 < Real.sin (2 * t) := by
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) ?_
  linarith [ht.2, hb]

/-- **A point below the average**, on an arbitrary interval `[a,b]` with `a < b`: a function
integrable there is at most its own average `(b-a)⁻¹ ∫_{[a,b]} f` at some point of `[a,b]`.
(No continuity is needed; it is the minimum of an integrable function versus its mean.) -/
theorem exists_min_le_average_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hint : IntegrableOn f (Set.Icc a b)) :
    ∃ θ₀ ∈ Set.Icc a b, f θ₀ ≤ (b - a)⁻¹ * ∫ t in Set.Icc a b, f t := by
  have hμ0 : volume (Set.Icc a b) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hμtop : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨x, hx, hle⟩ := exists_le_setAverage (μ := volume) (s := Set.Icc a b)
    (f := f) hμ0 hμtop hint
  refine ⟨x, hx, ?_⟩
  rw [setAverage_eq volume f (Set.Icc a b), Real.volume_real_Icc_of_le hab.le,
    smul_eq_mul] at hle
  exact hle

/-- For `a ≤ u ≤ v ≤ b`, the interval integral of a nonnegative function is at most its set
integral over `Icc a b`. -/
theorem intervalIntegral_le_setIntegral_Icc {p : ℝ → ℝ} {a b u v : ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hpnn : ∀ t ∈ Set.Icc a b, 0 ≤ p t)
    (hpint : IntegrableOn p (Set.Icc a b)) :
    ∫ t in u..v, p t ≤ ∫ t in Set.Icc a b, p t := by
  rw [intervalIntegral.integral_of_le huv]
  refine setIntegral_mono_set hpint ?_ ?_
  · exact ae_restrict_of_forall_mem measurableSet_Icc hpnn
  · exact Filter.Eventually.of_forall fun t ht =>
      ⟨le_trans hau ht.1.le, le_trans ht.2 hvb⟩

/-- **The total-variation bound, integrated form, over a subinterval.**  Same as
`TvUniform.integral_tv_le`, with the outer interval `[0, π/2]` replaced by `[a,b]`. -/
theorem integral_tv_le_Icc {F p q : ℝ → ℝ} {a b u v : ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hFpq : Set.EqOn F (fun θ => 2 * (Real.sqrt (p θ) * Real.sqrt (q θ))) (Set.Ioo u v))
    (hpnn : ∀ θ ∈ Set.Icc a b, 0 ≤ p θ)
    (hqnn : ∀ θ ∈ Set.Icc a b, 0 ≤ q θ)
    (hpint : IntegrableOn p (Set.Icc a b))
    (hqint : IntegrableOn q (Set.Icc a b)) :
    ∫ θ in u..v, F θ
      ≤ 2 * Real.sqrt ((∫ θ in Set.Icc a b, p θ) * (∫ θ in Set.Icc a b, q θ)) := by
  have hsub : Set.Ioc u v ⊆ Set.Icc a b := fun x hx =>
    ⟨le_trans hau hx.1.le, le_trans hx.2 hvb⟩
  have hpI : IntegrableOn p (Set.Ioc u v) := hpint.mono_set hsub
  have hqI : IntegrableOn q (Set.Ioc u v) := hqint.mono_set hsub
  have hpn' : 0 ≤ᵐ[volume.restrict (Set.Ioc u v)] p :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hpnn x (hsub hx)
  have hqn' : 0 ≤ᵐ[volume.restrict (Set.Ioc u v)] q :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hqnn x (hsub hx)
  have hCS := Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
    (volume.restrict (Set.Ioc u v)) hpn' hqn' hpI hqI
  have hCS' : ∫ θ in Set.Ioc u v, Real.sqrt (p θ) * Real.sqrt (q θ)
      ≤ Real.sqrt (∫ θ in Set.Ioc u v, p θ) * Real.sqrt (∫ θ in Set.Ioc u v, q θ) := hCS
  have hIp' : ∫ θ in Set.Ioc u v, p θ ≤ ∫ θ in Set.Icc a b, p θ := by
    rw [← intervalIntegral.integral_of_le huv]
    exact intervalIntegral_le_setIntegral_Icc hau huv hvb hpnn hpint
  have hIq' : ∫ θ in Set.Ioc u v, q θ ≤ ∫ θ in Set.Icc a b, q θ := by
    rw [← intervalIntegral.integral_of_le huv]
    exact intervalIntegral_le_setIntegral_Icc hau huv hvb hqnn hqint
  have hA0 : 0 ≤ ∫ θ in Set.Icc a b, p θ := setIntegral_nonneg measurableSet_Icc hpnn
  have hstep : ∫ θ in Set.Ioc u v, Real.sqrt (p θ) * Real.sqrt (q θ)
      ≤ Real.sqrt (∫ θ in Set.Icc a b, p θ) * Real.sqrt (∫ θ in Set.Icc a b, q θ) :=
    le_trans hCS' (mul_le_mul (Real.sqrt_le_sqrt hIp') (Real.sqrt_le_sqrt hIq')
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hcongr : ∫ θ in u..v, F θ
      = ∫ θ in u..v, 2 * (Real.sqrt (p θ) * Real.sqrt (q θ)) :=
    intervalIntegral.integral_congr_Ioo_of_le huv hFpq
  rw [hcongr, intervalIntegral.integral_const_mul]
  calc 2 * ∫ θ in u..v, Real.sqrt (p θ) * Real.sqrt (q θ)
      = 2 * ∫ θ in Set.Ioc u v, Real.sqrt (p θ) * Real.sqrt (q θ) := by
        rw [intervalIntegral.integral_of_le huv]
    _ ≤ 2 * (Real.sqrt (∫ θ in Set.Icc a b, p θ)
          * Real.sqrt (∫ θ in Set.Icc a b, q θ)) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 2 * Real.sqrt ((∫ θ in Set.Icc a b, p θ) * (∫ θ in Set.Icc a b, q θ)) := by
        rw [Real.sqrt_mul hA0]

-- `hcont` is part of the assigned statement but is not needed by the argument: the minimum of an
-- integrable function lies below its mean without any continuity assumption.
set_option linter.unusedVariables false in
theorem tv_bound_subinterval {Ξ Ξ₁ : ℝ → ℝ} {c a b x : ℝ}
    (hab : a < b) (ha : 0 < a) (hb : b < Real.pi / 2)
    (hx : x ∈ Set.Icc a b)
    (hcont : ContinuousOn Ξ (Set.Icc a b))
    (hΞnn : ∀ t ∈ Set.Icc a b, 0 ≤ Ξ t)
    (hΞ₁nn : ∀ t ∈ Set.Icc a b, 0 ≤ Ξ₁ t)
    (hTV : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      |Ξ v - Ξ u| ≤ ∫ t in u..v, 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t))
    (hintΞ : MeasureTheory.IntegrableOn Ξ (Set.Icc a b))
    (hintA : MeasureTheory.IntegrableOn
      (fun t : ℝ => Ξ t * (Real.sin (2 * t)) ^ (-c)) (Set.Icc a b))
    (hintB : MeasureTheory.IntegrableOn
      (fun t : ℝ => Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2)) (Set.Icc a b)) :
    Ξ x ≤ (2 / (b - a)) * (∫ t in Set.Icc a b, Ξ t)
      + 2 * Real.sqrt
          ((∫ t in Set.Icc a b, Ξ t * (Real.sin (2 * t)) ^ (-c))
            * (∫ t in Set.Icc a b, Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))) := by
  -- a point of `[a,b]` at which `Ξ` is below its average
  obtain ⟨θ₀, hθ₀, hθ₀le⟩ := exists_min_le_average_Icc (f := Ξ) hab hintΞ
  have hI0 : 0 ≤ ∫ t in Set.Icc a b, Ξ t := setIntegral_nonneg measurableSet_Icc hΞnn
  have hθ₀le' : Ξ θ₀ ≤ (2 / (b - a)) * (∫ t in Set.Icc a b, Ξ t) := by
    have h1 : (b - a)⁻¹ ≤ 2 / (b - a) := by
      rw [div_eq_mul_inv]
      have h2 : (0 : ℝ) ≤ (b - a)⁻¹ := inv_nonneg.mpr (by linarith)
      linarith
    have h2 : (b - a)⁻¹ * (∫ t in Set.Icc a b, Ξ t)
        ≤ (2 / (b - a)) * (∫ t in Set.Icc a b, Ξ t) :=
      mul_le_mul_of_nonneg_right h1 hI0
    exact le_trans hθ₀le h2
  -- nonnegativity of the two weighted profiles on `[a,b]`
  have hpnn : ∀ t ∈ Set.Icc a b,
      0 ≤ Ξ t * (Real.sin (2 * t)) ^ (-c) := fun t ht =>
    mul_nonneg (hΞnn t ht) (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Icc ha hb ht)) _)
  have hqnn : ∀ t ∈ Set.Icc a b,
      0 ≤ Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2) := fun t ht =>
    mul_nonneg (hΞ₁nn t ht) (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Icc ha hb ht)) _)
  -- the pointwise identification of the two forms of the total-variation integrand
  have hFpq : ∀ {u v : ℝ}, a ≤ u → v ≤ b →
      Set.EqOn (fun t => 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t))
        (fun t => 2 * (Real.sqrt (Ξ t * (Real.sin (2 * t)) ^ (-c))
          * Real.sqrt (Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2)))) (Set.Ioo u v) := by
    intro u v hau hvb t ht
    have htA : t ∈ Set.Icc a b := ⟨le_trans hau ht.1.le, le_trans ht.2.le hvb⟩
    have ht0 : 0 < t := lt_of_lt_of_le ha htA.1
    have ht1 : t < Real.pi / 2 := lt_of_le_of_lt htA.2 hb
    have h := Work.FTS.TransportS.TvUniform.csc_sqrt_specialise (c := c) ⟨ht0, ht1⟩
      (hΞnn t htA) (hΞ₁nn t htA)
    simpa only [mul_assoc] using h
  -- the uniform bound for the total variation between `x` and `θ₀`
  have hTVb : |Ξ x - Ξ θ₀| ≤ 2 * Real.sqrt
      ((∫ t in Set.Icc a b, Ξ t * (Real.sin (2 * t)) ^ (-c))
        * (∫ t in Set.Icc a b, Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))) := by
    rcases le_total x θ₀ with hle | hle
    · have h1 := hTV x θ₀ hx.1 hle hθ₀.2
      have h2 := integral_tv_le_Icc
        (F := fun t => 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t))
        (p := fun t => Ξ t * (Real.sin (2 * t)) ^ (-c))
        (q := fun t => Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))
        hx.1 hle hθ₀.2 (hFpq hx.1 hθ₀.2) hpnn hqnn hintA hintB
      rw [abs_sub_comm]
      exact le_trans h1 h2
    · have h1 := hTV θ₀ x hθ₀.1 hle hx.2
      have h2 := integral_tv_le_Icc
        (F := fun t => 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t))
        (p := fun t => Ξ t * (Real.sin (2 * t)) ^ (-c))
        (q := fun t => Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))
        hθ₀.1 hle hx.2 (hFpq hθ₀.1 hx.2) hpnn hqnn hintA hintB
      exact le_trans h1 h2
  calc Ξ x = Ξ θ₀ + (Ξ x - Ξ θ₀) := by ring
    _ ≤ Ξ θ₀ + |Ξ x - Ξ θ₀| := by linarith [le_abs_self (Ξ x - Ξ θ₀)]
    _ ≤ (2 / (b - a)) * (∫ t in Set.Icc a b, Ξ t)
        + 2 * Real.sqrt
            ((∫ t in Set.Icc a b, Ξ t * (Real.sin (2 * t)) ^ (-c))
              * (∫ t in Set.Icc a b, Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))) :=
        add_le_add hθ₀le' hTVb

end Work.FTS.TransportS.T2SupB2.TvSub
end
-- ===== merged: Submission.Work.FTS.TransportS.TvUniform.tv_uniform_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.TvUniform

open MeasureTheory

/-- `sin (2θ) ≥ 0` on the interval `[0, π/2]`. -/
theorem sin_two_nonneg_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩




end Work.FTS.TransportS.TvUniform
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.noDecayPieces.false_of_log_divergence =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.noDecayPieces

theorem false_of_log_divergence {g : ℝ → ℝ} {z c : ℝ}
    (hz : 0 < z) (hc : 0 < c)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] g)
    (hg : ∀ x, z ≤ x → c / x ≤ g x) : False :=
  Work.FTS_RXTPieces.noDecayPieces.false_of_log_divergence hz hc hint hnn hg

end Work.FTS_RegExport.RXT.noDecayPieces
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.noDecayPieces.le_sub_setIntegral_of_deriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.noDecayPieces

theorem le_sub_setIntegral_of_deriv_le {F F' G : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Ioi (0 : ℝ)))
    (hmeas : MeasureTheory.AEStronglyMeasurable F' (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' x) x)
    (hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |F' x| ≤ G x)
    (hGint : MeasureTheory.IntegrableOn G (Set.Ioi 0))
    (hGnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] G)
    {z : ℝ} (hz : 0 < z) :
    ∀ x, z ≤ x → F z - (∫ t in Set.Ioi 0, G t) ≤ F x :=
  Work.FTS_RXTPieces.noDecayPieces.le_sub_setIntegral_of_deriv_le
    hcont hmeas hderiv hbd hGint hGnn hz

end Work.FTS_RegExport.RXT.noDecayPieces
end
-- ===== merged: Submission.Work.H2.T1Q.Cutoff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The cutoff function `χ` of the `T1` estimate

This file constructs the smooth cutoff `χ ζ θ` (with a uniform constant `B`) used to localise
the `θ`-variable away from the two singular ends `θ = 0` and `θ = π/2` of the quadrant, with a
*uniform in `ζ`* bound on `|sin (2θ) · ∂_θ χ ζ θ|`.

The construction is the product `χ ζ θ = φ_ζ θ · ψ_ζ θ` of two rescalings of Mathlib's smooth
step function `Real.smoothTransition`:

* `φ ζ θ = smoothTransition (2/ζ · θ - 1)` rises from `0` at `θ = ζ/2` to `1` at `θ = ζ`;
* `ψ ζ θ = smoothTransition (2/ζ · (π/2 - ζ/2) - 2/ζ · θ)` falls from `1` at `θ = π/2 - ζ`
  to `0` at `θ = π/2 - ζ/2`.

Hence `χ ζ θ = 1` on `[ζ, π/2 - ζ]`, `χ ζ θ = 0` on `[0, ζ/2] ∪ [π/2 - ζ/2, π/2]`, and the
derivative is supported in the two windows `(ζ/2, ζ)` and `(π/2 - ζ, π/2 - ζ/2)`. In either
window `|sin (2θ)| ≤ 2ζ`, so `|∂_θ χ| ≤ 4/ζ · (number of active factors)` and
`|sin (2θ) ∂_θ χ| ≤ 8 M`, with `M` a bound for `|deriv smoothTransition|`.
-/

open scoped Real Topology
open Filter Set

noncomputable section

namespace Work.H2.T1Q

/-- The rising factor: `φ_ζ θ = smoothTransition (2/ζ · θ - 1)`. -/
def phi (ζ : ℝ) : ℝ → ℝ := fun t => Real.smoothTransition (2 / ζ * t - 1)

/-- The falling factor: `ψ_ζ θ = smoothTransition (2/ζ · (π/2 - ζ/2) - 2/ζ · θ)`. -/
def psi (ζ : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * t)

/-- The cutoff `χ ζ = φ_ζ · ψ_ζ`. -/
def chiFun (ζ : ℝ) : ℝ → ℝ := phi ζ * psi ζ

private lemma contDiff_phi (ζ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phi ζ) := by
  unfold phi; fun_prop

private lemma contDiff_psi (ζ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psi ζ) := by
  unfold psi; fun_prop

theorem Cutoff : ∃ (chi : ℝ → ℝ → ℝ) (B : ℝ), 0 < B ∧
    (∀ ζ : ℝ, ContDiff ℝ (⊤ : ℕ∞) (chi ζ)) ∧
    (∀ ζ θ : ℝ, 0 ≤ chi ζ θ) ∧ (∀ ζ θ : ℝ, chi ζ θ ≤ 1) ∧
    (∀ ζ θ : ℝ, 0 < ζ → ζ ≤ θ → θ ≤ π / 2 - ζ → chi ζ θ = 1) ∧
    (∀ ζ θ : ℝ, 0 < ζ → θ ≤ ζ / 2 → chi ζ θ = 0) ∧
    (∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 ≤ θ → chi ζ θ = 0) ∧
    (∀ ζ θ : ℝ, 0 < ζ → θ < ζ / 2 → deriv (chi ζ) θ = 0) ∧
    (∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 < θ → deriv (chi ζ) θ = 0) ∧
    (∀ ζ : ℝ, 0 < ζ → ∀ θ : ℝ, |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B) ∧
    (∀ θ : ℝ, 0 < θ → θ < π / 2 →
      Filter.Tendsto (fun ζ : ℝ => chi ζ θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1))
    := by
  obtain ⟨hderiv_nonpos, hderiv_one_le, M, hM0, hMbd⟩ := SmoothTransitionDeriv
  refine ⟨chiFun, max (8 * M) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness in `θ`
    intro ζ
    exact (contDiff_phi ζ).mul (contDiff_psi ζ)
  · -- nonnegativity
    intro ζ θ
    show 0 ≤ phi ζ θ * psi ζ θ
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · -- upper bound `1`
    intro ζ θ
    show phi ζ θ * psi ζ θ ≤ 1
    calc phi ζ θ * psi ζ θ ≤ 1 * psi ζ θ :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
            (Real.smoothTransition.nonneg _)
      _ = psi ζ θ := one_mul _
      _ ≤ 1 := Real.smoothTransition.le_one _
  · -- `χ = 1` on the middle interval
    intro ζ θ hζ h1 h2
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hA : 1 ≤ 2 / ζ * θ - 1 := by
      have hle : 2 / ζ * ζ ≤ 2 / ζ * θ := mul_le_mul_of_nonneg_left h1 h2ζ.le
      have hval : 2 / ζ * ζ = 2 := div_mul_cancel₀ 2 hζ.ne'
      linarith
    have hB : 1 ≤ 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ := by
      have hle : 2 / ζ * θ ≤ 2 / ζ * (Real.pi / 2 - ζ) :=
        mul_le_mul_of_nonneg_left h2 h2ζ.le
      have hval : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * (Real.pi / 2 - ζ) = 1 := by
        field_simp
        ring
      linarith
    show phi ζ θ * psi ζ θ = 1
    rw [show phi ζ θ = 1 from Real.smoothTransition.one_of_one_le hA,
        show psi ζ θ = 1 from Real.smoothTransition.one_of_one_le hB, mul_one]
  · -- `χ = 0` for `θ ≤ ζ/2`
    intro ζ θ hζ h
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hA : 2 / ζ * θ - 1 ≤ 0 := by
      have hle : 2 / ζ * θ ≤ 2 / ζ * (ζ / 2) := mul_le_mul_of_nonneg_left h h2ζ.le
      have hval : 2 / ζ * (ζ / 2) = 1 := by field_simp
      linarith
    show phi ζ θ * psi ζ θ = 0
    rw [show phi ζ θ = 0 from Real.smoothTransition.zero_of_nonpos hA, zero_mul]
  · -- `χ = 0` for `π/2 - ζ/2 ≤ θ`
    intro ζ θ hζ h
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hB : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ ≤ 0 := by
      have hle : 2 / ζ * (Real.pi / 2 - ζ / 2) ≤ 2 / ζ * θ :=
        mul_le_mul_of_nonneg_left h h2ζ.le
      linarith
    show phi ζ θ * psi ζ θ = 0
    rw [show psi ζ θ = 0 from Real.smoothTransition.zero_of_nonpos hB, mul_zero]
  · -- `deriv χ = 0` for `θ < ζ/2`
    intro ζ θ hζ hθ
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hev : chiFun ζ =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hθ] with t ht
      have hA : 2 / ζ * t - 1 ≤ 0 := by
        have hle : 2 / ζ * t ≤ 2 / ζ * (ζ / 2) := mul_le_mul_of_nonneg_left ht.le h2ζ.le
        have hval : 2 / ζ * (ζ / 2) = 1 := by field_simp
        linarith
      show phi ζ t * psi ζ t = 0
      rw [show phi ζ t = 0 from Real.smoothTransition.zero_of_nonpos hA, zero_mul]
    rw [hev.deriv_eq]
    exact deriv_const θ 0
  · -- `deriv χ = 0` for `π/2 - ζ/2 < θ`
    intro ζ θ hζ hθ
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hev : chiFun ζ =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hθ] with t ht
      have hB : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * t ≤ 0 := by
        have hle : 2 / ζ * (Real.pi / 2 - ζ / 2) < 2 / ζ * t :=
          mul_lt_mul_of_pos_left ht h2ζ
        linarith
      show phi ζ t * psi ζ t = 0
      rw [show psi ζ t = 0 from Real.smoothTransition.zero_of_nonpos hB, mul_zero]
    rw [hev.deriv_eq]
    exact deriv_const θ 0
  · -- the uniform weighted derivative bound
    intro ζ hζ θ
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hdphi : deriv (phi ζ) θ = deriv Real.smoothTransition (2 / ζ * θ - 1) * (2 / ζ) := by
      unfold phi
      have h1 : HasDerivAt (fun t : ℝ => 2 / ζ * t - 1) (2 / ζ) θ := by
        simpa using (((hasDerivAt_id θ).const_mul (2 / ζ)).sub_const 1)
      have h2 : DifferentiableAt ℝ Real.smoothTransition (2 / ζ * θ - 1) := by fun_prop
      exact (h2.hasDerivAt.comp θ h1).deriv
    have hdpsi : deriv (psi ζ) θ =
        deriv Real.smoothTransition (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ) * (-(2 / ζ)) := by
      unfold psi
      have h1 : HasDerivAt (fun t : ℝ => 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * t)
          (-(2 / ζ)) θ := by
        have hh := (hasDerivAt_id θ).const_mul (2 / ζ)
        simpa using hh.const_sub (2 / ζ * (Real.pi / 2 - ζ / 2))
      have h2 : DifferentiableAt ℝ Real.smoothTransition
          (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ) := by fun_prop
      exact (h2.hasDerivAt.comp θ h1).deriv
    have hdmul : deriv (chiFun ζ) θ = deriv (phi ζ) θ * psi ζ θ + phi ζ θ * deriv (psi ζ) θ := by
      have d1 : DifferentiableAt ℝ (phi ζ) θ := by unfold phi; fun_prop
      have d2 : DifferentiableAt ℝ (psi ζ) θ := by unfold psi; fun_prop
      unfold chiFun
      exact deriv_mul d1 d2
    have hphi_le : |phi ζ θ| ≤ 1 := by
      unfold phi
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have hpsi_le : |psi ζ θ| ≤ 1 := by
      unfold psi
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have hb_phi : |Real.sin (2 * θ)| * |deriv (phi ζ) θ| ≤ 4 * M := by
      rw [hdphi, abs_mul, abs_of_pos h2ζ]
      by_cases hA : 0 < 2 / ζ * θ - 1 ∧ 2 / ζ * θ - 1 < 1
      · have hwin : ζ / 2 < θ ∧ θ < ζ := by
          obtain ⟨hA1, hA2⟩ := hA
          have h1 : 1 < 2 / ζ * θ := by linarith
          have h2 : 2 / ζ * θ < 2 := by linarith
          have h3 : ζ < 2 * θ := by
            rw [div_mul_eq_mul_div] at h1
            have := (lt_div_iff₀ hζ).mp h1
            simpa using this
          have h4 : 2 * θ < 2 * ζ := by
            rw [div_mul_eq_mul_div] at h2
            have := (div_lt_iff₀ hζ).mp h2
            simpa using this
          constructor <;> linarith
        have hsin4 : |Real.sin (2 * θ)| * (2 / ζ) ≤ 4 := SinRatioBound hζ (Or.inl hwin)
        calc |Real.sin (2 * θ)| * (|deriv Real.smoothTransition (2 / ζ * θ - 1)| * (2 / ζ))
            ≤ |Real.sin (2 * θ)| * (M * (2 / ζ)) := by
              gcongr
              exact hMbd _
          _ = M * (|Real.sin (2 * θ)| * (2 / ζ)) := by ring
          _ ≤ M * 4 := mul_le_mul_of_nonneg_left hsin4 hM0
          _ = 4 * M := by ring
      · have hz : deriv Real.smoothTransition (2 / ζ * θ - 1) = 0 := by
          rcases not_and_or.mp hA with h | h
          · exact hderiv_nonpos _ (not_lt.mp h)
          · exact hderiv_one_le _ (not_lt.mp h)
        rw [hz, abs_zero, zero_mul, mul_zero]
        exact mul_nonneg (by norm_num) hM0
    have hb_psi : |Real.sin (2 * θ)| * |deriv (psi ζ) θ| ≤ 4 * M := by
      rw [hdpsi, abs_mul, abs_neg, abs_of_pos h2ζ]
      by_cases hB : 0 < 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ ∧
          2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ < 1
      · have hwin : Real.pi / 2 - ζ < θ ∧ θ < Real.pi / 2 - ζ / 2 := by
          obtain ⟨hB1, hB2⟩ := hB
          have h5 : 2 / ζ * θ < 2 / ζ * (Real.pi / 2 - ζ / 2) := by linarith
          have h6 : θ < Real.pi / 2 - ζ / 2 := lt_of_mul_lt_mul_left h5 h2ζ.le
          have h7 : 2 / ζ * (Real.pi / 2 - ζ / 2 - θ) < 1 := by
            have hfac : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ =
                2 / ζ * (Real.pi / 2 - ζ / 2 - θ) := by ring
            linarith
          have h8 : Real.pi / 2 - ζ / 2 - θ < ζ / 2 := by
            have hv : (1 : ℝ) = 2 / ζ * (ζ / 2) := by field_simp
            rw [hv] at h7
            exact lt_of_mul_lt_mul_left h7 h2ζ.le
          constructor <;> linarith
        have hsin4 : |Real.sin (2 * θ)| * (2 / ζ) ≤ 4 := SinRatioBound hζ (Or.inr hwin)
        calc |Real.sin (2 * θ)| *
              (|deriv Real.smoothTransition (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ)| * (2 / ζ))
            ≤ |Real.sin (2 * θ)| * (M * (2 / ζ)) := by
              gcongr
              exact hMbd _
          _ = M * (|Real.sin (2 * θ)| * (2 / ζ)) := by ring
          _ ≤ M * 4 := mul_le_mul_of_nonneg_left hsin4 hM0
          _ = 4 * M := by ring
      · have hz : deriv Real.smoothTransition
            (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ) = 0 := by
          rcases not_and_or.mp hB with h | h
          · exact hderiv_nonpos _ (not_lt.mp h)
          · exact hderiv_one_le _ (not_lt.mp h)
        rw [hz, abs_zero, zero_mul, mul_zero]
        exact mul_nonneg (by norm_num) hM0
    have hderivchi : |deriv (chiFun ζ) θ| ≤ |deriv (phi ζ) θ| + |deriv (psi ζ) θ| := by
      rw [hdmul]
      calc |deriv (phi ζ) θ * psi ζ θ + phi ζ θ * deriv (psi ζ) θ|
          ≤ |deriv (phi ζ) θ * psi ζ θ| + |phi ζ θ * deriv (psi ζ) θ| := abs_add_le _ _
        _ = |deriv (phi ζ) θ| * |psi ζ θ| + |phi ζ θ| * |deriv (psi ζ) θ| := by
            rw [abs_mul, abs_mul]
        _ ≤ |deriv (phi ζ) θ| * 1 + 1 * |deriv (psi ζ) θ| := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpsi_le (abs_nonneg _)
            · exact mul_le_mul_of_nonneg_right hphi_le (abs_nonneg _)
        _ = |deriv (phi ζ) θ| + |deriv (psi ζ) θ| := by ring
    calc |Real.sin (2 * θ) * deriv (chiFun ζ) θ|
        = |Real.sin (2 * θ)| * |deriv (chiFun ζ) θ| := by rw [abs_mul]
      _ ≤ |Real.sin (2 * θ)| * (|deriv (phi ζ) θ| + |deriv (psi ζ) θ|) :=
            mul_le_mul_of_nonneg_left hderivchi (abs_nonneg _)
      _ = |Real.sin (2 * θ)| * |deriv (phi ζ) θ| + |Real.sin (2 * θ)| * |deriv (psi ζ) θ| := by
            ring
      _ ≤ 4 * M + 4 * M := add_le_add hb_phi hb_psi
      _ = 8 * M := by ring
      _ ≤ max (8 * M) 1 := le_max_left _ _
  · -- the limiting behaviour as `ζ → 0⁺`
    intro θ hθ0 hθπ
    have hc : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ0 (by linarith)
    have hmem : Set.Ioo (0 : ℝ) (min θ (Real.pi / 2 - θ)) ∈ 𝓝[>] (0 : ℝ) := by
      have h1 : Set.Iio (min θ (Real.pi / 2 - θ)) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iio_mem_nhds hc)
      have h2 : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
      exact Filter.mem_of_superset (inter_mem h1 h2) (fun x hx => ⟨hx.2, hx.1⟩)
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
    filter_upwards [hmem] with ζ hζ
    obtain ⟨hζ0, hζlt⟩ := hζ
    have h1 : ζ ≤ θ := le_of_lt (lt_of_lt_of_le hζlt (min_le_left _ _))
    have h2 : θ ≤ Real.pi / 2 - ζ := by
      have : ζ ≤ Real.pi / 2 - θ := le_of_lt (lt_of_lt_of_le hζlt (min_le_right _ _))
      linarith
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ0
    have hA : 1 ≤ 2 / ζ * θ - 1 := by
      have hle : 2 / ζ * ζ ≤ 2 / ζ * θ := mul_le_mul_of_nonneg_left h1 h2ζ.le
      have hval : 2 / ζ * ζ = 2 := div_mul_cancel₀ 2 hζ0.ne'
      linarith
    have hB : 1 ≤ 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ := by
      have hle : 2 / ζ * θ ≤ 2 / ζ * (Real.pi / 2 - ζ) := mul_le_mul_of_nonneg_left h2 h2ζ.le
      have hval : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * (Real.pi / 2 - ζ) = 1 := by
        field_simp
        ring
      linarith
    show (1 : ℝ) = chiFun ζ θ
    show (1 : ℝ) = phi ζ θ * psi ζ θ
    rw [show phi ζ θ = 1 from Real.smoothTransition.one_of_one_le hA,
        show psi ζ θ = 1 from Real.smoothTransition.one_of_one_le hB, mul_one]

end Work.H2.T1Q
end
end
-- ===== merged: Submission.Work.LWP.BiotSavart.biotSavart_reflZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix
open MeasureTheory

namespace Work.LWP.BiotSavart

/-! ## The reflection as a linear isometry equivalence of `ℝ³` -/

/-- The coordinate flip `v ↦ (v₀, v₁, -v₃)` as a linear isometry equivalence of `ℝ`, applied to
the `i`-th coordinate. -/
private noncomputable def coordFlip (i : Fin 3) : ℝ ≃ₗᵢ[ℝ] ℝ :=
  if i = 2 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

/-- **The reflection `σ : x ↦ (x₀, x₁, -x₃)` of `ℝ³`, as a linear isometry equivalence.**  Its
underlying function is `Work.LWP.reflZ = Work.LWP.flipZ`. -/
private noncomputable def reflZEquiv : R3 ≃ₗᵢ[ℝ] R3 :=
  LinearIsometryEquiv.piLpCongrRight 2 coordFlip

/-- The action of `reflZEquiv` on coordinates, as a self-map of `Fin 3 → ℝ`. -/
private noncomputable def flipCoord : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun v i => coordFlip i (v i)

private lemma reflZEquiv_toLp (v : Fin 3 → ℝ) :
    reflZEquiv (WithLp.toLp 2 v) = WithLp.toLp 2 (flipCoord v) := rfl

private lemma ofLp_reflZEquiv (x : R3) : (reflZEquiv x).ofLp = flipCoord x.ofLp := by
  rw [← WithLp.toLp_ofLp 2 x, reflZEquiv_toLp]

private lemma reflZEquiv_eq_reflZ (x : R3) : reflZEquiv x = reflZ x := by
  rw [← WithLp.toLp_ofLp 2 x, reflZEquiv_toLp]
  congr 1
  funext i
  fin_cases i <;> simp [flipCoord, coordFlip]

private lemma reflZEquiv_eq_flipZ (x : R3) : reflZEquiv x = flipZ x := by
  rw [reflZEquiv_eq_reflZ]; rfl

/-! ## The coordinate flip -/

private lemma flipCoord_smul (c : ℝ) (a : Fin 3 → ℝ) : flipCoord (c • a) = c • flipCoord a := by
  funext i; fin_cases i <;> simp [flipCoord, coordFlip]

private lemma flipCoord_sub (a b : Fin 3 → ℝ) :
    flipCoord (a - b) = flipCoord a - flipCoord b := by
  funext i; fin_cases i <;> (simp [flipCoord, coordFlip] <;> ring)

private lemma flipCoord_cross (a b : Fin 3 → ℝ) :
    flipCoord a ⨯₃ flipCoord b = - flipCoord (a ⨯₃ b) := by
  ext i
  fin_cases i <;> (simp [flipCoord, coordFlip, cross_apply] <;> ring)

private lemma cross_neg_left (a b : Fin 3 → ℝ) : (-a) ⨯₃ b = - (a ⨯₃ b) := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-! ## The pointwise identity for the Biot–Savart integrand -/

/-- **The Biot–Savart integrand is equivariant under the reflection.**  For `ω` of parity
`IsOddVorticity` (i.e. `ω (reflZ x) = - flipZ (ω x)`), the integrand of `biotSavart ω` at the
reflected pair `(σ x, σ z)` is the reflection `σ` of the integrand at `(x, z)`. -/
private lemma biotSavart_integrand_reflZ {ω : R3 → R3} (h : IsOddVorticity ω) (x z : R3) :
    WithLp.toLp 2 ((‖reflZEquiv x - reflZEquiv z‖ ^ (3 : ℕ))⁻¹ •
        ((ω (reflZEquiv z)) ⨯₃ (reflZEquiv x - reflZEquiv z)))
      = reflZEquiv (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
  have h1 : ‖reflZEquiv x - reflZEquiv z‖ = ‖x - z‖ := by
    rw [← LinearIsometryEquiv.map_sub]
    exact reflZEquiv.norm_map (x - z)
  have hz : ω (reflZEquiv z) = - reflZEquiv (ω z) := by
    rw [reflZEquiv_eq_reflZ, reflZEquiv_eq_flipZ]
    exact h z
  have e1 : (ω (reflZEquiv z)).ofLp = - flipCoord ((ω z).ofLp) := by
    rw [hz, WithLp.ofLp_neg, ofLp_reflZEquiv]
  have e2 : (reflZEquiv x).ofLp - (reflZEquiv z).ofLp = flipCoord (x.ofLp - z.ofLp) := by
    rw [ofLp_reflZEquiv, ofLp_reflZEquiv, ← flipCoord_sub]
  have hkey : ((ω (reflZEquiv z)) ⨯₃ (reflZEquiv x - reflZEquiv z))
      = flipCoord ((ω z) ⨯₃ (x - z)) := by
    rw [e1, e2, cross_neg_left, flipCoord_cross, neg_neg]
  rw [h1, hkey, reflZEquiv_toLp, flipCoord_smul]

/-! ## Reflection equivariance of the Biot–Savart operator -/

/-- **`biotSavart` commutes with the reflection `σ = reflZ = flipZ`** for a vorticity of parity
`IsOddVorticity`.  This is the algebraic content of `biotSavart_reflZ`. -/
private lemma biotSavart_reflZEquiv {ω : R3 → R3} (h : IsOddVorticity ω) (x : R3) :
    biotSavart ω (reflZEquiv x) = reflZEquiv (biotSavart ω x) := by
  rw [biotSavart, biotSavart]
  rw [LinearIsometryEquiv.map_smul]
  congr 1
  calc ∫ z, WithLp.toLp 2 ((‖reflZEquiv x - z‖ ^ (3 : ℕ))⁻¹ •
          ((ω z) ⨯₃ (reflZEquiv x - z)))
      = ∫ z, WithLp.toLp 2 ((‖reflZEquiv x - reflZEquiv z‖ ^ (3 : ℕ))⁻¹ •
          ((ω (reflZEquiv z)) ⨯₃ (reflZEquiv x - reflZEquiv z))) := by
        exact (MeasureTheory.integral_comp reflZEquiv (fun z => WithLp.toLp 2
          ((‖reflZEquiv x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (reflZEquiv x - z))))).symm
    _ = ∫ z, reflZEquiv (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        exact biotSavart_integrand_reflZ h x z
    _ = reflZEquiv (∫ z, WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) :=
        LinearIsometry.integral_comp_comm reflZEquiv.toLinearIsometry _

/-- **Reflection equivariance of the Biot–Savart operator**: a vorticity in the parity class
`IsOddVorticity` produces a velocity field `biotSavart ω` that is reflection invariant, i.e.
`biotSavart ω (reflZ x) = flipZ (biotSavart ω x)`.  This is the "odd" clause of the
Lichtenstein–Gunther class at the level of the Biot–Savart map, proved here directly from the
Newtonian-potential form of `biotSavart` (no Schauder input, no integrability of `ω` needed). -/
theorem biotSavart_reflZ {ω : R3 → R3} (h : IsOddVorticity ω) (x : R3) :
    biotSavart ω (reflZ x) = flipZ (biotSavart ω x) := by
  rw [← reflZEquiv_eq_reflZ x, biotSavart_reflZEquiv h x, reflZEquiv_eq_flipZ]

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.BiotSavart.integrand_norm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix

namespace Work.LWP.BiotSavart

/-- The Euclidean (`L²`) norm of the cross product of two vectors of `ℝ³` is at most the product
of their norms.  `crossProduct` (`⨯₃`) is Mathlib's bilinear form on `Fin 3 → ℝ`; the coercion
`R3 → (Fin 3 → ℝ)` is `WithLp.ofLp` and `WithLp.toLp 2` puts the `L²` norm back on the codomain,
so this is `‖u × v‖ = ‖u‖‖v‖ sin θ ≤ ‖u‖‖v‖`. -/
theorem norm_toLp_crossProduct_le (u v : R3) :
    ‖WithLp.toLp 2 (crossProduct u v)‖ ≤ ‖u‖ * ‖v‖ := by
  have h : ‖WithLp.toLp 2 (crossProduct u v)‖
      = ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v) :=
    InnerProductGeometry.norm_ofLp_crossProduct u v
  calc ‖WithLp.toLp 2 (crossProduct u v)‖
      = ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v) := h
    _ ≤ ‖u‖ * ‖v‖ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by positivity)
    _ = ‖u‖ * ‖v‖ := by ring

/-- **Pointwise bound on the Biot–Savart integrand.**  If `‖x‖ ≥ 2R` and `‖y‖ ≤ R` then
`‖x - y‖ ≥ ‖x‖/2`, so the kernel `(‖x - y‖³)⁻¹ • (ω y × (x - y))` is bounded by
`‖ω y‖ · 4/‖x‖² ≤ 4 M/‖x‖²`. -/
theorem integrand_norm_le {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) {x y : R3} (hx : 2 * R ≤ ‖x‖) (hy : ‖y‖ ≤ R) :
    ‖WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y))‖
      ≤ 4 / ‖x‖ ^ 2 * M := by
  have hX : 0 ≤ ‖x‖ := norm_nonneg x
  have ha : 0 ≤ ‖x - y‖ := norm_nonneg _
  -- `‖y‖ ≤ R ≤ ‖x‖/2`
  have hy2 : ‖y‖ ≤ ‖x‖ / 2 := by linarith
  -- `‖x‖/2 ≤ ‖x - y‖`, hence `‖x‖ ≤ 2‖x - y‖`
  have h1 : ‖x‖ ≤ 2 * ‖x - y‖ := by
    have h := norm_sub_norm_le x y
    linarith
  -- `‖x - y‖ ≤ ‖x‖ + ‖y‖ ≤ 3‖x‖/2`
  have h2 : ‖x - y‖ ≤ 3 * ‖x‖ / 2 := by
    have h := norm_sub_le x y
    linarith
  have hcore : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ ≤ 4 * (‖x‖ ^ 2)⁻¹ :=
    cube_inv_mul_le hX ha h1 h2
  have hcp : ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖ ≤ M * ‖x - y‖ :=
    le_trans (norm_toLp_crossProduct_le (ω y) (x - y))
      (mul_le_mul_of_nonneg_right (hω y) ha)
  calc ‖WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y))‖
      = (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖ := by
        rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
    _ ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * (M * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hcp (inv_nonneg.mpr (by positivity))
    _ = M * ((‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖) := by ring
    _ ≤ M * (4 * (‖x‖ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hcore hM
    _ = 4 / ‖x‖ ^ 2 * M := by ring

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.BiotSavart.volume_closedBall_real =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

/-- The Lebesgue volume of the closed ball of radius `R` about the origin in `ℝ³` is
`R³ · (4π/3)`.  `MeasureTheory.Measure.real` is `ENNReal.toReal` of the measure of the set,
and `R ≥ 0` makes `ENNReal.ofReal R`'s `toReal` come back to `R`. -/
theorem volume_closedBall_real (R : ℝ) (hR : 0 ≤ R) :
    MeasureTheory.Measure.real MeasureTheory.volume (Metric.closedBall (0 : R3) R)
      = R ^ 3 * (Real.pi * 4 / 3) := by
  rw [MeasureTheory.Measure.real, EuclideanSpace.volume_closedBall_fin_three]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.BiotSavart.volume_setOf_cross_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

open Matrix MeasureTheory

/-- The self dot product of a nonzero vector of `Fin 3 → ℝ` is nonzero: it is a sum of
squares of the coordinates. -/
lemma dotSelf_ne_zero_three {v : Fin 3 → ℝ} (hv : v ≠ 0) : v ⬝ᵥ v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ v j * v j := fun j _ => mul_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

/-- The set of points `y` for which `d ⨯ (c - y) = 0` — a line, when `d ≠ 0` — is Lebesgue
null: it is contained in the affine hyperplane `{y | y - c ∈ span {d}}`. -/
theorem volume_setOf_cross_eq_zero (d c : Work.LWP.R3) (hd : d ≠ 0) :
    MeasureTheory.volume {y : Work.LWP.R3 | crossProduct d (c - y) = 0} = 0 := by
  have hd' : ((d : Work.LWP.R3) : Fin 3 → ℝ) ≠ 0 := by simpa using hd
  -- the line through `c` with direction `d` is the strict vector subspace `span {d}`, shifted by `c`
  set S : Submodule ℝ Work.LWP.R3 := Submodule.span ℝ {d} with hS
  have hSne : S ≠ ⊤ := by
    intro h
    have h1 : Module.finrank ℝ S = 1 := by
      rw [hS]; exact finrank_span_singleton (K := ℝ) hd
    have h2 : Module.finrank ℝ S = 3 := by
      rw [h, finrank_top, finrank_euclideanSpace_fin]
    omega
  -- every point of the zero set lies on the affine hyperplane `(· + -c) ⁻¹' span {d}`
  have hsub : {y : Work.LWP.R3 | crossProduct d (c - y) = 0}
      ⊆ (fun h : Work.LWP.R3 => h + (-c)) ⁻¹' (S : Set Work.LWP.R3) := by
    intro y hy
    rw [Set.mem_preimage, hS]
    refine Submodule.mem_span_singleton.mpr ?_
    -- work with the coordinate vector `v = c - y` of `Fin 3 → ℝ`
    set v : Fin 3 → ℝ := ((y - c : Work.LWP.R3) : Fin 3 → ℝ) with hv
    have hv0 : crossProduct (d : Fin 3 → ℝ) v = 0 := by
      have hcy : ((c - y : Work.LWP.R3) : Fin 3 → ℝ) = -v := by simp [v]
      have hh : crossProduct (d : Fin 3 → ℝ) (-v) = 0 := by rw [← hcy]; exact hy
      rwa [map_neg, neg_eq_zero] at hh
    -- the vector triple product identity: `d ⨯ (d ⨯ v) = (d ⬝ v) • d - (d ⬝ d) • v`
    have hkey := cross_cross_eq_smul_sub_smul' (d : Fin 3 → ℝ) (d : Fin 3 → ℝ) v
    rw [hv0, map_zero] at hkey
    have hdd : (d : Fin 3 → ℝ) ⬝ᵥ (d : Fin 3 → ℝ) ≠ 0 := dotSelf_ne_zero_three hd'
    have hA : ((d : Fin 3 → ℝ) ⬝ᵥ v) • (d : Fin 3 → ℝ)
        = ((d : Fin 3 → ℝ) ⬝ᵥ (d : Fin 3 → ℝ)) • v := sub_eq_zero.mp hkey.symm
    -- hence `v` is a multiple of `d`
    have hveq : v = (((d : Fin 3 → ℝ) ⬝ᵥ (d : Fin 3 → ℝ))⁻¹
        * ((d : Fin 3 → ℝ) ⬝ᵥ v)) • (d : Fin 3 → ℝ) := by
      rw [mul_smul, hA, smul_smul, inv_mul_cancel₀ hdd, one_smul]
    have hyc : ((y + -c : Work.LWP.R3) : Fin 3 → ℝ) = ((y - c : Work.LWP.R3) : Fin 3 → ℝ) := by
      rw [WithLp.ofLp_add, WithLp.ofLp_neg, WithLp.ofLp_sub]; rfl
    refine ⟨((d : Fin 3 → ℝ) ⬝ᵥ (d : Fin 3 → ℝ))⁻¹ * ((d : Fin 3 → ℝ) ⬝ᵥ v), ?_⟩
    rw [WithLp.ext_iff, WithLp.ofLp_smul, hyc, ← hv]
    exact hveq.symm
  -- the affine hyperplane is a translate of the null subspace `span {d}`
  refine MeasureTheory.measure_mono_null hsub ?_
  rw [MeasureTheory.measure_preimage_add_right]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume S hSne

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.CurlFree.curlFree_isGradient =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix

namespace Work.LWP.CurlFree


end Work.LWP.CurlFree
end
-- ===== merged: Submission.Work.LWP.Inputs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-! ## 1. The Biot–Savart inputs -/

/-- **The Schauder / Calderón–Zygmund estimate for the Biot–Savart operator.**

`ω ∈ L¹ ∩ L^∞ ∩ C^{0,α}` divergence-free on `ℝ³` implies `u = biotSavart ω ∈ C^{1,α}`:
`ContDiff 1 u`, `Du` bounded and `α`-Hölder.  This is Schauder's second order estimate applied
to `u = (-Δ)^{-1}(∇×ω)`, whose second derivatives are Calderón–Zygmund transforms of `ω`;
equivalently it is the statement that the singular integral operators of order `1` map
`C^{0,α}_b` to itself.  This is the `C^{1,α}` *closure* of the Biot–Savart map. -/
def BiotSavartSchauder (α : NNReal) : Prop :=
  ∀ ω : R3 → R3, Integrable ω → IsBoundedFun ω → Holder α ω → (∀ x, div ω x = 0) →
    IsContDiffHolder ℝ α (biotSavart ω)

/-- **The Biot–Savart law for a divergence-free vorticity.**  `u = biotSavart ω` has vorticity
`ω` and is divergence-free.  (Both halves come from `u = ∇×A` with the Newtonian potential
`A = (4π)^{-1}∫ ω(y)/‖x-y‖ dy`, using `∇·A = 0` and `-ΔA = ω`.) -/
def BiotSavartLaw : Prop :=
  ∀ ω : R3 → R3, Integrable ω → IsBoundedFun ω → (∀ x, div ω x = 0) →
    (∀ x, vorticity (biotSavart ω) x = ω x) ∧ (∀ x, div (biotSavart ω) x = 0)

/-- **The inverse Biot–Savart law on `ℝ³`.**  A `C¹`, divergence-free velocity field which
decays at infinity is recovered from its vorticity by the Biot–Savart integral,
`u = biotSavart (∇×u)`.  (The proof is the standard one: `u - biotSavart (∇×u)` is a
divergence-free curl-free field, hence a gradient, hence — being bounded and decaying — zero;
equivalently the Helmholtz decomposition of `L²(ℝ³)`.) -/
def BiotSavartInverse : Prop :=
  ∀ u : R3 → R3, ContDiff ℝ 1 u → (∀ x, div u x = 0) → Integrable (vorticity u) →
    (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C / (1 + ‖x‖)) →
    ∀ x, biotSavart (vorticity u) x = u x

/-- **Reflection equivariance of Biot–Savart** (the "odd" clause of the Lichtenstein–Gunther
class).  If the vorticity is in the parity class `IsOddVorticity` (i.e. `ω ∘ reflZ = -flipZ ∘ ω`,
the parity of `∇×u` for an odd `u`), then `u = biotSavart ω` is reflection invariant,
`u (reflZ x) = flipZ (u x)`; combined with axisymmetry this is `IsOdd u`.  The proof is the
change of variables `y ↦ reflZ y` in the Biot–Savart integral, using that `reflZ` preserves
Lebesgue measure and that `σ(a × b) = det(σ) · (σ a × σ b)` for a reflection `σ`. -/
def BiotSavartReflection : Prop :=
  ∀ ω : R3 → R3, IsOddVorticity ω → ∀ x, biotSavart ω (reflZ x) = flipZ (biotSavart ω x)

/-! ## 2. The local existence inputs -/

/-- **The Lichtenstein–Gunther transport step: local existence for the vorticity equation.**

For every divergence-free `ω₀ ∈ L¹ ∩ L^∞ ∩ C^{0,α}(ℝ³)` there are `T > 0`, a vorticity field
`ω : ℝ³ × [0,T) → ℝ³` and a velocity field `u : ℝ³ × [0,T) → ℝ³` with `u(·,t) = biotSavart (ω(·,t))`,
as follows.

* `ω(·,0) = ω₀`;
* `ω(·,t) ∈ L¹ ∩ L^∞` and divergence-free for every `t ∈ [0,T)`;
* `u` has the *joint* `C^{1,α}` regularity of the Lichtenstein–Gunther class:
  `u.uncurry ∈ C^{1,α}(ℝ³ × [0,S])` for every `S < T`;
* `VorticityEquation u ω`, i.e. `∂ₜω + (u·∇)ω = (ω·∇)u`.

This is the Picard iteration of Lichtenstein and Günther: the vorticity equation is an ODE in the
Banach space `C^{0,α}_b ∩ L¹` whose vector field `ω ↦ -(BS ω ·∇)ω + (ω·∇)(BS ω)` is locally
Lipschitz by the Schauder estimate.  It is *strictly weaker* than the local existence theorem
`Work.LWP.local_existence`: it produces no pressure, no oddness, no identification of the initial
velocity, and states nothing about the Euler equation itself. -/
def VorticityTransportExistence (α : NNReal) : Prop :=
  ∀ ω₀ : R3 → R3, Integrable ω₀ → IsBoundedFun ω₀ → Holder α ω₀ → (∀ x, div ω₀ x = 0) →
    ∃ T : ℝ, 0 < T ∧ ∃ ω : R3 → ℝ → R3, ∃ u : R3 → ℝ → R3,
      (∀ x, ω x 0 = ω₀ x) ∧
      (∀ t ∈ Ico 0 T, ∀ x, u x t = biotSavart (fun y => ω y t) x) ∧
      (∀ t ∈ Ico 0 T, Integrable (fun x => ω x t)) ∧
      (∀ t ∈ Ico 0 T, IsBoundedFun (fun x => ω x t)) ∧
      (∀ t ∈ Ico 0 T, div (fun x => ω x t) = 0) ∧
      (∀ t ∈ Ico 0 T, ∀ x, vorticity (fun y => u y t) x = ω x t) ∧
      (∀ t ∈ Ico 0 T, div (fun x => u x t) = 0) ∧
      (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) ∧
      VorticityEquation u ω

/-- **Existence of the pressure by the Poincaré lemma on `ℝ³`.**  A `C¹` curl-free vector field
on the simply connected domain `ℝ³` is a gradient; the conclusion is written in the equivalent
Riesz form `fderiv ℝ P x y = ⟪F x, y⟫` rather than `∇ P x = F x`.  **This one is no longer an
input**: it is *proved* in `Submission/Work/LWP/CurlFree/curlFree_isGradient.lean`
(`Work.LWP.CurlFree.curlFree_isGradient`), and the abbreviation below is kept so that the
`LWPInputs` bundle can still carry it (a proved `Prop` is a valid field). -/
def CurlFreeIsGradient : Prop :=
  ∀ F : R3 → R3, ContDiff ℝ 1 F → (∀ x, vorticity F x = 0) →
    ∃ P : R3 → ℝ, ∀ x, ∀ y : R3, fderiv ℝ P x y = inner ℝ (F x) y

/-- **Reconstruction of the pressure.**  If `u` has the joint `C^{1,α}` regularity of the
Lichtenstein–Gunther class on `[0,T)`, if `ω(·,t) = ∇×u(·,t)` and `div u(·,t) = 0`, and if `ω`
solves the vorticity equation against `u`, then there is a pressure `p` — itself of class `C^1`
— with `∂ₜu + (u·∇)u + ∇p = 0` on `ℝ³ × (0,T)`.

The vector field `F = ∂ₜu + (u·∇)u` is curl-free: by the vector identity
`∇×((u·∇)u) = (u·∇)(∇×u) − ((∇×u)·∇)u + (div u)(∇×u)` valid for `div u = 0`, its curl is exactly
the left-hand side of the vorticity equation.  In the classical (smooth) case `F` is a gradient
by the Poincaré lemma (`CurlFreeIsGradient`); in the `C^{1,α}` case, where the product
`(∇u)·u` is only `C^{0,α}` and not differentientiable, the pressure is produced directly as the
Schauder solution of the Poisson equation `-Δp = div((u·∇)u)`, which is of class `C^{1,α}` —
this is the elliptic input of the Lichtenstein–Gunther theory. -/
def PressureReconstruction (α : NNReal) : Prop :=
  ∀ (u : R3 → ℝ → R3) (ω : R3 → ℝ → R3) (T : ℝ),
    (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) →
    (∀ t ∈ Ico 0 T, ∀ x, vorticity (fun y => u y t) x = ω x t) →
    (∀ t ∈ Ico 0 T, div (fun x => u x t) = 0) →
    VorticityEquation u ω →
    ∃ p : R3 → ℝ → ℝ, ContDiffOn ℝ 1 p.uncurry (univ ×ˢ Ico 0 T) ∧
      ∀ x t, t ∈ Ioo 0 T →
        timeDeriv u x t + directionalDeriv u u x t + spaceGrad p x t = 0

/-- **Uniqueness of classical solutions in the Lichtenstein–Gunther class.**  Two solutions with
the same data that are both jointly `C^{1,α}` agree on `[0,T)`.  (The classical proof compares
the vorticity fields along the flow of the difference; it is the "uniqueness" half of the
Lichtenstein–Gunther theorem.) -/
def EulerUniqueness (α : NNReal) : Prop :=
  ∀ (u₀ : R3 → R3) (T : ℝ) (p p' : R3 → ℝ → ℝ) (u u' : R3 → ℝ → R3),
    IsLocalEulerEquationSolution p u₀ T u → IsLocalEulerEquationSolution p' u₀ T u' →
    (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) →
    (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u'.uncurry (univ ×ˢ Icc 0 S)) →
    ∀ x t, t ∈ Ico 0 T → u x t = u' x t

/-- **Propagation of the odd symmetry.**  If the data are odd then every time slice of a classical
solution is odd.  (The reflected field `x ↦ flipZ (u (reflZ x) t)` is again a solution with the
same data, so uniqueness forces reflection invariance; combined with axisymmetry — which is
`Work.Cyl.isOdd_of_reflZ_invariant` — this is `IsOdd`.) -/
def IsOddPropagates : Prop :=
  ∀ (u₀ : R3 → R3) (T : ℝ) (p : R3 → ℝ → ℝ) (u : R3 → ℝ → R3),
    IsOdd u₀ → IsLocalEulerEquationSolution p u₀ T u →
    ∀ t ∈ Ico 0 T, IsOdd (u · t)

/-! ## 3. The continuation input -/

/-- **The Beale–Kato–Majda continuation criterion in the `C^{1,α}` class.**

If a solution exists on `[0,T)` and its BKM integral `bkm u t = ∫₀ᵗ ⨆ₓ‖ω(x,s)‖ ds` stays
*bounded* as `t ↑ T` — equivalently, by monotonicity, `∫₀^T ‖ω(·,s)‖_{L∞} ds < ∞` — then the
solution extends to a solution on `[0,T')` for some `T' > T`, agreeing with the original on
`[0,T)`.

The two ingredients are (i) the a priori estimate
`‖∇u(·,t)‖_{L∞} ≤ C ‖ω(·,t)‖_{L∞} (1 + log⁺(‖ω(·,t)‖_{C^α} / ‖ω(·,t)‖_{L∞}))`
(Calderón–Zygmund with a logarithmic loss), which combined with the transport identity for the
vorticity and the logarithmic Grönwall inequality
(`Work.LWP.BKM.gronwall_log`) bounds the `C^{0,α}` norm of `ω` on `[0,T)`; and (ii) restarting the
local existence theorem at time `T`.

The hypothesis is stated with `bkm` (rather than `IntegrableOn`) so that it is neither stronger
nor weaker than the criterion in the junk-free case, and so that it is *literally* the failure of
the conclusion `Tendsto (bkm u) (𝓝[<] T) atTop` (see `Work.LWP.bkm_divergence_of_maximal`). -/
def BKMExtension (α : NNReal) : Prop :=
  ∀ (u₀ : R3 → R3) (T : ℝ) (p : R3 → ℝ → ℝ) (u : R3 → ℝ → R3),
    IsLocalEulerEquationSolution p u₀ T u →
    (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) →
    (∃ M : ℝ, ∀ t ∈ Ico 0 T, bkm u t ≤ M) →
    ∃ T' : ℝ, T < T' ∧ ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
      IsLocalEulerEquationSolution p' u₀ T' u' ∧ ExtendsField u u' T

/-- **Existence of a maximal solution.**  Starting from `EulerData α u₀` (plus the
Biot–Savart-compatible extra data of `EulerDataBS`), the local existence theorem and the
Beale–Kato–Majda continuation criterion produce a maximal solution on some `[0,T)`: one takes
`T = sup {S : a Lichtenstein–Gunther solution exists on [0,S)}` and glues the chain of solutions
along an increasing sequence, using `EulerUniqueness` for well-definedness.  The maximal time is
finite here because the bootstrap produces a genuinely singular solution. -/
def MaximalSolutionExists (α : NNReal) : Prop :=
  ∀ u₀ : R3 → R3, EulerData α u₀ → EulerDataBS α u₀ →
    ∃ T : ℝ, 0 < T ∧ Nonempty (MaximalSolution α u₀ T)

end Work.LWP
end
-- ===== merged: Submission.Work.LWP.VorticityAPI =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

open scoped Matrix



end Work.LWP
end
