import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.ModeEnergyWeighted =====
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

/-- The integrand of the per-mode weighted energy identity: `flux` (see `ModeEnergyDefs`) is a
primitive of it, along the mode ODE. -/
def enInt (α lam : ℝ) (a c : ℝ → ℝ) (z : ℝ) : ℝ :=
  α ^ 2 * rw z * (deriv a z) ^ 2 - (α ^ 2 / 2) * rwbb z * (a z) ^ 2
    + ((α * (5 + α)) / 2) * rwc z * (a z) ^ 2 + lam * (a z) ^ 2 * (Work.Spaces.w z) ^ 2
    - c z * a z * (Work.Spaces.w z) ^ 2

/-- **The pointwise identity**: along the mode ODE, `flux α a` has derivative `enInt α lam a c`. -/
theorem hasDerivAt_flux {α lam : ℝ} (hα : 0 < α) {a c : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (ha : HasDerivAt a (deriv a z) z)
    (ha' : HasDerivAt (deriv a) (deriv (deriv a) z) z)
    (hode : α ^ 2 * z ^ 2 * deriv (deriv a) z + α * (5 + α) * z * deriv a z
      = lam * a z - c z) :
    HasDerivAt (flux α a) (enInt α lam a c z) z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 := (hasDerivAt_rw hz0).mul (ha'.mul ha)
  have h2 := (hasDerivAt_rwb hz0).mul (ha.pow 2)
  have h3 := (hasDerivAt_rwDiv hz0).mul (ha.pow 2)
  have hmain := ((h1.const_mul (α ^ 2)).sub (h2.const_mul (α ^ 2 / 2))).add
    (h3.const_mul ((α * (5 + α)) / 2))
  convert hmain using 1
  · -- the two functions agree
    funext t
    simp only [flux, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply]
    ring_nf
  · -- the two derivative values agree
    have hDa : deriv (deriv a) z
        = (lam * a z - c z - α * (5 + α) * z * deriv a z) / (α ^ 2 * z ^ 2) := by
      rw [eq_div_iff (by positivity)]
      linarith [hode]
    rw [hDa]
    simp only [enInt, rw, rwb, rwbb, rwc, Work.Spaces.w, Pi.pow_apply, Pi.mul_apply,
      Pi.div_apply]
    field_simp
    ring

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.flux_radGreen_atTop =====
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

/-!
# `Work.FTS.ClassC.flux_radGreen_atTop`

The boundary term `flux α a` of the per-mode weighted energy identity
(`FTS/ClassC/ModeEnergyDefs.lean`) is

  `flux α a z = α²·(rw z · a' a) - (α²/2)·(rwb z · a²) + ((α(5+α))/2)·(rw z / z)·a²`,

with `rw z = (1+z)^4/z^2` and `rwb z = (1+z)^3(2z-2)/z^3`.  The two hypotheses of the target
say that, for `a = radGreen α m c`,

  `z·a(z)² → 0`  and  `z·a(z)·(z·a'(z)) → 0`  as `z → ∞`.

Both decay statements are *exactly* what is needed: each of the three coefficients of `flux`
equals an explicit bounded function times one of the two small quantities.  Since
`(1+z)/z → 1` and `(2z-2)/z → 2`, we have (for `z ≠ 0`)

  `rw z ·(a'a)   = ((1+z)/z)^4 · (z·a·(z a'))`,
  `rwb z·a²      = (((1+z)/z)^3·((2z-2)/z)) · (z·a²)`,
  `(rw z/z)·a²   = ((1+z)/z)^4 · (z·a²)`,

and each right-hand side is the product of a convergent coefficient with a function tending to
`0`, hence tends to `0`.  The conclusion follows by linearity.

Note that neither `hα` nor `m` nor `c` is used: the statement holds for any `α` and any
function satisfying the two decay hypotheses.
-/

/-- `(1+z)/z → 1` at `atTop`. -/
private lemma tendsto_one_add_div_self : Tendsto (fun z : ℝ => (1 + z) / z) atTop (nhds 1) := by
  have hdiv : Tendsto (fun z : ℝ => (1 : ℝ) / z) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_id (α := ℝ) (x := Filter.atTop))
  have h : Tendsto (fun z : ℝ => 1 + 1 / z) atTop (nhds 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1))).add hdiv
  refine Tendsto.congr' ?_ h
  filter_upwards [Filter.eventually_ne_atTop (α := ℝ) (0 : ℝ)] with z hz
  field_simp
  ring

/-- `((1+z)/z)^n → 1` at `atTop`. -/
private lemma tendsto_one_add_div_self_pow (n : ℕ) :
    Tendsto (fun z : ℝ => ((1 + z) / z) ^ n) atTop (nhds 1) := by
  simpa using tendsto_one_add_div_self.pow n

/-- `(2z-2)/z → 2` at `atTop`. -/
private lemma tendsto_two_mul_sub_div_self :
    Tendsto (fun z : ℝ => (2 * z - 2) / z) atTop (nhds 2) := by
  have hdiv : Tendsto (fun z : ℝ => (2 : ℝ) / z) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_id (α := ℝ) (x := Filter.atTop))
  have h : Tendsto (fun z : ℝ => 2 - 2 / z) atTop (nhds 2) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2))).sub hdiv
  refine Tendsto.congr' ?_ h
  filter_upwards [Filter.eventually_ne_atTop (α := ℝ) (0 : ℝ)] with z hz
  field_simp
  try ring

theorem flux_radGreen_atTop {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (h1 : Filter.Tendsto (fun z => z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2)
      Filter.atTop (nhds 0))
    (h2 : Filter.Tendsto
      (fun z => z * (Work.FTS.PhiStar.Radial.radGreen α m c z)
        * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (Work.FTS.ClassC.flux α (Work.FTS.PhiStar.Radial.radGreen α m c))
      Filter.atTop (nhds 0) := by
  let a : ℝ → ℝ := Work.FTS.PhiStar.Radial.radGreen α m c
  have h1' : Tendsto (fun z : ℝ => z * (a z) ^ 2) atTop (nhds 0) := h1
  have h2' : Tendsto (fun z : ℝ => z * a z * (z * deriv a z)) atTop (nhds 0) := h2
  have he1 : Tendsto (fun z : ℝ => ((1 + z) / z) ^ 4) atTop (nhds 1) :=
    tendsto_one_add_div_self_pow 4
  have he2 : Tendsto (fun z : ℝ => ((1 + z) / z) ^ 3 * ((2 * z - 2) / z)) atTop (nhds 2) := by
    simpa using (tendsto_one_add_div_self_pow 3).mul tendsto_two_mul_sub_div_self
  have hA : Tendsto (fun z : ℝ => α ^ 2 * (((1 + z) / z) ^ 4 * (z * a z * (z * deriv a z))))
      atTop (nhds 0) := by
    simpa using ((he1.mul h2').const_mul (α ^ 2))
  have hB : Tendsto (fun z : ℝ =>
      (α ^ 2 / 2) * (((1 + z) / z) ^ 3 * ((2 * z - 2) / z) * (z * (a z) ^ 2))) atTop (nhds 0) := by
    simpa using ((he2.mul h1').const_mul (α ^ 2 / 2))
  have hC : Tendsto (fun z : ℝ => ((α * (5 + α)) / 2) * (((1 + z) / z) ^ 4 * (z * (a z) ^ 2)))
      atTop (nhds 0) := by
    simpa using ((he1.mul h1').const_mul ((α * (5 + α)) / 2))
  have hF : Tendsto (fun z : ℝ =>
        α ^ 2 * (((1 + z) / z) ^ 4 * (z * a z * (z * deriv a z)))
        - (α ^ 2 / 2) * (((1 + z) / z) ^ 3 * ((2 * z - 2) / z) * (z * (a z) ^ 2))
        + ((α * (5 + α)) / 2) * (((1 + z) / z) ^ 4 * (z * (a z) ^ 2))) atTop (nhds 0) := by
    simpa using ((hA.sub hB).add hC)
  refine Tendsto.congr' ?_ hF
  filter_upwards [Filter.eventually_ne_atTop (α := ℝ) (0 : ℝ)] with z hz
  simp only [flux, Work.FTS.ClassC.rw, Work.FTS.ClassC.rwb, a]
  field_simp
  try ring

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.flux_radGreen_zero =====
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

/-!
# `Work.FTS.ClassC.flux_radGreen_zero`

The boundary term `flux α a` of the per-mode weighted energy identity
(`FTS/ClassC/ModeEnergyDefs.lean`) is

  `flux α a z = α²·(rw z · a'·a) - (α²/2)·(rwb z · a²) + ((α(5+α))/2)·(rw z / z)·a²`,

with `rw z = (1+z)^4/z^2` and `rwb z = (1+z)^3(2z-2)/z^3`.  The two hypotheses of the target say
that, for `a = radGreen α m c`,

  `a(z)²/z³ → 0`  and  `a'(z)·a(z)/z² → 0`  as `z → 0⁺`.

These are exactly what is needed: for `z ≠ 0`

  `rw z·(a'·a)   = (1+z)^4 · (a'·a/z²)`,
  `rwb z·a²      = ((1+z)^3(2z-2)) · (a²/z³)`,
  `(rw z/z)·a²   = (1+z)^4 · (a²/z³)`,

so `flux α a` is a sum of three products of a coefficient *continuous at `0`* with one of the
two quantities tending to `0` — hence it tends to `0` at `0⁺`.  Since `flux α a 0 = 0`
(`flux_zero`), this is continuity within `[0,∞)` at `0`.

Neither `m` nor `c` (nor the structure of `radGreen`) is used: the statement holds for any `α`
and any function satisfying the two decay hypotheses.
-/

/-- If `a` decays at `0⁺` in the two weighted senses recorded by the boundary term of the
per-mode energy identity, then that boundary term `flux α a` tends to `0` at `0⁺`. -/
lemma flux_tendsto_zero_of_small {α : ℝ} {a : ℝ → ℝ}
    (h1 : Tendsto (fun z => (a z) ^ 2 / z ^ 3) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h2 : Tendsto (fun z => deriv a z * a z / z ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (flux α a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- the three coefficients of `flux`, as functions continuous at `0`
  have hc1 : Tendsto (fun z : ℝ => α ^ 2 * (1 + z) ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (α ^ 2)) := by
    have hcont : Continuous fun z : ℝ => α ^ 2 * (1 + z) ^ 4 := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc2 : Tendsto (fun z : ℝ => (α ^ 2 / 2) * ((1 + z) ^ 3 * (2 * z - 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((α ^ 2 / 2) * (-2))) := by
    have hcont : Continuous fun z : ℝ => (α ^ 2 / 2) * ((1 + z) ^ 3 * (2 * z - 2)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc3 : Tendsto (fun z : ℝ => ((α * (5 + α)) / 2) * (1 + z) ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((α * (5 + α)) / 2)) := by
    have hcont : Continuous fun z : ℝ => ((α * (5 + α)) / 2) * (1 + z) ^ 4 := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  -- the three summands of the re-associated expression
  have hT1 : Tendsto (fun z : ℝ => α ^ 2 * (1 + z) ^ 4 * (deriv a z * a z / z ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hc1.mul h2
  have hT2 : Tendsto (fun z : ℝ =>
      (α ^ 2 / 2) * ((1 + z) ^ 3 * (2 * z - 2)) * ((a z) ^ 2 / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hc2.mul h1
  have hT3 : Tendsto (fun z : ℝ =>
      ((α * (5 + α)) / 2) * (1 + z) ^ 4 * ((a z) ^ 2 / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hc3.mul h1
  have hsum : Tendsto (fun z : ℝ => α ^ 2 * (1 + z) ^ 4 * (deriv a z * a z / z ^ 2)
      - (α ^ 2 / 2) * ((1 + z) ^ 3 * (2 * z - 2)) * ((a z) ^ 2 / z ^ 3)
      + ((α * (5 + α)) / 2) * (1 + z) ^ 4 * ((a z) ^ 2 / z ^ 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (hT1.sub hT2).add hT3
  refine Tendsto.congr' ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  simp only [flux, rw, rwb]
  field_simp
  try ring

theorem flux_radGreen_zero {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (h1 : Filter.Tendsto
      (fun z => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h2 : Filter.Tendsto
      (fun z => deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ContinuousWithinAt (Work.FTS.ClassC.flux α (Work.FTS.PhiStar.Radial.radGreen α m c))
      (Set.Ici 0) 0 := by
  have hlim := flux_tendsto_zero_of_small (α := α)
    (a := Work.FTS.PhiStar.Radial.radGreen α m c) h1 h2
  have hIci : Set.Ici (0 : ℝ) = insert 0 (Set.Ioi 0) := by
    ext x; simp [le_iff_lt_or_eq, eq_comm]
  rw [ContinuousWithinAt, hIci, nhdsWithin_insert,
    flux_zero α (Work.FTS.PhiStar.Radial.radGreen α m c)]
  rw [tendsto_sup]
  refine ⟨?_, hlim⟩
  show map (flux α (Work.FTS.PhiStar.Radial.radGreen α m c)) (pure 0) ≤ 𝓝 (0 : ℝ)
  rw [map_pure, flux_zero α (Work.FTS.PhiStar.Radial.radGreen α m c)]
  exact pure_le_nhds 0

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.JetDefs =====
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

/-! ### Basic facts about `xNear` and the neighbourhood `U` -/

/-- An open neighbourhood of the interval `[0, xNear]` on which `κ` is smooth: since
`xNear = √2/2 < 3/4`, the interval `(-3/4,3/4)` works. -/
def U : Set ℝ := Set.Ioo (-(3 / 4)) (3 / 4)


lemma xNear_pos : 0 < xNear := by
  rw [xNear, Real.sin_pi_div_four]
  positivity

lemma xNear_lt : xNear < 3 / 4 := by
  rw [xNear, Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  linarith

lemma xNear_le_one : xNear ≤ 1 := by linarith [xNear_lt]

lemma U_isOpen : IsOpen U := isOpen_Ioo



lemma Icc_subset_U : Set.Icc (0 : ℝ) xNear ⊆ U := fun _ hx =>
  ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩

/-! ### `κ = cos(arcsin ·)` on `U` -/

lemma two_mul_thetaOf (x : ℝ) : 2 * thetaOf x = Real.arcsin x := by
  rw [thetaOf]; ring

lemma kappa_eq_cos_arcsin (x : ℝ) : kappa x = Real.cos (Real.arcsin x) := by
  rw [kappa, two_mul_thetaOf]

/-- On `[-1,1]` (indeed everywhere, by the junk-value convention for `arcsin`) the function `κ`
is `√(1 - x²)`. -/
lemma kappa_eq_sqrt (x : ℝ) : kappa x = Real.sqrt (1 - x ^ 2) := by
  rw [kappa_eq_cos_arcsin, Real.cos_arcsin]

/-- `κ` is smooth on the neighbourhood `U` of `[0,xNear]`. -/
lemma contDiffOn_kappa : ContDiffOn ℝ ⊤ kappa U := by
  have hsub : U ⊆ ({-1, 1} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : ContDiffOn ℝ ⊤ Real.arcsin U :=
    (Real.contDiffOn_arcsin (n := ⊤)).mono hsub
  have h2 : ContDiffOn ℝ ⊤ (fun x => Real.cos (Real.arcsin x)) U :=
    Real.contDiff_cos.comp_contDiffOn h1
  exact h2.congr fun x _ => kappa_eq_cos_arcsin x

/-! ### The bounded-jet predicate -/

/-- `JetBdd K g C` says that `g` is smooth on the neighbourhood `U` of `[0, xNear]`, that
`C ≥ 0`, and that on `[0, xNear]` the first `K+1` derivatives of `g` are bounded by `C`. -/
def JetBdd (K : ℕ) (g : ℝ → ℝ) (C : ℝ) : Prop :=
  ContDiffOn ℝ ⊤ g U ∧ 0 ≤ C ∧ ∀ k ≤ K, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |iteratedDeriv k g x| ≤ C

lemma JetBdd.jet_smooth {K : ℕ} {g : ℝ → ℝ} {C : ℝ} (h : JetBdd K g C) :
    ContDiffOn ℝ ⊤ g U := h.1

lemma JetBdd.jet_nonneg {K : ℕ} {g : ℝ → ℝ} {C : ℝ} (h : JetBdd K g C) : 0 ≤ C := h.2.1

lemma JetBdd.jet_bound {K : ℕ} {g : ℝ → ℝ} {C : ℝ} (h : JetBdd K g C) :
    ∀ k ≤ K, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |iteratedDeriv k g x| ≤ C := h.2.2

lemma JetBdd.jet_mono {K K' : ℕ} (hKK : K' ≤ K) {g : ℝ → ℝ} {C : ℝ} (h : JetBdd K g C) :
    JetBdd K' g C :=
  ⟨h.1, h.2.1, fun k hk => h.2.2 k (le_trans hk hKK)⟩

lemma JetBdd.jet_le {K : ℕ} {g : ℝ → ℝ} {C D : ℝ} (h : JetBdd K g C) (hCD : C ≤ D) :
    JetBdd K g D :=
  ⟨h.1, le_trans h.2.1 hCD, fun k hk x hx => le_trans (h.2.2 k hk x hx) hCD⟩

lemma smooth_contDiffAt {f : ℝ → ℝ} (hf : ContDiffOn ℝ ⊤ f U) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) xNear) (k : ℕ) : ContDiffAt ℝ (k : WithTop ℕ∞) f x :=
  (hf.contDiffAt (U_isOpen.mem_nhds (Icc_subset_U hx))).of_le le_top

lemma JetBdd.jet_add {K : ℕ} {f g : ℝ → ℝ} {Cf Cg : ℝ} (hf : JetBdd K f Cf)
    (hg : JetBdd K g Cg) : JetBdd K (f + g) (Cf + Cg) := by
  refine ⟨hf.1.add hg.1, by linarith [hf.2.1, hg.2.1], ?_⟩
  intro k hk x hx
  rw [iteratedDeriv_add (smooth_contDiffAt hf.1 hx k) (smooth_contDiffAt hg.1 hx k)]
  exact (abs_add_le _ _).trans (add_le_add (hf.2.2 k hk x hx) (hg.2.2 k hk x hx))

lemma JetBdd.jet_const (K : ℕ) (c : ℝ) : JetBdd K (fun _ : ℝ => c) |c| := by
  refine ⟨contDiffOn_const, abs_nonneg c, ?_⟩
  intro k hk x hx
  rw [iteratedDeriv_const]
  split_ifs <;> simp

lemma JetBdd.jet_zero (K : ℕ) : JetBdd K (fun _ : ℝ => (0 : ℝ)) 0 := by
  refine ⟨contDiffOn_const, le_refl 0, ?_⟩
  intro k hk x hx
  simp

lemma JetBdd.jet_deriv {K : ℕ} {f : ℝ → ℝ} {C : ℝ} (hf : JetBdd (K + 1) f C) :
    JetBdd K (deriv f) C := by
  refine ⟨hf.1.deriv_of_isOpen U_isOpen (m := ⊤) (by simp), hf.2.1, ?_⟩
  intro k hk x hx
  have hiter : iteratedDeriv k (deriv f) x = iteratedDeriv (k + 1) f x := by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
      Function.iterate_succ_apply]
  rw [hiter]
  exact hf.2.2 (k + 1) (by omega) x hx

/-- The identity function has bounded jets on `[0,xNear]`, with bound `1`. -/
lemma JetBdd.jet_id (K : ℕ) : JetBdd K (fun x : ℝ => x) 1 := by
  have hd1 : deriv (fun x : ℝ => x) = fun _ => (1 : ℝ) := funext fun x => deriv_id x
  have hd0 : deriv (0 : ℝ → ℝ) = 0 := funext fun x => deriv_const x 0
  have hiter0 : ∀ k : ℕ, deriv^[k] (0 : ℝ → ℝ) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hd0, ih]
  have hd11 : deriv (fun _ : ℝ => (1 : ℝ)) = 0 := funext fun x => deriv_const x 1
  have hdd : deriv (deriv (fun x : ℝ => x)) = 0 := by rw [hd1, hd11]
  have h2 : ∀ k : ℕ, deriv^[Nat.succ (Nat.succ k)] (fun x : ℝ => x) = 0 := by
    intro k
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [hdd, hiter0 k]
  refine ⟨contDiffOn_id, by norm_num, ?_⟩
  intro k hk x hx
  rcases k with _ | k
  · rw [iteratedDeriv_zero]
    rw [abs_of_nonneg hx.1]
    linarith [hx.2, xNear_le_one]
  · rcases k with _ | k
    · rw [iteratedDeriv_one]
      rw [hd1]
      norm_num
    · rw [iteratedDeriv_eq_iterate]
      rw [h2 k]
      norm_num

lemma JetBdd.jet_mul {K : ℕ} {f g : ℝ → ℝ} {Cf Cg : ℝ} (hf : JetBdd K f Cf)
    (hg : JetBdd K g Cg) : JetBdd K (f * g) ((2 : ℝ) ^ K * Cf * Cg) := by
  refine ⟨hf.1.mul hg.1,
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) K) hf.2.1) hg.2.1, ?_⟩
  intro k hk x hx
  rw [iteratedDeriv_mul (n := k) (smooth_contDiffAt hf.1 hx k) (smooth_contDiffAt hg.1 hx k)]
  calc |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * iteratedDeriv i f x *
        iteratedDeriv (k - i) g x|
      ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (k - i) g x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf * Cg := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : |iteratedDeriv i f x| ≤ Cf := hf.2.2 i (le_trans hik hk) x hx
        have h2 : |iteratedDeriv (k - i) g x| ≤ Cg :=
          hg.2.2 (k - i) (le_trans (Nat.sub_le _ _) hk) x hx
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.choose i))]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (k.choose i))) h2
          (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg (k.choose i)) hf.2.1)
    _ = (2 : ℝ) ^ k * Cf * Cg := by
        have hsum : (∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℝ)) = (2 : ℝ) ^ k := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
          norm_num
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ ≤ (2 : ℝ) ^ K * Cf * Cg := by
        have h : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hk
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hf.2.1) hg.2.1


/-! ### A compactness bound: smooth on `U` implies bounded jets on `[0,xNear]` -/

lemma contDiffOn_iterate_deriv {f : ℝ → ℝ} (hf : ContDiffOn ℝ ⊤ f U) (k : ℕ) :
    ContDiffOn ℝ ⊤ (deriv^[k] f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      have h : ContDiffOn ℝ ⊤ (deriv (deriv^[k] f)) U :=
        ih.deriv_of_isOpen U_isOpen (m := ⊤) (by simp)
      simpa [Function.iterate_succ_apply'] using h

theorem exists_jetBdd_of_contDiffOn (K : ℕ) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ⊤ f U) :
    ∃ C : ℝ, JetBdd K f C := by
  have hbdd : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Set.Icc (0 : ℝ) xNear, |iteratedDeriv k f x| ≤ C := by
    intro k
    have hcont : ContinuousOn (fun x => iteratedDeriv k f x) (Set.Icc (0 : ℝ) xNear) := by
      have h := ((contDiffOn_iterate_deriv hf k).continuousOn).mono Icc_subset_U
      simpa [iteratedDeriv_eq_iterate] using h
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨max C 0, le_max_right _ _, fun x hx => le_trans (by simpa using hC x hx) (le_max_left _ _)⟩
  choose C hC using hbdd
  refine ⟨(∑ k ∈ Finset.range (K + 1), C k) + 1, hf,
    add_nonneg (Finset.sum_nonneg fun i _ => (hC i).1) zero_le_one, ?_⟩
  intro k hk x hx
  have hmem : k ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  have hle : C k ≤ ∑ k ∈ Finset.range (K + 1), C k :=
    Finset.single_le_sum (fun i _ => (hC i).1) hmem
  calc |iteratedDeriv k f x| ≤ C k := (hC k).2 x hx
    _ ≤ (∑ k ∈ Finset.range (K + 1), C k) + 1 := by linarith

/-! ### The common recursion `genCoeff` -/

/-- The recursion shared by `bCoeff` (`init = 1`) and `aCoeff` (`init = 2κ`): the coefficients
of the expansion of `G^i (init · u)`, where the recursion step is the one of the `x`-form of
`D_θ`. -/
def genCoeff (init : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, j => fun x => if j = 0 then init x else 0
  | (i + 1), j => fun x =>
      2 * kappa x * (x * deriv (genCoeff init i j) x + (j : ℝ) * genCoeff init i j x)
        + (if j = 0 then 0 else 2 * kappa x * genCoeff init i (j - 1) x)

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.WtDerivAux.summable_lam_sqrt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.WtDerivAux

open scoped Real

/-- The mode weight `(2m+1)/(λ_m √(2m+1))` decays like `√2/4 · m^{-3/2}`, hence is summable.

Indeed for `m ≥ 1` the numerator and the `Real.sqrt` cancel:
`(2m+1)/(λ_m √(2m+1)) = √(2m+1)/λ_m ≤ √2·√(m+1)/(m+1)^2 = √2·(m+1)^{-3/2}`,
using `λ_m = 2m(2m+5) ≥ (m+1)^2` and `2m+1 ≤ 2(m+1)`, and `Σ_m (m+1)^{-3/2}` converges.
At `m = 0` the quotient is `0` because `λ_0 = 0` and division by zero is total in `ℝ`. -/
theorem summable_lam_sqrt :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 1)
      / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
  -- the comparison series `∑ (m+1)^{-3/2}`
  have hbase : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(3 / 2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(3 / 2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  refine Summable.of_norm_bounded (hbase.mul_left (Real.sqrt 2)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  by_cases hm : m = 0
  · -- the zeroth term vanishes since `λ_0 = 0`
    subst hm
    have h0 : (2 * ((0 : ℕ) : ℝ) + 1)
        / (Work.FTS.PhiStar.Gegenbauer.lam 0 * Real.sqrt (2 * ((0 : ℕ) : ℝ) + 1)) = 0 := by
      rw [show Work.FTS.PhiStar.Gegenbauer.lam 0 = 0 by norm_num [Work.FTS.PhiStar.Gegenbauer.lam]]
      norm_num
    rw [h0, abs_zero]
    positivity
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hlam_pos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hA : (0 : ℝ) ≤ (2 * (m : ℝ) + 1)
        / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
      div_nonneg (by positivity) (mul_nonneg hlam_pos.le (Real.sqrt_nonneg _))
    rw [abs_of_nonneg hA]
    have hsne : Real.sqrt (2 * (m : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hsq : Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)
        = 2 * (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
    -- cancel the `√(2m+1)` between numerator and denominator
    have hstep : (2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        = Real.sqrt (2 * (m : ℝ) + 1) / Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [div_eq_iff (mul_ne_zero (ne_of_gt hlam_pos) hsne)]
      have h1 : Real.sqrt (2 * (m : ℝ) + 1) / Work.FTS.PhiStar.Gegenbauer.lam m
          * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          = Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
        rw [div_mul_eq_mul_div,
          show Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            = Work.FTS.PhiStar.Gegenbauer.lam m
                * (Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) by ring,
          mul_div_cancel_left₀ _ (ne_of_gt hlam_pos)]
      rw [h1, hsq]
    rw [hstep]
    -- `√(2m+1) ≤ √2·√(m+1)`
    have hsle : Real.sqrt (2 * (m : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith)
    -- `(m+1)^2 ≤ λ_m`
    have hlam2 : ((m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hb2pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
    -- the `rpow` identity `√(m+1)/(m+1)^2 = (m+1)^{-3/2}`
    have hcore : Real.sqrt ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2
        = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_natCast ((m : ℝ) + 1) 2,
        ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
      congr 1
      norm_num
    calc Real.sqrt (2 * (m : ℝ) + 1) / Work.FTS.PhiStar.Gegenbauer.lam m
        ≤ (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1)) / Work.FTS.PhiStar.Gegenbauer.lam m :=
          div_le_div_of_nonneg_right hsle hlam_pos.le
      _ = Real.sqrt 2 * (Real.sqrt ((m : ℝ) + 1)
            / Work.FTS.PhiStar.Gegenbauer.lam m) := by ring
      _ ≤ Real.sqrt 2 * (Real.sqrt ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_left (Real.sqrt_nonneg ((m : ℝ) + 1)) hb2pos hlam2
      _ = Real.sqrt 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by rw [hcore]

end Work.FTS.PhiStar.FlatWAux.WtDerivAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.lintegral_rpow_prim_weighted_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

theorem lintegral_rpow_prim_weighted_le {c : ℝ → ℝ} {r : ℝ} (hr : -2 < r)
    (hc : AEMeasurable c)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))
        (fun z => ENNReal.ofReal (z ^ (-(2 * r + 5)))
          * MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) z))
              (fun t => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))))
      ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))
          (fun t => ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hr' : -(2 * r + 5) < (-1 : ℝ) := by linarith
  have hv : (0 : ℝ) < 2 * r + 4 := by linarith
  have hc' : AEMeasurable c (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hc.mono_measure Measure.restrict_le_self
  have hFmeas : AEMeasurable (fun z : ℝ => ENNReal.ofReal (z ^ (-(2 * r + 5))))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (AEMeasurable.pow aemeasurable_id aemeasurable_const)
  have hGmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hc'.pow_const 2).mul (AEMeasurable.pow aemeasurable_id aemeasurable_const))
  have hQmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hc'.pow_const 2).div (aemeasurable_id.pow_const 4))
  -- the elementary primitive: for `t ∈ (0,1)` the `z`-integral is the `ofReal` of a number
  -- at most `t ^ (-(2r+4)) / (2r+4)`
  have hinner_le : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫⁻ z in Set.Ioo t 1, ENNReal.ofReal (z ^ (-(2 * r + 5))))
        ≤ ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)) := by
    intro t ht
    rw [lintegral_ofReal_rpow_Ioo_left (r := -(2 * r + 5)) (t := t) ht.1 (le_of_lt ht.2) hr']
    refine ENNReal.ofReal_le_ofReal ?_
    have hkey : (1 - t ^ (-(2 * r + 4))) / (-(2 * r + 4))
        = (t ^ (-(2 * r + 4)) - 1) / (2 * r + 4) := by
      rw [div_neg, ← neg_div, neg_sub]
    rw [show -(2 * r + 5) + 1 = -(2 * r + 4) by ring, hkey, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (le_of_lt hv))
  -- the pointwise rewriting of the weight `t ^ (2r) · t ^ (-(2r+4)) = t ^ (-4)`
  have hpteq : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
          * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4))
        = ENNReal.ofReal ((c t) ^ 2 / t ^ 4) * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hA : ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) * ENNReal.ofReal (t ^ (-(2 * r + 4)))
        = ENNReal.ofReal ((c t) ^ 2 / t ^ 4) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht0) _))]
      congr 1
      rw [div_eq_mul_inv, ← Real.rpow_natCast t 4, ← Real.rpow_neg (le_of_lt ht0) ((4 : ℕ) : ℝ)]
      rw [mul_assoc, ← Real.rpow_add ht0]
      have hE : 2 * r + (-(2 * r + 4)) = -(((4 : ℕ) : ℝ)) := by push_cast; ring
      rw [hE]
    have hB : ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4))
        = ENNReal.ofReal (t ^ (-(2 * r + 4))) * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos hv, div_eq_mul_inv]
    rw [hB, ← mul_assoc, hA]
  calc MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))
        (fun z => ENNReal.ofReal (z ^ (-(2 * r + 5)))
          * MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) z))
              (fun t => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))))
      = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
          * ∫⁻ z in Set.Ioo t 1, ENNReal.ofReal (z ^ (-(2 * r + 5))) :=
        lintegral_Ioo_triangle (a := 0) (b := 1) h01 hFmeas hGmeas
    _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
          * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact mul_le_mul_of_nonneg_left (hinner_le t ht) zero_le
    _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4)
          * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hpteq t ht
    _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
          * (ENNReal.ofReal (2 * r + 4))⁻¹ :=
        lintegral_mul_const'' _ hQmeas

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgBstep_integrableOn_Ioi_of_aestronglyMeasurable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set
open Work.FTS.EllExist

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * (|a| * |b|) ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  rw [abs_mul]
  linarith [h, sq_abs a, sq_abs b]

/-- AM–GM in the form used below: `|y| ≤ (y² + 1)/2`. -/
private lemma abs_le_sq_add_one_div_two (y : ℝ) : |y| ≤ (y ^ 2 + 1) / 2 := by
  have h : 2 * (|y| * 1) ≤ |y| ^ 2 + 1 ^ 2 := by nlinarith [sq_nonneg (|y| - 1)]
  rw [mul_one] at h
  linarith [h, sq_abs y]

/-- For `0 < t ≤ x` the negative power `x^{-p-1}` is dominated by its value at `t`,
provided the exponent is negative, i.e. `0 ≤ p`. -/
private lemma rpow_neg_sub_one_le {t x p : ℝ} (ht : 0 < t) (htx : t ≤ x) (hp : 0 ≤ p) :
    x ^ (-p - 1) ≤ t ^ (-p - 1) := by
  have hx : 0 < x := lt_of_lt_of_le ht htx
  rw [show -p - 1 = -(p + 1) from by ring]
  rw [Real.rpow_neg hx.le, Real.rpow_neg ht.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ht _) (Real.rpow_le_rpow ht.le htx (by linarith))


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.eFamSupDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer (gC gC_rec gC_ode contDiff_gC)

/-- `Npsi m = (2m+2)(2m+3)`: the constant of the radial Sturm–Liouville equation of `eFam m`.
It equals `(n+1)(n+2) = n(n+3) + 2` for `n = 2m+1`. -/
def Npsi (m : ℕ) : ℝ := (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)

/-- `ug m x = (1 - x^2)·C^{(3/2)}_{2m+1}(x)`. -/
def ug (m : ℕ) : ℝ → ℝ := fun x => (1 - x ^ 2) * gC (2 * m + 1) x

/-- The radial energy, written with products to keep the derivative bookkeeping free of
function powers: `ene m x = (u')^2 + N·(1-x^2)·q^2`.  Away from `x = ±1` it equals
`(u')^2 + N u^2/(1-x^2)`, and at `x = 1` it evaluates to `N^2`. -/
def ene (m : ℕ) : ℝ → ℝ :=
  fun x => deriv (ug m) x * deriv (ug m) x
    + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x * gC (2 * m + 1) x))

/-! ## Elementary facts about `Npsi` -/

lemma Npsi_pos (m : ℕ) : 0 < Npsi m := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [Npsi]
  positivity

lemma Npsi_eq (m : ℕ) :
    Npsi m = (((2 * m + 1 : ℕ) : ℝ) + 1) * (((2 * m + 1 : ℕ) : ℝ) + 2) := by
  rw [Npsi]
  push_cast
  ring

lemma Npsi_eq_two (m : ℕ) :
    Npsi m = (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 := by
  rw [Npsi_eq]
  ring

lemma Npsi_ge_one (m : ℕ) : 1 ≤ Npsi m := by
  rw [Npsi]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-- The value of `C^{(3/2)}_k` at `1`: `C^{(3/2)}_k(1) = (k+1)(k+2)/2`. -/
lemma gC_one (k : ℕ) : gC k 1 = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
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
        = ((n : ℝ) + 2) * (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2) / 2) := by
      rw [gC_rec n 1, ih1, ih2]
      push_cast
      ring
    have hh := mul_left_cancel₀ h2 h
    push_cast
    exact hh

/-- `√b` bounds `|a|` as soon as `a^2 ≤ b`. -/
lemma abs_le_sqrt_of_sq_le {a b : ℝ} (h : a ^ 2 ≤ b) : |a| ≤ Real.sqrt b := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-! ## Differentiability of `gC` -/

lemma differentiable_gC (k : ℕ) : Differentiable ℝ (gC k) :=
  (contDiff_gC k).differentiable (by norm_num)

lemma differentiable_deriv_gC (k : ℕ) : Differentiable ℝ (deriv (gC k)) :=
  ((contDiff_gC k).deriv' (n := 2)).differentiable (by norm_num)

lemma hasDerivAt_one_sub_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (-(2 * x)) x := by
  simpa using (hasDerivAt_pow 2 x).const_sub (1 : ℝ)

/-! ## The first and second derivatives of `ug` -/

lemma deriv_ug (m : ℕ) (x : ℝ) :
    deriv (ug m) x
      = -2 * x * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
  have h3 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y)
      ((-(2 * x)) * gC (2 * m + 1) x
        + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x) x :=
    (hasDerivAt_one_sub_sq x).mul
      ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h4 : deriv (ug m) x
      = (-(2 * x)) * gC (2 * m + 1) x
        + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
    rw [show ug m = fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y from rfl]
    exact h3.deriv
  rw [h4]
  ring

lemma differentiable_deriv_ug (m : ℕ) : Differentiable ℝ (deriv (ug m)) := by
  rw [funext (deriv_ug m)]
  have h1 : Differentiable ℝ (fun y : ℝ => (-2 : ℝ) * y) :=
    (differentiable_const (-2 : ℝ)).mul differentiable_id
  have h2 : Differentiable ℝ (fun y : ℝ => (1 : ℝ) - y ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  exact (h1.mul (differentiable_gC (2 * m + 1))).add
    (h2.mul (differentiable_deriv_gC (2 * m + 1)))

lemma deriv2_ug (m : ℕ) (x : ℝ) :
    deriv (deriv (ug m)) x
      = -2 * gC (2 * m + 1) x - 4 * x * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x := by
  have hfun : deriv (ug m)
      = fun y : ℝ => -2 * y * gC (2 * m + 1) y
        + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y := funext (deriv_ug m)
  rw [hfun]
  have h1 : HasDerivAt (fun y : ℝ => -2 * y * gC (2 * m + 1) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x) x := by
    have hlin : HasDerivAt (fun y : ℝ => (-2 : ℝ) * y) (-2) x := by
      simpa using (hasDerivAt_id x).const_mul (-2 : ℝ)
    exact hlin.mul ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((-(2 * x)) * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x) x :=
    (hasDerivAt_one_sub_sq x).mul
      ((differentiable_deriv_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h3 : HasDerivAt (fun y : ℝ => -2 * y * gC (2 * m + 1) y
        + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x
        + ((-(2 * x)) * deriv (gC (2 * m + 1)) x
          + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x)) x :=
    h1.add h2
  rw [h3.deriv]
  ring


/-- `u'(1) = -2 q(1) = -N`. -/
lemma deriv_ug_one (m : ℕ) : deriv (ug m) 1 = -Npsi m := by
  rw [deriv_ug m 1, gC_one (2 * m + 1), Npsi_eq m]
  push_cast
  ring

/-- `E(1) = (u'(1))^2 = N^2`. -/
lemma ene_one (m : ℕ) : ene m 1 = Npsi m * Npsi m := by
  show deriv (ug m) 1 * deriv (ug m) 1
      + Npsi m * ((1 - (1 : ℝ) ^ 2) * (gC (2 * m + 1) 1 * gC (2 * m + 1) 1))
      = Npsi m * Npsi m
  rw [deriv_ug_one m]
  ring

/-- `E` in quotient form, away from `x = ±1`: `E = (u')^2 + N u^2/(1-x^2)`. -/
lemma ene_eq (m : ℕ) {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) :
    ene m x = deriv (ug m) x * deriv (ug m) x
      + (Npsi m / (1 - x ^ 2)) * (ug m x * ug m x) := by
  show deriv (ug m) x * deriv (ug m) x
      + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x * gC (2 * m + 1) x))
      = deriv (ug m) x * deriv (ug m) x
        + (Npsi m / (1 - x ^ 2)) * (ug m x * ug m x)
  rw [show ug m x = (1 - x ^ 2) * gC (2 * m + 1) x from rfl]
  field_simp

/-- **`E'(x) = 2xN·q(x)^2 ≥ 0` for `x ≥ 0`**: the energy is non-decreasing. -/
lemma deriv_ene (m : ℕ) (x : ℝ) :
    deriv (ene m) x = 2 * x * Npsi m * (gC (2 * m + 1) x * gC (2 * m + 1) x) := by
  have hdu : HasDerivAt (deriv (ug m)) (deriv (deriv (ug m)) x) x :=
    (differentiable_deriv_ug m).differentiableAt.hasDerivAt
  have hg : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) x) x :=
    (differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => deriv (ug m) y * deriv (ug m) y)
      (2 * deriv (ug m) x * deriv (deriv (ug m)) x) x := by
    have h := hdu.mul hdu
    convert h using 1
    ring
  have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * (gC (2 * m + 1) y * gC (2 * m + 1) y))
      ((-(2 * x)) * (gC (2 * m + 1) x * gC (2 * m + 1) x)
        + (1 - x ^ 2) * (2 * gC (2 * m + 1) x * deriv (gC (2 * m + 1)) x)) x := by
    have hg2 : HasDerivAt (fun y : ℝ => gC (2 * m + 1) y * gC (2 * m + 1) y)
        (2 * gC (2 * m + 1) x * deriv (gC (2 * m + 1)) x) x := by
      have h := hg.mul hg
      convert h using 1
      ring
    have h := (hasDerivAt_one_sub_sq x).mul hg2
    convert h using 1
  have h3 : HasDerivAt (ene m)
      (2 * deriv (ug m) x * deriv (deriv (ug m)) x
        + Npsi m * ((-(2 * x)) * (gC (2 * m + 1) x * gC (2 * m + 1) x)
          + (1 - x ^ 2) * (2 * gC (2 * m + 1) x * deriv (gC (2 * m + 1)) x))) x := by
    have h := h1.add (h2.const_mul (Npsi m))
    convert h using 1
    rfl
  rw [h3.deriv, deriv2_ug m x, deriv_ug m x]
  have hode := (gC_ode (2 * m + 1)).2 x
  have hkey : (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x
      = 4 * x * deriv (gC (2 * m + 1)) x
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * gC (2 * m + 1) x := by
    linarith [hode]
  rw [hkey, Npsi_eq_two m]
  ring

lemma differentiable_ene (m : ℕ) : Differentiable ℝ (ene m) := by
  have h1 : Differentiable ℝ
      (fun x : ℝ => deriv (ug m) x * deriv (ug m) x) :=
    (differentiable_deriv_ug m).mul (differentiable_deriv_ug m)
  have h2 : Differentiable ℝ (fun y : ℝ => (1 : ℝ) - y ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  have h3 : Differentiable ℝ
      (fun x : ℝ => gC (2 * m + 1) x * gC (2 * m + 1) x) :=
    (differentiable_gC (2 * m + 1)).mul (differentiable_gC (2 * m + 1))
  have h4 : Differentiable ℝ
      (fun x : ℝ => Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x * gC (2 * m + 1) x))) :=
    (differentiable_const (Npsi m)).mul (h2.mul h3)
  exact h1.add h4

lemma continuous_ene (m : ℕ) : Continuous (ene m) := (differentiable_ene m).continuous

/-- **The energy bound**: `E(x) ≤ E(1) = N^2` for `0 ≤ x ≤ 1`. -/
lemma ene_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : ene m x ≤ Npsi m * Npsi m := by
  have hmono : MonotoneOn (ene m) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_ene m).continuousOn
      (differentiable_ene m).differentiableOn ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    rw [deriv_ene m y]
    exact mul_nonneg (mul_nonneg (by linarith) (le_of_lt (Npsi_pos m))) (mul_self_nonneg _)
  have h1 : ene m x ≤ ene m 1 := hmono hx ⟨by norm_num, le_rfl⟩ hx.2
  rwa [ene_one m] at h1

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EulerWeakFubini =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.EComparison

/-! ## The main identity -/

theorem EulerWeakFubini {α L : ℝ} {W : ℝ → ℝ} (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {ρ : ℝ → ℝ} (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hρc : HasCompactSupport ρ) (hsupp : tsupport ρ ⊆ Set.Ioo a b) :
    (∫ z in Set.Ioi 0, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
      = ∫ t in a..b, deriv (deriv ρ) t *
          (-(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
            + L * (∫ z in t..b, (z - t) * W z)) := by
  have hab' : a ≤ b := hab.le
  -- 0. `ρ` and its first two derivatives vanish off `(a,b)`
  have hmem : ∀ z : ℝ, z ∉ Set.Ioo a b → ρ z = 0 ∧ deriv ρ z = 0 ∧ deriv (deriv ρ) z = 0 := by
    intro z hz
    have h1 : z ∉ tsupport ρ := fun h => hz (hsupp h)
    have h2 : z ∉ tsupport (deriv ρ) := fun h => h1 (tsupport_deriv_subset h)
    have h3 : z ∉ tsupport (deriv (deriv ρ)) := fun h => h2 (tsupport_deriv_subset h)
    exact ⟨image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2,
      image_eq_zero_of_notMem_tsupport h3⟩
  -- 1. the left-hand side is an integral over `[a,b]`
  have hstep1 : (∫ z in Set.Ioi 0, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
      = ∫ z in a..b, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)) := by
    rw [intervalIntegral.integral_of_le hab']
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun z hz => lt_trans ha hz.1) (fun z hz => ?_)
    have hznot : z ∉ Set.Ioo a b := fun hcon => hz.2 ⟨hcon.1, hcon.2.le⟩
    obtain ⟨h1, h2, h3⟩ := hmem z hznot
    simp [h1, h2, h3]
  rw [hstep1]
  -- 2. continuity of `ρ`, `ρ'`, `ρ''`
  have hcontρ : ContinuousOn ρ (Set.Icc a b) := (hρ 1).continuous.continuousOn
  have hcontρ1 : ContinuousOn (deriv ρ) (Set.Icc a b) := ((hρ 1).continuous_deriv le_rfl).continuousOn
  have hcontρ2g : Continuous (deriv (deriv ρ)) := by
    have h2 : Continuous (iteratedDeriv 2 ρ) := (hρ 2).continuous_iteratedDeriv 2 (by norm_num)
    convert h2 using 1
    ext t
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hcontρ2 : ContinuousOn (deriv (deriv ρ)) (Set.Icc a b) := hcontρ2g.continuousOn
  -- 3. integrability of `W` and its moments on `[a,b]`
  have hWcc : MeasureTheory.IntegrableOn W (Set.Icc a b) :=
    hW.integrableOn_compact_subset (fun z hz => lt_of_lt_of_le ha hz.1) isCompact_Icc
  have hWzcc : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z) (Set.Icc a b) :=
    hWcc.mul_continuousOn (by fun_prop : ContinuousOn (fun z : ℝ => z) (Set.Icc a b)) isCompact_Icc
  have hWz2cc : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z ^ 2) (Set.Icc a b) :=
    hWcc.mul_continuousOn (by fun_prop : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Icc a b)) isCompact_Icc
  have hzWcc : MeasureTheory.IntegrableOn (fun z : ℝ => z * W z) (Set.Icc a b) :=
    hWzcc.congr_fun (fun z _ => mul_comm (W z) z) measurableSet_Icc
  -- 4. the three integrands on the `z`-side
  have hF0 : MeasureTheory.IntegrableOn (fun z : ℝ => W z * ρ z) (Set.Icc a b) :=
    hWcc.mul_continuousOn hcontρ isCompact_Icc
  have hF1 : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z * deriv ρ z) (Set.Icc a b) :=
    hWzcc.mul_continuousOn hcontρ1 isCompact_Icc
  have hF2 : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z ^ 2 * deriv (deriv ρ) z) (Set.Icc a b) :=
    hWz2cc.mul_continuousOn hcontρ2 isCompact_Icc
  have toII : ∀ {f : ℝ → ℝ}, MeasureTheory.IntegrableOn f (Set.Icc a b) → IntervalIntegrable f volume a b := by
    intro f hf
    rw [← Set.uIcc_of_le hab'] at hf
    exact hf.intervalIntegrable
  have iF0 : IntervalIntegrable (fun z : ℝ => W z * ρ z) volume a b := toII hF0
  have iF1 : IntervalIntegrable (fun z : ℝ => W z * z * deriv ρ z) volume a b := toII hF1
  have iF2 : IntervalIntegrable (fun z : ℝ => W z * z ^ 2 * deriv (deriv ρ) z) volume a b := toII hF2
  -- 5. continuity of the two `t`-primitives
  have hAcont : ContinuousOn (fun t : ℝ => ∫ z in t..b, W z * z) (Set.Icc a b) := by
    have h : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab']; exact hWzcc
    simpa only [Set.uIcc_of_le hab'] using intervalIntegral.continuousOn_primitive_interval_left h
  have hAzcont : ContinuousOn (fun t : ℝ => ∫ z in t..b, z * W z) (Set.Icc a b) := by
    have h : MeasureTheory.IntegrableOn (fun z : ℝ => z * W z) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab']; exact hzWcc
    simpa only [Set.uIcc_of_le hab'] using intervalIntegral.continuousOn_primitive_interval_left h
  have hA1cont : ContinuousOn (fun t : ℝ => ∫ z in t..b, W z) (Set.Icc a b) := by
    have h : MeasureTheory.IntegrableOn W (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab']; exact hWcc
    simpa only [Set.uIcc_of_le hab'] using intervalIntegral.continuousOn_primitive_interval_left h
  have hBcont : ContinuousOn (fun t : ℝ => ∫ z in t..b, (z - t) * W z) (Set.Icc a b) := by
    have hcont : ContinuousOn
        (fun t : ℝ => (∫ z in t..b, z * W z) - t * (∫ z in t..b, W z)) (Set.Icc a b) :=
      hAzcont.sub (continuous_id.continuousOn.mul hA1cont)
    refine hcont.congr (fun t ht => ?_)
    have ht1 : a ≤ t := ht.1
    have ht2 : t ≤ b := ht.2
    have hleft : Set.Ioc t b ⊆ Set.Icc a b := fun z hz => ⟨le_trans ht1 hz.1.le, hz.2⟩
    have hright : Set.Ioc b t ⊆ Set.Icc a b :=
      fun z hz => absurd (le_trans hz.2 ht2) (not_le_of_gt hz.1)
    have hi1 : IntervalIntegrable (fun z : ℝ => z * W z) volume t b :=
      ⟨hzWcc.mono_set hleft, hzWcc.mono_set hright⟩
    have hiW : IntervalIntegrable (fun z : ℝ => W z) volume t b :=
      ⟨hWcc.mono_set hleft, hWcc.mono_set hright⟩
    have hi2 : IntervalIntegrable (fun z : ℝ => t * W z) volume t b := hiW.const_mul t
    calc (∫ z in t..b, (z - t) * W z) = ∫ z in t..b, (z * W z - t * W z) :=
          intervalIntegral.integral_congr (fun z _ => by ring)
      _ = (∫ z in t..b, z * W z) - (∫ z in t..b, t * W z) := intervalIntegral.integral_sub hi1 hi2
      _ = (∫ z in t..b, z * W z) - t * (∫ z in t..b, W z) := by
          rw [intervalIntegral.integral_const_mul]
  -- 6. the three integrands on the `t`-side
  have hK1int : MeasureTheory.IntegrableOn (fun t : ℝ => deriv (deriv ρ) t * (t ^ 2 * W t)) (Set.Icc a b) :=
    hF2.congr_fun (fun z _ => by ring) measurableSet_Icc
  have hK2int : MeasureTheory.IntegrableOn
      (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, W z * z)) (Set.Icc a b) :=
    (hcontρ2.mul hAcont).integrableOn_compact isCompact_Icc
  have hK3int : MeasureTheory.IntegrableOn
      (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z)) (Set.Icc a b) :=
    (hcontρ2.mul hBcont).integrableOn_compact isCompact_Icc
  have iK1 : IntervalIntegrable (fun t : ℝ => deriv (deriv ρ) t * (t ^ 2 * W t)) volume a b := toII hK1int
  have iK2 : IntervalIntegrable
      (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, W z * z)) volume a b := toII hK2int
  have iK3 : IntervalIntegrable
      (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z)) volume a b := toII hK3int
  -- 7. splitting a three-term integrand
  have split3 : ∀ {f1 f2 f3 : ℝ → ℝ}, IntervalIntegrable f1 volume a b →
      IntervalIntegrable f2 volume a b → IntervalIntegrable f3 volume a b →
      (∫ x in a..b, (f1 x + f2 x + f3 x))
        = (∫ x in a..b, f1 x) + (∫ x in a..b, f2 x) + (∫ x in a..b, f3 x) := by
    intro f1 f2 f3 h1 h2 h3
    rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  -- 8. the left-hand side
  have hsplitL : (∫ z in a..b, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
      = (∫ z in a..b, L * (W z * ρ z)) + (∫ z in a..b, (-α ^ 2) * (W z * z ^ 2 * deriv (deriv ρ) z))
        + (∫ z in a..b, (-(α * (5 + α))) * (W z * z * deriv ρ z)) := by
    rw [← split3 (f1 := fun z : ℝ => L * (W z * ρ z))
      (f2 := fun z : ℝ => (-α ^ 2) * (W z * z ^ 2 * deriv (deriv ρ) z))
      (f3 := fun z : ℝ => (-(α * (5 + α))) * (W z * z * deriv ρ z))
      (iF0.const_mul L) (iF2.const_mul (-α ^ 2)) (iF1.const_mul (-(α * (5 + α))))]
    exact intervalIntegral.integral_congr (fun z _ => by ring)
  have hLHS2 : (∫ z in a..b, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
      = -α ^ 2 * (∫ z in a..b, W z * z ^ 2 * deriv (deriv ρ) z)
        - α * (5 + α) * (∫ z in a..b, W z * z * deriv ρ z)
        + L * (∫ z in a..b, W z * ρ z) := by
    rw [hsplitL,
      intervalIntegral.integral_const_mul L (fun z : ℝ => W z * ρ z),
      intervalIntegral.integral_const_mul (-α ^ 2) (fun z : ℝ => W z * z ^ 2 * deriv (deriv ρ) z),
      intervalIntegral.integral_const_mul (-(α * (5 + α))) (fun z : ℝ => W z * z * deriv ρ z)]
    ring
  -- 9. the right-hand side
  have hsplitR : (∫ t in a..b, deriv (deriv ρ) t *
        (-(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
          + L * (∫ z in t..b, (z - t) * W z)))
      = (∫ t in a..b, (-α ^ 2) * (deriv (deriv ρ) t * (t ^ 2 * W t)))
        + (∫ t in a..b, (-(α * (5 + α))) * (deriv (deriv ρ) t * (∫ z in t..b, W z * z)))
        + (∫ t in a..b, L * (deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))) := by
    rw [← split3 (f1 := fun t : ℝ => (-α ^ 2) * (deriv (deriv ρ) t * (t ^ 2 * W t)))
      (f2 := fun t : ℝ => (-(α * (5 + α))) * (deriv (deriv ρ) t * (∫ z in t..b, W z * z)))
      (f3 := fun t : ℝ => L * (deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z)))
      (iK1.const_mul (-α ^ 2)) (iK2.const_mul (-(α * (5 + α)))) (iK3.const_mul L)]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have hRHS2 : (∫ t in a..b, deriv (deriv ρ) t *
        (-(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
          + L * (∫ z in t..b, (z - t) * W z)))
      = -α ^ 2 * (∫ t in a..b, deriv (deriv ρ) t * (t ^ 2 * W t))
        - α * (5 + α) * (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, W z * z))
        + L * (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z)) := by
    rw [hsplitR,
      intervalIntegral.integral_const_mul (-α ^ 2) (fun t : ℝ => deriv (deriv ρ) t * (t ^ 2 * W t)),
      intervalIntegral.integral_const_mul (-(α * (5 + α)))
        (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, W z * z)),
      intervalIntegral.integral_const_mul L
        (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))]
    ring
  -- 10. the two Fubini steps and the identification of the `t²`-slot
  have hKK : (∫ t in a..b, deriv (deriv ρ) t * (t ^ 2 * W t))
      = ∫ z in a..b, W z * z ^ 2 * deriv (deriv ρ) z :=
    intervalIntegral.integral_congr (fun z _ => by ring)
  have hI2 : (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, W z * z))
      = ∫ z in a..b, W z * z * deriv ρ z := FubiniZWeight hW ha hab hρ hρc hsupp
  have hI3 : (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))
      = ∫ z in a..b, W z * ρ z := FubiniWeightZ hW ha hab hρ hρc hsupp
  rw [hLHS2, hRHS2, hKK, hI2, hI3]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.HbdPointwiseLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **From the squared boundary estimate to a linear pointwise bound.**  If a.e. `z > 0` satisfies

  `(f z θ - lam z)^2 ≤ 100/(γ-1) * sin(2θ)^{γ-1} * Ibd α f z`   for all `θ ∈ (0,π/4)`

(with `γ = Work.Spaces.gam α`, `0 < α ≤ 1`, so that `γ - 1 > 0`), then a.e. `z > 0` satisfies

  `|f z θ - lam z| ≤ (100/(γ-1) * Ibd α f z + 1) / 2`   for all `θ ∈ (0,π/4)`.

Route: `|f z θ - lam z| = sqrt ((f z θ - lam z)^2) ≤ sqrt (A * sin(2θ)^{γ-1} * Ibd α f z) ≤
sqrt (A * Ibd α f z) ≤ (A * Ibd α f z + 1)/2` with `A := 100/(γ-1) ≥ 0`, using
`sin(2θ)^{γ-1} ≤ 1` for `θ ∈ (0,π/4)` (`Real.rpow_le_one`), `Real.sqrt_le_sqrt`,
`Real.sqrt_mul`, and the elementary inequality `2 * sqrt x ≤ x + 1` for `x ≥ 0`; also
`0 ≤ Ibd α f z` (`integral_nonneg` on the nonnegative integrand, or `Real.rpow_nonneg`).
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem HbdPointwiseLe {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
      (f z θ - lam z)^2
        ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * Ibd α f z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
      |f z θ - lam z| ≤ (100 / (Work.Spaces.gam α - 1) * Ibd α f z + 1) / 2 := by
  have hgam1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith [hα.1]
  have hA : 0 ≤ 100 / (Work.Spaces.gam α - 1) := by positivity
  filter_upwards [hbd] with z hz θ hθ
  -- nonnegativity of the angular energy `Ibd α f z`
  have hIbd : 0 ≤ Ibd α f z := by
    apply setIntegral_nonneg measurableSet_Icc
    intro σ hσ
    have hsin : 0 ≤ Real.sin (2 * σ) := by
      apply Real.sin_nonneg_of_mem_Icc
      constructor <;> linarith [hσ.1, hσ.2, Real.pi_pos]
    exact mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
  -- the squared bound at `θ`
  have hsin2 : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hrpow : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1) ≤ 1 :=
    Real.rpow_le_one hsin2.le (Real.sin_le_one _) hgam1.le
  have hsq : (f z θ - lam z) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1) * Ibd α f z := by
    calc (f z θ - lam z) ^ 2
        ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1)
            * Ibd α f z := hz θ hθ
      _ ≤ 100 / (Work.Spaces.gam α - 1) * 1 * Ibd α f z := by
          apply mul_le_mul_of_nonneg_right _ hIbd
          exact mul_le_mul_of_nonneg_left hrpow hA
      _ = 100 / (Work.Spaces.gam α - 1) * Ibd α f z := by ring
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((f z θ - lam z) ^ 2)
      ≤ Real.sqrt (100 / (Work.Spaces.gam α - 1) * Ibd α f z) := Real.sqrt_le_sqrt hsq
    _ ≤ (100 / (Work.Spaces.gam α - 1) * Ibd α f z + 1) / 2 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by nlinarith [mul_nonneg hA hIbd], ?_⟩
        nlinarith [sq_nonneg (100 / (Work.Spaces.gam α - 1) * Ibd α f z - 1)]

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.SinPowIntegralPiO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem SinPowIntegralPiO {γ : ℝ} (h1 : 1 < γ) (h2 : γ ≤ 2) {a b : ℝ}
    (ha : Real.pi / 4 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2) ≤ (100 / (γ - 1)) * (Real.sin (2 * a)) ^ (γ - 1) := by
  have hγ1 : 0 < γ - 1 := by linarith
  -- Substitution `x ↦ π/2 - x`, under which `sin (2 x) ↦ sin (π - 2 x) = sin (2 x)`.
  have hsym : (∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2))
      = ∫ x in (Real.pi / 2 - b)..(Real.pi / 2 - a), (Real.sin (2 * x)) ^ (γ - 2) := by
    rw [← intervalIntegral.integral_comp_sub_left
      (f := fun x : ℝ => (Real.sin (2 * x)) ^ (γ - 2)) (a := a) (b := b) (Real.pi / 2)]
    apply intervalIntegral.integral_congr
    intro x _
    show (Real.sin (2 * x)) ^ (γ - 2) = (Real.sin (2 * (Real.pi / 2 - x))) ^ (γ - 2)
    have harg : 2 * (Real.pi / 2 - x) = Real.pi - 2 * x := by ring
    rw [harg, Real.sin_pi_sub]
  -- The reflected interval lies in `[0, π/4]`, where the sibling estimate applies.
  have h0 : (0 : ℝ) ≤ Real.pi / 2 - b := by linarith
  have hle : Real.pi / 2 - b ≤ Real.pi / 2 - a := by linarith
  have hq : Real.pi / 2 - a ≤ Real.pi / 4 := by linarith
  have hbnd := SinPowIntegral (γ := γ) h1 h2 h0 hle hq
  have harg2 : 2 * (Real.pi / 2 - a) = Real.pi - 2 * a := by ring
  rw [harg2, Real.sin_pi_sub] at hbnd
  rw [hsym]
  exact hbnd

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.ae_limit_eq_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Identification of an a.e. limit with the derivative of a uniform limit (1-D engine)

This file isolates the one-dimensional "ACL" argument used to identify the a.e. limit of the
level-5 slots with the corresponding mixed derivative of the limit function.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The clamped limit and the "bad" set of rational difference quotients -/

/-- The composition of `Llim` with the projection onto the box `[a,b] × [c,d]`; it is globally
continuous as soon as `Llim` is continuous on the box, and it agrees with `Llim` there. -/
def Lclamp {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (Llim : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Llim (Set.projIcc a b hab z) (Set.projIcc c d hcd θ)

/-- The set of points of the box at which the rational difference quotients of the clamped limit
are *not* close to `w`.  This is the set whose nullity is produced by Fubini; it is measurable
without any measurability assumption on `Llim` itself, thanks to the clamping. -/
def BadSet {a b c d : ℝ} (Lc : ℝ → ℝ → ℝ) (w : ℝ × ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ Set.Icc a b ×ˢ Set.Icc c d ∧ ∃ k : ℕ, ∀ m : ℕ, ∃ h : ℚ,
      0 < |(h : ℝ)| ∧ |(h : ℝ)| < 1 / (m + 1) ∧ p.1 + (h : ℝ) ∈ Set.Icc a b ∧
      1 / (k + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|}

theorem badSet_measurable {a b c d : ℝ} {Lc : ℝ → ℝ → ℝ} {w : ℝ × ℝ → ℝ}
    (hLc : Continuous (Function.uncurry Lc)) (hw : Measurable w) :
    MeasurableSet (BadSet (a := a) (b := b) (c := c) (d := d) Lc w) := by
  rw [BadSet]
  have hbox : MeasurableSet {p : ℝ × ℝ | p ∈ Set.Icc a b ×ˢ Set.Icc c d} :=
    measurableSet_Icc.prod measurableSet_Icc
  have hstep : ∀ (k m : ℕ) (h : ℚ), MeasurableSet {p : ℝ × ℝ | 0 < |(h : ℝ)| ∧
      |(h : ℝ)| < 1 / ((m : ℝ) + 1) ∧ p.1 + (h : ℝ) ∈ Set.Icc a b ∧
      1 / ((k : ℝ) + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|} := by
    intro k m h
    have hshift : MeasurableSet {p : ℝ × ℝ | p.1 + (h : ℝ) ∈ Set.Icc a b} :=
      measurableSet_Icc.preimage (by fun_prop)
    have hval : MeasurableSet {p : ℝ × ℝ |
        1 / ((k : ℝ) + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|} := by
      refine measurableSet_lt measurable_const ?_
      have h1 : Continuous fun p : ℝ × ℝ => Lc (p.1 + (h : ℝ)) p.2 :=
        hLc.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
      have h2 : Continuous fun p : ℝ × ℝ => Lc p.1 p.2 :=
        hLc.comp (continuous_fst.prodMk continuous_snd)
      have hm1 : Measurable fun p : ℝ × ℝ =>
          (Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) := ((h1.sub h2).div_const _).measurable
      exact (hm1.sub hw).abs
    have hconst1 : MeasurableSet {p : ℝ × ℝ | 0 < |(h : ℝ)|} := by
      by_cases hh : 0 < |(h : ℝ)| <;> simp [hh]
    have hconst2 : MeasurableSet {p : ℝ × ℝ | |(h : ℝ)| < 1 / ((m : ℝ) + 1)} := by
      by_cases hh : |(h : ℝ)| < 1 / ((m : ℝ) + 1) <;> simp [hh]
    exact hconst1.inter (hconst2.inter (hshift.inter hval))
  rw [show {p : ℝ × ℝ | p ∈ Set.Icc a b ×ˢ Set.Icc c d ∧ ∃ k : ℕ, ∀ m : ℕ, ∃ h : ℚ,
        0 < |(h : ℝ)| ∧ |(h : ℝ)| < 1 / ((m : ℝ) + 1) ∧ p.1 + (h : ℝ) ∈ Set.Icc a b ∧
        1 / ((k : ℝ) + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|}
      = {p : ℝ × ℝ | p ∈ Set.Icc a b ×ˢ Set.Icc c d} ∩
        (⋃ k : ℕ, ⋂ m : ℕ, ⋃ h : ℚ, {p : ℝ × ℝ | 0 < |(h : ℝ)| ∧
          |(h : ℝ)| < 1 / ((m : ℝ) + 1) ∧ p.1 + (h : ℝ) ∈ Set.Icc a b ∧
          1 / ((k : ℝ) + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|}) from by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter]]
  exact hbox.inter (MeasurableSet.iUnion fun k => MeasurableSet.iInter fun m =>
    MeasurableSet.iUnion fun h => hstep k m h)

/-! ## The two directions of the characterisation -/

/-- **Reverse direction**: at a point `z` where the primitive of `w(·,θ)` is differentiable with
derivative `w (z,θ)`, the rational difference quotients satisfy the quantitative bounds, so
`(z,θ)` is not in the bad set. -/
theorem notMemBad_of_good {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {Lc : ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ} {w : ℝ × ℝ → ℝ}
    (hLc_eq : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, Lc z θ = Llim z θ)
    {θ : ℝ} (hθI : θ ∈ Set.Icc c d) {z : ℝ} (hzIoo : z ∈ Set.Ioo a b)
    (hidz : ∀ z' ∈ Set.Icc a b, Llim z' θ - Llim z θ = ∫ u in z..z', w (u, θ))
    (hgood : ∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)
    (hint : IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume) :
    (z, θ) ∉ BadSet (a := a) (b := b) (c := c) (d := d) Lc w := by
  intro hzbad
  obtain ⟨hzbox, k, hk⟩ := hzbad
  have hzab : z ∈ Set.Icc a b := ⟨le_of_lt hzIoo.1, le_of_lt hzIoo.2⟩
  have haab : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr (le_of_lt hab)
  obtain ⟨δ, hδpos, hδ⟩ :=
    exists_delta_hasDerivAt (hgood a (Set.left_mem_uIcc))
      (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 / ((m : ℝ) + 1) ≤ δ := by
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
    refine ⟨m, ?_⟩
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    rw [div_lt_iff₀ hδpos] at hm
    linarith
  obtain ⟨h, hh1, hh2, hh3, hh4⟩ := hk m
  have hzhmem : z + (h : ℝ) ∈ Set.Icc a b := hh3
  have hi1 : IntervalIntegrable (fun t => w (t, θ)) volume a (z + (h : ℝ)) :=
    (hint.mono_set (by
      rw [Set.uIcc_of_le hzhmem.1]
      exact Set.Icc_subset_Icc_right hzhmem.2)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => w (t, θ)) volume a z :=
    (hint.mono_set (by
      rw [Set.uIcc_of_le hzab.1]
      exact Set.Icc_subset_Icc_right hzab.2)).intervalIntegrable
  have hq : (Lc (z + (h : ℝ)) θ - Lc z θ) / (h : ℝ)
      = (((fun x => ∫ t in a..x, w (t, θ)) (z + (h : ℝ)))
          - ((fun x => ∫ t in a..x, w (t, θ)) z)) / (h : ℝ) := by
    have h1 : Lc (z + (h : ℝ)) θ - Lc z θ = ∫ u in z..(z + (h : ℝ)), w (u, θ) := by
      rw [hLc_eq (z + (h : ℝ)) hzhmem θ hθI, hLc_eq z hzab θ hθI,
        ← hidz (z + (h : ℝ)) hzhmem]
    have h2 : ((fun x => ∫ t in a..x, w (t, θ)) (z + (h : ℝ)))
        - ((fun x => ∫ t in a..x, w (t, θ)) z) = ∫ u in z..(z + (h : ℝ)), w (u, θ) :=
      intervalIntegral.integral_interval_sub_left hi1 hi2
    rw [h1, h2]
  have hh1' : 0 < |z + (h : ℝ) - z| := by simpa using hh1
  have hh2' : |z + (h : ℝ) - z| < δ := by
    have : |(h : ℝ)| < 1 / ((m : ℝ) + 1) := hh2
    simp only [add_sub_cancel_left]
    exact lt_of_lt_of_le this hm
  have hbound := hδ (z + (h : ℝ)) hh1' hh2'
  simp only [add_sub_cancel_left] at hbound
  rw [hq] at hh4
  exact absurd hh4 (not_lt.mpr hbound.le)

/-- **Forward direction**: if the rational difference quotients of the clamped limit satisfy the
quantitative bounds (all `k`, on a small interval of steps), then the honest difference quotients
of `Llim (·,θ)` at `z` converge to `w (z,θ)`, so the derivative exists and equals `w (z,θ)`. -/
theorem hasDerivAt_of_notMemBad {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {Lc : ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ} {w : ℝ × ℝ → ℝ}
    (hLc_cont : Continuous (Function.uncurry Lc))
    (hLc_eq : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, Lc z θ = Llim z θ)
    {θ : ℝ} (hθI : θ ∈ Set.Icc c d) {z : ℝ} (hzIoo : z ∈ Set.Ioo a b)
    (hidz : ∀ z' ∈ Set.Icc a b, Llim z' θ - Llim z θ = ∫ u in z..z', w (u, θ))
    (hint : IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume)
    (hnb : (z, θ) ∉ BadSet (a := a) (b := b) (c := c) (d := d) Lc w) :
    HasDerivAt (fun z' => Llim z' θ) (w (z, θ)) z := by
  have hzab : z ∈ Set.Icc a b := ⟨le_of_lt hzIoo.1, le_of_lt hzIoo.2⟩
  -- the quantitative statement extracted from `¬Bad`
  have hQ : ∀ k : ℕ, ∃ m : ℕ, ∀ h : ℚ, 0 < |(h : ℝ)| → |(h : ℝ)| < 1 / ((m : ℝ) + 1) →
      z + (h : ℝ) ∈ Set.Icc a b →
      |(Lc (z + (h : ℝ)) θ - Lc z θ) / (h : ℝ) - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    by_contra hcon
    push Not at hcon
    exact hnb ⟨⟨hzab, hθI⟩, k, fun m => hcon m⟩
  -- the `ε`-`δ` statement for the difference quotients
  have hεδ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < |y - z| → |y - z| < δ →
      |(Llim y θ - Llim z θ) / (y - z) - w (z, θ)| < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < ε := by
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
      refine ⟨k, ?_⟩
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      rw [div_lt_iff₀ hε] at hk
      linarith
    obtain ⟨m, hm⟩ := hQ k
    obtain ⟨δc, hδcpos, hδc1, hδc2, hδc3⟩ : ∃ δc : ℝ, 0 < δc ∧ δc ≤ 1 / ((m : ℝ) + 1) ∧
        δc ≤ z - a ∧ δc ≤ b - z :=
      ⟨min (1 / ((m : ℝ) + 1)) (min (z - a) (b - z)),
        lt_min (by positivity) (lt_min (by linarith [hzIoo.1]) (by linarith [hzIoo.2])),
        min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
        le_trans (min_le_right _ _) (min_le_right _ _)⟩
    have hcont1 : Continuous fun t : ℝ => Lc (z + t) θ :=
      hLc_cont.comp ((continuous_const.add continuous_id).prodMk continuous_const)
    have hcont_pos : ContinuousOn (fun t : ℝ => (Lc (z + t) θ - Lc z θ) / t - w (z, θ))
        (Set.Ioo (0 : ℝ) δc) := by
      have hnum : ContinuousOn (fun t : ℝ => Lc (z + t) θ - Lc z θ) (Set.Ioo (0 : ℝ) δc) :=
        (hcont1.sub continuous_const).continuousOn
      exact (hnum.div continuousOn_id (fun t ht => ne_of_gt ht.1)).sub continuousOn_const
    have hcont_neg : ContinuousOn (fun t : ℝ => (Lc (z + t) θ - Lc z θ) / t - w (z, θ))
        (Set.Ioo (-δc) 0) := by
      have hnum : ContinuousOn (fun t : ℝ => Lc (z + t) θ - Lc z θ) (Set.Ioo (-δc) 0) :=
        (hcont1.sub continuous_const).continuousOn
      exact (hnum.div continuousOn_id (fun t ht => ne_of_lt ht.2)).sub continuousOn_const
    -- the rational bounds on either half-interval
    have hrat : ∀ t : ℚ, (t : ℝ) ∈ Set.Ioo (-δc) 0 ∪ Set.Ioo (0 : ℝ) δc →
        |(Lc (z + (t : ℝ)) θ - Lc z θ) / (t : ℝ) - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) := by
      intro t ht
      have htabs : |(t : ℝ)| < δc := by
        rcases ht with ht | ht
        · rw [abs_of_neg ht.2]; linarith [ht.1]
        · rw [abs_of_pos ht.1]; exact ht.2
      have ht0 : 0 < |(t : ℝ)| := abs_pos.mpr (by
        rcases ht with ht | ht
        · exact ne_of_lt ht.2
        · exact ne_of_gt ht.1)
      have htz : z + (t : ℝ) ∈ Set.Icc a b := by
        rcases ht with ht | ht
        · -- the negative side
          refine ⟨by linarith [ht.1, hδc2], by linarith [hzIoo.2, ht.2]⟩
        · -- the positive side
          refine ⟨by linarith [hzIoo.1, ht.1], by linarith [ht.2, hδc3]⟩
      exact hm t ht0 (lt_of_lt_of_le htabs hδc1) htz
    have hbound_pos : ∀ t ∈ Set.Ioo (0 : ℝ) δc,
        |(Lc (z + t) θ - Lc z θ) / t - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) :=
      abs_le_of_forall_rat_of_continuousOn isOpen_Ioo hcont_pos (fun q hq => hrat q (Or.inr hq))
    have hbound_neg : ∀ t ∈ Set.Ioo (-δc) 0,
        |(Lc (z + t) θ - Lc z θ) / t - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) :=
      abs_le_of_forall_rat_of_continuousOn isOpen_Ioo hcont_neg (fun q hq => hrat q (Or.inl hq))
    refine ⟨δc, hδcpos, fun y hy hyδ => ?_⟩
    have hyne : y - z ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hy
      exact absurd hy (lt_irrefl 0)
    have hyab : y ∈ Set.Icc a b := by
      rcases lt_or_gt_of_ne hyne with hneg | hpos
      · rw [abs_of_neg hneg] at hyδ
        exact ⟨by linarith [hδc2], by linarith [hzIoo.2, hneg]⟩
      · rw [abs_of_pos hpos] at hyδ
        exact ⟨by linarith [hzIoo.1, hpos], by linarith [hδc3]⟩
    have hbound : |(Lc y θ - Lc z θ) / (y - z) - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) := by
      rcases lt_or_gt_of_ne hyne with hneg | hpos
      · have hmem : y - z ∈ Set.Ioo (-δc) 0 := by
          refine ⟨?_, hneg⟩
          rw [abs_of_neg hneg] at hyδ; linarith
        have := hbound_neg (y - z) hmem
        rwa [show z + (y - z) = y from by ring] at this
      · have hmem : y - z ∈ Set.Ioo (0 : ℝ) δc := by
          refine ⟨hpos, ?_⟩
          rw [abs_of_pos hpos] at hyδ; exact hyδ
        have := hbound_pos (y - z) hmem
        rwa [show z + (y - z) = y from by ring] at this
    -- convert to the primitive's difference quotient
    have hb2 : |(Llim y θ - Llim z θ) / (y - z) - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) := by
      rw [← hLc_eq y hyab θ hθI, ← hLc_eq z hzab θ hθI]
      exact hbound
    have hi1 : IntervalIntegrable (fun t => w (t, θ)) volume a y :=
      (hint.mono_set (by
        rw [Set.uIcc_of_le hyab.1]
        exact Set.Icc_subset_Icc_right hyab.2)).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t => w (t, θ)) volume a z :=
      (hint.mono_set (by
        rw [Set.uIcc_of_le hzab.1]
        exact Set.Icc_subset_Icc_right hzab.2)).intervalIntegrable
    rw [hidz y hyab, ← intervalIntegral.integral_interval_sub_left hi1 hi2] at hb2 ⊢
    exact lt_of_le_of_lt hb2 hk
  -- conclude
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hεδ ε hε
  rw [eventually_nhdsWithin_iff]
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds z hδpos) fun y hy hyne => ?_
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hyne
  have hyδ : |y - z| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hy
  have hy0 : 0 < |y - z| := by
    rw [abs_pos]
    intro h0
    exact hyne (sub_eq_zero.mp h0)
  have h := hδ y hy0 hyδ
  rw [slope_def_field, Real.dist_eq]
  simpa [abs_sub_comm] using h



/-! ## The main identification statement -/

theorem ae_limit_eq_deriv {a b a₀ b₀ c d : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a < b)
    (hbb₀ : b < b₀) (hcd : c < d)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ} {W : ℕ → ℝ × ℝ → ℝ} {w : ℝ × ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (fun p : ℝ × ℝ => L n p.1 p.2) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hslice : ∀ n, ∀ θ ∈ Set.Icc c d, ContDiffOn ℝ 1 (fun z => L n z θ) (Set.Ioo a₀ b₀))
    (hW : ∀ n, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, W n p = Work.Spaces.pz (L n) p.1 p.2)
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hwmeas : Measurable w)
    (hint : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
      Filter.Tendsto (fun k => ∫ u in z..z₀, W k (u, θ)) Filter.atTop
        (nhds (∫ u in z..z₀, w (u, θ))))
    (hwint : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)),
      IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume) :
    ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)),
      w p = Work.Spaces.pz Llim p.1 p.2 := by
  classical
  have hab' : a ≤ b := le_of_lt hab
  have hcd' : c ≤ d := le_of_lt hcd
  have hmemR : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc c d :=
    fun z hz θ hθ => Set.mem_prod.mpr ⟨hz, hθ⟩
  have hmemR₀ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (z, θ) ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d := fun z hz θ hθ => Set.mem_prod.mpr
    ⟨⟨by linarith [hz.1, ha₀a], by linarith [hz.2, hbb₀]⟩, hθ⟩
  have hIccab : ∀ z ∈ Set.Icc a b, z ∈ Set.Ioo a₀ b₀ := fun z hz =>
    ⟨by linarith [hz.1, ha₀a], by linarith [hz.2, hbb₀]⟩
  have hboxsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d := by
    intro p hp
    exact hmemR₀ p.1 hp.1 p.2 hp.2
  -- continuity of `Llim` on the box, and of the clamped version
  have hlimcont : ContinuousOn (Function.uncurry Llim) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    hconv.continuousOn (Filter.Eventually.of_forall hcont).frequently
  have hlimcont' : ContinuousOn (Function.uncurry Llim) (Set.Icc a b ×ˢ Set.Icc c d) :=
    hlimcont.mono hboxsub
  set Lc : ℝ → ℝ → ℝ := Lclamp hab' hcd' Llim with hLcdef
  have hLc_eq : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, Lc z θ = Llim z θ := by
    intro z hz θ hθ
    rw [hLcdef]
    simp only [Lclamp, Set.projIcc_of_mem hab' hz, Set.projIcc_of_mem hcd' hθ, Subtype.coe_mk]
  have hLccont : Continuous (Function.uncurry Lc) := by
    have h1a : Continuous fun p : ℝ × ℝ => ((Set.projIcc a b hab' p.1 : Set.Icc a b) : ℝ) :=
      continuous_subtype_val.comp
        ((continuous_projIcc (a := a) (b := b) (h := hab')).comp continuous_fst)
    have h1b : Continuous fun p : ℝ × ℝ => ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ) :=
      continuous_subtype_val.comp
        ((continuous_projIcc (a := c) (b := d) (h := hcd')).comp continuous_snd)
    have h1 : Continuous fun p : ℝ × ℝ =>
        (((Set.projIcc a b hab' p.1 : Set.Icc a b) : ℝ),
         ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) := h1a.prodMk h1b
    have h2 : ∀ p : ℝ × ℝ,
        (((Set.projIcc a b hab' p.1 : Set.Icc a b) : ℝ),
         ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) ∈ Set.Icc a b ×ˢ Set.Icc c d :=
      fun p => Set.mem_prod.mpr ⟨(Set.projIcc a b hab' p.1).2, (Set.projIcc c d hcd' p.2).2⟩
    have h4 : Function.uncurry Lc = (Function.uncurry Llim) ∘
        fun p : ℝ × ℝ =>
          (((Set.projIcc a b hab' p.1 : Set.Icc a b) : ℝ),
           ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) := by
      funext p
      simp only [Function.uncurry, Function.comp_apply, hLcdef, Lclamp]
    rw [h4]
    exact hlimcont'.comp_continuous h1 h2
  -- the identity for a.e. angle
  have hid : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
      Llim z₀ θ - Llim z θ = ∫ u in z..z₀, w (u, θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hint] with θ hθI hθ
    intro z hz z₀ hz₀
    have hFTC : ∀ k : ℕ, (∫ u in z..z₀, W k (u, θ)) = L k z₀ θ - L k z θ := by
      intro k
      have hsub : Set.uIcc z z₀ ⊆ Set.Icc a b := by
        rcases le_total z z₀ with hle | hle
        · rw [Set.uIcc_of_le hle]; exact Set.Icc_subset_Icc hz.1 hz₀.2
        · rw [Set.uIcc_of_ge hle]; exact Set.Icc_subset_Icc hz₀.1 hz.2
      have hderiv : ∀ u ∈ Set.uIcc z z₀, HasDerivAt (fun z' => L k z' θ) (W k (u, θ)) u := by
        intro u hu
        have huab : u ∈ Set.Icc a b := hsub hu
        have hd : HasDerivAt (fun z' => L k z' θ) (Work.Spaces.pz (L k) u θ) u :=
          (((hslice k θ hθI).differentiableOn (by simp)).differentiableAt
            (isOpen_Ioo.mem_nhds (hIccab u huab))).hasDerivAt
        have hWk : W k (u, θ) = Work.Spaces.pz (L k) u θ := by
          simpa using hW k (u, θ) (hmemR u huab θ hθI)
        rw [← hWk] at hd
        exact hd
      have hii : IntervalIntegrable (fun u => W k (u, θ)) volume z z₀ := by
        have hcont' : ContinuousOn (fun u => Work.Spaces.pz (L k) u θ) (Set.uIcc z z₀) :=
          ((hslice k θ hθI).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono
            (fun u hu => hIccab u (hsub hu))
        have hloc : IntegrableOn (fun u => W k (u, θ)) (Set.uIcc z z₀) volume :=
          (hcont'.integrableOn_compact isCompact_uIcc).congr_fun
            (fun u hu => (hW k (u, θ) (hmemR u (hsub hu) θ hθI)).symm) measurableSet_uIcc
        exact hloc.intervalIntegrable
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii]
    have h2 : Filter.Tendsto (fun k => L k z₀ θ - L k z θ) Filter.atTop
        (nhds (Llim z₀ θ - Llim z θ)) := by
      have hA : Filter.Tendsto (fun k => L k z₀ θ) Filter.atTop (nhds (Llim z₀ θ)) := by
        simpa using hconv.tendsto_at (hmemR₀ z₀ hz₀ θ hθI)
      have hB : Filter.Tendsto (fun k => L k z θ) Filter.atTop (nhds (Llim z θ)) := by
        simpa using hconv.tendsto_at (hmemR₀ z hz θ hθI)
      exact hA.sub hB
    have h2' : Filter.Tendsto (fun k => ∫ u in z..z₀, W k (u, θ)) Filter.atTop
        (nhds (Llim z₀ θ - Llim z θ)) :=
      h2.congr' (Filter.Eventually.of_forall fun k => (hFTC k).symm)
    exact tendsto_nhds_unique h2' (hθ z hz z₀ hz₀)
  -- the Lebesgue differentiation theorem, for a.e. angle
  have hLDT : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), ∀ᵐ z ∂volume,
      z ∈ Set.uIcc a b → ∀ c' ∈ Set.uIcc a b,
        HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z := by
    filter_upwards [hwint] with θ hθ
    exact IntervalIntegrable.ae_hasDerivAt_integral
      ((hθ.mono_set (le_of_eq (Set.uIcc_of_le hab'))).intervalIntegrable)
  -- the set of good angles
  set Θ : Set ℝ := {θ | θ ∈ Set.Icc c d ∧
    (∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b, Llim z₀ θ - Llim z θ = ∫ u in z..z₀, w (u, θ)) ∧
    IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume ∧
    (∀ᵐ z ∂volume, z ∈ Set.uIcc a b → ∀ c' ∈ Set.uIcc a b,
      HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)} with hΘdef
  have hmemΘ : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), θ ∈ Θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hid, hwint, hLDT] with θ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hΘnull : (volume.restrict (Set.Icc c d)) Θᶜ = 0 := MeasureTheory.ae_iff.mp hmemΘ
  -- the "bad" set is measurable
  have hBadmeas : MeasurableSet (BadSet (a := a) (b := b) (c := c) (d := d) Lc w) :=
    badSet_measurable hLccont hwmeas
  -- its sections are a.e. null
  have hsec : ∀ θ ∈ Θ,
      (volume.restrict (Set.Icc a b)) {z | (z, θ) ∈ BadSet (a := a) (b := b) (c := c) (d := d) Lc w}
        = 0 := by
    intro θ hθ
    obtain ⟨hθI, hθid, hθint, hθLDT⟩ := hθ
    have hnull : volume {z : ℝ | z ∈ Set.uIcc a b ∧
        ¬ (∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)}
        = 0 := by
      refine measure_mono_null ?_ (MeasureTheory.ae_iff.mp hθLDT)
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      exact fun h => hz.2 (h hz.1)
    have hnull2 : volume ({a, b} : Set ℝ) = 0 :=
      ((Set.finite_singleton b).insert a).measure_zero volume
    have hsub2 : {z | (z, θ) ∈ BadSet (a := a) (b := b) (c := c) (d := d) Lc w} ⊆
        ({a, b} : Set ℝ) ∪ {z : ℝ | z ∈ Set.uIcc a b ∧
          ¬ (∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)} := by
      intro z hz
      by_cases hzab : z ∈ ({a, b} : Set ℝ)
      · exact Or.inl hzab
      right
      simp only [Set.mem_setOf_eq] at hz ⊢
      have hzI : z ∈ Set.Icc a b := hz.1.1
      refine ⟨by rw [Set.uIcc_of_le hab']; exact hzI, fun hgood => ?_⟩
      have hzIoo : z ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne hzI.1 (by intro h0; exact hzab (by simp [h0])),
          lt_of_le_of_ne hzI.2 (by intro h0; exact hzab (by simp [h0]))⟩
      exact absurd hz (notMemBad_of_good hab hcd hLc_eq hθI hzIoo
        (fun z' hz' => hθid z hzI z' hz') hgood hθint)
    refine le_antisymm ?_ bot_le
    calc (volume.restrict (Set.Icc a b))
          {z | (z, θ) ∈ BadSet (a := a) (b := b) (c := c) (d := d) Lc w}
        ≤ (volume.restrict (Set.Icc a b)) (({a, b} : Set ℝ) ∪ {z : ℝ | z ∈ Set.uIcc a b ∧
            ¬ (∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)}) :=
          measure_mono hsub2
      _ ≤ volume (({a, b} : Set ℝ) ∪ {z : ℝ | z ∈ Set.uIcc a b ∧
            ¬ (∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)}) :=
          Measure.restrict_apply_le _ _
      _ = 0 := measure_union_null hnull2 hnull
  -- the bad set is null (Fubini)
  have hBadnull : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      (BadSet (a := a) (b := b) (c := c) (d := d) Lc w) = 0 := by
    have hμν : (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))
        = volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
    rw [← hμν]
    have hsm : MeasurableSet (Prod.swap ⁻¹'
        BadSet (a := a) (b := b) (c := c) (d := d) Lc w) :=
      hBadmeas.preimage measurable_swap
    have hsec' : (fun θ => (volume.restrict (Set.Icc a b))
        (Prod.mk θ ⁻¹' (Prod.swap ⁻¹' BadSet (a := a) (b := b) (c := c) (d := d) Lc w)))
        =ᵐ[volume.restrict (Set.Icc c d)] 0 := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
      refine measure_mono_null ?_ hΘnull
      intro θ hθ
      simp only [Pi.zero_apply, Set.mem_setOf_eq] at hθ ⊢
      exact fun hΘmem => hθ (hsec θ hΘmem)
    have hmain := Measure.measure_prod_null_of_ae_null (μ := volume.restrict (Set.Icc c d))
      (ν := volume.restrict (Set.Icc a b)) hsm hsec'
    have hfab : (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))
        (BadSet (a := a) (b := b) (c := c) (d := d) Lc w)
        = (volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Icc a b))
          (Prod.swap ⁻¹' BadSet (a := a) (b := b) (c := c) (d := d) Lc w) := by
      rw [← Measure.map_apply measurable_swap hBadmeas,
        (Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc c d))
          (ν := volume.restrict (Set.Icc a b))).map_eq]
    rw [hfab]
    exact hmain
  -- the final a.e. statement
  rw [MeasureTheory.ae_iff]
  have hμν : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
  have hpiece0 : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      {p : ℝ × ℝ | p ∉ Set.Icc a b ×ˢ Set.Icc c d} = 0 := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | p ∉ Set.Icc a b ×ˢ Set.Icc c d} :=
      (measurableSet_Icc.prod measurableSet_Icc).compl
    rw [Measure.restrict_apply hmeas]
    have h0 : {p : ℝ × ℝ | p ∉ Set.Icc a b ×ˢ Set.Icc c d} ∩ (Set.Icc a b ×ˢ Set.Icc c d)
        = (∅ : Set (ℝ × ℝ)) := by
      ext p; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and]; exact fun h1 h2 => h1 h2
    rw [h0, measure_empty]
  have hpiece2 : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) {p : ℝ × ℝ | p.2 ∉ Θ} = 0 := by
    rw [hμν, show {p : ℝ × ℝ | p.2 ∉ Θ} = Set.univ ×ˢ Θᶜ from by
      ext p; simp]
    rw [Measure.prod_prod, hΘnull, mul_zero]
  have hpiece3 : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      {p : ℝ × ℝ | p.1 ∈ ({a, b} : Set ℝ)} = 0 := by
    rw [hμν, show {p : ℝ × ℝ | p.1 ∈ ({a, b} : Set ℝ)} = ({a, b} : Set ℝ) ×ˢ Set.univ from by
      ext p; simp]
    rw [Measure.prod_prod]
    have h0 : (volume.restrict (Set.Icc a b)) ({a, b} : Set ℝ) = 0 :=
      le_antisymm ((Measure.restrict_apply_le (Set.Icc a b) ({a, b} : Set ℝ)).trans
        (le_of_eq (((Set.finite_singleton b).insert a).measure_zero volume))) bot_le
    rw [h0, zero_mul]
  refine measure_mono_null ?_ (measure_union_null hpiece0 (measure_union_null hBadnull
    (measure_union_null hpiece2 hpiece3)))
  intro p hp
  by_cases hbox : p ∈ Set.Icc a b ×ˢ Set.Icc c d
  · by_cases h2 : p.2 ∉ Θ
    · exact Or.inr (Or.inr (Or.inl h2))
    · push Not at h2
      by_cases h3 : p.1 ∈ ({a, b} : Set ℝ)
      · exact Or.inr (Or.inr (Or.inr h3))
      · refine Or.inr (Or.inl ?_)
        by_contra hnb
        have hp1I : p.1 ∈ Set.Icc a b := hbox.1
        have hp1Ioo : p.1 ∈ Set.Ioo a b :=
          ⟨lt_of_le_of_ne hp1I.1 (by intro h0; exact h3 (by simp [h0])),
            lt_of_le_of_ne hp1I.2 (by intro h0; exact h3 (by simp [h0]))⟩
        obtain ⟨hθI, hθid, hθint, -⟩ := h2
        have hder := hasDerivAt_of_notMemBad hab hcd hLccont hLc_eq hθI hp1Ioo
          (fun z' hz' => hθid p.1 hp1I z' hz') hθint hnb
        have hdw : Work.Spaces.pz Llim p.1 p.2 = w p := by
          rw [show Work.Spaces.pz Llim p.1 p.2
            = deriv (fun z' => Llim z' p.2) p.1 from rfl]
          exact hder.deriv
        exact hp hdw.symm
  · exact Or.inl hbox

end Work.FTS.StrongEps.LocUnif.D5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.V5_eq_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The order-5 `ℋ`-majorant `V5` agrees a.e. with `ofReal (HkIntegrand α 5 f)`

`V5 α fn p` is, by definition, the `liminf`, as `n → ∞`, of `ofReal (HkIntegrand α 5 (fn n) p)`.
Every slot of `HkIntegrand α 5` is a `mixed j i` with `i + j ≤ 5` (the `D_z^i`-terms are the slots
`(j,i) = (i,0)`, since `mixed j 0 = DzIter j`).  The slots with `i + j ≤ 4` converge everywhere on
the rectangle `[a,b] × [c,d]` (hypothesis `hconv4`) and those with `i + j = 5` converge almost
everywhere (hypothesis `hconv5`), so a.e. the whole integrand converges and its `liminf` is the
value at `f`. -/

open MeasureTheory Filter

namespace Work.FTS.StrongEps.LocUnif

/-- **Convergence of the `ℋ^5`-integrand from convergence of the slots.**  If at a point `p` every
slot `D_z^j D_θ^i (fn n)` with `j + i ≤ 5` converges to the corresponding slot of `f`, then the
value of `HkIntegrand α 5 (fn n)` at `p` converges to the value at `p` of `HkIntegrand α 5 f`
(the weights depend only on `p`, and the sum is finite). -/
private lemma tendsto_HkIntegrand_of_tendsto_mixed {α : ℝ} {fn : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    {p : ℝ × ℝ}
    (h : ∀ j i : ℕ, j + i ≤ 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2))) :
    Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.HkIntegrand α 5 f p.1 p.2)) := by
  -- every summand is a slot times a weight depending only on `p`, squared
  have key : ∀ (c : ℝ) (j i : ℕ), j + i ≤ 5 →
      Filter.Tendsto (fun n => (Work.Spaces.mixed j i (fn n) p.1 p.2 * c) ^ 2) Filter.atTop
        (nhds ((Work.Spaces.mixed j i f p.1 p.2 * c) ^ 2)) :=
    fun c j i hji => ((h j i hji).mul_const c).pow 2
  simp only [Work.Spaces.HkIntegrand]
  refine Tendsto.add ?_ ?_
  · -- the `D_z^i`-block: `DzIter i g = mixed i 0 g`
    refine tendsto_finsetSum (Finset.range (5 + 1)) (fun i hi => ?_)
    exact key _ i 0 (by have := Finset.mem_range.mp hi; omega)
  · -- the mixed block
    refine tendsto_finsetSum (Finset.range (5 + 1)) (fun i hi => ?_)
    refine tendsto_finsetSum (Finset.range (5 + 1)) (fun j hj => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ 5
    · simp only [ite_eq_left hc]
      exact key _ j i (by omega)
    · simp only [ite_eq_right hc]
      exact tendsto_const_nhds

theorem V5_eq_ae {α : ℝ} {fn : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hconv4 : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, ∀ (j i : ℕ), j + i ≤ 4 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)))
    (hconv5 : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)),
      ∀ (j i : ℕ), j + i = 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2))) :
    Work.FTS.StrongEps.LocUnif.V5 α fn =ᵐ[MeasureTheory.volume.restrict
        (Set.Icc a b ×ˢ Set.Icc c d)]
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)) := by
  have hs : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  filter_upwards [hconv5, ae_restrict_mem hs] with p h5 hpmem
  rw [V5]
  -- all the slots of order `≤ 5` converge at `p`
  have hall : ∀ j i : ℕ, j + i ≤ 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    intro j i hji
    rcases lt_or_eq_of_le hji with hlt | heq
    · exact hconv4 p hpmem j i (by omega)
    · exact h5 j i heq
  have ht := tendsto_HkIntegrand_of_tendsto_mixed (α := α) hall
  exact ((ENNReal.continuous_ofReal.tendsto
    (Work.Spaces.HkIntegrand α 5 f p.1 p.2)).comp ht).liminf_eq

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_V6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## Auxiliary lemmas -/

/-- **A.e.-measurability transfers under a *vertical* translation.**  The second-coordinate
analogue of `aemeasurable_comp_sub_of_aemeasurable`: if `F` is a.e.-measurable on `A` and the
shift `q ↦ (q.1, q.2 - h)` maps `B` into `A`, then the composite is a.e.-measurable on `B`.

Proof: `AEMeasurable F (volume.restrict A)` unfolds to a *measurable* `g` with
`F =ᵐ[volume.restrict A] g`; the a.e.-equality is transported across the shift by
`ae_shift_preimage_sub_snd`, and `g ∘ shift` is measurable. -/
private theorem aemeasurable_comp_sub_snd_of_aemeasurable {A B : Set (ℝ × ℝ)} {h : ℝ}
    {β : Type*} [MeasurableSpace β] {F : ℝ × ℝ → β}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hmap : ∀ q ∈ B, (q.1, q.2 - h) ∈ A)
    (hf : AEMeasurable F (MeasureTheory.volume.restrict A)) :
    AEMeasurable (fun q : ℝ × ℝ => F (q.1, q.2 - h)) (MeasureTheory.volume.restrict B) := by
  obtain ⟨g, hgm, hfg⟩ := hf
  refine ⟨fun q : ℝ × ℝ => g (q.1, q.2 - h), hgm.comp ?_, ?_⟩
  · exact measurable_fst.prodMk (measurable_snd.sub measurable_const)
  · filter_upwards [ae_shift_preimage_sub_snd (Q := fun q => F q = g q) hAm hBm hfg hmap]
      with q hq
    exact hq

/-- **Dropping finitely many initial terms does not change a `liminf` over `atTop`.** -/
private theorem liminf_add_atTop_eq {u : ℕ → ℝ≥0∞} (n : ℕ) :
    Filter.liminf (fun j : ℕ => u (j + n)) Filter.atTop = Filter.liminf u Filter.atTop := by
  have h := Filter.liminf_comp u (fun j : ℕ => j + n) Filter.atTop
  rw [Filter.map_add_atTop_eq_nat n] at h
  exact h

/-- The level-6 weight function `rho6`, as a function of the point `(z,θ)`, is measurable. -/
private theorem measurable_rho6 (α : ℝ) (i : ℕ) :
    Measurable (fun p : ℝ × ℝ => rho6 α i p.1 p.2) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hw : Measurable (fun z : ℝ => Work.Spaces.w z) := by
    rw [show Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 from rfl]
    exact ((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)
  by_cases hi : i = 0
  · have hρ : (fun p : ℝ × ℝ => rho6 α i p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
      funext p
      simp only [rho6, hi, ite_true]
    rw [hρ]
    exact (hw.comp measurable_fst).div ((hsin.comp measurable_snd).pow_const _)
  · have hρ : (fun p : ℝ × ℝ => rho6 α i p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p
      simp only [rho6, hi, ite_false, Work.Spaces.Wt, Work.Spaces.wTheta]
    rw [hρ]
    exact (hw.comp measurable_fst).mul ((hsin.comp measurable_snd).pow_const _)

theorem aemeasurable_V6 {α : ℝ} {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hd : d < π / 2)
    (hW : ∀ (j i : ℕ), j + i = 5 →
      AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))) :
    AEMeasurable (Work.FTS.StrongEps.LocUnif.V6z α f)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) ∧
      AEMeasurable (Work.FTS.StrongEps.LocUnif.V6t α f)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  have hQmeas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hBmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hBQ : (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ))
      ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    rintro ⟨z, θ⟩ hx
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hx
    obtain ⟨haz, hzb⟩ := Set.mem_Icc.mp hz
    obtain ⟨hcθ, hθd⟩ := Set.mem_Icc.mp hθ
    exact Set.mem_prod.mpr
      ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩
  -- Number of initial shifts that have to be discarded.
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / min a c)
  have hmpos : 0 < min a c := lt_min ha hc
  have hNmul : 1 < (N : ℝ) * min a c := by
    have h := (div_lt_iff₀ hmpos).mp hN
    linarith
  have hnN : 1 / ((N : ℝ) + 1) < min a c := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hsh : ∀ j : ℕ, 1 / (((j + N : ℕ) : ℝ) + 1) < min a c := by
    intro j
    have hle : ((N : ℝ) + 1) ≤ (((j + N : ℕ) : ℝ) + 1) := by
      have h1 : (N : ℕ) ≤ j + N := Nat.le_add_left N j
      have h2 : (N : ℝ) ≤ ((j + N : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hmono := one_div_le_one_div_of_le hpos hle
    linarith
  -- The shifts stay inside the open quadrant.
  have hmapz : ∀ j : ℕ, ∀ q ∈ (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)),
      (q.1 - 1 / (((j + N : ℕ) : ℝ) + 1), q.2)
        ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    intro j q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    obtain ⟨haz, hzb⟩ := Set.mem_Icc.mp hq1
    obtain ⟨hcθ, hθd⟩ := Set.mem_Icc.mp hq2
    have h1 : 1 / (((j + N : ℕ) : ℝ) + 1) < a :=
      lt_of_lt_of_le (hsh j) (min_le_left _ _)
    have hp : 0 < q.1 - 1 / (((j + N : ℕ) : ℝ) + 1) := by linarith
    have hp2 : 0 < q.2 := by linarith
    have hq2' : q.2 < π / 2 := by linarith
    exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hp, Set.mem_Ioo.mpr ⟨hp2, hq2'⟩⟩
  have hmapθ : ∀ j : ℕ, ∀ q ∈ (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)),
      (q.1, q.2 - 1 / (((j + N : ℕ) : ℝ) + 1))
        ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    intro j q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    obtain ⟨haz, hzb⟩ := Set.mem_Icc.mp hq1
    obtain ⟨hcθ, hθd⟩ := Set.mem_Icc.mp hq2
    have h1 : 1 / (((j + N : ℕ) : ℝ) + 1) < c :=
      lt_of_lt_of_le (hsh j) (min_le_right _ _)
    have hpos : (0 : ℝ) < 1 / (((j + N : ℕ) : ℝ) + 1) := by positivity
    have hp : 0 < q.1 := by linarith
    have hp2 : 0 < q.2 - 1 / (((j + N : ℕ) : ℝ) + 1) := by linarith
    have hq2' : q.2 - 1 / (((j + N : ℕ) : ℝ) + 1) < π / 2 := by linarith
    exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hp, Set.mem_Ioo.mpr ⟨hp2, hq2'⟩⟩
  -- A.e.-measurability of a single `z`-difference quotient term (generic shift and constant).
  have key : ∀ (h cst : ℝ), (∀ q ∈ (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)),
        (q.1 - h, q.2) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) →
      AEMeasurable (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - h) p.2) * cst
          * (p.1 * rho6 α i p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
    intro h cst hmap
    have hterm : ∀ i ∈ Finset.range 6, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - h) p.2) * cst
          * (p.1 * rho6 α i p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hbase : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed (5 - i) i f p.1 p.2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        AEMeasurable.mono_set hBQ (hW (5 - i) i (by omega))
      have hshift : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed (5 - i) i f (p.1 - h) p.2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        aemeasurable_comp_sub_of_aemeasurable
          (f := fun p : ℝ × ℝ => Work.Spaces.mixed (5 - i) i f p.1 p.2)
          hQmeas hBmeas hmap (hW (5 - i) i (by omega))
      have hw : AEMeasurable (fun p : ℝ × ℝ => p.1 * rho6 α i p.1 p.2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        (measurable_fst.mul (measurable_rho6 α i)).aemeasurable
      exact ((((hbase.sub hshift).mul_const cst).mul hw).pow_const 2).ennreal_ofReal
    exact Finset.aemeasurable_sum (Finset.range 6) hterm
  -- A.e.-measurability of the `θ`-difference quotient term.
  have keyT : ∀ (h cst : ℝ), (∀ q ∈ (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)),
        (q.1, q.2 - h) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) →
      AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - h)) * cst
          * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
    intro h cst hmap
    have hbase : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed 0 5 f p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      AEMeasurable.mono_set hBQ (hW 0 5 (by norm_num))
    have hshift : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed 0 5 f p.1 (p.2 - h))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      aemeasurable_comp_sub_snd_of_aemeasurable
        (F := fun p : ℝ × ℝ => Work.Spaces.mixed 0 5 f p.1 p.2)
        hQmeas hBmeas hmap (hW 0 5 (by norm_num))
    have hw : AEMeasurable (fun p : ℝ × ℝ => Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      ((Real.measurable_sin.comp (measurable_const.mul measurable_snd)).mul
        (measurable_rho6 α 6)).aemeasurable
    exact ((((hbase.sub hshift).mul_const cst).mul hw).pow_const 2).ennreal_ofReal
  constructor
  · have hseq : ∀ j : ℕ, AEMeasurable (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / (((j + N : ℕ) : ℝ) + 1)) p.2)
          * (((j + N : ℕ) : ℝ) + 1) * (p.1 * rho6 α i p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      fun j => key (1 / (((j + N : ℕ) : ℝ) + 1)) (((j + N : ℕ) : ℝ) + 1) (hmapz j)
    have hlim := AEMeasurable.liminf hseq
    have heq : V6z α f = fun p : ℝ × ℝ => Filter.liminf (fun j : ℕ =>
        ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / (((j + N : ℕ) : ℝ) + 1)) p.2)
          * (((j + N : ℕ) : ℝ) + 1) * (p.1 * rho6 α i p.1 p.2)) ^ 2)) Filter.atTop := by
      funext p
      show Filter.liminf (fun j : ℕ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / ((j : ℝ) + 1)) p.2)
          * ((j : ℝ) + 1) * (p.1 * rho6 α i p.1 p.2)) ^ 2)) Filter.atTop = _
      exact (liminf_add_atTop_eq N (u := fun j : ℕ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / ((j : ℝ) + 1)) p.2)
          * ((j : ℝ) + 1) * (p.1 * rho6 α i p.1 p.2)) ^ 2))).symm
    rw [heq]
    exact hlim
  · have hseq : ∀ j : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / (((j + N : ℕ) : ℝ) + 1)))
          * (((j + N : ℕ) : ℝ) + 1)
          * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      fun j => keyT (1 / (((j + N : ℕ) : ℝ) + 1)) (((j + N : ℕ) : ℝ) + 1) (hmapθ j)
    have hlim := AEMeasurable.liminf hseq
    have heq : V6t α f = fun p : ℝ × ℝ => Filter.liminf (fun j : ℕ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / (((j + N : ℕ) : ℝ) + 1)))
          * (((j + N : ℕ) : ℝ) + 1)
          * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2)) Filter.atTop := by
      funext p
      show Filter.liminf (fun j : ℕ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / ((j : ℝ) + 1)))
          * ((j : ℝ) + 1) * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2)) Filter.atTop = _
      exact (liminf_add_atTop_eq N (u := fun j : ℕ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / ((j : ℝ) + 1)))
          * ((j : ℝ) + 1) * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2))).symm
    rw [heq]
    exact hlim

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The backward difference-quotient weighted `L²` bound

`diffQuot_backward_lintegral_le`: the weighted `L²`-norm of the backward difference quotient
`z ↦ (u z θ - u (z - h) θ)/h` over `[a', b'] × [c, d]` is bounded by `C` times the weighted
`L²`-norm of `∂_z u` over the larger rectangle `[a, b] × [c, d]`.

The proof is the standard local-uniformity computation: the fundamental theorem of calculus
writes the difference quotient as the mean of `∂_z u` over the window `[z - h, z]`, Cauchy–Schwarz
bounds the square of the mean by the mean of the squares, and the hypothesis `hCw` compares the
weight `w z θ` with `w (z - s) θ` inside the window.  The remaining task is measure-theoretic: the
sliding-window average must be exchanged with the outer integral, done with Tonelli
(`lintegral_lintegral_shift_le`) after replacing the (only a.e. measurable) integrand by a
measurable representative (`ae_lintegral_shift_eq`, from `ae_shift_measure_null`).
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The sliding-window average only sees a null set of parameters.** If `G` and `G'` agree
a.e. on `[a,b] × [c,d]`, then for a.e. `p` in the smaller rectangle `[a',b'] × [c,d]` the
`s`-integrals of `G (p.1 - s, p.2)` and `G' (p.1 - s, p.2)` over `(0, h]` coincide.

This is the a.e. form of "the shift `(p, s) ↦ (p.1 - s, p.2)` pushes a null set of
`[a,b] × [c,d]` to a null set" (`ae_shift_measure_null`); the hypotheses `h < a' - a` and
`b' < b` guarantee that every shifted point `(p.1 - s, p.2)` lies in the larger rectangle, so
the null set where `G ≠ G'` is exactly what has to be avoided. -/
theorem ae_lintegral_shift_eq {a b a' b' c d h : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a)
    {G G' : ℝ × ℝ → ENNReal}
    (hae : G =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)] G') :
    (fun p : ℝ × ℝ => ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2))
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)]
      (fun p : ℝ × ℝ => ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)) := by
  set N : Set (ℝ × ℝ) := {q : ℝ × ℝ | ¬ (G q = G' q)} with hNdef
  have hbad : (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) N = 0 := by
    rw [hNdef]; exact MeasureTheory.ae_iff.mp hae
  set B : Set (ℝ × ℝ) := MeasureTheory.toMeasurable
    (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) N with hBdef
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact measurableSet_toMeasurable _ _
  have hBnull : (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) B = 0 := by
    rw [hBdef, MeasureTheory.measure_toMeasurable]; exact hbad
  have hsub : N ⊆ B := by rw [hBdef]; exact MeasureTheory.subset_toMeasurable _ _
  refine (ae_shift_measure_null haa' hb'b hh hah hBmeas hBnull).mono fun p hp => ?_
  refine lintegral_congr_ae (MeasureTheory.ae_iff.mpr ?_)
  refine measure_mono_null (fun s hs => ?_) hp
  exact hsub hs

theorem diffQuot_backward_lintegral_le {a b a' b' c d h C : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ h → (w z θ) ^ 2 ≤ C * (w y θ) ^ 2)
    (hu_sm : ∀ θ ∈ Set.Icc c d, ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b))
    (hu_c : ∀ θ ∈ Set.Icc c d, ContinuousOn (fun z => u z θ) (Set.Icc a b))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal C * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2) := by
  set G : ℝ × ℝ → ENNReal :=
    fun q => ENNReal.ofReal ((deriv (fun z' => u z' q.2) q.1) ^ 2 * (w q.1 q.2) ^ 2) with hGdef
  have hGmeas : AEMeasurable G (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    hmeas
  obtain ⟨G', hG'meas, hG'ae⟩ := hGmeas
  have hcne : ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hh).ne')
  -- Step 1: the pointwise weighted Cauchy–Schwarz / Jensen bound, integrated.
  have hstep1 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2) := by
    rw [← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)
          (f := fun p : ℝ × ℝ =>
            ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)),
        ← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)
          (f := fun p : ℝ × ℝ => ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2)),
        ← lintegral_const_mul' _ _ hcne]
    refine lintegral_mono fun p => ?_
    by_cases hp : p ∈ Set.Icc a' b' ×ˢ Set.Icc c d
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      exact diffQuot_pointwise_le haa' hb'b hh hah hC hw hCw hu_sm hp.1 hp.2
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
  -- Step 2: replace `G` by the measurable representative `G'` (a.e. in `p`).
  have hstep2 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2)
      = ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2) :=
    lintegral_congr_ae (ae_lintegral_shift_eq haa' hb'b hh hah hG'ae)
  -- Step 3: Tonelli + translation invariance of Lebesgue measure.
  have hstep3 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)
      ≤ ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q :=
    lintegral_lintegral_shift_le haa' hb'b hh hah hG'meas
  -- Step 4: back to `G` on the large rectangle.
  have hstep4 : ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q
      = ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q :=
    lintegral_congr_ae hG'ae.symm
  calc ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2) := hstep1
    _ = (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2) := by rw [hstep2]
    _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        (ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q) :=
        mul_le_mul_right hstep3 _
    _ = (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        (ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q) := by rw [hstep4]
    _ = ENNReal.ofReal C * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q := by
        rw [mul_assoc, ← mul_assoc (ENNReal.ofReal h)⁻¹,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hh).ne' ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal C * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun z' => u z' q.2) q.1) ^ 2 * (w q.1 q.2) ^ 2) := rfl

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.level6_identities =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- The child `D_z`-slot of the level-`(j+1)` slot `mixed j i g` is `z` times the plain
`z`-derivative of the parent: this is `D_z (D_z^j D_θ^i g) = z ∂_z (D_z^j D_θ^i g)`. -/
lemma mixed_succ_fst (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed (j + 1) i g
      = fun z θ => z * deriv (fun z' => Work.Spaces.mixed j i g z' θ) z := rfl


theorem level6_identities (α : ℝ) :
    (∀ (g : ℝ → ℝ → ℝ) (z θ : ℝ),
        Work.Spaces.HkIntegrand α 6 g z θ
          = Work.Spaces.HkIntegrand α 5 g z θ
            + Work.FTS.StrongEps.LocUnif.level6Z α g z θ
            + Work.FTS.StrongEps.LocUnif.level6T α g z θ) ∧
    (∀ (g : ℝ → ℝ → ℝ) (p : ℝ × ℝ),
        Work.FTS.StrongEps.LocUnif.level6Z α g p.1 p.2
          = ∑ k ∈ Finset.range 6,
              (deriv (fun z' => Work.Spaces.mixed (5 - k) k g z' p.2) p.1
                * (p.1 * Work.FTS.StrongEps.LocUnif.rho6 α k p.1 p.2)) ^ 2) ∧
    (∀ (g : ℝ → ℝ → ℝ) (p : ℝ × ℝ),
        Work.FTS.StrongEps.LocUnif.level6T α g p.1 p.2
          = (deriv (fun θ' => Work.Spaces.mixed 0 5 g p.1 θ') p.2
                * (Real.sin (2 * p.2) * Work.FTS.StrongEps.LocUnif.rho6 α 6 p.1 p.2)) ^ 2)
    := by
  refine ⟨?_, ?_, ?_⟩
  · -- The level-6 integrand is the level-5 integrand plus the six `D_z`-directed slots
    -- `mixed (6-i) i` (`0 ≤ i ≤ 5`, weight `rho6 α i`) and the `D_θ`-directed slot
    -- `mixed 0 6` (weight `rho6 α 6 = Wt α`).
    intro g z θ
    simp only [Work.Spaces.HkIntegrand, level6Z, level6T, rho6,
      Finset.sum_range_succ, Finset.sum_range_zero,
      Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, Nat.reduceSub]
    simp
    ring
  · -- Each `D_z`-directed slot is `z ∂_z` of its level-5 parent.
    intro g p
    rw [level6Z]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ 5 := by simp [Finset.mem_range] at hk; omega
    have h6 : 6 - k = (5 - k) + 1 := by omega
    rw [h6, mixed_succ_fst]
    ring
  · -- The `D_θ`-directed slot is `sin(2θ) ∂_θ` of its level-5 parent.
    intro g p
    rw [level6T]
    have h : Work.Spaces.mixed 0 6 g
        = fun z θ => Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.mixed 0 5 g z θ') θ := rfl
    rw [h]
    ring

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.lintegral_V5_le_liminf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∫⁻ V5 ≤ liminf ∫⁻ ofReal (HkIntegrand α 5 (fn n))`

`V5 α fn p` is *defined* as the `liminf`, as `n → ∞`, of `ofReal (HkIntegrand α 5 (fn n) p)`
(see `V5Defs`), so the inequality is exactly Fatou's lemma for the sequence of a.e.-measurable
functions `n ↦ ENNReal.ofReal (HkIntegrand α 5 (fn n) ·)`: the only hypothesis needed is the
a.e.-measurability of the members, which is the hypothesis `hmeas` of the statement.  Nothing
about the rectangle, or about `α`, is used. -/

namespace Work.FTS.StrongEps.LocUnif

theorem lintegral_V5_le_liminf {α : ℝ} {fn : ℕ → ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hmeas : ∀ n, AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d), Work.FTS.StrongEps.LocUnif.V5 α fn p
      ≤ Filter.liminf (fun n => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2)) Filter.atTop := by
  -- `V5 α fn p = liminf_n ofReal (HkIntegrand α 5 (fn n) p)`, so this is Fatou's lemma
  simpa only [Work.FTS.StrongEps.LocUnif.V5] using
    MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      (u := Filter.atTop)
      (f := fun (n : ℕ) (p : ℝ × ℝ) =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2))
      hmeas

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.holder_half_of_L4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

/-!
# The 2-D Morrey estimate `W^{1,4}(ℝ²) ⊂ C^{0,1/2}` with constant `4`

`|v p - v q| ≤ 4 (∫ ‖∇v‖⁴)^{1/4} √(dist p q)` for `v : ℝ × ℝ → ℝ` of class `C¹` with compact
support (and the fundamental-theorem-of-calculus identity along segments).

The proof averages the segment identity over the ball `B(0, a)`, `a = ρ/2 = dist p q / 2`:

* `leg_one_bound` : `⨍_{ζ ∈ B(0,a)} |v p - v (p+ζ)| ≤ √2 (∫‖∇v‖⁴)^{1/4} √a`;
* `leg_two_bound` : `⨍_{ζ ∈ B(0,a)} |v (p+ζ) - v q| ≤ √2 (∫‖∇v‖⁴)^{1/4} (a + dist p q)/√a`.

Both are proved by Fubini plus the substitution that scales the ball, followed by Hölder with
exponents `(4, 4/3)` on the ball `B(0, ta)` of volume `4t²a²`, and `∫_0^1 t^{-1/2} dt = 2`.
Adding the two legs (the ball has volume `4a²` in the product/sup norm on `ℝ × ℝ`, so
`1/(4a²) ∫_B` is the mean value) and using
`√2 (√a + (a+ρ)/√a) = 4√ρ` for `a = ρ/2` gives the stated constant `4`.
-/

/-- Ball volume in `ℝ × ℝ` in real-valued form (for normalising averages). -/
private lemma vol_ball_real (x : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (ℝ × ℝ)).real (Metric.ball x r) = 4 * r ^ 2 := by
  rw [Measure.real_def, vol_ball_prod x hr, ENNReal.toReal_ofReal (by positivity)]

/-- The arithmetic core of the two-leg estimate: for `a = ρ/2`,
`√2 (√a + (a+ρ)/√a) = 4√ρ`. -/
private lemma arith {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt 2 * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)) = 4 * Real.sqrt ρ := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt (ρ / 2) * Real.sqrt (ρ / 2) = ρ / 2 := Real.mul_self_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (ρ / 2) := Real.sqrt_pos.mpr (by positivity)
  have hrp : Real.sqrt ρ = Real.sqrt 2 * Real.sqrt (ρ / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hrp]
  field_simp
  nlinarith [h2, hs]

theorem holder_half_of_L4 {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p)) :
    ∀ p q : ℝ × ℝ, |v p - v q| ≤ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt (dist p q) := by
  intro p q
  rcases eq_or_ne p q with hp | hpq
  · subst hp
    simp
  let ρ : ℝ := dist p q
  have hρpos : 0 < ρ := dist_pos.mpr hpq
  have ha' : 0 < ρ / 2 := by positivity
  -- integrability of the two summands on the ball
  have hvint : Integrable v := hv.continuous.integrable_of_hasCompactSupport hc
  have hvit : Integrable (fun ζ : ℝ × ℝ => v (p + ζ)) := by
    have h := hvint.comp_add_right p
    simpa [add_comm] using h
  have hBne : (volume : Measure (ℝ × ℝ)) (Metric.ball (0 : ℝ × ℝ) (ρ / 2)) ≠ ⊤ := by
    rw [vol_ball_prod (0 : ℝ × ℝ) (by positivity)]
    exact ENNReal.ofReal_ne_top
  have hint1 : IntegrableOn (fun ζ : ℝ × ℝ => |v p - v (p + ζ)|)
      (Metric.ball (0 : ℝ × ℝ) (ρ / 2)) :=
    Integrable.norm ((integrableOn_const (C := v p) hBne).sub hvit.integrableOn)
  have hint2 : IntegrableOn (fun ζ : ℝ × ℝ => |v (p + ζ) - v q|)
      (Metric.ball (0 : ℝ × ℝ) (ρ / 2)) :=
    Integrable.norm (hvit.integrableOn.sub (integrableOn_const (C := v q) hBne))
  have hconstint : IntegrableOn (fun _ : ℝ × ℝ => |v p - v q|)
      (Metric.ball (0 : ℝ × ℝ) (ρ / 2)) :=
    integrableOn_const (C := |v p - v q|) hBne
  -- the averaging step: `|v p - v q|` is bounded by the mean of `|v p - v (p+ζ)| + |v(p+ζ) - v q|`
  have hvolreal : (volume : Measure (ℝ × ℝ)).real (Metric.ball (0 : ℝ × ℝ) (ρ / 2))
      = 4 * (ρ / 2) ^ 2 := vol_ball_real _ (by positivity)
  have hconst : ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v q|
      = (4 * (ρ / 2) ^ 2) * |v p - v q| := by
    rw [setIntegral_const, smul_eq_mul, hvolreal]
  have hmono : ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v q|
      ≤ ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2),
          (|v p - v (p + ζ)| + |v (p + ζ) - v q|) := by
    refine integral_mono hconstint (hint1.add hint2) (fun ζ => ?_)
    calc |v p - v q| = |(v p - v (p + ζ)) + (v (p + ζ) - v q)| := by ring_nf
      _ ≤ |v p - v (p + ζ)| + |v (p + ζ) - v q| := abs_add_le _ _
  have hadd : ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2),
        (|v p - v (p + ζ)| + |v (p + ζ) - v q|)
      = (∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
        + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q| :=
    integral_add hint1 hint2
  have hstep : (4 * (ρ / 2) ^ 2) * |v p - v q|
      ≤ (∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
        + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q| := by
    rw [← hconst]
    exact hmono.trans (le_of_eq hadd)
  have key : |v p - v q| ≤ (1 / (4 * (ρ / 2) ^ 2)) *
      ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
        + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|) := by
    have hpos : 0 < 4 * (ρ / 2) ^ 2 := by positivity
    calc |v p - v q| = (1 / (4 * (ρ / 2) ^ 2)) * ((4 * (ρ / 2) ^ 2) * |v p - v q|) := by
          field_simp
      _ ≤ (1 / (4 * (ρ / 2) ^ 2)) *
            ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
              + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  -- the two leg estimates
  have hl1 := leg_one_bound (v := v) hv hc hseg p ha'
  have hl2 := leg_two_bound (v := v) hv hc hseg p q ha'
  have hG4 : (0 : ℝ) ≤ (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) := integral_nonneg (fun x => by positivity)
  have hcomb : (1 / (4 * (ρ / 2) ^ 2)) *
        ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
          + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|)
      ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
          * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)) := by
    calc (1 / (4 * (ρ / 2) ^ 2)) *
          ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
            + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|)
        = (1 / (4 * (ρ / 2) ^ 2)) * (∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
          + (1 / (4 * (ρ / 2) ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q| := by
            ring
      _ ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt (ρ / 2)
          + Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
              * ((ρ / 2 + ρ) / Real.sqrt (ρ / 2)) := add_le_add hl1 hl2
      _ = Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
            * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)) := by ring
  have harith : Real.sqrt 2 * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2))
      = 4 * Real.sqrt ρ := arith hρpos
  calc |v p - v q| ≤ (1 / (4 * (ρ / 2) ^ 2)) *
        ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
          + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|) := key
    _ ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
          * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)) := hcomb
    _ = 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt ρ := by
        have e : Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
              * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2))
            = (Real.sqrt 2 * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)))
              * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) := by ring
        rw [e, harith]
        ring
    _ = 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt (dist p q) := by
        rw [show ρ = dist p q from rfl]

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux.Abnd_rpow_sq_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T45Aux

/-- Pointwise form of the angular bound.  For `i ≠ 0` the factor `Abnd α i θ` is
`(α + sin 2θ)·sin(2θ)^{α/5}`, hence
`sin(2θ)^{-q}·Abnd α i θ² ≤ 4·sin(2θ)^{2α/5 - q}`: the first factor contributes
`(α + sin 2θ)² ≤ 4` and the second `sin(2θ)^{2α/5}·sin(2θ)^{-q} = sin(2θ)^{2α/5-q}`. -/
private lemma Abnd_rpow_mul_sq_le {α q : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {i : ℕ}
    (hi : i ≠ 0) (hq1 : 1 ≤ q) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-q) * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2
      ≤ 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hα5' : α / 5 + α / 5 ≠ 0 := by linarith
  have hAbnd : Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ
      = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.Abnd, hi, ↓reduceIte]
  have hpow : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
    rw [pow_two, ← Real.rpow_add' hs hα5']
    congr 1
    ring
  have hab : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
    have h0 : 0 ≤ α + Real.sin (2 * θ) := by linarith
    nlinarith [sq_nonneg (α + Real.sin (2 * θ) - 2)]
  have hne : -q + 2 * (α / 5) ≠ 0 := by
    have h2 : 2 * (α / 5) ≤ 2 / 5 := by linarith
    linarith
  have key : (Real.sin (2 * θ)) ^ (-q) * (4 * (Real.sin (2 * θ)) ^ (2 * (α / 5)))
      = 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q) := by
    rw [show 2 * (α / 5) - q = -q + 2 * (α / 5) by ring, Real.rpow_add' hs hne]
    ring
  rw [hAbnd, mul_pow, hpow]
  calc (Real.sin (2 * θ)) ^ (-q)
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5)))
      ≤ (Real.sin (2 * θ)) ^ (-q) * (4 * (Real.sin (2 * θ)) ^ (2 * (α / 5))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hs _)) (Real.rpow_nonneg hs _)
    _ = 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q) := key

theorem Abnd_rpow_sq_integral_le {α q : ℝ} {i : ℕ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hi : i ≠ 0) (hq1 : 1 ≤ q) (hq2 : q < 1 + 2 * (α / 5)) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ 4 * (100 / (2 * (α / 5) - q + 1)) := by
  have hp1 : -1 < 2 * (α / 5) - q := by linarith
  have hp0 : 2 * (α / 5) - q ≤ 0 := by
    have h2 : 2 * (α / 5) ≤ 2 / 5 := by linarith
    linarith
  obtain ⟨hint, hval⟩ := Work.Spaces.sin_two_rpow (2 * (α / 5) - q) hp1 hp0
  -- the majorant `4·sin(2θ)^{2α/5-q}` is integrable on `Iθ`
  have hmaj : MeasureTheory.Integrable
      (fun θ : ℝ => 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hint.const_mul 4
  -- measurability of the integrand
  have hsin : Measurable fun θ : ℝ => Real.sin (2 * θ) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hAbnd : Measurable fun θ : ℝ => Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ := by
    have hfun : (fun θ : ℝ => Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ)
        = fun θ : ℝ => (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
      funext θ
      simp only [Work.FTS.StrongPersist.H6Pair6Aux.Abnd, hi, ↓reduceIte]
    rw [hfun]
    exact (measurable_const.add hsin).mul (hsin.pow_const (α / 5))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
        * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((hsin.pow_const (-q)).mul (hAbnd.pow_const 2)).aestronglyMeasurable
  have hsin_nonneg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Real.sin (2 * θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  constructor
  · refine hmaj.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _))]
    exact Abnd_rpow_mul_sq_le hα0 hα1 hi hq1 hθ
  · have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) := by
      filter_upwards [hsin_nonneg] with θ hs
      exact mul_nonneg (Real.rpow_nonneg hs _) (sq_nonneg _)
    have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Abnd_rpow_mul_sq_le hα0 hα1 hi hq1 hθ
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        = ∫ θ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := rfl
      _ ≤ ∫ θ, 4 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - q)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          MeasureTheory.integral_mono_of_nonneg hnn hmaj hle
      _ = 4 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - q)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 4 * (100 / (2 * (α / 5) - q + 1)) :=
          mul_le_mul_of_nonneg_left hval (by norm_num)

end Work.FTS.StrongPersist.H6Pair6Aux.T45Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.fkPairCSae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open MeasureTheory

/-- AM–GM in the form used to dominate a product of square roots: for `a, b ≥ 0`,
`2 √a √b ≤ a + b`. -/
private lemma fkPairCSae_sqrt_amgm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt a * Real.sqrt b ≤ a + b := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, sq_nonneg (Real.sqrt a - Real.sqrt b)]

theorem fkPairCSae {ρ : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {V₁ V₂ : ℝ → ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hr : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), |r z| ≤ K)
    (hρ : ∀ z, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 ≤ ρ z θ)
    (hI1 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ) ^ 2) Work.Spaces.Iz)
    (hI2 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ) ^ 2) Work.Spaces.Iz)
    (hs1 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (V₁ z θ) ^ 2) Work.Spaces.Iθ)
    (hs2 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (V₂ z θ) ^ 2) Work.Spaces.Iθ) :
    |∫ z in Work.Spaces.Iz, r z * (∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ)|
      ≤ K * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ) ^ 2) := by
  -- nonnegativity of the angular slice densities, pointwise in `z`: the hypothesis is only
  -- a.e. in `θ`, which is exactly what an integral can see.
  have hPnn : ∀ z, 0 ≤ (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2) := by
    intro z
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact (hρ z).mono fun θ hθ => mul_nonneg hθ (sq_nonneg _)
  have hQnn : ∀ z, 0 ≤ (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) := by
    intro z
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact (hρ z).mono fun θ hθ => mul_nonneg hθ (sq_nonneg _)
  -- Cauchy–Schwarz in the angular variable, for each fixed `z ∈ Iz`
  have hθcs : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) := by
    intro z hz
    have h1i : MeasureTheory.Integrable (fun θ => ρ z θ * (V₁ z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hs1 z hz
    have h2i : MeasureTheory.Integrable (fun θ => ρ z θ * (V₂ z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hs2 z hz
    have hpnn : 0 ≤ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iθ)]
        (fun θ => ρ z θ * (V₁ z θ)^2) :=
      (hρ z).mono fun θ hθ => mul_nonneg hθ (sq_nonneg _)
    have hqnn : 0 ≤ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iθ)]
        (fun θ => ρ z θ * (V₂ z θ)^2) :=
      (hρ z).mono fun θ hθ => mul_nonneg hθ (sq_nonneg _)
    have hcs := Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) hpnn hqnn h1i h2i
    have hpt : ∀ a x y : ℝ, 0 ≤ a → |a * x * y| = Real.sqrt (a * x^2) * Real.sqrt (a * y^2) := by
      intro a x y ha
      have h1 : Real.sqrt (a * x^2) = Real.sqrt a * |x| := by
        rw [Real.sqrt_mul ha, Real.sqrt_sq_eq_abs]
      have h2 : Real.sqrt (a * y^2) = Real.sqrt a * |y| := by
        rw [Real.sqrt_mul ha, Real.sqrt_sq_eq_abs]
      have h3 : Real.sqrt a * Real.sqrt a = a := by rw [← sq, Real.sq_sqrt ha]
      calc |a * x * y| = a * |x| * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha]
        _ = (Real.sqrt a * Real.sqrt a) * (|x| * |y|) := by rw [h3]; ring
        _ = Real.sqrt (a * x^2) * Real.sqrt (a * y^2) := by rw [h1, h2]; ring
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * V₁ z θ * V₂ z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ θ in Work.Spaces.Iθ,
            Real.sqrt (ρ z θ * (V₁ z θ)^2) * Real.sqrt (ρ z θ * (V₂ z θ)^2) :=
          MeasureTheory.integral_congr_ae ((hρ z).mono fun θ hθ =>
            hpt (ρ z θ) (V₁ z θ) (V₂ z θ) hθ)
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) := hcs
  -- the pointwise-in-`z` bound, a.e. on `Iz`
  have hmain : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |r z * (∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ)|
        ≤ K * (Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2)) := by
    filter_upwards [hr, MeasureTheory.ae_restrict_mem (measurableSet_Ici (a := (0:ℝ)))]
      with z hrz hz
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hrz (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hθcs z hz) hK)
  -- the dominating profile is integrable, being bounded by `(P + Q)/2`
  have hInt_sqrt : MeasureTheory.Integrable
      (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun z => (1/2) * ((∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
        + (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2))) ?_ ?_ ?_
    · exact (hI1.add hI2).const_mul (1/2)
    · exact ((hI1.aemeasurable.sqrt).aestronglyMeasurable).mul
        ((hI2.aemeasurable.sqrt).aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ici (a := (0:ℝ)))] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      have h2 := fkPairCSae_sqrt_amgm (hPnn z) (hQnn z)
      linarith
  have hIntK : MeasureTheory.Integrable
      (fun z => K * (Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hInt_sqrt.const_mul K
  have hpae : 0 ≤ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iz)]
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2) :=
    Filter.Eventually.of_forall hPnn
  have hqae : 0 ≤ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iz)]
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) :=
    Filter.Eventually.of_forall hQnn
  -- the radial Cauchy–Schwarz
  calc |∫ z in Work.Spaces.Iz, r z * (∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ)|
      ≤ ∫ z in Work.Spaces.Iz, |r z * (∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ)| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, K * (Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2)) :=
        MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          hIntK hmain
    _ = K * ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) :=
        MeasureTheory.integral_const_mul K _
    _ ≤ K * (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2)) :=
        mul_le_mul_of_nonneg_left
          (Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
            (MeasureTheory.volume.restrict Work.Spaces.Iz) hpae hqae hI1 hI2) hK
    _ = K * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) := by
        ring

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.cw_Phi_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.cw_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS_EllLimOK.PkgJets



end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.cw_integrable =====
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
## Integrability of the comparison functions `cwG`, `cwPhiD` near `θ = 0`

The two functions

`cwG θ = sin(2θ)^{-η}/cos(θ)^4`,
`cwPhiD θ = 50 · sin(2θ)^{-η} · (2(1-η)cos(2θ) + 8 sin²θ)/cos(θ)^4`

(with `η = 99/100`) are continuous on a neighbourhood of every point of `(0, π/2)`, and at `θ = 0`
they behave like `(2θ)^{-η}` (times the bounded factor `cos(0)^{-4} = 1`, resp.
`50·(2(1-η) + 0)`).  Since `η < 1`, the endpoint `0` is an integrable singularity, so both are
integrable on `(0, θ]` for every `θ ∈ (0, π/2)`.  The second statement follows from the first
because the extra factor `2(1-η)cos(2θ) + 8 sin²θ` is bounded by `2(1-η) + 8 ≤ 10`, so
`|cwPhiD| ≤ 500 · cwG`.
-/









end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_second_deriv_le_six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.SecondDeriv

open Set Real Filter
open scoped Real Topology

open Work.FTS_EllLimOK.ProducerH.SliceBound

local notation "sliceI" => Set.Ioo 0 (π / 2)

/-!
# The angular slice second-derivative bound with the sharp constant `6`

We specialise the argument of `Work.FTS_EllLimOK.ProducerH.SliceBound.slice_second_deriv_le`
(the `∃ K` version) to the explicit constant `K = 6`.

With `f := sin(2θ)/2 · S' + S` and `V := f - 2 S cos²θ`, the ODE

  `S'' = tan θ · S' + cos(θ)⁻² · S - 6 S - G`

is equivalent to `V' = tan θ (V - G cos²θ)`.  The monotone barriers
`Z = 3 V cos θ - M cos³θ` and `Zt = 3 V cos θ + M cos³θ` then force
`|V| ≤ (M/3) cos²θ`, and since `S'' = V / cos²θ - 4 S - G` we get
`|S''| ≤ M/3 + 4 M + M ≤ 6 M`.
-/

theorem slice_second_deriv_le_six {S G : ℝ → ℝ}
    (hS : ContDiffOn ℝ 2 S (Set.Ioo 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv S) θ
        = Real.tan θ * deriv S θ + ((Real.cos θ) ^ 2)⁻¹ * S θ - 6 * S θ - G θ)
    {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Real.sin (2 * θ) / 2 * deriv S θ + S θ| ≤ M)
    (hSb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |S θ| ≤ M)
    (hGb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |G θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv (deriv S) θ| ≤ 6 * M := by
  have hIopen : IsOpen sliceI := isOpen_Ioo
  have hIconv : Convex ℝ sliceI := convex_Ioo 0 (π / 2)
  have hIint : interior sliceI = sliceI := hIopen.interior_eq
  have hS1 : ContDiffOn ℝ 1 (deriv S) sliceI := hS.deriv_of_isOpen hIopen (by norm_num)
  have hSd : ∀ θ ∈ sliceI, HasDerivAt S (deriv S θ) θ := fun θ hθ =>
    ((hS.contDiffAt (hIopen.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hSd2 : ∀ θ ∈ sliceI, HasDerivAt (deriv S) (deriv (deriv S) θ) θ := fun θ hθ =>
    ((hS1.contDiffAt (hIopen.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hcospos : ∀ θ ∈ sliceI, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by have := hθ.1; linarith [Real.pi_pos], hθ.2⟩
  have hcosne : ∀ θ ∈ sliceI, Real.cos θ ≠ 0 := fun θ hθ => ne_of_gt (hcospos θ hθ)
  -- derivative of `sliceV S`
  have hVd : ∀ θ ∈ sliceI,
      HasDerivAt (sliceV S) (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2)) θ := by
    intro θ hθ
    have h1 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) / 2) (Real.cos (2 * θ)) θ := by
      have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      have h : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ :=
        (Real.hasDerivAt_sin (2 * θ)).comp θ h2
      convert h.div_const 2 using 1
      ring
    have hF : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) / 2 * deriv S θ + S θ)
        (Real.cos (2 * θ) * deriv S θ + Real.sin (2 * θ) / 2 * deriv (deriv S) θ
          + deriv S θ) θ :=
      ((h1.mul (hSd2 θ hθ)).add (hSd θ hθ)).congr_deriv (by ring)
    have hc2 : HasDerivAt (fun θ : ℝ => (Real.cos θ) ^ 2) (2 * Real.cos θ * (-Real.sin θ)) θ :=
      ((Real.hasDerivAt_cos θ).pow 2).congr_deriv (by norm_num)
    have hG2 : HasDerivAt (fun θ : ℝ => 2 * S θ * (Real.cos θ) ^ 2)
        (2 * deriv S θ * (Real.cos θ) ^ 2 + 2 * S θ * (2 * Real.cos θ * (-Real.sin θ))) θ :=
      (((hSd θ hθ).const_mul 2).mul hc2).congr_deriv (by ring)
    have hraw := hF.sub hG2
    have hfun : ((fun θ : ℝ => Real.sin (2 * θ) / 2 * deriv S θ + S θ)
        - (fun θ : ℝ => 2 * S θ * (Real.cos θ) ^ 2)) = sliceV S := by
      funext x
      simp only [Pi.sub_apply, sliceV, sliceF]
    rw [hfun] at hraw
    refine hraw.congr_deriv ?_
    simp only [sliceV, sliceF]
    rw [heq θ hθ, Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
    field_simp [hcosne θ hθ]
    ring
  -- derivative of `sliceZ S M`
  have hZd : ∀ θ ∈ sliceI,
      HasDerivAt (sliceZ S M) (3 * Real.sin θ * (Real.cos θ) ^ 2 * (M - G θ)) θ := by
    intro θ hθ
    have h3V : HasDerivAt (fun θ : ℝ => 3 * sliceV S θ)
        (3 * (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2))) θ :=
      (hVd θ hθ).const_mul 3
    have hprod : HasDerivAt (fun θ : ℝ => 3 * sliceV S θ * Real.cos θ)
        (3 * (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2)) * Real.cos θ
          + 3 * sliceV S θ * (-Real.sin θ)) θ :=
      ((h3V.mul (Real.hasDerivAt_cos θ)).congr_deriv (by ring))
    have hc3 : HasDerivAt (fun θ : ℝ => (Real.cos θ) ^ 3)
        (3 * (Real.cos θ) ^ 2 * (-Real.sin θ)) θ :=
      ((Real.hasDerivAt_cos θ).pow 3).congr_deriv (by ring)
    have hMc : HasDerivAt (fun θ : ℝ => M * (Real.cos θ) ^ 3)
        (M * (3 * (Real.cos θ) ^ 2 * (-Real.sin θ))) θ := hc3.const_mul M
    have hraw := hprod.sub hMc
    have hfun : ((fun θ : ℝ => 3 * sliceV S θ * Real.cos θ)
        - (fun θ : ℝ => M * (Real.cos θ) ^ 3)) = sliceZ S M := by
      funext x
      simp only [Pi.sub_apply, sliceZ]
    rw [hfun] at hraw
    refine hraw.congr_deriv ?_
    simp only [sliceV, sliceF]
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp [hcosne θ hθ]
    ring
  -- derivative of `sliceZt S M`
  have hZtd : ∀ θ ∈ sliceI,
      HasDerivAt (sliceZt S M) (-(3 * Real.sin θ * (Real.cos θ) ^ 2 * (G θ + M))) θ := by
    intro θ hθ
    have h3V : HasDerivAt (fun θ : ℝ => 3 * sliceV S θ)
        (3 * (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2))) θ :=
      (hVd θ hθ).const_mul 3
    have hprod : HasDerivAt (fun θ : ℝ => 3 * sliceV S θ * Real.cos θ)
        (3 * (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2)) * Real.cos θ
          + 3 * sliceV S θ * (-Real.sin θ)) θ :=
      ((h3V.mul (Real.hasDerivAt_cos θ)).congr_deriv (by ring))
    have hc3 : HasDerivAt (fun θ : ℝ => (Real.cos θ) ^ 3)
        (3 * (Real.cos θ) ^ 2 * (-Real.sin θ)) θ :=
      ((Real.hasDerivAt_cos θ).pow 3).congr_deriv (by ring)
    have hMc : HasDerivAt (fun θ : ℝ => M * (Real.cos θ) ^ 3)
        (M * (3 * (Real.cos θ) ^ 2 * (-Real.sin θ))) θ := hc3.const_mul M
    have hraw := hprod.add hMc
    have hfun : ((fun θ : ℝ => 3 * sliceV S θ * Real.cos θ)
        + (fun θ : ℝ => M * (Real.cos θ) ^ 3)) = sliceZt S M := by
      funext x
      simp only [Pi.add_apply, sliceZt]
    rw [hfun] at hraw
    refine hraw.congr_deriv ?_
    simp only [sliceV, sliceF]
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp [hcosne θ hθ]
    ring
  have hZcont : ContinuousOn (sliceZ S M) sliceI :=
    DifferentiableOn.continuousOn (fun θ hθ => (hZd θ hθ).differentiableAt.differentiableWithinAt)
  have hZmono : MonotoneOn (sliceZ S M) sliceI := by
    refine monotoneOn_of_deriv_nonneg hIconv hZcont ?_ ?_
    · intro x hx
      rw [hIint] at hx
      exact (hZd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [hIint] at hx
      rw [(hZd x hx).deriv]
      have hsinx : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
      have hGle : G x ≤ M := (abs_le.mp (hGb x hx)).2
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsinx) (sq_nonneg _))
        (by linarith)
  have hZtcont : ContinuousOn (sliceZt S M) sliceI :=
    DifferentiableOn.continuousOn (fun θ hθ => (hZtd θ hθ).differentiableAt.differentiableWithinAt)
  have hZtanti : AntitoneOn (sliceZt S M) sliceI := by
    refine antitoneOn_of_deriv_nonpos hIconv hZtcont ?_ ?_
    · intro x hx
      rw [hIint] at hx
      exact (hZtd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [hIint] at hx
      rw [(hZtd x hx).deriv]
      have hsinx : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
      have hGle : -M ≤ G x := (abs_le.mp (hGb x hx)).1
      have hnonneg : 0 ≤ 3 * Real.sin x * (Real.cos x) ^ 2 * (G x + M) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsinx) (sq_nonneg _)) (by linarith)
      linarith
  -- upper bound on `sliceV`
  have hVupper : ∀ θ ∈ sliceI, sliceV S θ ≤ M / 3 * (Real.cos θ) ^ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨θ₀, hθ₀, hgt⟩ := hcon
    refine mode_contradiction_up (V := sliceV S) (Z₀ := sliceZ S M θ₀) (θ₀ := θ₀) hM hθ₀ ?_ ?_ ?_
    · have hcp : 0 < Real.cos θ₀ := hcospos θ₀ hθ₀
      have h3 : 0 < 3 * sliceV S θ₀ - M * (Real.cos θ₀) ^ 2 := by nlinarith [hgt]
      have hthis : 0 < (3 * sliceV S θ₀ - M * (Real.cos θ₀) ^ 2) * Real.cos θ₀ :=
        mul_pos h3 hcp
      have hZeq : (3 * sliceV S θ₀ - M * (Real.cos θ₀) ^ 2) * Real.cos θ₀
          = sliceZ S M θ₀ := by simp only [sliceZ]; ring
      rwa [hZeq] at hthis
    · intro θ hθ hle
      exact hZmono hθ₀ hθ hle
    · intro θ hθ
      have hfm : sliceF S θ ≤ M := (abs_le.mp (hf θ hθ)).2
      have hSm : -M ≤ S θ := (abs_le.mp (hSb θ hθ)).1
      have hVeq : sliceV S θ = sliceF S θ - 2 * S θ * (Real.cos θ) ^ 2 := rfl
      rw [hVeq]
      have hstep : -2 * S θ * (Real.cos θ) ^ 2 ≤ 2 * M * (Real.cos θ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hSm (by positivity : (0:ℝ) ≤ 2 * (Real.cos θ) ^ 2)
        linarith
      linarith
  -- lower bound on `sliceV`
  have hVlower : ∀ θ ∈ sliceI, -(M / 3) * (Real.cos θ) ^ 2 ≤ sliceV S θ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨θ₀, hθ₀, hlt⟩ := hcon
    refine mode_contradiction_down (V := sliceV S) (Z₀ := sliceZt S M θ₀) (θ₀ := θ₀) hM hθ₀ ?_ ?_ ?_
    · have hcp : 0 < Real.cos θ₀ := hcospos θ₀ hθ₀
      have h3 : 3 * sliceV S θ₀ + M * (Real.cos θ₀) ^ 2 < 0 := by nlinarith [hlt]
      have hthis : (3 * sliceV S θ₀ + M * (Real.cos θ₀) ^ 2) * Real.cos θ₀ < 0 :=
        mul_neg_of_neg_of_pos h3 hcp
      have hZeq : (3 * sliceV S θ₀ + M * (Real.cos θ₀) ^ 2) * Real.cos θ₀
          = sliceZt S M θ₀ := by simp only [sliceZt]; ring
      rwa [hZeq] at hthis
    · intro θ hθ hle
      exact hZtanti hθ₀ hθ hle
    · intro θ hθ
      have hfm : -M ≤ sliceF S θ := (abs_le.mp (hf θ hθ)).1
      have hSm : S θ ≤ M := (abs_le.mp (hSb θ hθ)).2
      have hVeq : sliceV S θ = sliceF S θ - 2 * S θ * (Real.cos θ) ^ 2 := rfl
      rw [hVeq]
      have hstep : -2 * M * (Real.cos θ) ^ 2 ≤ -2 * S θ * (Real.cos θ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hSm (by positivity : (0:ℝ) ≤ 2 * (Real.cos θ) ^ 2)
        linarith
      linarith
  -- final assembly
  intro θ hθ
  have hW : deriv (deriv S) θ = sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ - G θ := by
    rw [heq θ hθ, sliceV, sliceF, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp [hcosne θ hθ]
    ring
  rw [hW]
  have hc2pos : 0 < (Real.cos θ) ^ 2 := pow_pos (hcospos θ hθ) 2
  have hc2inv : (Real.cos θ) ^ 2 * ((Real.cos θ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hc2pos)
  have hW1 : sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ ≤ M / 3 := by
    have h := mul_le_mul_of_nonneg_right (hVupper θ hθ) (inv_nonneg.mpr hc2pos.le)
    rwa [mul_assoc, hc2inv, mul_one] at h
  have hW2 : -(M / 3) ≤ sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right (hVlower θ hθ) (inv_nonneg.mpr hc2pos.le)
    rwa [mul_assoc, hc2inv, mul_one] at h
  have hWabs : |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹| ≤ M / 3 := by
    rw [abs_le]
    exact ⟨hW2, hW1⟩
  have h4S : |4 * S θ| ≤ 4 * M := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith [hSb θ hθ]
  calc |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ - G θ|
      ≤ |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹| + |4 * S θ| + |G θ| := by
        have h2 : |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ|
            ≤ |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹| + |4 * S θ| := by
          have := abs_sub_le (sliceV S θ * ((Real.cos θ) ^ 2)⁻¹) (0 : ℝ) (4 * S θ)
          simpa using this
        have h1 : |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ - G θ|
            ≤ |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ| + |G θ| := by
          have := abs_sub_le (sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ) (0 : ℝ) (G θ)
          simpa using this
        linarith
    _ ≤ M / 3 + 4 * M + M := by linarith [hWabs, h4S, hGb θ hθ]
    _ ≤ 6 * M := by linarith [hM]

end Work.FTS_EllLimOK.ProducerH.SecondDeriv
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SliceTrace.tendsto_zero_of_deriv_sq_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Real

namespace Work.FTS_EllLimOK.SliceTrace

/-!
# The endpoint trace of a function with two weighted `L²` bounds

This is the first-order companion of `deriv_tendsto_zero_at_pi_div_two`.  There, `f` is `C²`
and the conclusion is `deriv f → 0`; here `g` is only `C¹` and the conclusion is `g → 0`.

The two hypotheses are the natural ones for the argument:

* `∫_t^{π/2} g² sin(2θ)^{-γ} < ∞` with `γ > 1`: since `sin(2θ)^{-γ}` fails to be
  integrable at `π/2`, `g` must be small somewhere on every tail
  (`exists_abs_le_of_integrable_weighted`), giving a point `τ` with `|g τ| ≤ ε/2`;
* `∫_0^{π/2} (g')² sin(2θ)^{-η} < ∞` with `η ≥ 0`: on the tail `(t', π/2)` the fundamental
  theorem of calculus bounds the *variation* of `g` by
  `(∫ (g')² sin^{-η} + ∫ sin^{η})/2` (AM–GM against the weight), and both pieces can be made
  as small as we wish.

Combining the two gives `g x → 0` as `x → π/2⁻`.
-/

/-- **Fundamental theorem of calculus for a `C¹` function** on a closed subinterval of
`(0, π/2)`: the oscillation of `g` is bounded by the integral of `|g'|`. -/
private theorem abs_sub_le_intervalIntegral_deriv {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi / 2))) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    |g b - g a| ≤ ∫ x in a..b, |deriv g x| := by
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hsub' : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  -- `deriv g` is continuous on `[a,b]`, hence interval integrable
  have hcont : ContinuousOn (deriv g) (Set.uIcc a b) :=
    (hg.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn.mono hsub
  have hint : IntervalIntegrable (deriv g) volume a b := hcont.intervalIntegrable
  have hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt g (deriv g x) x := by
    intro x hx
    exact ((hg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩)).hasDerivAt
  have hFTC : ∫ x in a..b, deriv g x = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hg.continuousOn.mono hsub')
      hdiff hint
  rw [← hFTC]
  exact intervalIntegral.abs_integral_le_integral_abs hab

/-- **The variation bound**: the oscillation of a `C¹` function `g` on a tail is bounded by
half the sum of the two weighted `L²`-tails (`η`-weight on `g'`, and the reciprocal weight). -/
private theorem abs_sub_le_half_weights_deriv_aux {η : ℝ} (hη : 0 ≤ η) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)))
    {t x y : ℝ} (ht : 0 < t) (hx : x ∈ Set.Ioo t (Real.pi / 2))
    (hy : y ∈ Set.Ioo t (Real.pi / 2)) :
    |g x - g y| ≤
      ((∫ z in Set.Ioo t (Real.pi / 2),
          (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
  have hF1int : MeasureTheory.IntegrableOn
      (fun z => (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
      (Set.Ioo t (Real.pi / 2)) := h2.mono_set (Set.Ioo_subset_Ioo_left ht.le)
  have hSint : MeasureTheory.IntegrableOn (fun z => (Real.sin (2 * z)) ^ η)
      (Set.Ioo t (Real.pi / 2)) := integrableOn_sin_two_rpow hη ht.le
  have hcont2 : ContinuousOn (fun z => |deriv g z|) (Set.Ioo t (Real.pi / 2)) :=
    ((hg.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn.mono
      (Set.Ioo_subset_Ioo_left ht.le)).abs
  have hpoint : ∀ z ∈ Set.Ioo t (Real.pi / 2),
      |deriv g z| ≤ ((deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η)
        + (Real.sin (2 * z)) ^ η) / 2 :=
    fun z hz => abs_le_half_sq_mul_rpow_add
      (sin_two_pos_of_mem_Ioo ⟨lt_trans ht hz.1, hz.2⟩)
  have hgint : MeasureTheory.IntegrableOn (fun z => |deriv g z|)
      (Set.Ioo t (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' (f := fun z => |deriv g z|)
      ((hF1int.add hSint).div_const 2)
      (hcont2.aestronglyMeasurable measurableSet_Ioo) (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
        rw [Real.norm_eq_abs, abs_abs]
        exact hpoint z hz)
  have hmono := MeasureTheory.setIntegral_mono_on hgint ((hF1int.add hSint).div_const 2)
    measurableSet_Ioo hpoint
  have hsplit : (∫ z in Set.Ioo t (Real.pi / 2),
        ((deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η) + (Real.sin (2 * z)) ^ η) / 2)
      = ((∫ z in Set.Ioo t (Real.pi / 2),
            (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
          + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hF1int hSint]
  have hL1 : ∫ z in Set.Ioo t (Real.pi / 2), |deriv g z| ≤
      ((∫ z in Set.Ioo t (Real.pi / 2),
          (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 := by
    rw [← hsplit]
    exact hmono
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm]
    refine (abs_sub_le_intervalIntegral_deriv hg (lt_trans ht hx.1) hxy hy.2).trans ?_
    rw [intervalIntegral.integral_of_le hxy, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact (MeasureTheory.setIntegral_mono_set hgint
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun z (hz : z ∈ Set.Ioo x y) =>
        ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩)).trans hL1
  · refine (abs_sub_le_intervalIntegral_deriv (a := y) (b := x) hg (lt_trans ht hy.1) hyx
      hx.2).trans ?_
    rw [intervalIntegral.integral_of_le hyx, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact (MeasureTheory.setIntegral_mono_set hgint
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun z (hz : z ∈ Set.Ioo y x) =>
        ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hx.2⟩)).trans hL1

theorem tendsto_zero_of_deriv_sq_integrable {η γ : ℝ} (hη : 0 ≤ η) (hγ : 1 < γ)
    {g : ℝ → ℝ} {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
      (Set.Ioo t (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ δ > 0, ∀ x : ℝ, x ∈ Set.Iio (Real.pi / 2) →
      dist x (Real.pi / 2) < δ → dist (g x) 0 < ε := by
    intro ε hε hε1
    -- a short tail on which the weighted derivative integral is small
    obtain ⟨t', ht', ht'len, ht'U⟩ := exists_tail_le
      (F := fun θ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) h2
      (a := ε ^ 2 / 16) (ε := ε ^ 2 / 8) (by positivity) (by positivity)
    have ht'V : ∫ z in Set.Ioo t' (Real.pi / 2), (Real.sin (2 * z)) ^ η ≤ ε ^ 2 / 8 :=
      (setIntegral_sin_two_rpow_le_length hη ht'.1.le ht'.2.le).trans
        (by nlinarith [ht'len, hε])
    have hF'int : MeasureTheory.IntegrableOn
        (fun z => (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        (Set.Ioo t' (Real.pi / 2)) := h2.mono_set (Set.Ioo_subset_Ioo_left ht'.1.le)
    have hS'int : MeasureTheory.IntegrableOn (fun z => (Real.sin (2 * z)) ^ η)
        (Set.Ioo t' (Real.pi / 2)) := integrableOn_sin_two_rpow hη ht'.1.le
    have hF'nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo t' (Real.pi / 2))]
        (fun z => (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt
        (sin_two_pos_of_mem_Ioo ⟨lt_trans ht'.1 hz.1, hz.2⟩)) _)
    have hS'nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo t' (Real.pi / 2))]
        (fun z => (Real.sin (2 * z)) ^ η) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      exact Real.rpow_nonneg (le_of_lt
        (sin_two_pos_of_mem_Ioo ⟨lt_trans ht'.1 hz.1, hz.2⟩)) _
    -- shrink the tail so that it also sits inside `(t, π/2)`, where `h1` lives
    set t'' : ℝ := max t t' with ht''def
    have ht''1 : 0 < t'' := lt_of_lt_of_le ht.1 (le_max_left t t')
    have ht''2 : t'' < Real.pi / 2 := max_lt ht.2 ht'.2
    have ht''mem : t'' ∈ Set.Ioo 0 (Real.pi / 2) := ⟨ht''1, ht''2⟩
    have hsub'' : Set.Ioo t'' (Real.pi / 2) ⊆ Set.Ioo t' (Real.pi / 2) :=
      Set.Ioo_subset_Ioo_left (le_max_right t t')
    have hU'' : ∫ z in Set.Ioo t'' (Real.pi / 2),
        (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η) ≤ ε ^ 2 / 8 :=
      (MeasureTheory.setIntegral_mono_set hF'int hF'nonneg
        (Filter.Eventually.of_forall fun _ hz => hsub'' hz)).trans ht'U
    have hV'' : ∫ z in Set.Ioo t'' (Real.pi / 2), (Real.sin (2 * z)) ^ η ≤ ε ^ 2 / 8 :=
      (MeasureTheory.setIntegral_mono_set hS'int hS'nonneg
        (Filter.Eventually.of_forall fun _ hz => hsub'' hz)).trans ht'V
    -- a point of the tail where `g` is small
    obtain ⟨τ, hτ, hτle⟩ := exists_abs_le_of_integrable_weighted hγ (f := g)
      (t := t'') ht''mem (h1.mono_set (Set.Ioo_subset_Ioo_left (le_max_left t t')))
      (d := ε / 2) (by positivity)
    refine ⟨Real.pi / 2 - t'', by linarith, fun x hx hdx => ?_⟩
    have hxt : x ∈ Set.Ioo t'' (Real.pi / 2) := by
      rw [Real.dist_eq] at hdx
      rw [abs_lt] at hdx
      exact ⟨by linarith [hdx.1], hx⟩
    have hvar := abs_sub_le_half_weights_deriv_aux (t := t'') hη hg h2 ht''1 hxt hτ
    have hbound : ((∫ z in Set.Ioo t'' (Real.pi / 2),
          (deriv g z) ^ 2 * (Real.sin (2 * z)) ^ (-η))
        + (∫ z in Set.Ioo t'' (Real.pi / 2), (Real.sin (2 * z)) ^ η)) / 2 ≤ ε ^ 2 / 8 := by
      linarith
    have htri : |g x| ≤ |g x - g τ| + |g τ| := by
      have h := abs_add_le (g x - g τ) (g τ)
      rwa [sub_add_cancel] at h
    have hε2 : ε ^ 2 ≤ ε := by nlinarith [hε1, hε.le]
    rw [Real.dist_eq, sub_zero]
    linarith [hvar.trans hbound, hτle, htri, hε2]
  intro ε hε
  rcases le_or_gt (1 / 2 : ℝ) ε with hbig | hsmall
  · obtain ⟨δ, hδ0, hδ⟩ := key (1 / 2) (by norm_num) (by norm_num)
    exact ⟨δ, hδ0, fun x hx hd => lt_of_lt_of_le (hδ x hx hd) hbig⟩
  · exact key ε hε (by linarith)

end Work.FTS_EllLimOK.SliceTrace
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ZDecayAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-! ## The half-integer power -/


/-! ## The pointwise bounds -/





/-! ## The endpoint vanishing of the radial derivatives -/



end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.CaseLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FamOde.CaseLeft` — the first-order bound on the left half `(0, π/4]`

The left half of `Work.FTS_StreamBdry.SB3.P2Aux.fam_ode_deriv_bound_proved`: with the
mean-value anchor `P2Aux.exists_anchor_left` at scale `θ²` one finds `ξ ∈ (θ²/8, θ²/4)` with
`|F' ξ| ≤ 16K₀/θ²`; since `W = m·F'` is Lipschitz with constant `≤ (A/2)θ + Cθ²` on `[ξ,θ]`
and `m(θ) ≥ θ²/(2π²)`, this gives `|F' θ| ≤ 2π²(K₀ + A/2 + Cπ/4)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux.FamOde


end Work.FTS_StreamBdry.SB3.P2Aux.FamOde
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.CaseRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FamOde.CaseRight` — the first-order bound on the right half `[π/4, π/2)`

The right half of `Work.FTS_StreamBdry.SB3.P2Aux.fam_ode_deriv_bound_proved`.  Writing
`δ = π/2 - θ`, the mean-value anchor `P2Aux.exists_anchor_right` at scale `a = δ²` gives
`ξ ∈ (π/2 - δ²/2, π/2 - δ²/4)` with `|F' ξ| ≤ 8K₀/δ²`, whence `|W ξ| ≤ (δ²/2)³·8K₀/δ² = K₀δ⁴`
(as `m ≤ cos³`); `W` is Lipschitz with constant `≤ (A/2)δ² + Cδ³` on `[θ,ξ]` and
`m(θ) ≥ 2δ³/π³`, giving `|F' θ| ≤ (π³/2)(K₀ + A/2 + Cπ/4)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux.FamOde


end Work.FTS_StreamBdry.SB3.P2Aux.FamOde
end
end
-- ===== merged: Submission.Work.Spaces.ThetaAgmon.HardyWeightedInterval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces.ThetaAgmon

set_option autoImplicit false


end Work.Spaces.ThetaAgmon
end
-- ===== merged: Submission.Work.Spaces.ThetaAgmon.agmon_interval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces.ThetaAgmon

open scoped Real Topology
open MeasureTheory Set Filter

/-- Elementary bound: `|t| ≤ 1/2 + t²/2` for every real `t`. -/
theorem abs_le_half_add_half_sq (t : ℝ) : |t| ≤ (1 / 2 : ℝ) + (1 / 2) * t ^ 2 := by
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

/-- **Agmon's inequality on a dyadic angular annulus.**

For `a > 0` and `φ` continuous on `[0,2a]`, differentiable on `(0,2a)` with square-integrable
derivative, one has for every `x ∈ annulus a = [a,2a]`

`φ(x)² ≤ (2/a)·∫_0^a φ² + 4a·∫_0^{2a} (φ')²`.

The proof is the classical one: for `y ∈ [0,a]` the fundamental theorem of calculus gives
`φ x - φ y = ∫_y^x φ'`, so by `(u+v)² ≤ 2u² + 2v²` and Cauchy–Schwarz on `[y,x]`

`φ(x)² ≤ 2φ(y)² + 2(x-y)·∫_y^x (φ')² ≤ 2φ(y)² + 4a·∫_0^{2a}(φ')²`,

and averaging this over `y ∈ [0,a]` produces the stated bound. -/
theorem agmon_interval {a : ℝ} (ha : 0 < a) (φ : ℝ → ℝ)
    (hcont : ContinuousOn φ (Set.Icc 0 (2 * a)))
    (hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) (2 * a), HasDerivAt φ (deriv φ x) x)
    (hint : MeasureTheory.IntegrableOn (fun s => (deriv φ s) ^ 2) (Set.Ioo (0 : ℝ) (2 * a))) :
    ∀ x ∈ Work.Spaces.ThetaAgmon.annulus a,
      (φ x) ^ 2 ≤ (2 / a) * (∫ s in (0 : ℝ)..a, (φ s) ^ 2)
        + 4 * a * (∫ s in (0 : ℝ)..(2 * a), (deriv φ s) ^ 2) := by
  intro x hx
  rw [annulus, Set.mem_Icc] at hx
  obtain ⟨hxa, hx2a⟩ := hx
  have ha0 : (0 : ℝ) ≤ a := ha.le
  have ha2a : (0 : ℝ) ≤ 2 * a := by linarith
  set B : ℝ := ∫ s in (0 : ℝ)..(2 * a), (deriv φ s) ^ 2 with hBdef
  -- ## Integrability of `(deriv φ)²` on `Ioc 0 (2a)` and on every sub-interval
  have hfsq_Ioc : MeasureTheory.IntegrableOn (fun s => (deriv φ s) ^ 2)
      (Set.Ioc (0 : ℝ) (2 * a)) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2 hint
  have hfsq_ii : IntervalIntegrable (fun s => (deriv φ s) ^ 2) volume (0 : ℝ) (2 * a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha2a).2 hfsq_Ioc
  have hfsq_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (2 * a))] (fun s => (deriv φ s) ^ 2) :=
    Eventually.of_forall fun s => sq_nonneg _
  -- ## Step 1: the pointwise bound, valid at every `y ∈ [0,a]`
  have key : ∀ y ∈ Set.Icc (0 : ℝ) a, (φ x) ^ 2 ≤ 2 * (φ y) ^ 2 + 4 * a * B := by
    intro y hy
    obtain ⟨hy0, hya⟩ := hy
    have hyx : y ≤ x := le_trans hya hxa
    have hfsq_yx : MeasureTheory.IntegrableOn (fun s => (deriv φ s) ^ 2) (Set.Ioc y x) :=
      hfsq_Ioc.mono_set (Set.Ioc_subset_Ioc hy0 hx2a)
    -- `deriv φ` is integrable on `Ioc y x`, being dominated by `1/2 + (1/2)(deriv φ)²`
    have hvol_ne : (volume : MeasureTheory.Measure ℝ) (Set.Ioc y x) ≠ ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have hhalf : MeasureTheory.IntegrableOn
        (fun s => (1 / 2 : ℝ) + (1 / 2) * (deriv φ s) ^ 2) (Set.Ioc y x) :=
      (MeasureTheory.integrableOn_const (C := (1 / 2 : ℝ)) hvol_ne).add
        (hfsq_yx.const_mul (1 / 2))
    have hderiv_int : MeasureTheory.IntegrableOn (deriv φ) (Set.Ioc y x) :=
      Integrable.mono' hhalf (measurable_deriv φ).aestronglyMeasurable
        (Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]
          exact abs_le_half_add_half_sq (deriv φ s))
    -- fundamental theorem of calculus on `[y,x]`
    have hcont_sub : ContinuousOn φ (Set.Icc y x) :=
      hcont.mono (Set.Icc_subset_Icc hy0 hx2a)
    have hdiff_sub : ∀ z ∈ Set.Ioo y x, HasDerivAt φ (deriv φ z) z :=
      fun z hz => hdiff z ⟨lt_of_le_of_lt hy0 hz.1, lt_of_lt_of_le hz.2 hx2a⟩
    have hii : IntervalIntegrable (deriv φ) volume y x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hyx).2 hderiv_int
    have hFTC : ∫ s in y..x, deriv φ s = φ x - φ y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hyx hcont_sub hdiff_sub hii
    -- Cauchy–Schwarz on `Ioc y x`
    have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc y x)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_const).mpr
        (by simpa using (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol_ne))
    have hmem2 : MemLp (deriv φ) 2 (volume.restrict (Set.Ioc y x)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq
        (measurable_deriv φ).aestronglyMeasurable).mpr hfsq_yx
    have hcs := Work.Spaces.cs_integral hmem1 hmem2
    have e1 : (∫ s in Set.Ioc y x, (1 : ℝ) * deriv φ s) = ∫ s in y..x, deriv φ s := by
      rw [intervalIntegral.integral_of_le hyx]
      simp
    have e2 : (∫ s in Set.Ioc y x, (1 : ℝ) ^ 2) = x - y := by
      rw [one_pow, setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ x - y)]
      simp
    have hI2_nonneg : 0 ≤ ∫ s in Set.Ioc y x, (deriv φ s) ^ 2 :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s _ => sq_nonneg _))
    have hB_ge : (∫ s in Set.Ioc y x, (deriv φ s) ^ 2) ≤ B := by
      rw [hBdef]
      have h := intervalIntegral.integral_mono_interval (f := fun s => (deriv φ s) ^ 2)
        (c := (0 : ℝ)) (d := 2 * a) hy0 hyx hx2a hfsq_nonneg hfsq_ii
      rwa [intervalIntegral.integral_of_le hyx] at h
    have hI2_le : (∫ s in y..x, deriv φ s) ^ 2 ≤ (2 * a) * B := by
      have h1 : (∫ s in y..x, deriv φ s) ^ 2
          ≤ (x - y) * (∫ s in Set.Ioc y x, (deriv φ s) ^ 2) := by
        rw [← e1, ← e2]
        exact hcs
      have h2 : (x - y) * (∫ s in Set.Ioc y x, (deriv φ s) ^ 2) ≤ (2 * a) * B :=
        mul_le_mul (by linarith) hB_ge hI2_nonneg ha2a
      linarith
    have hFTC' : φ x = φ y + ∫ s in y..x, deriv φ s := by linarith
    have hsq : (φ x) ^ 2 ≤ 2 * (φ y) ^ 2 + 2 * (∫ s in y..x, deriv φ s) ^ 2 := by
      rw [hFTC']
      nlinarith [sq_nonneg (φ y - ∫ s in y..x, deriv φ s)]
    nlinarith [hsq, hI2_le]
  -- ## Step 2: average the pointwise bound over `y ∈ [0,a]`
  have hcont_a : ContinuousOn φ (Set.Icc (0 : ℝ) a) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  have hf2 : IntervalIntegrable (fun y => 2 * (φ y) ^ 2) volume (0 : ℝ) a :=
    ((hcont_a.pow 2).const_mul 2).intervalIntegrable_of_Icc ha0
  have hg2 : IntervalIntegrable (fun _ : ℝ => 4 * a * B) volume (0 : ℝ) a :=
    intervalIntegrable_const
  have hgi : IntervalIntegrable (fun y => 2 * (φ y) ^ 2 + 4 * a * B) volume (0 : ℝ) a :=
    (((hcont_a.pow 2).const_mul 2).add continuousOn_const).intervalIntegrable_of_Icc ha0
  have hfi : IntervalIntegrable (fun _ : ℝ => (φ x) ^ 2) volume (0 : ℝ) a :=
    intervalIntegrable_const
  have hmono : (∫ y in (0 : ℝ)..a, (φ x) ^ 2)
      ≤ ∫ y in (0 : ℝ)..a, (2 * (φ y) ^ 2 + 4 * a * B) :=
    intervalIntegral.integral_mono_on ha0 hfi hgi (fun y hy => key y hy)
  have hL : (∫ y in (0 : ℝ)..a, (φ x) ^ 2) = a * (φ x) ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp
  have hR : (∫ y in (0 : ℝ)..a, (2 * (φ y) ^ 2 + 4 * a * B))
      = 2 * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a ^ 2 * B := by
    rw [intervalIntegral.integral_add hf2 hg2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp
    ring
  have hmain : a * (φ x) ^ 2 ≤ 2 * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a ^ 2 * B := by
    rw [hL, hR] at hmono
    linarith [hmono]
  have hquot : (φ x) ^ 2
      ≤ (2 * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a ^ 2 * B) / a :=
    (le_div_iff₀ ha).2 (by linarith [hmain])
  have heq : (2 * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a ^ 2 * B) / a
      = (2 / a) * (∫ y in (0 : ℝ)..a, (φ y) ^ 2) + 4 * a * B := by
    field_simp
  rw [heq] at hquot
  simpa [hBdef] using hquot

end Work.Spaces.ThetaAgmon
end
