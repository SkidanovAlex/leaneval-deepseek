import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.Coercivity.Basic =====
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

/-! ## Agreement of the angular data with `Work.Spaces` and `Work.FM` -/





/-- `c` is positive throughout the range of parameters used in the paper. -/
theorem c_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 < Spaces.c α :=
  lt_of_lt_of_le (by norm_num) (Spaces.c_bounds α hα hα1).1

theorem c_ne_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : Spaces.c α ≠ 0 :=
  ne_of_gt (c_pos hα hα1)

/-- `Γ(θ)/c` is bounded by `10` on the angular interval. -/
theorem Gam_div_c_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    |Spaces.Gam α θ / Spaces.c α| ≤ 10 := by
  have hc := (Spaces.c_bounds α hα hα1).1
  have hG := (Spaces.Gam_bounds α θ hα hθ).2
  have hG0 := (Spaces.Gam_bounds α θ hα hθ).1
  have hcp := c_pos hα hα1
  rw [abs_of_nonneg (div_nonneg hG0 (le_of_lt hcp))]
  rw [div_le_iff₀ hcp]
  nlinarith

/-! ## The weight `w` -/

theorem w_eq (z : ℝ) : Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl

theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Spaces.w z := by
  rw [w_eq]; positivity

theorem w_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Spaces.w z := by
  rw [w_eq]; positivity

theorem w_eq_decomp {z : ℝ} (hz : z ≠ 0) :
    Spaces.w z = 1 / z ^ 2 + 2 / z + 1 := by
  rw [w_eq]; field_simp; ring

theorem inv_sq_le_w {z : ℝ} (hz : 0 < z) : 1 / z ^ 2 ≤ Spaces.w z := by
  have h := w_eq_decomp (ne_of_gt hz)
  rw [h]
  have : 0 ≤ 2 / z + 1 := by positivity
  linarith


theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Spaces.w z := by
  have h := w_eq_decomp (ne_of_gt hz)
  rw [h]
  have h1 : 0 ≤ 1 / z ^ 2 + 2 / z := by positivity
  linarith

theorem w_sq_eq {z : ℝ} (hz : z ≠ 0) :
    Spaces.w z ^ 2 = 1 / z ^ 4 + 4 / z ^ 3 + 6 / z ^ 2 + 4 / z + 1 := by
  have h := w_eq_decomp hz
  rw [h]; field_simp; ring

/-! ## The identity `𝓛(g)·w = g·w + z∂_z(g·w)` -/

/-- **The identity `LW` of the paper**, in algebraic form (no differentiability needed):
`𝓛(g)·w = g·w + z ∂_z(g·w)`, with the derivative written out.  This is the pointwise
identity behind every coercivity computation of §6 of the paper. -/
theorem L_mul_w (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hz : 0 < z) :
    L f z θ * Spaces.w z
      = f z θ * Spaces.w z
        + z * (Spaces.pz f z θ * Spaces.w z - f z θ * (2 * (1 + z) / z ^ 3)) := by
  have h : ((1 : ℝ) + z) ≠ 0 := by positivity
  rw [L, Spaces.Dz, Spaces.pz]
  simp only [Spaces.w]
  field_simp
  ring

/-! ## The energies in weighted-inner-product form -/

theorem Ef_eq_wip (f : ℝ → ℝ → ℝ) :
    Ef f = wip (fun z _ => Spaces.w z ^ 2) f f := by
  simp only [Ef, Spaces.L2Sq, wip]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  ring

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.SmoothNbhd_pth_slice =====
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
-- ===== merged: Submission.Work.Elliptic.L12_profile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- `L₁₂` of the fundamental profile `α (Γ(θ)/c) F_*(z)` equals `2α/(1+z)`. -/
theorem L12_profile (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (z : ℝ) (hz : 0 ≤ z) :
    L12 (fun w θ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar w) z
      = 2 * α / (1 + z) := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  -- the angular density is `α F_*(w)/w`
  have hdens : ∀ w : ℝ,
      L12dens (fun w θ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar w) w
        = α * Work.FM.Fstar w / w := by
    intro w
    rw [L12dens]
    have hpt : (fun θ : ℝ => Ktheta θ
          * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar w) / w)
        = fun θ : ℝ =>
          (α * Work.FM.Fstar w / (Work.Spaces.c α * w)) * (Work.Spaces.K θ * Work.Spaces.Gam α θ) := by
      funext θ
      simp only [Ktheta_eq_K]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
    have hcint : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ)
        = Work.Spaces.c α := by
      have h : Work.Spaces.c α = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ := rfl
      rw [h]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hcint]
    rcases eq_or_ne w 0 with hw | hw
    · subst hw; simp
    · field_simp
  rw [L12]
  simp only [hdens]
  have hfun : (fun r : ℝ => α * Work.FM.Fstar r / r)
      = fun r : ℝ => α * (Work.FM.Fstar r / r) := by
    funext r; ring
  rw [hfun, MeasureTheory.integral_const_mul, Work.FM.integral_Ioi_Fstar_div z hz]
  ring

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.pth_contDiffOn_succ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

/-- The curried `θ`-partial derivative `∂_θ G` of a function which is `C^{n+1}` on an open
set is `C^n` on that set.  (The `⊤`-version is `Work.Spaces.contDiffOn_uncurry_pth`.) -/
theorem pth_contDiffOn_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  -- the Fréchet derivative of `uncurry G` is `C^n` on `V`
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hV.uniqueDiffOn (by simp)
    refine h'.congr fun p hp => ?_
    rw [fderivWithin_of_isOpen hV hp]
  -- evaluate it in the direction `(0,1)`
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) V)
  -- identify `∂_θ G` with that evaluation of the Fréchet derivative
  refine hcomp.congr fun p hp => ?_
  have hdiff : DifferentiableAt ℝ (Function.uncurry G) p :=
    (h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp)
  simp only [Function.uncurry]
  exact Work.Spaces.pth_eq_fderiv hdiff

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Topology

/-- `∂_z` lowers the order of differentiability by one: if `Function.uncurry G` is `C^{n+1}` on
the open set `U`, then `Function.uncurry (∂_z G)` is `C^n` there.

Indeed on `U` the `z`-partial is the Fréchet derivative in the direction `(1,0)`, which is `C^n`
by `ContDiffOn.fderiv_of_isOpen` followed by `ContDiffOn.clm_apply` with the constant direction
`(1,0)`. -/
theorem contDiffOn_uncurry_pz_succ {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ} (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G) U) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) U := by
  have hfd : ContDiffOn ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry G)) U :=
    h.fderiv_of_isOpen hU (by simp)
  have hcomp : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (1, 0)) U :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))

/-- The second `z`-partial `∂_z²V` is jointly continuous on any open set on which the
uncurried `V` is `C²`.  `pzIter 2 V z θ` is the second derivative of the one-variable slice
`z' ↦ V z' θ`, and it coincides on `U` with the second iterated Fréchet derivative of
`Function.uncurry V` evaluated on the constant direction `(1,0)`, which is continuous whenever
`Function.uncurry V` is `C²` on the open set `U`.

Suggested sorry-free route (avoid the still-`sorry` `DzAmgm.SliceIteratedDerivFDeriv`): first
prove that `pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1,0)` for every `p ∈ U` by
`Work.Spaces.pz_eq_fderiv` together with `ContDiffOn.differentiableOn` and
`IsOpen.mem_nhds`; then for `G` which is `C^{n+1}` on the open `U` show that
`Function.uncurry (pz G)` is `C^n` on `U` by `ContDiffOn.fderivWithin` (with
`hU.uniqueDiffOn`), `fderivWithin_of_isOpen` and `ContDiffOn.clm_apply contDiffOn_const`,
and apply this twice (`n = 1` then `n = 0`) to `V` (use `pzIter_succ`, `pzIter_zero` to
identify `pzIter 2 V` with `pz (pz V)`). -/
theorem PzIterTwoContinuousOn {V : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ContDiffOn ℝ 2 (Function.uncurry V) U) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 V)) U := by
  have h1 : ContDiffOn ℝ (1 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz V)) U :=
    contDiffOn_uncurry_pz_succ hU (n := 1) h
  have h2 : ContDiffOn ℝ (0 : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz V))) U :=
    contDiffOn_uncurry_pz_succ hU (n := 0) h1
  simpa [Work.Spaces.pzIter_succ] using h2.continuousOn_zero

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.truncZIbp2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The `θ`-integrated radial integration by parts with tests `χ`, `ψ`

We prove `I1Wk.truncZIbp2`: for `u` of class `C^∞` on the open quadrant, `χ ∈ C¹_c((0,∞))`
and `ψ ∈ C¹` with `tsupport ψ ⊆ (0,π/2)`,

`∫_z ∫_θ χ w² σ ψ (z²∂_z²u)(∂_θ²u)
  = - ∫_z ∫_θ (∂_z(χ w² z²)/z) σ ψ (z∂_zu)(∂_θ²u)
    - ∫_z ∫_θ χ w² σ ψ (z∂_zu)(z∂_z∂_θ²u)`,  `σ = sin(2θ)^{-η}`.

This is `∫_z ∂_z[(χ w² z²)·∂_zu·∂_θ²u] = 0` for every fixed `θ` (the radial integration by
parts, whose boundary terms vanish because `χ` is compactly supported away from `0` —
`tsupport χ ⊆ (0,∞)` — and `ψ` is supported in a compact subinterval of `(0,π/2)`), followed
by Fubini in `(z,θ)`.
-/

/-! ## Notation -/

private abbrev qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_qd : IsOpen qd := isOpen_Ioi.prod isOpen_Ioo

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
private def sg (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The radial weight `ω(z) = χ(z)·w(z)²·z²`. -/
private def om (χ : ℝ → ℝ) (z : ℝ) : ℝ := χ z * (Work.Spaces.w z) ^ 2 * z ^ 2

/-- The boundary primitive of the `z`-integral. -/
private def prim (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ * Work.Spaces.pthIter 2 u z θ

/-- The left-hand integrand. -/
private def J1 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  om χ z * sg θ * ψ θ * Work.Spaces.pzIter 2 u z θ * Work.Spaces.pthIter 2 u z θ

/-- The first right-hand integrand. -/
private def J2 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (deriv (om χ) z / z) * sg θ * ψ θ * (z * Work.Spaces.pz u z θ)
    * Work.Spaces.pthIter 2 u z θ

/-- The second right-hand integrand. -/
private def J3 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ
    * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ

/-- The `z`-derivative of the boundary primitive. -/
private def J4 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  deriv (fun z' => prim u χ ψ z' θ) z

private theorem sg_rfl (θ : ℝ) : sg θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

private theorem om_rfl (χ : ℝ → ℝ) (z : ℝ) : om χ z = χ z * (Work.Spaces.w z) ^ 2 * z ^ 2 := rfl

private theorem prim_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    prim u χ ψ z θ = om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ
      * Work.Spaces.pthIter 2 u z θ := rfl

private theorem J1_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    J1 u χ ψ z θ = om χ z * sg θ * ψ θ * Work.Spaces.pzIter 2 u z θ
      * Work.Spaces.pthIter 2 u z θ := rfl

private theorem J2_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    J2 u χ ψ z θ = (deriv (om χ) z / z) * sg θ * ψ θ * (z * Work.Spaces.pz u z θ)
      * Work.Spaces.pthIter 2 u z θ := rfl

private theorem J3_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    J3 u χ ψ z θ = om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ
      * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := rfl

private theorem J4_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    J4 u χ ψ z θ = deriv (fun z' => prim u χ ψ z' θ) z := rfl

/-! ## Calculus on the open quadrant -/

/-- `Work.Spaces.pz` lowers the order of smoothness by one (open set, finite order). -/
private theorem contDiffOn_uncurry_pz_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V,
      Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) :=
    fun p hp => Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `Work.Spaces.pth` lowers the order of smoothness by one (open set, finite order). -/
private theorem contDiffOn_uncurry_pth_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V,
      Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) :=
    fun p hp => Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `z`-slices of a function which is `C^n` on an open set are `C^n`. -/
private theorem contDiffOn_zslice {G : ℝ → ℝ → ℝ} {n : WithTop ℕ∞} {V : Set (ℝ × ℝ)}
    (_hV : IsOpen V) (h : ContDiffOn ℝ n (Function.uncurry G) V) {θ : ℝ} {W : Set ℝ}
    (_hW : IsOpen W) (hmem : ∀ z ∈ W, (z, θ) ∈ V) :
    ContDiffOn ℝ n (fun z => G z θ) W := by
  have hf : ContDiffOn ℝ n (fun z : ℝ => (z, θ)) W :=
    ContDiffOn.prodMk contDiffOn_id (contDiffOn_const (c := θ))
  have h2 := h.comp hf hmem
  simpa [Function.comp_def, Function.uncurry] using h2

/-! ## The weight `ω = χ w² z²` -/

private theorem contDiffOn_om (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) :
    ContDiffOn ℝ 1 (om χ) (Set.Ioi 0) := by
  have hχ' : ContDiffOn ℝ 1 χ (Set.Ioi 0) := hχ.contDiffOn
  have hw2 : ContDiffOn ℝ 1 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hnum : ContDiffOn ℝ 1 (fun z : ℝ => ((1 + z) ^ 2) ^ 2) (Set.Ioi 0) := by fun_prop
    have hden : ContDiffOn ℝ 1 (fun z : ℝ => (z ^ 2) ^ 2) (Set.Ioi 0) := by fun_prop
    have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (z ^ 2) ^ 2 ≠ 0 := fun z hz =>
      pow_ne_zero _ (pow_ne_zero _ (ne_of_gt (show (0 : ℝ) < z from hz)))
    refine (hnum.div hden hne).congr ?_
    intro z _
    simp only [Pi.div_apply, Work.Spaces.w, div_pow]
  have hz2 : ContDiffOn ℝ 1 (fun z : ℝ => z ^ 2) (Set.Ioi 0) := by fun_prop
  exact (hχ'.mul hw2).mul hz2

/-- The boundary primitive vanishes where its weight does. -/
private theorem prim_zero_off {u : ℝ → ℝ → ℝ} {χ ψ : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → om χ z = 0) :
    ∀ z θ : ℝ, z ∉ Set.Icc a b → prim u χ ψ z θ = 0 := by
  intro z θ hz
  rw [prim_rfl, hω0 z hz]
  ring

/-- The derivative of a function vanishing off `[a,b]` vanishes off `[a,b]`. -/
private theorem deriv_eq_zero_off {F : ℝ → ℝ} {a b : ℝ}
    (h : ∀ z, z ∉ Set.Icc a b → F z = 0) :
    ∀ z, z ∉ Set.Icc a b → deriv F z = 0 := by
  intro z hz
  have hz' : z < a ∨ b < z := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hz
  have hev : F =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      exact h y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
      exact h y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)
  rw [hev.deriv_eq]
  simp

/-! ## The angular weight `σ` and the two support separations -/

private theorem continuousOn_sg {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn sg (Set.Icc c d) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc c d) := by fun_prop
  refine ContinuousOn.rpow hsin continuousOn_const ?_
  intro θ hθ
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hc])
    (by linarith [hθ.2, hd])))

/-- A compactly supported function whose (closed) support avoids `0` vanishes off a compact
interval `[a,b]` with `0 < a ≤ b`. -/
private theorem exists_sep_chi {χ : ℝ → ℝ} (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Set.Ioi (0 : ℝ)) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ z : ℝ, z ∉ Set.Icc a b → χ z = 0 := by
  have hcomp : IsCompact (tsupport χ) := hc.isCompact
  have hne : (0 : ℝ) ∉ tsupport χ := fun h => lt_irrefl 0 (Set.mem_Ioi.mp (hs h))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport χ).isOpen_compl.mem_nhds hne)
  obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨min (ε / 2) 1, max R 1, lt_min (by linarith) one_pos, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (le_max_right _ _)
  · intro z hz
    by_contra hzc
    have hzmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hzc)
    have hz0 : 0 < z := hs hzmem
    have hza : min (ε / 2) 1 ≤ z := by
      have hge : ε ≤ z := by
        by_contra hlt
        push Not at hlt
        have hb : z ∈ Metric.ball (0 : ℝ) ε := by
          simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hz0]
          exact hlt
        exact (hball hb) hzmem
      exact le_trans (min_le_left _ _) (by linarith)
    have hzb : z ≤ max R 1 := by
      have hmem := hR hzmem
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
      exact le_trans (le_trans (le_abs_self z) hmem) (le_max_left _ _)
    exact hz ⟨hza, hzb⟩

/-- A function whose (closed) support is contained in `(0,π/2)` vanishes off a compact
interval `[c,d]` with `0 < c ≤ d < π/2`. -/
private theorem exists_sep_psi {ψ : ℝ → ℝ} (hs : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2)) :
    ∃ c d : ℝ, 0 < c ∧ c ≤ d ∧ d < Real.pi / 2 ∧
      ∀ θ : ℝ, θ ∉ Set.Icc c d → ψ θ = 0 := by
  have hbdd : Bornology.IsBounded (tsupport ψ) := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mpr ⟨Real.pi / 2, ?_⟩
    intro z hz
    have hz' := hs hz
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz'.1, Real.pi_pos], le_of_lt hz'.2⟩
  have hne0 : (0 : ℝ) ∉ tsupport ψ := fun h => lt_irrefl 0 (hs h).1
  have hne1 : (Real.pi / 2) ∉ tsupport ψ := fun h => lt_irrefl _ (hs h).2
  obtain ⟨ε, hε, hball0⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hne0)
  obtain ⟨δ, hδ, hball1⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hne1)
  refine ⟨min (ε / 2) (Real.pi / 4), max (Real.pi / 4) (Real.pi / 2 - δ / 2),
    lt_min (by linarith) (by linarith [Real.pi_pos]), ?_, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (le_max_left _ _)
  · exact max_lt (by linarith [Real.pi_pos]) (by linarith)
  · intro θ hθ
    by_contra hne
    have hmem : θ ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hne)
    have hθ' := hs hmem
    have hge : ε ≤ θ := by
      by_contra hlt
      push Not at hlt
      have hb : θ ∈ Metric.ball (0 : ℝ) ε := by
        simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
          abs_of_pos hθ'.1]
        exact hlt
      exact (hball0 hb) hmem
    have hle : δ ≤ Real.pi / 2 - θ := by
      by_contra hlt
      push Not at hlt
      have hb : θ ∈ Metric.ball (Real.pi / 2) δ := by
        rw [Metric.mem_ball, Real.dist_eq,
          abs_of_neg (show θ - Real.pi / 2 < 0 by linarith [hθ'.2])]
        linarith
      exact (hball1 hb) hmem
    exact hθ ⟨le_trans (min_le_left _ _) (by linarith),
      le_trans (by linarith) (le_max_right _ _)⟩

/-! ## Smoothness of the derivative factors -/

private theorem contDiffOn_pz_one {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz u)) qd :=
  contDiffOn_uncurry_pz_fin isOpen_qd (n := 1) (hu 2)

private theorem contDiffOn_pzIter_two {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 u)) qd := by
  have hp : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz u)) qd :=
    contDiffOn_uncurry_pz_fin isOpen_qd (n := 2) (hu 3)
  have hp2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz u))) qd :=
    contDiffOn_uncurry_pz_fin isOpen_qd (n := 1) hp
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hp2

private theorem contDiffOn_pthIter_two {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 u)) qd := by
  have hp : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth u)) qd :=
    contDiffOn_uncurry_pth_fin isOpen_qd (n := 2) (hu 3)
  have hp2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth u))) qd :=
    contDiffOn_uncurry_pth_fin isOpen_qd (n := 1) hp
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hp2

private theorem contDiffOn_pz_pth2 {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 u))) qd := by
  have h1 : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.pth u)) qd :=
    contDiffOn_uncurry_pth_fin isOpen_qd (n := 3) (hu 4)
  have h2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth u))) qd :=
    contDiffOn_uncurry_pth_fin isOpen_qd (n := 2) h1
  have h3 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pthIter 2 u)) qd := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2
  exact contDiffOn_uncurry_pz_fin isOpen_qd (n := 1) h3

/-! ## The `z`-derivative of the slices -/

private theorem hasDerivAt_pz_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) {z θ : ℝ}
    (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => Work.Spaces.pz u z' θ) (Work.Spaces.pzIter 2 u z θ) z := by
  have hslice : ContDiffOn ℝ 1 (fun z => Work.Spaces.pz u z θ) (Set.Ioi 0) :=
    contDiffOn_zslice isOpen_qd (contDiffOn_pz_one hu) isOpen_Ioi
      (fun z hz => ⟨hz, hθ1, hθ2⟩)
  have h := ((hslice.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have h2 : Work.Spaces.pzIter 2 u z θ = deriv (fun z' => Work.Spaces.pz u z' θ) z := rfl
  rw [h2]
  exact h

private theorem hasDerivAt_pth2_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) {z θ : ℝ}
    (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => Work.Spaces.pthIter 2 u z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z := by
  have hslice : ContDiffOn ℝ 1 (fun z => Work.Spaces.pthIter 2 u z θ) (Set.Ioi 0) :=
    contDiffOn_zslice isOpen_qd (contDiffOn_pthIter_two hu) isOpen_Ioi
      (fun z hz => ⟨hz, hθ1, hθ2⟩)
  have h := ((hslice.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have h2 : Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ
      = deriv (fun z' => Work.Spaces.pthIter 2 u z' θ) z := rfl
  rw [h2]
  exact h

/-! ## The pointwise derivative identity on the open quadrant -/

/-- On `z ≠ 0` the first right-hand integrand is `∂_zω·σψ·∂_zu·∂_θ²u`. -/
private theorem J2_eq {u : ℝ → ℝ → ℝ} {χ ψ : ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0) :
    J2 u χ ψ z θ = deriv (om χ) z * sg θ * ψ θ * Work.Spaces.pz u z θ
      * Work.Spaces.pthIter 2 u z θ := by
  have h : deriv (om χ) z / z * z = deriv (om χ) z := div_mul_cancel₀ _ hz
  calc J2 u χ ψ z θ
      = (deriv (om χ) z / z * z) * (sg θ * ψ θ * Work.Spaces.pz u z θ
          * Work.Spaces.pthIter 2 u z θ) := by rw [J2_rfl]; ring
    _ = deriv (om χ) z * sg θ * ψ θ * Work.Spaces.pz u z θ
          * Work.Spaces.pthIter 2 u z θ := by rw [h]; ring

/-- The pointwise identity `J1 + J2 + J3 = J4` on the open quadrant. -/
private theorem hasDerivAt_prim_slice {u : ℝ → ℝ → ℝ} (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    (hχ : ContDiff ℝ 1 χ) {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => prim u χ ψ z' θ)
      (J1 u χ ψ z θ + J2 u χ ψ z θ + J3 u χ ψ z θ) z := by
  have hω : HasDerivAt (om χ) (deriv (om χ) z) z :=
    ((contDiffOn_om χ hχ).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt
  have hA : HasDerivAt (fun z' => Work.Spaces.pz u z' θ)
      (Work.Spaces.pzIter 2 u z θ) z := hasDerivAt_pz_slice hu hz hθ1 hθ2
  have hB : HasDerivAt (fun z' => Work.Spaces.pthIter 2 u z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z :=
    hasDerivAt_pth2_slice hu hz hθ1 hθ2
  have hc1 : HasDerivAt (fun _ : ℝ => sg θ) 0 z := hasDerivAt_const z (sg θ)
  have hc2 : HasDerivAt (fun _ : ℝ => ψ θ) 0 z := hasDerivAt_const z (ψ θ)
  have hall : HasDerivAt
      (fun z' => om χ z' * sg θ * ψ θ * Work.Spaces.pz u z' θ
        * Work.Spaces.pthIter 2 u z' θ)
      (J1 u χ ψ z θ + J2 u χ ψ z θ + J3 u χ ψ z θ) z := by
    have h0 := (((hω.mul hc1).mul hc2).mul hA).mul hB
    refine h0.congr_deriv ?_
    simp only [Pi.mul_apply, mul_zero, add_zero]
    rw [J2_eq (ne_of_gt hz), J1_rfl, J3_rfl]
    ring
  have hfun : (fun z' => prim u χ ψ z' θ) = fun z' => om χ z' * sg θ * ψ θ
      * Work.Spaces.pz u z' θ * Work.Spaces.pthIter 2 u z' θ := by
    funext z'
    rw [prim_rfl]
  rw [hfun]
  exact hall

private theorem J1_add_J2_add_J3_eq_J4 {u : ℝ → ℝ → ℝ} {χ ψ : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    (hχ : ContDiff ℝ 1 χ) {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ)
    (hθ2 : θ < Real.pi / 2) :
    J1 u χ ψ z θ + J2 u χ ψ z θ + J3 u χ ψ z θ = J4 u χ ψ z θ :=
  (hasDerivAt_prim_slice χ ψ hu hχ hz hθ1 hθ2).deriv.symm

/-! ## The per-angle radial integration by parts -/

private theorem slice_integral_zero {u : ℝ → ℝ → ℝ} (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    (hχ : ContDiff ℝ 1 χ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → om χ z = 0)
    {θ : ℝ} (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    (∫ z in Set.Ioi 0, deriv (fun z' => prim u χ ψ z' θ) z) = 0 := by
  have hωd : ContDiffOn ℝ 1 (om χ) (Set.Ioi 0) := contDiffOn_om χ hχ
  have hpz : ContDiffOn ℝ 1 (fun z => Work.Spaces.pz u z θ) (Set.Ioi 0) :=
    contDiffOn_zslice isOpen_qd (contDiffOn_pz_one hu) isOpen_Ioi
      (fun z hz => ⟨hz, hθ1, hθ2⟩)
  have hpth : ContDiffOn ℝ 1 (fun z => Work.Spaces.pthIter 2 u z θ) (Set.Ioi 0) :=
    contDiffOn_zslice isOpen_qd (contDiffOn_pthIter_two hu) isOpen_Ioi
      (fun z hz => ⟨hz, hθ1, hθ2⟩)
  set G : ℝ → ℝ := fun z => prim u χ ψ z θ with hGdef
  have hG1 : ContDiffOn ℝ 1 G (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 1 (fun z : ℝ => om χ z * sg θ) (Set.Ioi 0) :=
      ContDiffOn.mul hωd contDiffOn_const
    have h2 : ContDiffOn ℝ 1 (fun z : ℝ => om χ z * sg θ * ψ θ) (Set.Ioi 0) :=
      ContDiffOn.mul h1 contDiffOn_const
    have h3 : ContDiffOn ℝ 1
        (fun z : ℝ => om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ) (Set.Ioi 0) :=
      ContDiffOn.mul h2 hpz
    have h4 : ContDiffOn ℝ 1
        (fun z : ℝ => om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ
          * Work.Spaces.pthIter 2 u z θ) (Set.Ioi 0) :=
      ContDiffOn.mul h3 hpth
    rw [hGdef]
    exact h4
  have hGoff : ∀ z, 0 < z → (z < a ∨ b < z) → G z = 0 := by
    intro z hz hc
    have hzc : z ∉ Set.Icc a b := by
      intro hmem
      rcases hc with h | h <;> linarith [hmem.1, hmem.2]
    exact prim_zero_off hω0 z θ hzc
  have hGderiv_off : ∀ z, 0 < z → (z < a ∨ b < z) → deriv G z = 0 := by
    intro z hz hc
    have hev : G =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      rcases hc with hlt | hgt
      · filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo 0 a from ⟨hz, hlt⟩)]
          with y hy
        exact hGoff y hy.1 (Or.inl hy.2)
      · filter_upwards [isOpen_Ioo.mem_nhds
          (show z ∈ Set.Ioo b (z + 1) from ⟨hgt, by linarith⟩)] with y hy
        exact hGoff y (by linarith [hy.1, hgt, ha]) (Or.inr hy.1)
    rw [hev.deriv_eq]
    simp
  have hsub : Set.Icc (a / 2) (b + 1) ⊆ Set.Ioi (0 : ℝ) := fun z hz => by
    simp only [Set.mem_Ioi]; linarith [hz.1, ha]
  have hcontG : ContinuousOn G (Set.Icc (a / 2) (b + 1)) := hG1.continuousOn.mono hsub
  have hderivG : ContinuousOn (deriv G) (Set.Icc (a / 2) (b + 1)) :=
    (hG1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hGint : IntervalIntegrable (deriv G) volume (a / 2) (b + 1) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) hderivG
  have hFTC : (∫ x in (a / 2)..(b + 1), deriv G x) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show a / 2 ≤ b + 1 by linarith)
      hcontG (fun x hx => ((hG1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩))).hasDerivAt) hGint
    rw [h]
    have e1 : G (b + 1) = 0 := hGoff (b + 1) (by linarith) (Or.inr (by linarith))
    have e2 : G (a / 2) = 0 := hGoff (a / 2) (by linarith) (Or.inl (by linarith))
    rw [e1, e2, sub_zero]
  have hset : (∫ z in Set.Ioi 0, deriv G z) = ∫ z in (a / 2)..(b + 1), deriv G z := by
    have h1 : (∫ z in Set.Ioi (0 : ℝ), deriv G z)
        = ∫ z in Set.Icc (a / 2) (b + 1), deriv G z :=
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
        (fun x hx => by
          have hx' : ¬ (a / 2 ≤ x ∧ x ≤ b + 1) := hx.2
          have hc : x < a / 2 ∨ b + 1 < x := by
            by_contra hcon
            push Not at hcon
            exact hx' ⟨hcon.1, hcon.2⟩
          exact hGderiv_off x hx.1 (by
            rcases hc with h | h
            · exact Or.inl (by linarith)
            · exact Or.inr (by linarith)))
    rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show a / 2 ≤ b + 1 by linarith)]
  rw [hset, hFTC]

/-! ## Fubini for the product of the two integrations -/

private theorem setIntegral_prod_eq {F : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (h : MeasureTheory.IntegrableOn F (s ×ˢ t)) :
    (∫ p in s ×ˢ t, F p) = ∫ z in s, ∫ θ in t, F (z, θ) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact MeasureTheory.setIntegral_prod F h

private theorem setIntegral_swap {F : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (h : MeasureTheory.IntegrableOn F (s ×ˢ t)) :
    (∫ z in s, ∫ θ in t, F (z, θ)) = ∫ θ in t, ∫ z in s, F (z, θ) := by
  have hInt : MeasureTheory.Integrable F ((volume.restrict s).prod (volume.restrict t)) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    exact h
  have hsw := MeasureTheory.integral_integral_swap (μ := volume.restrict s)
    (ν := volume.restrict t) (f := fun z θ => F (z, θ)) hInt
  simpa using hsw

/-! ## The two-dimensional identity -/

private theorem master (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Set.Ioi (0 : ℝ))
    (hψ : ContDiff ℝ 1 ψ) (hψsupp : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J1 u χ ψ z θ)
      = -(∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J2 u χ ψ z θ)
        -(∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J3 u χ ψ z θ) := by
  obtain ⟨a, b, ha, hab, hχ0⟩ := exists_sep_chi hχc hχsupp
  obtain ⟨c, d, hc, hcd, hd, hψ0⟩ := exists_sep_psi hψsupp
  have hωd : ContDiffOn ℝ 1 (om χ) (Set.Ioi 0) := contDiffOn_om χ hχ
  have hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → om χ z = 0 := fun z hz => by
    rw [om_rfl, hχ0 z hz]
    ring
  have hω0' : ∀ z : ℝ, z ∉ Set.Icc a b → deriv (om χ) z = 0 := deriv_eq_zero_off hω0
  have hboxc : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hboxsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ qd := fun p hp =>
    ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  -- the four integrands on the product
  set A : ℝ × ℝ → ℝ := fun p => J1 u χ ψ p.1 p.2 with hA
  set B : ℝ × ℝ → ℝ := fun p => J2 u χ ψ p.1 p.2 with hB
  set C : ℝ × ℝ → ℝ := fun p => J3 u χ ψ p.1 p.2 with hC
  set D : ℝ × ℝ → ℝ := fun p => J4 u χ ψ p.1 p.2 with hD
  -- ## the pointwise identity `A + B + C = D` on the open quadrant
  have hpt : ∀ p ∈ qd, A p + B p + C p = D p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ1, hθ2⟩ := hp
    have hz' : 0 < z := hz
    have h := J1_add_J2_add_J3_eq_J4 (u := u) (χ := χ) (ψ := ψ) hu hχ hz' hθ1 hθ2
    have hA' : A (z, θ) = J1 u χ ψ z θ := by rw [hA]
    have hB' : B (z, θ) = J2 u χ ψ z θ := by rw [hB]
    have hC' : C (z, θ) = J3 u χ ψ z θ := by rw [hC]
    have hD' : D (z, θ) = J4 u χ ψ z θ := by rw [hD]
    rw [hA', hB', hC', hD']
    exact h
  -- ## vanishing off the box
  have hA0 : ∀ p, p ∉ Set.Icc a b ×ˢ Set.Icc c d → A p = 0 := by
    rintro ⟨z, θ⟩ hp
    by_cases hz : z ∈ Set.Icc a b
    · have hθ : θ ∉ Set.Icc c d := fun hθ' => hp ⟨hz, hθ'⟩
      show J1 u χ ψ z θ = 0
      rw [J1_rfl, hψ0 θ hθ]
      ring
    · show J1 u χ ψ z θ = 0
      rw [J1_rfl, hω0 z hz]
      ring
  have hB0 : ∀ p, p ∉ Set.Icc a b ×ˢ Set.Icc c d → B p = 0 := by
    rintro ⟨z, θ⟩ hp
    by_cases hz : z ∈ Set.Icc a b
    · have hθ : θ ∉ Set.Icc c d := fun hθ' => hp ⟨hz, hθ'⟩
      show J2 u χ ψ z θ = 0
      rw [J2_rfl, hψ0 θ hθ]
      ring
    · show J2 u χ ψ z θ = 0
      rw [J2_rfl, hω0' z hz]
      ring
  have hC0 : ∀ p, p ∉ Set.Icc a b ×ˢ Set.Icc c d → C p = 0 := by
    rintro ⟨z, θ⟩ hp
    by_cases hz : z ∈ Set.Icc a b
    · have hθ : θ ∉ Set.Icc c d := fun hθ' => hp ⟨hz, hθ'⟩
      show J3 u χ ψ z θ = 0
      rw [J3_rfl, hψ0 θ hθ]
      ring
    · show J3 u χ ψ z θ = 0
      rw [J3_rfl, hω0 z hz]
      ring
  -- ## continuity on the box
  have hcontA : ContinuousOn A (Set.Icc a b ×ˢ Set.Icc c d) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => om χ p.1) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hωd.continuousOn.comp continuous_fst.continuousOn (fun p hp => by
        simp only [Set.mem_Ioi]; linarith [hp.1.1, ha])
    have h2 : ContinuousOn (fun p : ℝ × ℝ => sg p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (continuousOn_sg hc hd).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => ψ p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hψ.continuous.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pzIter_two hu).continuousOn.mono hboxsub
    have h5 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pthIter_two hu).continuousOn.mono hboxsub
    have hprod : ContinuousOn (fun p : ℝ × ℝ => om χ p.1 * sg p.2 * ψ p.2
        * Work.Spaces.pzIter 2 u p.1 p.2 * Work.Spaces.pthIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) := (((h1.mul h2).mul h3).mul h4).mul h5
    have hEqA : A = (fun p : ℝ × ℝ => om χ p.1) * (fun p : ℝ × ℝ => sg p.2)
        * (fun p : ℝ × ℝ => ψ p.2) * (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2) := by
      rw [hA]
      funext p
      simp only [Pi.mul_apply, J1_rfl]
    rw [hEqA]
    exact hprod
  have hcontB : ContinuousOn B (Set.Icc a b ×ˢ Set.Icc c d) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => deriv (om χ) p.1 / p.1)
        (Set.Icc a b ×ˢ Set.Icc c d) := by
      refine ContinuousOn.div ?_ continuous_fst.continuousOn ?_
      · exact (hωd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp
          continuous_fst.continuousOn (fun p hp => by
            simp only [Set.mem_Ioi]; linarith [hp.1.1, ha])
      · intro p hp
        have hpos : (0 : ℝ) < p.1 := by linarith [hp.1.1, ha]
        exact ne_of_gt hpos
    have h2 : ContinuousOn (fun p : ℝ × ℝ => sg p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (continuousOn_sg hc hd).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => ψ p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hψ.continuous.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      continuous_fst.continuousOn.mul
        ((contDiffOn_pz_one hu).continuousOn.mono hboxsub)
    have h5 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pthIter_two hu).continuousOn.mono hboxsub
    have hprod : ContinuousOn (fun p : ℝ × ℝ => deriv (om χ) p.1 / p.1 * sg p.2 * ψ p.2
        * (p.1 * Work.Spaces.pz u p.1 p.2) * Work.Spaces.pthIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) := (((h1.mul h2).mul h3).mul h4).mul h5
    have hEqB : B = (fun p : ℝ × ℝ => deriv (om χ) p.1 / p.1) * (fun p : ℝ × ℝ => sg p.2)
        * (fun p : ℝ × ℝ => ψ p.2) * (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2) := by
      rw [hB]
      funext p
      simp only [Pi.mul_apply, J2_rfl]
    rw [hEqB]
    exact hprod
  have hcontC : ContinuousOn C (Set.Icc a b ×ˢ Set.Icc c d) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => om χ p.1) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hωd.continuousOn.comp continuous_fst.continuousOn (fun p hp => by
        simp only [Set.mem_Ioi]; linarith [hp.1.1, ha])
    have h2 : ContinuousOn (fun p : ℝ × ℝ => sg p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (continuousOn_sg hc hd).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => ψ p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hψ.continuous.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pz_one hu).continuousOn.mono hboxsub
    have h5 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pz_pth2 hu).continuousOn.mono hboxsub
    have hprod : ContinuousOn (fun p : ℝ × ℝ => om χ p.1 * sg p.2 * ψ p.2
        * Work.Spaces.pz u p.1 p.2
        * Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) := (((h1.mul h2).mul h3).mul h4).mul h5
    have hEqC : C = (fun p : ℝ × ℝ => om χ p.1) * (fun p : ℝ × ℝ => sg p.2)
        * (fun p : ℝ × ℝ => ψ p.2) * (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2) := by
      rw [hC]
      funext p
      simp only [Pi.mul_apply, J3_rfl]
    rw [hEqC]
    exact hprod
  -- ## integrability
  have hIntAbox : MeasureTheory.IntegrableOn A (Set.Icc a b ×ˢ Set.Icc c d) :=
    hcontA.integrableOn_compact hboxc
  have hIntBbox : MeasureTheory.IntegrableOn B (Set.Icc a b ×ˢ Set.Icc c d) :=
    hcontB.integrableOn_compact hboxc
  have hIntCbox : MeasureTheory.IntegrableOn C (Set.Icc a b ×ˢ Set.Icc c d) :=
    hcontC.integrableOn_compact hboxc
  have hIntA : MeasureTheory.IntegrableOn A qd :=
    hIntAbox.of_forall_sdiff_eq_zero isOpen_qd.measurableSet (fun p hp => hA0 p hp.2)
  have hIntB : MeasureTheory.IntegrableOn B qd :=
    hIntBbox.of_forall_sdiff_eq_zero isOpen_qd.measurableSet (fun p hp => hB0 p hp.2)
  have hIntC : MeasureTheory.IntegrableOn C qd :=
    hIntCbox.of_forall_sdiff_eq_zero isOpen_qd.measurableSet (fun p hp => hC0 p hp.2)
  have hIntD : MeasureTheory.IntegrableOn D qd :=
    ((hIntA.add hIntB).add hIntC).congr_fun (fun p hp => hpt p hp)
      isOpen_qd.measurableSet
  -- ## the integral of `D` vanishes
  have hDzero : (∫ p in qd, D p) = 0 := by
    rw [setIntegral_prod_eq hIntD, setIntegral_swap hIntD]
    have hinner : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (∫ z in Set.Ioi 0, D (z, θ)) = 0 := by
      intro θ hθ
      simpa only [hD, J4_rfl] using slice_integral_zero χ ψ hu hχ ha hab hω0 hθ.1 hθ.2
    rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Set.Ioi 0, D (z, θ))
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (0 : ℝ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hinner]
    simp
  -- ## linearity
  have hAdd : (∫ p in qd, A p) + (∫ p in qd, B p) + (∫ p in qd, C p) = 0 := by
    have h1 : (∫ p in qd, A p + B p) = (∫ p in qd, A p) + (∫ p in qd, B p) :=
      MeasureTheory.integral_add hIntA hIntB
    have h2 : (∫ p in qd, A p + B p + C p)
        = (∫ p in qd, A p + B p) + (∫ p in qd, C p) :=
      MeasureTheory.integral_add (hIntA.add hIntB) hIntC
    have h3 : (∫ p in qd, A p + B p + C p) = ∫ p in qd, D p :=
      MeasureTheory.setIntegral_congr_fun isOpen_qd.measurableSet (fun p hp => hpt p hp)
    linarith [h1, h2, h3, hDzero]
  -- ## back to the iterated integrals
  have c1 : (∫ p in qd, A p)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J1 u χ ψ z θ := by
    simpa only [hA] using setIntegral_prod_eq hIntA
  have c2 : (∫ p in qd, B p)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J2 u χ ψ z θ := by
    simpa only [hB] using setIntegral_prod_eq hIntB
  have c3 : (∫ p in qd, C p)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J3 u χ ψ z θ := by
    simpa only [hC] using setIntegral_prod_eq hIntC
  linarith [hAdd, c1, c2, c3]

/-! ## The requested identity -/

theorem truncZIbp2 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Set.Ioi (0:ℝ))
    (hψ : ContDiff ℝ 1 ψ) (hψsupp : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z^2 * Work.Spaces.pzIter 2 u z θ) * (Work.Spaces.pthIter 2 u z θ))
    = - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (deriv (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2) z / z)
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
            * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ))
      - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
          * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)) := by
  have h1 : ∀ z θ : ℝ, χ z * (Work.Spaces.w z)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
        * ψ θ * (z^2 * Work.Spaces.pzIter 2 u z θ) * (Work.Spaces.pthIter 2 u z θ)
      = J1 u χ ψ z θ := fun z θ => by rw [J1_rfl, om_rfl, sg_rfl]; ring
  have h2 : ∀ z θ : ℝ,
      (deriv (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2) z / z)
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ)
      = J2 u χ ψ z θ := fun z θ => by
    rw [J2_rfl, show om χ = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2 from rfl,
      sg_rfl]
  have h3 : ∀ z θ : ℝ, χ z * (Work.Spaces.w z)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
        * ψ θ * (z * Work.Spaces.pz u z θ)
        * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      = J3 u χ ψ z θ := fun z θ => by rw [J3_rfl, om_rfl, sg_rfl]; ring
  simp only [h1, h2, h3]
  exact master u χ ψ hu hχ hχc hχsupp hψ hψsupp

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The unweighted `L²` norm (definitionally the one of `Work.Elliptic.Estimates`) -/










/-! ## The operators `U`, `V`, `ℛ` of §Modulation (tex 1320) -/

/-- `U(Ψ) := -3Ψ - α z ∂_z Ψ` (paper (Relations), tex 1320): the coefficient of `∂_θΩ`. -/
def Uop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -3 * Ψ z θ - α * z * Work.Spaces.pz Ψ z θ

/-- `V(Ψ) := ∂_θΨ - tan θ · Ψ`: the coefficient of `α z ∂_zΩ`. -/
def Vop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ

/-- `ℛ(Ψ) := (1/cos θ)(2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ)`: the coefficient of
`Ω` in the self-similar vorticity equation (paper (Relations), tex 1320). -/
def Rop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
    + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ

/-! ## The calculus of pointwise negation

The totalised `deriv` is odd (`deriv.neg`), so every operator of the chapter commutes with
pointwise negation; these lemmas are the formal content of "the estimates are sign-invariant". -/

theorem deriv_neg_apply (f : ℝ → ℝ) (x : ℝ) : deriv (fun y => -(f y)) x = -deriv f x := by
  simpa using deriv.neg (f := f) (x := x)

theorem pz_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (-f) = fun z θ => -(Work.Spaces.pz f z θ) := by
  funext z θ
  simp only [Work.Spaces.pz, Pi.neg_apply]
  exact deriv_neg_apply _ _

theorem pth_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (-f) = fun z θ => -(Work.Spaces.pth f z θ) := by
  funext z θ
  simp only [Work.Spaces.pth, Pi.neg_apply]
  exact deriv_neg_apply _ _

theorem pzIter_neg (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (-f) = fun z θ => -(Work.Spaces.pzIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      calc Work.Spaces.pzIter (n + 1) (-f)
          = Work.Spaces.pz (Work.Spaces.pzIter n (-f)) := Work.Spaces.pzIter_succ n (-f)
        _ = Work.Spaces.pz (fun z θ => -(Work.Spaces.pzIter n f z θ)) := by rw [ih]
        _ = fun z θ => -(Work.Spaces.pz (Work.Spaces.pzIter n f) z θ) := pz_neg _
        _ = fun z θ => -(Work.Spaces.pzIter (n + 1) f z θ) := by
              rw [Work.Spaces.pzIter_succ]

theorem pthIter_neg (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pthIter n (-f) = fun z θ => -(Work.Spaces.pthIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      calc Work.Spaces.pthIter (n + 1) (-f)
          = Work.Spaces.pth (Work.Spaces.pthIter n (-f)) := Work.Spaces.pthIter_succ n (-f)
        _ = Work.Spaces.pth (fun z θ => -(Work.Spaces.pthIter n f z θ)) := by rw [ih]
        _ = fun z θ => -(Work.Spaces.pth (Work.Spaces.pthIter n f) z θ) := pth_neg _
        _ = fun z θ => -(Work.Spaces.pthIter (n + 1) f z θ) := by
              rw [Work.Spaces.pthIter_succ]

theorem Dz_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (-f) = fun z θ => -(Work.Spaces.Dz f z θ) := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_neg, Pi.neg_apply]
  ring

theorem Dth_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (-f) = fun z θ => -(Work.Spaces.Dth f z θ) := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_neg, Pi.neg_apply]
  ring

theorem DzIter_neg (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DzIter n (-f) = fun z θ => -(Work.Spaces.DzIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      calc Work.Spaces.DzIter (n + 1) (-f)
          = Work.Spaces.Dz (Work.Spaces.DzIter n (-f)) := Work.Spaces.DzIter_succ n (-f)
        _ = Work.Spaces.Dz (fun z θ => -(Work.Spaces.DzIter n f z θ)) := by rw [ih]
        _ = fun z θ => -(Work.Spaces.Dz (Work.Spaces.DzIter n f) z θ) := Dz_neg _
        _ = fun z θ => -(Work.Spaces.DzIter (n + 1) f z θ) := by
              rw [Work.Spaces.DzIter_succ]

theorem DthIter_neg (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (-f) = fun z θ => -(Work.Spaces.DthIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      calc Work.Spaces.DthIter (n + 1) (-f)
          = Work.Spaces.Dth (Work.Spaces.DthIter n (-f)) := Work.Spaces.DthIter_succ n (-f)
        _ = Work.Spaces.Dth (fun z θ => -(Work.Spaces.DthIter n f z θ)) := by rw [ih]
        _ = fun z θ => -(Work.Spaces.Dth (Work.Spaces.DthIter n f) z θ) := Dth_neg _
        _ = fun z θ => -(Work.Spaces.DthIter (n + 1) f z θ) := by
              rw [Work.Spaces.DthIter_succ]

theorem mixed_neg (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (-f) = fun z θ => -(Work.Spaces.mixed j i f z θ) := by
  have h1 := DthIter_neg f i
  have h2 := DzIter_neg (Work.Spaces.DthIter i f) j
  simp only [Work.Spaces.mixed]
  rw [h1]
  exact h2

/-! ## The boundary decay used by the integrations by parts in `z` -/

/-- The decay hypothesis at `z → ∞` that makes the integration by parts in the radial variable
of the elliptic section legitimate: for every angle `θ ∈ [0,π/2]`,

  `z ^ 2 * ((Ψ z θ) ^ 2 + (∂_zΨ z θ) ^ 2 + (∂_zzΨ z θ) ^ 2 + (∂_θΨ z θ) ^ 2
      + (∂_θθΨ z θ) ^ 2) → 0`,

so that every boundary term of the form `z ^ 2 * ∂_zΨ * Ψ` or `z * Ψ ^ 2` (and their analogues
for the derivatives used in the proof) vanishes at infinity.  Every function of `z`-decay
`O(z ^ (-1-ε))`, uniformly in `θ`, satisfies this; in particular every compactly supported
function. -/
def ZDecay (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => z ^ 2 * ((Ψ z θ) ^ 2 + (Work.Spaces.pz Ψ z θ) ^ 2
    + (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 + (Work.Spaces.pth Ψ z θ) ^ 2
    + (Work.Spaces.pthIter 2 Ψ z θ) ^ 2)) atTop (𝓝 0)


/-! ## Sign invariance of the vocabulary of the elliptic section -/






/-- `L₁₂` is odd in the source. -/
theorem L12dens_neg (F : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.Elliptic.L12dens (-F) s = -Work.Elliptic.L12dens F s := by
  simp only [Work.Elliptic.L12dens, Pi.neg_apply]
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * -F s θ / s)
      = ∫ θ in Work.Spaces.Iθ, -(Work.Elliptic.Ktheta θ * F s θ / s) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [integral_neg (f := fun θ => Work.Elliptic.Ktheta θ * F s θ / s)
    (μ := volume.restrict Work.Spaces.Iθ)]

theorem L12_neg (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12 (-F) z = -Work.Elliptic.L12 F z := by
  have hfun : (fun r => Work.Elliptic.L12dens (-F) r)
      = fun r => -(Work.Elliptic.L12dens F r) := by
    funext r; exact L12dens_neg F r
  simp only [Work.Elliptic.L12]
  rw [hfun, integral_neg (f := fun r => Work.Elliptic.L12dens F r)
    (μ := volume.restrict (Set.Ioi z))]







/-- The elliptic operator is odd. -/
theorem bslOp_neg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.bslOp α (-Ψ) = fun z θ => -(Work.Elliptic.bslOp α Ψ z θ) := by
  funext z θ
  have h2 : Work.Spaces.pzIter 2 (-Ψ) z θ = -(Work.Spaces.pzIter 2 Ψ z θ) := by
    simpa using congrFun (congrFun (pzIter_neg Ψ 2) z) θ
  have h1 : Work.Spaces.pz (-Ψ) z θ = -(Work.Spaces.pz Ψ z θ) := by
    simpa using congrFun (congrFun (pz_neg Ψ) z) θ
  have ht2 : Work.Spaces.pthIter 2 (-Ψ) z θ = -(Work.Spaces.pthIter 2 Ψ z θ) := by
    simpa using congrFun (congrFun (pthIter_neg Ψ 2) z) θ
  have ht1 : Work.Spaces.pth (fun z θ => Real.tan θ * -Ψ z θ) z θ
      = -(Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) := by
    have hfun : (fun z θ => Real.tan θ * -Ψ z θ)
        = (fun z θ => -(Real.tan θ * Ψ z θ)) := by
      funext a b; ring
    rw [hfun]
    simp only [Work.Spaces.pth]
    exact deriv_neg_apply (f := fun θ' => Real.tan θ' * Ψ z θ') θ
  simp only [Work.Elliptic.bslOp, Work.Elliptic.Lzero, Pi.neg_apply]
  rw [h2, h1, ht2, ht1]
  ring


/-! ## `H^k`-norm invariance under negation -/

theorem HkIntegrand_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkIntegrand α k (-f) = Work.Spaces.HkIntegrand α k f := by
  funext z θ
  simp only [Work.Spaces.HkIntegrand, DzIter_neg, mixed_neg]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  · ring
  · split_ifs <;> ring

theorem HkSq_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (-f) = Work.Spaces.HkSq α k f := by
  simp only [Work.Spaces.HkSq]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  exact congrFun (congrFun (HkIntegrand_neg α k f) z) θ

theorem HkNorm_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm α k (-f) = Work.Spaces.HkNorm α k f := by
  simp only [Work.Spaces.HkNorm, HkSq_neg]

/-! ## The zero function: `HkIntegrand`, `HkMem`, `L2Mem`, `ZDecay` are inhabited -/

theorem pz_zero_fun : Work.Spaces.pz (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ; simp [Work.Spaces.pz]

theorem pth_zero_fun : Work.Spaces.pth (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ; simp [Work.Spaces.pth]

theorem pzIter_zero_fun (n : ℕ) : Work.Spaces.pzIter n (0 : ℝ → ℝ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pzIter_succ, ih, pz_zero_fun]

theorem pthIter_zero_fun (n : ℕ) : Work.Spaces.pthIter n (0 : ℝ → ℝ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pthIter_succ, ih, pth_zero_fun]

theorem Dz_zero_fun : Work.Spaces.Dz (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ; simp [Work.Spaces.Dz, pz_zero_fun]

theorem Dth_zero_fun : Work.Spaces.Dth (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ; simp [Work.Spaces.Dth, pth_zero_fun]

theorem DzIter_zero_fun (n : ℕ) : Work.Spaces.DzIter n (0 : ℝ → ℝ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, ih, Dz_zero_fun]

theorem DthIter_zero_fun (n : ℕ) : Work.Spaces.DthIter n (0 : ℝ → ℝ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, ih, Dth_zero_fun]

theorem mixed_zero_fun (j i : ℕ) : Work.Spaces.mixed j i (0 : ℝ → ℝ → ℝ) = 0 := by
  rw [Work.Spaces.mixed, DthIter_zero_fun, DzIter_zero_fun]

theorem pz_const_zero (z θ : ℝ) : Work.Spaces.pz (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Spaces.pz]

theorem pth_const_zero (z θ : ℝ) : Work.Spaces.pth (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Spaces.pth]

theorem pzIter_const_zero (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter n (fun _ _ => (0 : ℝ)) z θ = 0 := by
  have h : (fun _ _ => (0 : ℝ)) = (0 : ℝ → ℝ → ℝ) := rfl
  rw [h, pzIter_zero_fun n]; rfl

theorem pthIter_const_zero (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pthIter n (fun _ _ => (0 : ℝ)) z θ = 0 := by
  have h : (fun _ _ => (0 : ℝ)) = (0 : ℝ → ℝ → ℝ) := rfl
  rw [h, pthIter_zero_fun n]; rfl

theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (0 : ℝ → ℝ → ℝ) z θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, DzIter_zero_fun, mixed_zero_fun]
  simp

theorem HkSq_zero (α : ℝ) (k : ℕ) : Work.Spaces.HkSq α k (0 : ℝ → ℝ → ℝ) = 0 := by
  rw [Work.Spaces.HkSq]
  have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (0 : ℝ → ℝ → ℝ) z θ) = fun _ => (0 : ℝ) := by
    funext z; simp [HkIntegrand_zero α k z]
  rw [h]; simp

theorem HkNorm_zero (α : ℝ) (k : ℕ) : Work.Spaces.HkNorm α k (0 : ℝ → ℝ → ℝ) = 0 := by
  rw [Work.Spaces.HkNorm, HkSq_zero, Real.sqrt_zero]

theorem HkMem_zero (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k (0 : ℝ → ℝ → ℝ) := by
  constructor
  · intro z hz
    have h : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (0 : ℝ → ℝ → ℝ) z θ)
        = fun _ => (0 : ℝ) := by
      funext θ; exact HkIntegrand_zero α k z θ
    rw [h]; exact integrableOn_zero
  · have h : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (0 : ℝ → ℝ → ℝ) z θ) = fun _ => (0 : ℝ) := by
      funext z; simp [HkIntegrand_zero α k z]
    rw [h]; exact integrableOn_zero





theorem IsBslSol_zero (α : ℝ) :
    Work.Elliptic.IsBslSol α (0 : ℝ → ℝ → ℝ) (0 : ℝ → ℝ → ℝ) := by
  refine ⟨fun z hz θ h0 h1 => ?_, fun z => rfl, fun z => rfl, fun θ hθ => ?_⟩
  · simp [Work.Elliptic.bslOp, Work.Elliptic.Lzero, pz_zero_fun, pth_zero_fun,
      pzIter_zero_fun, pthIter_zero_fun, pz_const_zero, pth_const_zero,
      pzIter_const_zero, pthIter_const_zero, Pi.zero_apply]
  · simp only [Pi.zero_apply]
    exact tendsto_const_nhds

/-- **The class of data of the elliptic a-priori estimates.**

This bundles the hypotheses of Propositions `prop:L2`, `prop:H2`, `prop:Hk` and Theorem
`RemovingL12` of §'Elliptic Regularity Estimates':

* `smooth` and `sol`: `Ψ` is a smooth solution of (PolarBSL) with source `F`, vanishing at
  `θ = 0, π/2` and decaying at `z → ∞` (the paper's class of solutions);
* `memF`: the honesty of the weighted `H^k`-norm of the source, `Work.Spaces.HkMem α k F`;

together with the two formal corrections recorded in the module docstring:

* `zdecay`: the boundary terms of the integration by parts in `z` vanish at infinity;
* the `Work.Spaces.HkMem`/`Work.Spaces.L2Mem` fields: the honesty of the left-hand quantities,
  i.e. that the integrals which the estimates bound are the honest squares of norms rather than
  the junk value `0` of the totalised integral.

The class is inhabited by the zero function: `ellHyp_zero`.

**Re-scope of the `smooth` field (2024, at the lead's direction).**  The field was
`Work.Spaces.SmoothNbhd Ψ`.  In this Mathlib pin `SmoothNbhd Ψ = ContDiffOn ℝ ⊤ (uncurry Ψ) U`
with `⊤ : WithTop ℕ∞` the *analytic* level (`ContDiff ℝ ⊤ f ↔ AnalyticOnNhd ℝ f univ`), so
`EllHyp` was the class of *analytic-on-`U`* solutions; and since `U` is preconnected, any such
datum vanishing on an open subset of `U` is identically zero.  That is fatal for the
"removal-of-hypotheses by cutoff" design (`Mine.CutoffApprox`, `Mine.NOTES_CutoffApproxHolds.md`):
no datum produced by truncating with a `C^∞` cutoff can be `EllHyp`.  The field is therefore the
*non-analytic* smoothness `Work.Spaces.SmoothInt Ψ` (`C^∞` on the open quadrant `(-1,∞) × (0,π/2)`
together with `C^∞` `z`-slices down to `z = 0`) — which is the smoothness the estimates of
§'Elliptic Regularity Estimates' actually use.  Every previously available provider of
`SmoothNbhd Ψ` still yields an `EllHyp` datum through `Work.Spaces.SmoothInt.of_SmoothNbhd`
(`Spaces/WProductRule.lean`); consequently only the *consumers* that passed `h.smooth` into a
lemma whose statement demands `SmoothNbhd` have to be weakened — the checklist of such lemmas is
recorded in `Mine/CutoffPieces/NOTES_SmoothIntRescope.md`. -/
structure EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- `Ψ` is `C^∞` on the open quadrant `(-1,∞) × (0,π/2)` and its `z`-slices are `C^∞` down to
  `z = 0` (`Work.Spaces.SmoothInt`).  (*Not* analyticity: see the note above.) -/
  smooth : Work.Spaces.SmoothInt Ψ
  /-- `Ψ` solves (PolarBSL) with source `F`, with Dirichlet data and decay. -/
  sol : Work.Elliptic.IsBslSol α F Ψ
  /-- The `H^k`-integral of `F` is honest. -/
  memF : Work.Spaces.HkMem α k F
  memPsi : Work.Spaces.HkMem α k Ψ
  memDth : Work.Spaces.HkMem α k (Work.Spaces.pth Ψ)
  memDth2 : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)
  memZ2 : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  memDivCos : Work.Spaces.HkMem α k (fun z θ => Ψ z θ / Real.cos θ)
  l2Dth2 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ)
  l2Z2 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  l2DivCos : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ)
  l2F : Work.Spaces.L2Mem F
  /-- The boundary terms of the integration by parts in `z` vanish at infinity. -/
  zdecay : ZDecay Ψ
  /-- **The closed-quadrant regularity of the certificates.**  `Ψ` is smooth on an open
  neighbourhood of the closed quadrant, `Work.Spaces.SmoothNbhd Ψ`.

  `smooth : SmoothInt Ψ` above constrains the angular slice only on the *open* interval
  `(0, π/2)`, so it does not determine the one-sided limits at `θ → 0⁺`, `θ → (π/2)⁻`.  Two
  independent reviewers exhibited, from `SmoothInt` alone, the failure of the constrained slice
  Poincaré gap `L2Sq_pth_ge_nine` and of the `θ`-energy identity `PropL2Cut.energy1_inf` (see
  `SmoothInt_rescope_blocker.md`, `Final/NOTES_energy1_inf_int_FALSE.md`), and the statement
  "`F_*` is `C^m` on `(0,∞)` for `EllHyp`-data" was refuted
  (`SmoothIntRescope/Fstar_smooth_of_EllHyp_smoothInt`; cf. `Spaces/SmoothStripDefs.lean`).

  This field is the *closed-quadrant* regularity that the hypotheses of the original statements
  of `Work.Elliptic.Estimates` carry (`Work.Spaces.SmoothNbhd Ψ`) and that the level-`0` and
  certificate layers of this chapter need.  It is *not* implied by `smooth`; a datum carrying it
  is `EllHypN`-data (`EllHypN.toEllHyp`), and every provider of `SmoothNbhd`-data supplies both
  fields.  The `smooth` field is kept so that every consumer of the re-scoped (2026) interface
  keeps working. -/
  smoothNbhd : Work.Spaces.SmoothNbhd Ψ
  /-- **The diagonal second-order honesty** of the datum: `HkMem α k (∂_θθ(z∂_zΨ))`, i.e.
  `Work.Spaces.HkMem α k (fun z θ => z * ∂_z∂_θθΨ)`.  This is the conjunct that the weak class
  `TT.EllWeakPos` carries (`AeI1Paper_repair.md`, `TT/WeakDescent.lean`) and that every datum
  fed into the level-`k` estimate `TT.EllEstUnif` must satisfy;
  `TT.ellWeakPos_of_hyps` consumes it as its last argument.  It is *not* implied by the other
  fields (`H2W/AeWAux/NOTES_aeI1Data_FALSE.md`), so it is carried here. -/
  memZPth2 : Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)


/-! ## The closed-quadrant-regular twin `EllHypN` of the hypothesis bundle

The `smooth` field of `EllHyp` is `Work.Spaces.SmoothInt Ψ`: `C^∞` on the *open* quadrant
together with `C^∞` `z`-slices.  That class is strictly weaker than the one the estimates of
`prop:L2` are stated for, and *strictly weaker than what the level-`0` estimates need*:
`SmoothInt` constrains the angular slice only on `(0, π/2)`, so the conditions `Ψ z 0 = 0`,
`Ψ z (π/2) = 0` are conditions on a null set and do not control the one-sided limits of the slice
at `θ → 0⁺` and `θ → (π/2)⁻`.  Two independent reviewers exhibited, from `SmoothInt` alone, the
failure of the constrained slice Poincaré gap `L2Sq_pth_ge_nine` and of the `θ`-energy identity
`PropL2Cut.energy1_inf` (see `SmoothInt_rescope_blocker.md` and
`Final/NOTES_energy1_inf_int_FALSE.md`), and a third refuted the resulting smoothness of the
angular moment `F_*` (`Spaces/SmoothStripDefs.lean`).  The honest classes carrying the angular
traces are

* `Work.Spaces.SmoothStrip` — `C^∞` (*not* analytic) on the open neighbourhood
  `(-1,∞) × (-1, π/2+1)` of the closed quadrant, so it admits cutoff data *and* determines the
  traces; and
* `Work.Spaces.SmoothNbhd` — analytic on that neighbourhood, the class in which the *original*
  statements of `Work.Elliptic.Estimates` are phrased.

`EllHypN` is the twin of `EllHyp` in the `SmoothNbhd` class: the same twelve hypothesis fields
with `smooth : Work.Spaces.SmoothNbhd Ψ`.  It is the class in which the level-`0` cluster
(`propL2_fts`, `PropL2Cut.energy1_inf`, `energy2_aux`, `z2_pz2_int_dev`, `L2Mem_zpz_aux`,
`L2Mem_pthDiv_aux`, `HkMem_zero_imp_L2Mem`) is *proved*, so a target restated on `EllHypN` is
provable without touching the auxiliary development.  Every provider of `SmoothNbhd`-data feeds
it, and `EllHypN → EllHyp` (`SmoothNbhd ⊆ SmoothInt`), so it can be used wherever `EllHyp` is. -/
structure EllHypN (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- `Ψ` is smooth on an open neighbourhood of the closed quadrant: `Work.Spaces.SmoothNbhd Ψ`.
  This is the class in which the original statements are phrased and in which the level-`0`
  cluster is proved. -/
  smooth : Work.Spaces.SmoothNbhd Ψ
  /-- `Ψ` solves (PolarBSL) with source `F`, with Dirichlet data and decay. -/
  sol : Work.Elliptic.IsBslSol α F Ψ
  /-- The `H^k`-integral of `F` is honest. -/
  memF : Work.Spaces.HkMem α k F
  memPsi : Work.Spaces.HkMem α k Ψ
  memDth : Work.Spaces.HkMem α k (Work.Spaces.pth Ψ)
  memDth2 : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)
  memZ2 : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  memDivCos : Work.Spaces.HkMem α k (fun z θ => Ψ z θ / Real.cos θ)
  l2Dth2 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ)
  l2Z2 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  l2DivCos : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ)
  l2F : Work.Spaces.L2Mem F
  /-- The boundary terms of the integration by parts in `z` vanish at infinity. -/
  zdecay : ZDecay Ψ
  /-- The diagonal second-order honesty `HkMem α k (∂_θθ(z∂_zΨ))`; see the corresponding field
  of `EllHyp`. -/
  memZPth2 : Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)




end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgm.ContinuousOnUncurryPzIterTwo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.DzAmgm

open scoped Real Topology
open MeasureTheory Set Filter



end Work.FTS.EllipticEst.DzAmgm
end
-- ===== merged: Submission.Work.FTS.EllipticEst.EllGap.MLevelBookkeeping.mLevel_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.EllGap.MLevelBookkeeping

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Finite-order smoothness of the first partial derivatives

The hypothesis of the main theorem is only *finite-order* smoothness of `G`
(`∀ n : ℕ, ContDiffOn ℝ n …`), so the `⊤`-order calculus of `Work.Spaces.CurrySmooth`
does not apply.  The two lemmas below are the finite-order analogues, for an arbitrary
open set `V`. -/

/-- `∂_z` lowers finite order by one on an open set. -/
theorem contDiffOn_uncurry_pz_of_isOpen {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain




/-! ## Differentiation under the integral sign over a compact interval -/


/-! ## The main statement -/


end

end Work.FTS.EllipticEst.EllGap.MLevelBookkeeping
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.thFluxHasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology

/-- `∂_z` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pz_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hne : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by simp
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn hne).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `∂_θ` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pth_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hne : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by simp
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn hne).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The angular slice of `∂_z G` is differentiable, with derivative the corresponding
mixed partial `∂_θ ∂_z G`. -/
theorem hasDerivAt_pz_slice {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz G)) (z, θ)) :
    HasDerivAt (fun θ' => Work.Spaces.pz G z θ') (Work.Spaces.pth (Work.Spaces.pz G) z θ) θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  have hh := h.hasFDerivAt.comp_hasDerivAt θ hcurve
  rw [← Work.Spaces.pth_eq_fderiv h] at hh
  simpa only [Function.comp_def, Function.uncurry] using hh


end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.H2.T2Easy.L2Mem_prod_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T2Easy

open MeasureTheory Set Filter


end Work.FTS.H2.T2Easy
end
-- ===== merged: Submission.Work.FTS.H2.T2HardAux =====
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

/-! ## Angular factors commute with `D_z` -/


/-! ## The angular vanishing of the mixed derivatives -/



/-! ## Bounds for the angular slices -/


/-! ## The five weights and the five summands of `Hhard` -/

/-- `Thard g k` is `mixed (4 - k) k g`, uniformly in `k : Fin 5`. -/
theorem Thard_eq_mixed (g : ℝ → ℝ → ℝ) (k : Fin 5) :
    Thard g k = fun z θ => Spaces.mixed (4 - k.val) k.val g z θ := by
  fin_cases k <;> rfl



end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.DzIterCpt.DzIter_contDiff_of_forall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `D_z^j` preserves smoothness (finite order, global)

`D_z = z ∂_z` is a first-order differential operator with `C^∞` coefficients, hence it lowers
the differentiability order by exactly one: if `G` is `C^{n+1}` on all of `ℝ²`, then
`D_z G` is `C^n`.  Iterating, `D_z^j G` is `C^{n-j}` — and in particular, if `G` is `C^n` for
every `n`, so is `D_z^j G` for every `j`.  That is the statement proved here.

The single-order step is the standard `fderiv` argument: on `ℝ²` the partial derivative
`∂_z` is the Fréchet derivative in the direction `(1,0)` (`Work.Spaces.pz_eq_fderiv`), the
Fréchet derivative of a `C^{n+1}` map is `C^n` (`ContDiff.fderiv_right`), and multiplication
by the `C^∞` coefficient `z` preserves the order.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty.DzIterCpt

/-- `∂_z` lowers the differentiability order by one (global version). -/
private theorem contDiff_uncurry_pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G)) :
    ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) := by
  have hfd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry G)) := by
    have hh := h.fderiv_right (m := (n : WithTop ℕ∞)) (by simp)
    simpa using hh
  have hcomp : ContDiff ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) :=
    hfd.clm_apply contDiff_const
  have hfun : Function.uncurry (Work.Spaces.pz G)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0) := by
    funext p
    obtain ⟨z, θ⟩ := p
    exact Work.Spaces.pz_eq_fderiv ((h.differentiable (by norm_num)).differentiableAt)
  rw [hfun]
  exact hcomp

/-- `D_z = z ∂_z` lowers the differentiability order by one (global version). -/
private theorem contDiff_uncurry_Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G)) :
    ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dz G)) := by
  have hpz := contDiff_uncurry_pz_fin h
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  rw [hfun]
  exact contDiff_fst.mul hpz

/-- `D_z^j` lowers the differentiability order by `j` (global version). -/
private theorem contDiff_uncurry_DzIter_shift {G : ℝ → ℝ → ℝ} :
    ∀ (j n : ℕ), ContDiff ℝ ((n + j : ℕ) : WithTop ℕ∞) (Function.uncurry G) →
      ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DzIter j G)) := by
  intro j
  induction j with
  | zero => intro n h; simpa using h
  | succ j ih =>
      intro n h
      have h' : ContDiff ℝ ((n + 1 + j : ℕ) : WithTop ℕ∞) (Function.uncurry G) := by
        rw [show n + 1 + j = n + (j + 1) from by omega]; exact h
      exact contDiff_uncurry_Dz_fin (ih (n + 1) h')

/-- **`D_z^j` preserves `C^n`-for-all-`n`.**  If `G` is of class `C^n` on `ℝ²` for every `n`,
then so is `D_z^j G`. -/
theorem DzIter_contDiff_of_forall {G : ℝ → ℝ → ℝ}
    (hG : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry G)) (j : ℕ) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (Work.Spaces.DzIter j G)) := by
  intro n
  exact contDiff_uncurry_DzIter_shift j n (hG (n + j))

end Work.FTS.PhiStar.Honesty.DzIterCpt
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.clmPairAPI =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- The canonical linear isomorphism `ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)`,
`(a,b) ↦ ((x,y) ↦ a * x + b * y)`, packaged as a continuous linear map. -/
def clmPair : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ))
    + ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem clmPair_apply (a b x y : ℝ) : clmPair (a, b) (x, y) = a * x + b * y := by
  simp only [clmPair, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  show x * a + y * b = a * x + b * y
  ring

@[simp] theorem clmPair_fst (a b : ℝ) : clmPair (a, b) (1, 0) = a := by
  rw [clmPair_apply]; ring

@[simp] theorem clmPair_snd (a b : ℝ) : clmPair (a, b) (0, 1) = b := by
  rw [clmPair_apply]; ring

/-- Two continuous linear functionals on `ℝ × ℝ` that agree on the two basis vectors agree. -/
theorem clm_eq_of_fst_snd {L M : (ℝ × ℝ) →L[ℝ] ℝ} (h1 : L (1, 0) = M (1, 0))
    (h2 : L (0, 1) = M (0, 1)) : L = M := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    ext <;> simp
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, h2]

/-- **The Fréchet derivative of an uncurried two-variable function** is the pair of its
partial derivatives. -/
theorem fderiv_uncurry_eq_clmPair {u : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry u) p) :
    fderiv ℝ (Function.uncurry u) p
      = clmPair (Work.Spaces.pz u p.1 p.2, Work.Spaces.pth u p.1 p.2) := by
  refine clm_eq_of_fst_snd ?_ ?_
  · rw [clmPair_fst]
    exact (Work.Spaces.pz_eq_fderiv h).symm
  · rw [clmPair_snd]
    exact (Work.Spaces.pth_eq_fderiv h).symm

/-- Locally uniform convergence passes through the continuous linear map `clmPair`. -/
theorem tendstoLocallyUniformlyOn_clmPair {A B : ℕ → ℝ × ℝ → ℝ} {a b : ℝ × ℝ → ℝ}
    {s : Set (ℝ × ℝ)}
    (hA : TendstoLocallyUniformlyOn A a Filter.atTop s)
    (hB : TendstoLocallyUniformlyOn B b Filter.atTop s) :
    TendstoLocallyUniformlyOn (fun n p => clmPair (A n p, B n p))
      (fun p => clmPair (a p, b p)) Filter.atTop s :=
  (ContinuousLinearMap.uniformContinuous clmPair).comp_tendstoLocallyUniformlyOn
    (hA.prodMk hB)

/-- A constant sequence converges locally uniformly to its value. -/
theorem tlu_const {α β : Type*} [TopologicalSpace α] [UniformSpace β] (g : α → β)
    (s : Set α) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => g) g Filter.atTop s := by
  intro u hu x _
  exact ⟨Set.univ, Filter.univ_mem,
    Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩

end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.VelLipAux.lipschitz_pair_of_deriv_bounds_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS_RegExport.RXR7.VelLipAux

/-- **Two-variable Lipschitz bound from first partial-derivative bounds, with an explicit
constant.**  Let `Fz`, `Fθ` be functions of `(z,θ)` whose one-variable slices are differentiable
on the half-strip `(Lz,∞) × (0,π/2)`, with the four partial derivatives bounded there by `Mz`,
`Mθ`, `Nz`, `Nθ` respectively.  If `Mz + Mθ + Nz + Nθ ≤ K`, then the map
`p ↦ (Fz p.1 p.2, Fθ p.1 p.2)` into `ℝ × ℝ` (with the product/max norm) is `K`-Lipschitz on the
convex half-strip.

This is the same estimate as `lipschitz_pair_of_deriv_bounds` but with the constant exposed
(the consumer needs a `τ`-uniform constant and so cannot use an unspecified `∃ K`).

Proof: the two-step mean value inequality on the convex factors `Ioi Lz` and `Ioo 0 (π/2)`
(`Convex.norm_image_sub_le_of_norm_deriv_le` in the `θ`-direction with the `z` coordinate fixed,
then in the `z`-direction); add the two increments, use `|a|, |b| ≤ ‖(a,b)‖` (`Prod.norm_def`)
and `‖(z,θ)‖ = max |z| |θ|`, and finish with the hypothesis `hK` and
`lipschitzOnWith_iff_norm_sub_le`. -/
theorem lipschitz_pair_of_deriv_bounds_le {Fz Fθ : ℝ → ℝ → ℝ} {Lz Mz Mθ Nz Nθ : ℝ} {K : NNReal}
    (hLz : 0 < Lz) (hMz : 0 ≤ Mz) (hMθ : 0 ≤ Mθ) (hNz : 0 ≤ Nz) (hNθ : 0 ≤ Nθ)
    (hK : Mz + Mθ + Nz + Nθ ≤ (K : ℝ))
    (hdFz : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Fz z' θ) z ∧ DifferentiableAt ℝ (fun θ' => Fz z θ') θ)
    (hdFθ : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Fθ z' θ) z ∧ DifferentiableAt ℝ (fun θ' => Fθ z θ') θ)
    (h1 : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 → |deriv (fun z' => Fz z' θ) z| ≤ Mz)
    (h2 : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 → |deriv (fun θ' => Fz z θ') θ| ≤ Mθ)
    (h3 : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 → |deriv (fun z' => Fθ z' θ) z| ≤ Nz)
    (h4 : ∀ z θ : ℝ, Lz < z → 0 < θ → θ < π / 2 → |deriv (fun θ' => Fθ z θ') θ| ≤ Nθ) :
    LipschitzOnWith K (fun p : ℝ × ℝ => (Fz p.1 p.2, Fθ p.1 p.2))
      (Set.prod (Set.Ioi Lz) (Set.Ioo 0 (Real.pi / 2))) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro p hp q hq
  change p.1 ∈ Set.Ioi Lz ∧ p.2 ∈ Set.Ioo 0 (π / 2) at hp
  change q.1 ∈ Set.Ioi Lz ∧ q.2 ∈ Set.Ioo 0 (π / 2) at hq
  -- coordinate comparisons with `dist p q`
  have hd1 : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_right _ _
  -- `z`-increment of `Fz` at fixed `θ = p.2`
  have hA : |Fz p.1 p.2 - Fz q.1 p.2| ≤ Mz * |p.1 - q.1| := by
    have hdiff : ∀ w ∈ Set.Ioi Lz, DifferentiableAt ℝ (fun z' => Fz z' p.2) w :=
      fun w hw => (hdFz w p.2 hw hp.2.1 hp.2.2).1
    have hb : ∀ w ∈ Set.Ioi Lz, ‖deriv (fun z' => Fz z' p.2) w‖ ≤ Mz :=
      fun w hw => by rw [Real.norm_eq_abs]; exact h1 w p.2 hw hp.2.1 hp.2.2
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_Ioi Lz) hp.1 hq.1
    calc |Fz p.1 p.2 - Fz q.1 p.2| = ‖Fz q.1 p.2 - Fz p.1 p.2‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Mz * ‖q.1 - p.1‖ := h
      _ = Mz * |p.1 - q.1| := by rw [Real.norm_eq_abs, abs_sub_comm]
  -- `θ`-increment of `Fz` at fixed `z = q.1`
  have hB : |Fz q.1 p.2 - Fz q.1 q.2| ≤ Mθ * |p.2 - q.2| := by
    have hdiff : ∀ w ∈ Set.Ioo (0 : ℝ) (π / 2),
        DifferentiableAt ℝ (fun θ' => Fz q.1 θ') w :=
      fun w hw => (hdFz q.1 w hq.1 hw.1 hw.2).2
    have hb : ∀ w ∈ Set.Ioo (0 : ℝ) (π / 2),
        ‖deriv (fun θ' => Fz q.1 θ') w‖ ≤ Mθ :=
      fun w hw => by rw [Real.norm_eq_abs]; exact h2 q.1 w hq.1 hw.1 hw.2
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb
      (convex_Ioo 0 (π / 2)) hp.2 hq.2
    calc |Fz q.1 p.2 - Fz q.1 q.2| = ‖Fz q.1 q.2 - Fz q.1 p.2‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Mθ * ‖q.2 - p.2‖ := h
      _ = Mθ * |p.2 - q.2| := by rw [Real.norm_eq_abs, abs_sub_comm]
  -- `z`-increment of `Fθ` at fixed `θ = p.2`
  have hC : |Fθ p.1 p.2 - Fθ q.1 p.2| ≤ Nz * |p.1 - q.1| := by
    have hdiff : ∀ w ∈ Set.Ioi Lz, DifferentiableAt ℝ (fun z' => Fθ z' p.2) w :=
      fun w hw => (hdFθ w p.2 hw hp.2.1 hp.2.2).1
    have hb : ∀ w ∈ Set.Ioi Lz, ‖deriv (fun z' => Fθ z' p.2) w‖ ≤ Nz :=
      fun w hw => by rw [Real.norm_eq_abs]; exact h3 w p.2 hw hp.2.1 hp.2.2
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_Ioi Lz) hp.1 hq.1
    calc |Fθ p.1 p.2 - Fθ q.1 p.2| = ‖Fθ q.1 p.2 - Fθ p.1 p.2‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Nz * ‖q.1 - p.1‖ := h
      _ = Nz * |p.1 - q.1| := by rw [Real.norm_eq_abs, abs_sub_comm]
  -- `θ`-increment of `Fθ` at fixed `z = q.1`
  have hD : |Fθ q.1 p.2 - Fθ q.1 q.2| ≤ Nθ * |p.2 - q.2| := by
    have hdiff : ∀ w ∈ Set.Ioo (0 : ℝ) (π / 2),
        DifferentiableAt ℝ (fun θ' => Fθ q.1 θ') w :=
      fun w hw => (hdFθ q.1 w hq.1 hw.1 hw.2).2
    have hb : ∀ w ∈ Set.Ioo (0 : ℝ) (π / 2),
        ‖deriv (fun θ' => Fθ q.1 θ') w‖ ≤ Nθ :=
      fun w hw => by rw [Real.norm_eq_abs]; exact h4 q.1 w hq.1 hw.1 hw.2
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb
      (convex_Ioo 0 (π / 2)) hp.2 hq.2
    calc |Fθ q.1 p.2 - Fθ q.1 q.2| = ‖Fθ q.1 q.2 - Fθ q.1 p.2‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Nθ * ‖q.2 - p.2‖ := h
      _ = Nθ * |p.2 - q.2| := by rw [Real.norm_eq_abs, abs_sub_comm]
  have hFz : |Fz p.1 p.2 - Fz q.1 q.2| ≤ (Mz + Mθ + Nz + Nθ) * dist p q := by
    calc |Fz p.1 p.2 - Fz q.1 q.2|
        = |(Fz p.1 p.2 - Fz q.1 p.2) + (Fz q.1 p.2 - Fz q.1 q.2)| := by congr 1; ring
      _ ≤ |Fz p.1 p.2 - Fz q.1 p.2| + |Fz q.1 p.2 - Fz q.1 q.2| := abs_add_le _ _
      _ ≤ Mz * |p.1 - q.1| + Mθ * |p.2 - q.2| := add_le_add hA hB
      _ ≤ Mz * dist p q + Mθ * dist p q :=
            add_le_add (mul_le_mul_of_nonneg_left hd1 hMz) (mul_le_mul_of_nonneg_left hd2 hMθ)
      _ ≤ (Mz + Mθ + Nz + Nθ) * dist p q := by
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  have hFθ : |Fθ p.1 p.2 - Fθ q.1 q.2| ≤ (Mz + Mθ + Nz + Nθ) * dist p q := by
    calc |Fθ p.1 p.2 - Fθ q.1 q.2|
        = |(Fθ p.1 p.2 - Fθ q.1 p.2) + (Fθ q.1 p.2 - Fθ q.1 q.2)| := by congr 1; ring
      _ ≤ |Fθ p.1 p.2 - Fθ q.1 p.2| + |Fθ q.1 p.2 - Fθ q.1 q.2| := abs_add_le _ _
      _ ≤ Nz * |p.1 - q.1| + Nθ * |p.2 - q.2| := add_le_add hC hD
      _ ≤ Nz * dist p q + Nθ * dist p q :=
            add_le_add (mul_le_mul_of_nonneg_left hd1 hNz) (mul_le_mul_of_nonneg_left hd2 hNθ)
      _ ≤ (Mz + Mθ + Nz + Nθ) * dist p q := by
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  -- replace the explicit sum of the four bounds by the hypothesis constant `K`
  have hFz' : |Fz p.1 p.2 - Fz q.1 q.2| ≤ (K : ℝ) * dist p q :=
    le_trans hFz (mul_le_mul_of_nonneg_right hK dist_nonneg)
  have hFθ' : |Fθ p.1 p.2 - Fθ q.1 q.2| ≤ (K : ℝ) * dist p q :=
    le_trans hFθ (mul_le_mul_of_nonneg_right hK dist_nonneg)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le hFz' hFθ'

end Work.FTS_RegExport.RXR7.VelLipAux
end
-- ===== merged: Submission.Work.Spaces.BoxBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Auxiliary calculus lemmas in the angular direction -/



/-! ## Auxiliary calculus lemmas in the radial direction -/






/-! ## The two box bounds -/



end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.DzDthIterCommOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-! ## Congruence of `pth` on an open set -/

/-- Functions that agree on an open set containing `(z,θ)` have the same `θ`-slice
derivative at `(z,θ)`. -/
lemma pth_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    pth f z θ = pth f' z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (Continuous.prodMk_right z).continuousAt.eventually (hV.mem_nhds hz)
  have hslice : (fun θ' => Function.uncurry f (z, θ')) =ᶠ[𝓝 θ]
      (fun θ' => Function.uncurry f' (z, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  simpa only [pth, Function.uncurry] using hslice.deriv_eq

/-- Functions that agree on an open set containing `(z,θ)` have the same `z`-slice
derivative at `(z,θ)`. -/
lemma pz_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    pz f z θ = pz f' z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hz)
  have hslice : (fun z' => Function.uncurry f (z', θ)) =ᶠ[𝓝 z]
      (fun z' => Function.uncurry f' (z', θ)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  simpa only [pz, Function.uncurry] using hslice.deriv_eq

/-! ## The commutation identity -/


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.DzIterSmoothOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

set_option autoImplicit false

/-- The differential operator `D_z g = z · ∂_z g` maps functions smooth on an open set
`V` to functions smooth on `V`.  Indeed, after currying,
`Function.uncurry (Dz g) p = p.1 * Function.uncurry (pz g) p` is the product of the
smooth projection `p ↦ p.1` with the curried `z`-partial, which is smooth by
`contDiffOn_uncurry_pz`. -/
theorem contDiffOn_uncurry_Dz {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry g) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Dz g)) V := by
  have hpz : ContDiffOn ℝ ⊤ (Function.uncurry (pz g)) V := contDiffOn_uncurry_pz hV h
  have hz : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1) V := contDiffOn_fst
  have hmul : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 * Function.uncurry (pz g) p) V :=
    hz.mul hpz
  refine hmul.congr ?_
  intro p hp
  rfl

/-- Iterating `D_z` preserves smoothness on an open set: the map
`(z,θ) ↦ D_z^j f (z,θ)` is `C^∞` on `V` whenever `f` is. -/
theorem DzIterSmoothOn {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (j : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j f)) V := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
      have hstep : ContDiffOn ℝ ⊤ (Function.uncurry (Dz (DzIter j f))) V :=
        contDiffOn_uncurry_Dz hV ih
      simpa using hstep

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.PairIntegralLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open MeasureTheory Set Filter

/-! ## Two tools for the totalised integral, and the slice AM–GM bound -/

/-- Two-case monotonicity of the (totalised) Bochner integral: if `g` is integrable and
nonnegative a.e. and `f ≤ g` a.e., then `∫ f ≤ ∫ g`.

If `f` is not integrable its Bochner integral is `0` (`integral_undef`), so the bound is
`0 ≤ ∫ g`, which holds because `g ≥ 0` a.e. (`integral_nonneg_of_ae`); otherwise the usual
`integral_mono_ae` applies.  This is exactly the step needed when the integrand carries no
measurability hypothesis. -/
theorem integral_le_integral_of_ae_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hgi : Integrable g μ) (hg : 0 ≤ᵐ[μ] g) (h : f ≤ᵐ[μ] g) :
    ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ := by
  by_cases hfi : Integrable f μ
  · exact integral_mono_ae hfi hgi h
  · rw [integral_undef hfi]
    exact integral_nonneg_of_ae hg

/-- The arithmetic–geometric mean inequality `|a| · |b| ≤ (a² + b²)/2`. -/
theorem abs_mul_abs_le_half_add_sq (a b : ℝ) : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]



end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.twoOp_iterate_mul_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces


end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.uncurry_partial_c1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

theorem uncurry_partial_c1 {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ 2 (Function.uncurry G) V) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) V ∧
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth G)) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (n := 2) (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ 1 (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := 1) hV.uniqueDiffOn (by norm_num)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hfd1 : ContDiffOn ℝ 1
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  have hfd2 : ContDiffOn ℝ 1
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  refine ⟨?_, ?_⟩
  · refine hfd1.congr ?_
    intro p hp
    exact pz_eq_fderiv (hdiff p hp)
  · refine hfd2.congr ?_
    intro p hp
    exact pth_eq_fderiv (hdiff p hp)

end Work.Spaces
end
