import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

/-- The transported weight `α exp (5 s) cos θ` (this is `α z · z^((5-α)/α) cos θ` with
`z = exp (α s)`, i.e. the Jacobian `α exp (α s)` times the weight `z^((5-α)/α) cos θ`). -/
def wt (α : ℝ) : E2 → ℝ := fun x => α * Real.exp (5 * x 0) * Real.cos (x 1)

/-- The transported unknown `V = wt α · Ψ ∘ chart`, zero off the strip. -/
def Vf (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : E2 → ℝ :=
  stripE.indicator (fun x => wt α x * Ψ (Real.exp (α * x 0)) (x 1))

/-- The transported source `G = wt α · F ∘ chart`, zero off the strip. -/
def Gf (α : ℝ) (F : ℝ → ℝ → ℝ) : E2 → ℝ :=
  stripE.indicator (fun x => wt α x * F (Real.exp (α * x 0)) (x 1))

/-- **The weak identity on the strip**, complex form: for every smooth compactly supported test
function with topological support in the strip, `∫ V · Kop ψ = ∫ G · ψ`. -/
def StripWeakC (V G : E2 → ℂ) : Prop :=
  ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
    tsupport ψ ⊆ stripE →
    ∫ x, V x * Kop ψ x = ∫ x, G x * ψ x

/-- **The weak identity on the strip**, for the transported pair `(V, G)` of real-valued
functions. -/
def StripWeakQ0 (α : ℝ) (V G : E2 → ℝ) : Prop :=
  StripWeakC (fun x => (V x : ℂ)) (fun x => (G x : ℂ))




/-- The transported weight as an explicit function of the strip coordinates. -/
theorem wt_apply (α : ℝ) (x : E2) :
    wt α x = α * Real.exp (5 * x 0) * Real.cos (x 1) := rfl

theorem wt_contDiff (α : ℝ) : ∀ n : ℕ, ContDiff ℝ n (wt α) := by
  intro n
  unfold wt
  fun_prop


/-- The weight is positive on the strip. -/
theorem wt_pos {α : ℝ} (hα : 0 < α) {x : E2} (hx : x ∈ stripE) : 0 < wt α x := by
  rw [wt_apply]
  have h1 : 0 < Real.exp (5 * x 0) := Real.exp_pos _
  have h2 : 0 < Real.cos (x 1) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
  positivity

/-- The weight is nonzero on the strip. -/
theorem wt_ne_zero {α : ℝ} (hα : 0 < α) {x : E2} (hx : x ∈ stripE) : wt α x ≠ 0 :=
  ne_of_gt (wt_pos hα hx)

/-! ## Pairing predicates for the localized equation

The Sobolev tower works with the distributions `A = χ · U` (the localized unknown) and needs to
know that they pair against Schwartz functions as integrals of `χ · V`.  The two predicates
below record exactly that; they decouple the `L¹`/local-integrability bookkeeping (proved once,
from `U = distr (ρ · V)`) from the algebra of the localized equation. -/

/-- `Pair V χ A` says that the tempered distribution `A` pairs with Schwartz functions as the
integral of `ψ · (χ · V)`. -/
def Pair (V : E2 → ℂ) (χ : E2 → ℂ) (A : TemperedDistribution E2 ℂ) : Prop :=
  ∀ ψ : SchwartzMap E2 ℂ, A ψ = ∫ x, ψ x • (χ x * V x)

/-- **The localized integral identity** (the pairing form of the localized equation): this is
the identity proved by `Q0.localEq` from the weak formulation, transported to the level of the
concrete cut-offs.  It is stated separately so that the distributional algebra
(`Q0.distEq`) does not have to depend on the weak formulation. -/
def LocalId (V G : E2 → ℂ) (χ χ' σc tt : E2 → ℂ) : Prop :=
  ∀ φ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
    (∫ x, (χ x * (d0 (d0 φ) x + d1 (d1 φ) x)) * V x)
      = - (∫ x, (χ x * d0 (fun y => (5 * σc y) * φ y) x) * V x)
        + (∫ x, (χ x * d1 (fun y => (σc y * tt y) * φ y) x) * V x)
        - (∫ x, (χ x * (6 * σc x) * φ x) * V x)
        + (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φ x)) * V x)
        - (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φ y) x) * V x)
        - (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φ y) x) * V x)
        - (∫ x, (χ x * φ x) * G x)

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false

/-- The un-indicated pull-back of the unknown `Ψ · ω` to the strip coordinates:
`Ws α Ψ x = wt α x * Ψ (exp (α x₀)) x₁`. -/
def Ws (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : E2 → ℂ :=
  fun x => ((wt α x * Ψ (Real.exp (α * x 0)) (x 1) : ℝ) : ℂ)

/-- The complex unknown of the strip problem, zero off the strip: `Vc α Ψ`. -/
def Vc (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : E2 → ℂ := stripE.indicator (Ws α Ψ)

/-- The un-indicated pull-back of the source `F · ω` to the strip coordinates. -/
def Gs (α : ℝ) (F : ℝ → ℝ → ℝ) : E2 → ℂ :=
  fun x => ((wt α x * F (Real.exp (α * x 0)) (x 1) : ℝ) : ℂ)

/-- The complex source of the strip problem, zero off the strip: `Gc α F`. -/
def Gc (α : ℝ) (F : ℝ → ℝ → ℝ) : E2 → ℂ := stripE.indicator (Gs α F)

/-- The scaled bump function with `rIn = ρ`, `rOut = 2ρ` centred at `x₀`. -/
def cdb (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump x₀ :=
  ⟨ρ, 2 * ρ, hρ, by linarith⟩

/-- The complex-valued version of the scaled bump `cdb x₀ ρ hρ`. -/
def cfun (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) : E2 → ℂ :=
  fun x => (((cdb x₀ ρ hρ) x : ℝ) : ℂ)

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.cosNeZeroOfEqTanOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.VT

open Work.EllipticEst.InteriorRegularity

/-- If a smooth function `tt : E2 → ℂ` agrees with `θ ↦ tan θ` on an open set `U`,
then the cosine of the second coordinate cannot vanish on `U`.

Proof: the `ℂ`-valued function `y ↦ tt y * cos (y 1) - sin (y 1)` is continuous and
vanishes on `U ∩ {cos ≠ 0}`, a set whose closure contains `U`; hence it vanishes at every
point of `U` as well.  At a point of `U` with `cos (x 1) = 0` this would force
`sin (x 1) = 0`, contradicting `sin² + cos² = 1`. -/
theorem cosNeZeroOfEqTanOn {U : Set Work.EllipticEst.InteriorRegularity.E2}
    {tt : Work.EllipticEst.InteriorRegularity.E2 → ℂ} (hU : IsOpen U)
    (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ)) :
    ∀ x ∈ U, Real.cos (x 1) ≠ 0 := by
  intro x hx hcos
  -- where the cosine vanishes the sine is `±1`
  have hsin : Real.sin (x 1) ≠ 0 := by
    rcases Real.cos_eq_zero_iff_sin_eq.mp hcos with h | h <;> rw [h] <;> norm_num
  -- the second basis vector has norm one
  have he1norm : ‖(e1 : E2)‖ = 1 := by
    simp [e1, EuclideanSpace.basisFun_apply]
  -- points of `U` with nonvanishing cosine accumulate at `x`
  have hxcl : x ∈ closure (U ∩ {z : E2 | Real.cos (z 1) ≠ 0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases Metric.isOpen_iff.mp hU x hx with ⟨ρ, hρpos, hρsub⟩
    set h : ℝ := min (min ε ρ) (Real.pi / 2) / 2 with hh
    have hpos : 0 < h := by
      rw [hh]
      have h1 : 0 < min (min ε ρ) (Real.pi / 2) :=
        lt_min (lt_min hε hρpos) (by linarith [Real.pi_pos])
      linarith
    have hltε : h < ε := by
      rw [hh]
      have h1 : min (min ε ρ) (Real.pi / 2) ≤ ε :=
        (min_le_left (min ε ρ) (Real.pi / 2)).trans (min_le_left ε ρ)
      linarith
    have hltρ : h < ρ := by
      rw [hh]
      have h1 : min (min ε ρ) (Real.pi / 2) ≤ ρ :=
        (min_le_left (min ε ρ) (Real.pi / 2)).trans (min_le_right ε ρ)
      linarith
    have hltπ : h < Real.pi := by
      rw [hh]
      have h1 : min (min ε ρ) (Real.pi / 2) ≤ Real.pi / 2 :=
        min_le_right (min ε ρ) (Real.pi / 2)
      linarith [Real.pi_pos]
    have hcoord : (x + h • e1) 1 = x 1 + h := by
      simp [e1, EuclideanSpace.basisFun_apply]
    have hsub : x + h • e1 - x = h • e1 := by abel
    have hdistL : dist (x + h • e1) x = h := by
      rw [dist_eq_norm, hsub, norm_smul, he1norm, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
    have hdistR : dist x (x + h • e1) = h := by rw [dist_comm, hdistL]
    refine ⟨x + h • e1, ⟨?_, ?_⟩, ?_⟩
    · exact hρsub (Metric.mem_ball.mpr (by rw [hdistL]; exact hltρ))
    · rw [Set.mem_setOf_eq]
      rw [hcoord]
      rw [Real.cos_add]
      rw [hcos, zero_mul, zero_sub]
      intro hcontra
      exact (mul_ne_zero hsin (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hltπ)))
        (neg_eq_zero.mp hcontra)
    · rw [hdistR]; exact hltε
  -- the auxiliary continuous function
  have hFcont : Continuous (fun y : E2 =>
      tt y * (Real.cos (y 1) : ℂ) - (Real.sin (y 1) : ℂ)) := by
    have h1 : Continuous fun y : E2 => y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    have h2 : Continuous fun y : E2 => (Real.cos (y 1) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp h1)
    have h3 : Continuous fun y : E2 => (Real.sin (y 1) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_sin.comp h1)
    exact ((htts 0).continuous.mul h2).sub h3
  -- it vanishes on `U ∩ {cos ≠ 0}`
  have hF0 : ∀ y ∈ U ∩ {z : E2 | Real.cos (z 1) ≠ 0},
      tt y * (Real.cos (y 1) : ℂ) - (Real.sin (y 1) : ℂ) = 0 := by
    rintro y ⟨hyU, hyc⟩
    have hkey : (Real.tan (y 1) : ℂ) * (Real.cos (y 1) : ℂ) = (Real.sin (y 1) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hyc]
    rw [htt1 y hyU, hkey, sub_self]
  -- hence it vanishes on `U`
  have hFx : tt x * (Real.cos (x 1) : ℂ) - (Real.sin (x 1) : ℂ) = 0 :=
    closure_minimal hF0 (isClosed_eq hFcont continuous_const) hxcl
  -- which is impossible when `cos (x 1) = 0`
  have hs0 : (Real.sin (x 1) : ℂ) = 0 := by
    have h := hFx
    rw [hcos] at h
    simpa only [Complex.ofReal_zero, mul_zero, zero_sub, neg_eq_zero] using h
  exact hsin (Complex.ofReal_eq_zero.mp hs0)

end Work.EllipticEst.InteriorRegularity.VT
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.bslOp_comp_exp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter

namespace Work.EllipticEst.InteriorRegularity

/-- **First-order chain rule for a logarithm-composition.**  For `z ≠ 0` and `φ`
differentiable at `(1/α) log z`,
`d/dz [φ ((1/α) log z)] = φ'((1/α) log z) · 1/(α z)`. -/
lemma deriv_comp_const_mul_log (φ : ℝ → ℝ) {α z : ℝ} (hz : z ≠ 0)
    (hφ : DifferentiableAt ℝ φ ((1 / α) * Real.log z)) :
    deriv (fun w => φ ((1 / α) * Real.log w)) z
      = deriv φ ((1 / α) * Real.log z) * (1 / (α * z)) := by
  have hinner : DifferentiableAt ℝ (fun w : ℝ => (1 / α) * Real.log w) z :=
    (Real.differentiableAt_log hz).const_mul (1 / α)
  change deriv (φ ∘ fun w : ℝ => (1 / α) * Real.log w) z = _
  rw [deriv_comp (x := z) (h := fun w : ℝ => (1 / α) * Real.log w) (h₂ := φ) hφ hinner]
  have hd : deriv (fun w : ℝ => (1 / α) * Real.log w) z = 1 / (α * z) := by
    rw [deriv_const_mul (1/α) (Real.differentiableAt_log hz), Real.deriv_log, one_div,
      div_eq_mul_inv, mul_inv]
    ring
  rw [hd]

/-- **Second-order chain rule for a logarithm-composition.**  For `α ≠ 0`, `z ≠ 0`, `φ`
twice differentiable along the composition (hypotheses `hφ`, `hφd`),
`d²/dz² [φ ((1/α) log z)] = φ''((1/α) log z) /(α z)² - φ'((1/α) log z) /(α z²)`. -/
lemma deriv_deriv_comp_const_mul_log (φ : ℝ → ℝ) {α z : ℝ} (hα : α ≠ 0) (hz : z ≠ 0)
    (hφ : DifferentiableAt ℝ (deriv φ) ((1 / α) * Real.log z))
    (hφd : ∀ w, DifferentiableAt ℝ φ ((1 / α) * Real.log w)) :
    deriv (fun w => deriv (fun w' => φ ((1 / α) * Real.log w')) w) z
      = deriv (deriv φ) ((1 / α) * Real.log z) * (1 / (α * z)) * (1 / (α * z))
        - deriv φ ((1 / α) * Real.log z) * (1 / (α * z ^ 2)) := by
  have hinner : DifferentiableAt ℝ (fun w : ℝ => (1 / α) * Real.log w) z :=
    (Real.differentiableAt_log hz).const_mul (1 / α)
  have hev : (fun w => deriv (fun w' => φ ((1 / α) * Real.log w')) w)
      =ᶠ[nhds z] fun w => deriv φ ((1 / α) * Real.log w) * ((1 / α) * w⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    rw [deriv_comp_const_mul_log φ hw (hφd w)]
    congr 1
    rw [one_div, div_eq_mul_inv, mul_inv]
    ring
  rw [hev.deriv_eq]
  have hA : DifferentiableAt ℝ (fun w : ℝ => deriv φ ((1 / α) * Real.log w)) z := by
    change DifferentiableAt ℝ ((deriv φ) ∘ fun w : ℝ => (1 / α) * Real.log w) z
    exact hφ.comp z hinner
  have hB : DifferentiableAt ℝ (fun w : ℝ => (1 / α) * w⁻¹) z :=
    (differentiableAt_id.inv hz).const_mul (1 / α)
  change deriv ((fun w : ℝ => deriv φ ((1 / α) * Real.log w)) * fun w : ℝ => (1 / α) * w⁻¹) z = _
  rw [deriv_mul hA hB]
  have hA' : deriv (fun w : ℝ => deriv φ ((1 / α) * Real.log w)) z
      = deriv (deriv φ) ((1 / α) * Real.log z) * (1 / (α * z)) := by
    change deriv ((deriv φ) ∘ fun w : ℝ => (1 / α) * Real.log w) z = _
    rw [deriv_comp (x := z) (h := fun w : ℝ => (1 / α) * Real.log w) (h₂ := deriv φ) hφ hinner]
    congr 1
    rw [deriv_const_mul (1/α) (Real.differentiableAt_log hz), Real.deriv_log, one_div,
      div_eq_mul_inv, mul_inv]
    ring
  have hB' : deriv (fun w : ℝ => (1 / α) * w⁻¹) z = -(1 / (α * z ^ 2)) := by
    rw [deriv_const_mul (1/α) (differentiableAt_id.inv hz), deriv_inv]
    field_simp
  rw [hA', hB']
  field_simp
  ring

theorem bslOp_comp_exp {α : ℝ} (hα : 0 < α) {ψ : ℝ → ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) {s θ : ℝ}
    (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (fun z θ' => ψ ((1 / α) * Real.log z) θ') (Real.exp (α * s)) θ
      = - deriv (fun s' => deriv (fun s'' => ψ s'' θ) s') s
        - deriv (fun θ' => deriv (fun θ'' => ψ s θ'') θ') θ
        - 5 * deriv (fun s' => ψ s' θ) s + Real.tan θ * deriv (fun θ' => ψ s θ') θ
        + ((Real.tan θ) ^ 2 - 5) * ψ s θ := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hexp : Real.exp (α * s) ≠ 0 := Real.exp_ne_zero _
  have hlog : (1 / α) * Real.log (Real.exp (α * s)) = s := by
    rw [Real.log_exp, ← mul_assoc, one_div, inv_mul_cancel₀ hαne, one_mul]
  -- smoothness of the `s`-slices, which is all the chain rule needs
  have hsmooth : ContDiff ℝ 2 (fun s' : ℝ => ψ s' θ) := by
    have h : ContDiff ℝ 2 (fun s' : ℝ => (s', θ)) := ContDiff.prodMk contDiff_id contDiff_const
    exact (hψ 2).comp h
  have hφdiff : DifferentiableAt ℝ (fun s' : ℝ => ψ s' θ)
      ((1 / α) * Real.log (Real.exp (α*s))) :=
    (hsmooth.differentiable (by norm_num)) _
  have hφ'diff : DifferentiableAt ℝ (deriv (fun s' : ℝ => ψ s' θ))
      ((1 / α) * Real.log (Real.exp (α*s))) := hsmooth.differentiable_deriv_two _
  have hφddiff : ∀ w, DifferentiableAt ℝ (fun s' : ℝ => ψ s' θ) ((1 / α) * Real.log w) :=
    fun w => (hsmooth.differentiable (by norm_num)) ((1 / α) * Real.log w)
  -- the values of `pz` and `pzIter 2`
  have h1 : Work.Spaces.pz (fun z θ' => ψ ((1 / α) * Real.log z) θ') (Real.exp (α*s)) θ
      = deriv (fun s' => ψ s' θ) s * (1 / (α * Real.exp (α*s))) := by
    change deriv (fun w : ℝ => ψ ((1 / α) * Real.log w) θ) (Real.exp (α*s)) = _
    rw [deriv_comp_const_mul_log (fun s' : ℝ => ψ s' θ) hexp hφdiff, hlog]
  have h2 : Work.Spaces.pzIter 2 (fun z θ' => ψ ((1 / α) * Real.log z) θ') (Real.exp (α*s)) θ
      = deriv (fun s' => deriv (fun s'' => ψ s'' θ) s') s * (1 / (α * Real.exp (α*s))) ^ 2
        - deriv (fun s' => ψ s' θ) s * (1 / (α * (Real.exp (α*s)) ^ 2)) := by
    change deriv (fun w : ℝ => deriv (fun w' : ℝ => ψ ((1 / α) * Real.log w') θ) w)
      (Real.exp (α*s)) = _
    rw [deriv_deriv_comp_const_mul_log (fun s' : ℝ => ψ s' θ) hαne hexp hφ'diff hφddiff, hlog]
    have hd2 : deriv (deriv (fun s' : ℝ => ψ s' θ)) s
        = deriv (fun s' => deriv (fun s'' => ψ s'' θ) s') s := rfl
    rw [hd2, pow_two]
    ring
  -- the angular values: `Lzero`'s two derivative slots and the value slot
  have h4 : Work.Spaces.pthIter 2 (fun z θ' => ψ ((1 / α) * Real.log z) θ') (Real.exp (α*s)) θ
      = deriv (fun θ' => deriv (fun θ'' => ψ s θ'') θ') θ := by
    change deriv (fun θ' : ℝ =>
      deriv (fun θ'' : ℝ => ψ ((1 / α) * Real.log (Real.exp (α*s))) θ'') θ') θ = _
    rw [hlog]
  have h5 : Work.Spaces.pth (fun z θ' => Real.tan θ' * ψ ((1 / α) * Real.log z) θ')
      (Real.exp (α*s)) θ
      = Real.tan θ * deriv (fun θ' => ψ s θ') θ + (1 + (Real.tan θ) ^ 2) * ψ s θ := by
    change deriv (fun θ' : ℝ =>
      Real.tan θ' * ψ ((1 / α) * Real.log (Real.exp (α*s))) θ') θ = _
    rw [hlog]
    have htansmooth : DifferentiableAt ℝ Real.tan θ := (Real.differentiableAt_tan).mpr hcos
    have htsmooth : DifferentiableAt ℝ (fun θ' : ℝ => ψ s θ') θ := by
      have h : ContDiff ℝ 2 (fun θ' : ℝ => ψ s θ') := by
        have h2 : ContDiff ℝ 2 (fun θ' : ℝ => (s, θ')) :=
          ContDiff.prodMk contDiff_const contDiff_id
        exact (hψ 2).comp h2
      exact (h.differentiable (by norm_num)) θ
    change deriv (Real.tan * fun θ' : ℝ => ψ s θ') θ = _
    rw [deriv_mul htansmooth htsmooth, Real.deriv_tan]
    have hsec : (1 : ℝ) / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      linear_combination -Real.sin_sq_add_cos_sq θ
    rw [hsec]
    ring
  rw [Work.Elliptic.bslOp, Work.Elliptic.Lzero]
  rw [h1, h2, h4, h5, hlog]
  field_simp
  ring

end Work.EllipticEst.InteriorRegularity
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.contDiff_mul_of_tsupport_subset =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.EllipticEst.InteriorRegularity

open Set Filter

/-- **Multiplication of a smooth function by a function smooth on a neighbourhood of its
support.**  If `g` is `C^n` on an open set `U` and `f` is `C^∞` on the whole space with
`tsupport f ⊆ U`, then `f * g` is `C^n` on the whole space.

The proof is a two-open-set argument: `f` is `C^n` on the open set `U` (it is `C^m` for every
`m : ℕ`, so `contDiffWithinAt_iff_forall_nat_le` upgrades this to the order `n`, which may be
`∞`), while on the complement of the (closed) topological support of `f` the function `f`
vanishes identically on a neighbourhood of every point, so `f * g` agrees there with the zero
function.  The two open sets cover the space because `tsupport f ⊆ U`, so
`contDiff_of_contDiffOn_union_of_isOpen` applies. -/
theorem contDiff_mul_of_tsupport_subset {U : Set E2} {f g : E2 → ℂ} {n : ℕ∞}
    (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g U) (hU : IsOpen U) (hf : ∀ m : ℕ, ContDiff ℝ m f)
    (hfs : tsupport f ⊆ U) : ContDiff ℝ (n : WithTop ℕ∞) (fun x => f x * g x) := by
  -- `f` is `C^m` for every `m`, hence `C^n` on the open set `U`
  have hfU : ContDiffOn ℝ (n : WithTop ℕ∞) f U := by
    intro x hx
    rw [contDiffWithinAt_iff_forall_nat_le]
    exact fun m _ => (hf m).contDiffOn x hx
  -- off the topological support of `f`, the product vanishes on a neighbourhood of every point
  have hcompl : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => f x * g x) (tsupport f)ᶜ := by
    intro x hx
    have hev : (fun y => f y * g y) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev).contDiffWithinAt
  -- `U` and `(tsupport f)ᶜ` are open and cover the whole space
  refine contDiff_of_contDiffOn_union_of_isOpen (hfU.mul hg) hcompl ?_ hU
    (isClosed_tsupport f).isOpen_compl
  rw [eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact Or.inl (hfs hx)
  · exact Or.inr hx

end Work.EllipticEst.InteriorRegularity
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.curryC_bridge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity

/-! ### Coordinates of `E2 = EuclideanSpace ℝ (Fin 2)` along the `e₀`/`e₁` lines -/



lemma add_smul_e0_coords (x : E2) (t : ℝ) : x + t • e0 = coords (x 0 + t) (x 1) := by
  ext i
  fin_cases i <;> simp [coords, e0, EuclideanSpace.basisFun_apply]

lemma add_smul_e1_coords (x : E2) (t : ℝ) : x + t • e1 = coords (x 0) (x 1 + t) := by
  ext i
  fin_cases i <;> simp [coords, e1, EuclideanSpace.basisFun_apply]

/-! ### The line derivatives of a function on `E2` pulled back from `ℝ × ℝ`

These are the two "coordinate bridge" identities, in the form in which the
second-order identity needs them: they hold for *any* `Q`, differentiability is
irrelevant, because a line derivative along `e₀` is by definition the derivative of
the `e₀`-slice, i.e. of `t ↦ Q (x₀ + t, x₁)`, and shifting the variable only relabels
the point at which the one-variable derivative is taken. -/

lemma lineDeriv_e0_curry_prod (Q : ℝ × ℝ → ℂ) (x : E2) :
    lineDeriv ℝ (fun y : E2 => Q (y 0, y 1)) x e0 = deriv (fun s => Q (s, x 1)) (x 0) := by
  rw [lineDeriv]
  have h1 : (fun t : ℝ => (fun y : E2 => Q (y 0, y 1)) (x + t • e0))
      = fun t : ℝ => Q (x 0 + t, x 1) := by
    funext t
    rw [add_smul_e0_coords x t]
    simp [coords]
  rw [h1, deriv_comp_const_add (fun s => Q (s, x 1)) (x 0) (0 : ℝ)]
  simp

lemma lineDeriv_e1_curry_prod (Q : ℝ × ℝ → ℂ) (x : E2) :
    lineDeriv ℝ (fun y : E2 => Q (y 0, y 1)) x e1 = deriv (fun θ => Q (x 0, θ)) (x 1) := by
  rw [lineDeriv]
  have h1 : (fun t : ℝ => (fun y : E2 => Q (y 0, y 1)) (x + t • e1))
      = fun t : ℝ => Q (x 0, x 1 + t) := by
    funext t
    rw [add_smul_e1_coords x t]
    simp [coords]
  rw [h1, deriv_comp_const_add (fun θ => Q (x 0, θ)) (x 1) (0 : ℝ)]
  simp

theorem curryC_bridge {F : ℝ → ℝ → ℂ}
    (hF : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry F)) :
    (∀ n : ℕ, ContDiff ℝ n (curryC F)) ∧
    (∀ x : E2, lineDeriv ℝ (curryC F) x e0 = deriv (fun s => F s (x 1)) (x 0)) ∧
    (∀ x : E2, lineDeriv ℝ (curryC F) x e1 = deriv (fun θ => F (x 0) θ) (x 1)) ∧
    (∀ x : E2, d0 (d0 (curryC F)) x + d1 (d1 (curryC F)) x
      = deriv (fun s => deriv (fun s' => F s' (x 1)) s) (x 0)
        + deriv (fun θ => deriv (fun θ' => F (x 0) θ') θ) (x 1)) := by
  -- The two first-order identities: both sides are the derivative of the corresponding
  -- slice of `F`, after transporting along the `e₀`- (resp. `e₁`-) line.
  have hd0 : ∀ x : E2, lineDeriv ℝ (curryC F) x e0 = deriv (fun s => F s (x 1)) (x 0) := by
    intro x
    rw [lineDeriv]
    have h1 : (fun t : ℝ => curryC F (x + t • e0)) = fun t : ℝ => F (x 0 + t) (x 1) := by
      funext t
      rw [add_smul_e0_coords x t]
      exact curryC_curry'_apply F (x 0 + t) (x 1)
    rw [h1, deriv_comp_const_add (fun s => F s (x 1)) (x 0) (0 : ℝ)]
    simp
  have hd1 : ∀ x : E2, lineDeriv ℝ (curryC F) x e1 = deriv (fun θ => F (x 0) θ) (x 1) := by
    intro x
    rw [lineDeriv]
    have h1 : (fun t : ℝ => curryC F (x + t • e1)) = fun t : ℝ => F (x 0) (x 1 + t) := by
      funext t
      rw [add_smul_e1_coords x t]
      exact curryC_curry'_apply F (x 0) (x 1 + t)
    rw [h1, deriv_comp_const_add (fun θ => F (x 0) θ) (x 1) (0 : ℝ)]
    simp
  refine ⟨?_, hd0, hd1, ?_⟩
  · -- Smoothness: `curryC F` is `uncurry F` composed with the linear coordinate map.
    intro n
    have hphi : ContDiff ℝ n (fun x : E2 => (x 0, x 1)) := by
      have h : (fun x : E2 => (x 0, x 1))
          = fun x : E2 => ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) x,
                            (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) x) := rfl
      rw [h]
      exact (ContinuousLinearMap.prod (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))).contDiff
    exact (hF n).comp hphi
  · -- Second order: replace `d0 (curryC F)` and `d1 (curryC F)` by their slice forms
    -- (the first-order identities), then apply the bridge again.
    intro x
    have hG0 : d0 (curryC F) = fun y : E2 => deriv (fun s => F s (y 1)) (y 0) := by
      funext y
      rw [show d0 (curryC F) y = lineDeriv ℝ (curryC F) y e0 from rfl, hd0 y]
    have hG1 : d1 (curryC F) = fun y : E2 => deriv (fun θ => F (y 0) θ) (y 1) := by
      funext y
      rw [show d1 (curryC F) y = lineDeriv ℝ (curryC F) y e1 from rfl, hd1 y]
    have e0' : lineDeriv ℝ (fun y : E2 => deriv (fun s => F s (y 1)) (y 0)) x e0
        = deriv (fun s => deriv (fun s' => F s' (x 1)) s) (x 0) :=
      lineDeriv_e0_curry_prod (fun p : ℝ × ℝ => deriv (fun s => F s p.2) p.1) x
    have e1' : lineDeriv ℝ (fun y : E2 => deriv (fun θ => F (y 0) θ) (y 1)) x e1
        = deriv (fun θ => deriv (fun θ' => F (x 0) θ') θ) (x 1) :=
      lineDeriv_e1_curry_prod (fun p : ℝ × ℝ => deriv (fun θ => F p.1 θ) p.2) x
    rw [show d0 (d0 (curryC F)) x + d1 (d1 (curryC F)) x
          = lineDeriv ℝ (d0 (curryC F)) x e0 + lineDeriv ℝ (d1 (curryC F)) x e1 from rfl]
    rw [hG0, hG1, e0', e1']

end Work.EllipticEst.InteriorRegularity
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Bridge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep

set_option autoImplicit false



end Work.FTS.CoercivityStep
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The derivative of the identity function. -/
theorem deriv_self (z : ℝ) : deriv (fun y : ℝ => y) z = 1 := by
  rw [show (fun y : ℝ => y) = id from rfl, deriv_id]

/-! ## The operator `Q = z² ∂_z²` and the local calculus of the open quadrant

The target identity is stated on the open quadrant `Q0 = (0,∞) × (0,π/2)`, so everything below
is *local*: all differentiation happens at interior points of the quadrant, where the functions
at hand are `C^n` for every `n` (this is what `SmoothOpen` provides).  In particular the
commutation of `D_z` with the iterates of `D_θ` is obtained from the pointwise Clairaut identity
`Work.Spaces.Dz_Dth_comm`, which only needs `C²`: the lemma `Work.Spaces.DzDthIterCommOn` of the
library is stated with the hypothesis `ContDiffOn ℝ ⊤`, and in this Mathlib `⊤` is *analyticity*,
which `SmoothOpen` does not provide. -/

/-- The operator `Q = z² ∂_z²` acting on functions of `(z,θ)`: `Qop g z θ = z² ∂_z² g (z,θ)`. -/
def Qop (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ

variable {g : ℝ → ℝ → ℝ}

/-! ### Slices of a function that is smooth on the open quadrant -/

theorem contDiffOn_slice_z_nat {G : ℝ → ℝ → ℝ} {N : ℕ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ N (Function.uncurry G) (s ×ˢ t)) {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ N (fun z => G z θ) s := by
  have h1 : ContDiffOn ℝ (N : WithTop ℕ∞) (fun z : ℝ => (z, θ)) s :=
    (contDiffOn_id : ContDiffOn ℝ (N : WithTop ℕ∞) (fun z : ℝ => z) s).prodMk
      (contDiffOn_const (c := θ))
  exact (hG.comp h1 (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

theorem contDiffOn_slice_θ_nat {G : ℝ → ℝ → ℝ} {N : ℕ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ N (Function.uncurry G) (s ×ˢ t)) {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ N (fun θ => G z θ) t := by
  have h1 : ContDiffOn ℝ (N : WithTop ℕ∞) (fun θ : ℝ => (z, θ)) t :=
    (contDiffOn_const (c := z)).prodMk
      (contDiffOn_id : ContDiffOn ℝ (N : WithTop ℕ∞) (fun θ : ℝ => θ) t)
  exact (hG.comp h1 (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- The `z`-slice of a function smooth on the open quadrant is `C^N` on `(0,∞)`. -/
theorem slice_z_contDiffOn (hg : SmoothOpen g) (N : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ N (fun z => g z θ) (Set.Ioi 0) :=
  contDiffOn_slice_z_nat (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2)) (hg.forall N) hθ

/-- The `θ`-slice of a function smooth on the open quadrant is `C^N` on `(0,π/2)`. -/
theorem slice_θ_contDiffOn (hg : SmoothOpen g) (N : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ N (fun θ => g z θ) (Set.Ioo 0 (π / 2)) :=
  contDiffOn_slice_θ_nat (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2)) (hg.forall N) hz

/-- The `z`-slice of a function smooth on the open quadrant is differentiable at every `z > 0`. -/
theorem differentiableAt_slice_z_of (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : DifferentiableAt ℝ (fun z' => g z' θ) z :=
  ((slice_z_contDiffOn hg 1 hθ).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- The `θ`-slice of a function smooth on the open quadrant is differentiable at every
interior angle. -/
theorem differentiableAt_slice_θ_of (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
  ((slice_θ_contDiffOn hg 1 hz).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)

/-- The `∂_z`-derivative of the `z`-slice of a function smooth on the open quadrant is again
differentiable at every `z > 0`. -/
theorem differentiableAt_deriv_slice_z_of (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : DifferentiableAt ℝ (deriv (fun z' => g z' θ)) z :=
  (((slice_z_contDiffOn hg 2 hθ).deriv_of_isOpen (m := 1) isOpen_Ioi
      (by norm_num)).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- A function smooth on the open quadrant is `C²` at every point of the quadrant. -/
theorem contDiffAt_two_of_mem (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
  (hg.contDiffAt (isOpen_Q0.mem_nhds (mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))).of_le
    (by simp [Work.Stability.smoothOrder])

/-! ### Locality of `D_z`, `D_θ` and their iterates on the open quadrant -/

theorem Q0_Dz_congr {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz A)) (Function.uncurry (Work.Spaces.Dz B)) Q0 := by
  intro p hp
  have hz : Work.Spaces.pz A p.1 p.2 = Work.Spaces.pz B p.1 p.2 :=
    Work.Spaces.pz_congr_of_isOpen isOpen_Q0 h hp
  show p.1 * Work.Spaces.pz A p.1 p.2 = p.1 * Work.Spaces.pz B p.1 p.2
  rw [hz]


theorem Q0_DzIter_congr {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter k A))
      (Function.uncurry (Work.Spaces.DzIter k B)) Q0 := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [Work.Spaces.DzIter_succ] using Q0_Dz_congr ih


/-! ### `∂_z` and `∂_θ` of a difference -/

theorem Q0_pz_sub {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hB : DifferentiableAt ℝ (fun z' => B z' θ) z) :
    Work.Spaces.pz (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pz A z θ - Work.Spaces.pz B z θ := by
  have hfun : (fun z' : ℝ => A z' θ - B z' θ)
      = (fun z' => A z' θ) - (fun z' => B z' θ) := by
    funext x; rfl
  show deriv (fun z' => A z' θ - B z' θ) z
      = deriv (fun z' => A z' θ) z - deriv (fun z' => B z' θ) z
  rw [hfun, deriv_sub hA hB]

theorem Q0_pth_sub {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hB : DifferentiableAt ℝ (fun θ' => B z θ') θ) :
    Work.Spaces.pth (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pth A z θ - Work.Spaces.pth B z θ := by
  have hfun : (fun θ' : ℝ => A z θ' - B z θ')
      = (fun θ' => A z θ') - (fun θ' => B z θ') := by
    funext x; rfl
  show deriv (fun θ' => A z θ' - B z θ') θ
      = deriv (fun θ' => A z θ') θ - deriv (fun θ' => B z θ') θ
  rw [hfun, deriv_sub hA hB]

/-! ### `Q = D_z² - D_z` on the open quadrant -/

/-- **`z²∂_z² = D_z(D_z - 1)` on the open quadrant.**  For `g` smooth on `Q0` and
`(z,θ) ∈ Q0`, `z²∂_z² g = D_z² g - D_z g`.  The one-variable content is
`z²u'' = z(zu')' - zu'`, i.e. `(zu')' = u' + zu''` by the product rule. -/
theorem Qop_eq_Dz2_sub_Dz (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Qop g z θ = Work.Spaces.DzIter 2 g z θ - Work.Spaces.DzIter 1 g z θ := by
  have hderiv : DifferentiableAt ℝ (deriv (fun z' => g z' θ)) z :=
    differentiableAt_deriv_slice_z_of hg hz hθ
  have hpz2 : Work.Spaces.pzIter 2 g z θ = deriv (deriv (fun z' => g z' θ)) z := by
    rw [Work.Spaces.pzIter_eq_iteratedDeriv, iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : (fun y => Work.Spaces.DzIter 1 g y θ)
      = fun y => y * deriv (fun z' => g z' θ) y := by
    funext y
    rfl
  have hdm : deriv (fun y => y * deriv (fun z' => g z' θ) y) z
      = deriv (fun z' => g z' θ) z + z * deriv (deriv (fun z' => g z' θ)) z := by
    have hmul := deriv_mul (c := fun y : ℝ => y) (d := deriv (fun z' => g z' θ))
      differentiableAt_id hderiv
    have hfun2 : ((fun y : ℝ => y) * deriv (fun z' => g z' θ))
        = fun y => y * deriv (fun z' => g z' θ) y := by
      funext x; rfl
    rw [hfun2] at hmul
    rw [deriv_self] at hmul
    simpa only [one_mul] using hmul
  show z ^ 2 * Work.Spaces.pzIter 2 g z θ
      = Work.Spaces.DzIter 2 g z θ - Work.Spaces.DzIter 1 g z θ
  rw [hpz2]
  show z ^ 2 * deriv (deriv (fun z' => g z' θ)) z
      = z * deriv (fun y => Work.Spaces.DzIter 1 g y θ) z
        - z * deriv (fun z' => g z' θ) z
  rw [hfun, hdm]
  ring

/-! ### `Q` commutes with `D_z` -/

/-- On the open quadrant, `Q = z²∂_z²` commutes with `D_z = z∂_z`. -/
theorem Qop_Dz_eq (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Qop (Work.Spaces.Dz g) z θ = Work.Spaces.Dz (Qop g) z θ := by
  have hmem : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hEqOn : Set.EqOn (Function.uncurry (Qop g))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 g z θ
        - Work.Spaces.DzIter 1 g z θ)) Q0 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_Q0.mp hp
    exact Qop_eq_Dz2_sub_Dz hg h1 ⟨h2, h3⟩
  have hpzcongr : Work.Spaces.pz (Qop g) z θ
      = Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 g z θ
          - Work.Spaces.DzIter 1 g z θ) z θ :=
    Work.Spaces.pz_congr_of_isOpen isOpen_Q0 hEqOn hmem
  have hsub : Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 g z θ
        - Work.Spaces.DzIter 1 g z θ) z θ
      = Work.Spaces.pz (Work.Spaces.DzIter 2 g) z θ
        - Work.Spaces.pz (Work.Spaces.DzIter 1 g) z θ :=
    Q0_pz_sub (differentiableAt_slice_z_of (hg.DzIter 2) hz hθ)
      (differentiableAt_slice_z_of (hg.DzIter 1) hz hθ)
  have hdec : Qop (Work.Spaces.Dz g) z θ
      = Work.Spaces.DzIter 3 g z θ - Work.Spaces.DzIter 2 g z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
      using Qop_eq_Dz2_sub_Dz (hg.Dz) hz hθ
  have hrhs : Work.Spaces.Dz (Qop g) z θ
      = Work.Spaces.DzIter 3 g z θ - Work.Spaces.DzIter 2 g z θ := by
    show z * Work.Spaces.pz (Qop g) z θ
        = Work.Spaces.DzIter 3 g z θ - Work.Spaces.DzIter 2 g z θ
    rw [hpzcongr, hsub]
    show z * (Work.Spaces.pz (Work.Spaces.DzIter 2 g) z θ
          - Work.Spaces.pz (Work.Spaces.DzIter 1 g) z θ)
        = z * Work.Spaces.pz (Work.Spaces.DzIter 2 g) z θ
          - z * Work.Spaces.pz (Work.Spaces.DzIter 1 g) z θ
    ring
  rw [hdec, hrhs]

/-! ### `Q` commutes with `D_θ` -/

/-- On the open quadrant, `D_z` and `D_θ` commute (pointwise Clairaut; `C²` suffices). -/
theorem Q0_Dz_Dth_comm (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth g)))
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz g))) Q0 := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := mem_Q0.mp hp
  exact Work.Spaces.Dz_Dth_comm (contDiffAt_two_of_mem hg h1 ⟨h2, h3⟩)

/-- On the open quadrant, `D_z²` commutes with `D_θ`: `D_z²(D_θ g) = D_θ(D_z² g)`. -/
theorem Q0_DzIter2_Dth_comm (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter 2 (Work.Spaces.Dth g)))
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter 2 g))) Q0 := by
  have h1 : Set.EqOn
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.Dth g))))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.Dz g)))) Q0 :=
    Q0_Dz_congr (Q0_Dz_Dth_comm hg)
  have h2 : Set.EqOn
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.Dz g))))
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.Dz g)))) Q0 :=
    Q0_Dz_Dth_comm hg.Dz
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1.trans h2

/-- On the open quadrant, `Q = z²∂_z²` commutes with `D_θ = sin(2θ)∂_θ`. -/
theorem Qop_Dth_eq (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Qop (Work.Spaces.Dth g) z θ = Work.Spaces.Dth (Qop g) z θ := by
  have hmem : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hEqOn : Set.EqOn (Function.uncurry (Qop g))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 g z θ
        - Work.Spaces.DzIter 1 g z θ)) Q0 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_Q0.mp hp
    exact Qop_eq_Dz2_sub_Dz hg h1 ⟨h2, h3⟩
  have hpthcongr : Work.Spaces.pth (Qop g) z θ
      = Work.Spaces.pth (fun z θ => Work.Spaces.DzIter 2 g z θ
          - Work.Spaces.DzIter 1 g z θ) z θ :=
    Work.Spaces.pth_congr_of_isOpen isOpen_Q0 hEqOn hmem
  have hsub : Work.Spaces.pth (fun z θ => Work.Spaces.DzIter 2 g z θ
        - Work.Spaces.DzIter 1 g z θ) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter 2 g) z θ
        - Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ :=
    Q0_pth_sub (differentiableAt_slice_θ_of (hg.DzIter 2) hz hθ)
      (differentiableAt_slice_θ_of (hg.DzIter 1) hz hθ)
  have e1 : Work.Spaces.DzIter 2 (Work.Spaces.Dth g) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 2 g) z θ :=
    Q0_DzIter2_Dth_comm hg hmem
  have e2 : Work.Spaces.DzIter 1 (Work.Spaces.Dth g) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 1 g) z θ :=
    Q0_Dz_Dth_comm hg hmem
  have hdec : Qop (Work.Spaces.Dth g) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 2 g) z θ
        - Work.Spaces.Dth (Work.Spaces.DzIter 1 g) z θ := by
    rw [Qop_eq_Dz2_sub_Dz (hg.Dth) hz hθ, e1, e2]
  have hrhs : Work.Spaces.Dth (Qop g) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 2 g) z θ
        - Work.Spaces.Dth (Work.Spaces.DzIter 1 g) z θ := by
    show Real.sin (2 * θ) * Work.Spaces.pth (Qop g) z θ
        = Work.Spaces.Dth (Work.Spaces.DzIter 2 g) z θ
          - Work.Spaces.Dth (Work.Spaces.DzIter 1 g) z θ
    rw [hpthcongr, hsub]
    show Real.sin (2 * θ) * (Work.Spaces.pth (Work.Spaces.DzIter 2 g) z θ
          - Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ)
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 2 g) z θ
          - Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ
    ring
  rw [hdec, hrhs]

/-! ### The iterated versions -/

/-- On the open quadrant, `Q = z²∂_z²` commutes with every iterate of `D_z`. -/
theorem Qop_DzIter_eq (hg : SmoothOpen g) (m : ℕ) :
    Set.EqOn (Function.uncurry (Qop (Work.Spaces.DzIter m g)))
      (Function.uncurry (Work.Spaces.DzIter m (Qop g))) Q0 := by
  induction m with
  | zero => intro p hp; rfl
  | succ m ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ1, hθ2⟩ := mem_Q0.mp hp
      have h1 : Qop (Work.Spaces.DzIter (m + 1) g) z θ
          = Work.Spaces.Dz (Qop (Work.Spaces.DzIter m g)) z θ :=
        Qop_Dz_eq (hg.DzIter m) hz ⟨hθ1, hθ2⟩
      have h2 : Work.Spaces.Dz (Qop (Work.Spaces.DzIter m g)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter m (Qop g)) z θ :=
        Q0_Dz_congr (A := Qop (Work.Spaces.DzIter m g))
          (B := Work.Spaces.DzIter m (Qop g)) ih hp
      show Qop (Work.Spaces.DzIter (m + 1) g) z θ
          = Work.Spaces.DzIter (m + 1) (Qop g) z θ
      rw [h1, h2]
      simp only [Work.Spaces.DzIter_succ]

/-- On the open quadrant, `Q = z²∂_z²` commutes with every iterate of `D_θ`. -/
theorem Qop_DthIter_eq (hg : SmoothOpen g) (i : ℕ) :
    Set.EqOn (Function.uncurry (Qop (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Qop g))) Q0 := by
  induction i with
  | zero => intro p hp; rfl
  | succ i ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ1, hθ2⟩ := mem_Q0.mp hp
      have h1 : Qop (Work.Spaces.DthIter (i + 1) g) z θ
          = Work.Spaces.Dth (Qop (Work.Spaces.DthIter i g)) z θ :=
        Qop_Dth_eq (hg.DthIter i) hz ⟨hθ1, hθ2⟩
      have h2 : Work.Spaces.Dth (Qop (Work.Spaces.DthIter i g)) z θ
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Qop g)) z θ := by
        have hstep := Work.Spaces.pth_congr_of_isOpen
          (f := Qop (Work.Spaces.DthIter i g))
          (f' := Work.Spaces.DthIter i (Qop g)) isOpen_Q0 ih hp
        show Real.sin (2 * θ) * Work.Spaces.pth (Qop (Work.Spaces.DthIter i g)) z θ
            = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i (Qop g)) z θ
        rw [hstep]
      show Qop (Work.Spaces.DthIter (i + 1) g) z θ
          = Work.Spaces.DthIter (i + 1) (Qop g) z θ
      rw [h1, h2]
      simp only [Work.Spaces.DthIter_succ]

/-- **`z² ∂_z²` commutes with the iterated operators `D_z^m D_θ^i` on the open quadrant.**

For `f` smooth on the open quadrant `Q0 = (0,∞) × (0,π/2)` and all `m, i : ℕ`, the operator
`Q = z²∂_z²` (i.e. `fun z θ => z² · pzIter 2 f z θ`) commutes with `D_z^m D_θ^i`:

`z² ∂_z² (D_z^m D_θ^i f) = D_z^m D_θ^i (z² ∂_z² f)`  on `Q0`.

Route.  As operators, `z²∂_z² = D_z² - D_z = D_z(D_z - 1)`, hence `z²∂_z²` is a polynomial in
`D_z` and commutes with `D_z^m`; it also commutes with `D_θ^i`, because
`D_z (D_θ^i g) = D_θ^i (D_z g)` on the open quadrant (`Work.Spaces.DzDthIterCommOn` applied with
`V` the open quadrant), so that
`z²∂_z²(D_θ^i g) = D_z²(D_θ^i g) - D_z(D_θ^i g) = D_θ^i(D_z²g) - D_θ^i(D_zg) = D_θ^i(z²∂_z²g)`.
The pointwise identity `z²∂_z²(D_z g) = D_z(z²∂_z² g)` (the one-variable statement
`z²(zh')'' = z(z²h'')'`, i.e. `z²(z h')'' - z(z²h'')' = 0`, provable by differentiating
products: both sides equal `z³h''' + 2z²h''`) gives the induction on `m`.  Nothing here needs any
integrability hypothesis. -/
theorem ZsqPz2Comm (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) (m i : ℕ) :
    Set.EqOn (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z θ))
      (Function.uncurry (Work.Spaces.mixed m i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 := Qop_DzIter_eq (hf.DthIter i) m
  have h2 := Qop_DthIter_eq hf i
  have h3 := Q0_DzIter_congr h2 m
  exact h1.trans h3

end Work.FTS.EllipticEst.DzAmgm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open =====
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

/-- **Cauchy--Schwarz for the `j`-th radial moment `F_*(D_z^j F)`** (open-quadrant
source).  This is `PsiInt_sq_mul_w_le_open` with `u = F`: the `j`-th radial moment
`PsiInt F j z = ∫_θ D_z^j F(z,θ) sinθcos²θ dθ` of `F` is *by definition* the angular
moment `F_*(D_z^j F)(z)`, and the integrability hypothesis needed by the
Cauchy--Schwarz estimate is furnished by `integrableOn_zSummand` from `F ∈ ℋ^k`
(together with `j ≤ k`). -/
theorem FstarDzIter_sq_mul_w_le_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k)
    {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have hU : IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    integrableOn_zSummand α k hF hmem j hj hzI
  have h := PsiInt_sq_mul_w_le_open F hF j hz hU
  simpa only [PsiInt, Work.Elliptic.Fstar] using h

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-- **The slice identity.**  For every `z`, the radial weight `w2 z` times the angular
integral `∫_θ g z θ ^ 2 · σ θ` is the angular integral of the level-`0` `HkIntegrand`. -/
theorem w2_mul_slice_eq_HkIntegrand_slice (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ := by
  -- Push the constant `w2 z` into the angular integral, using `sq_mul_W` pointwise.
  have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.AngSecond.w2 z
            * (g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [HkIntegrand_zero_eq, AngSecond.sq_mul_W g hθ]
    ring
  have h2 : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.AngSecond.w2 z
          * (g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      = Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) :=
    MeasureTheory.integral_const_mul _ _
  exact h2.symm.trans h1.symm

theorem hksq_eq_w2_sliceIntegral {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn
        (fun z => Work.FTS.EllipticEst.AngSecond.w2 z
          * ∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        Work.Spaces.Iz
      ∧ ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.AngSecond.w2 z
            * (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        = Work.Spaces.HkSq α 0 g := by
  have hslice : ∀ z : ℝ,
      Work.FTS.EllipticEst.AngSecond.w2 z
          * (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ :=
    fun z => w2_mul_slice_eq_HkIntegrand_slice α g z
  constructor
  · -- Integrability transfers from `HkMem α 0 g` along the pointwise slice identity.
    exact MeasureTheory.IntegrableOn.congr_fun hg.2
      (fun z _ => (hslice z).symm) measurableSet_Ici
  · rw [Work.Spaces.HkSq]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => hslice z)

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ESW.Defs`: the vocabulary of the top angular slot `Tk α k (∂_θθΨ)`

This file sets up the abbreviations used by the induction step `TT.est_step_weak` and proves the
elementary bookkeeping lemmas (the slice form of the equation, the `η`-slot bound, the low-order
`(u')²`/`u²` bound).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular second derivative `B = ∂_θθΨ`. -/
abbrev Bsl (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- The radial second derivative `A = z²∂_zzΨ`. -/
abbrev Asl (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- The angular source `G = F + α²A + α(5+α)D_zΨ` of the sliced equation. -/
abbrev Gsl (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => F z θ + α ^ 2 * Asl Ψ z θ + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ

/-- `sin(2θ) ≤ 1` on `Iθ`. -/
theorem sin_two_le_one {θ : ℝ} (_hθ : θ ∈ Work.Spaces.Iθ) : Real.sin (2 * θ) ≤ 1 :=
  Real.sin_le_one _

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- **The sliced equation in the form used below**: on the open quadrant,
`Lzero1 (Ψ z ·) = G = F + α²A + α(5+α)D_zΨ`. -/
theorem slice_source_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Gsl α F Ψ z θ := by
  have h := Work.FTS.EllipticEst.remov.Lzero1_slice_eq_source
    (α := α) (F := F) (Ψ := Ψ) heq hΨ hz hθ
  have h2 := Work.FTS.EllipticEst.remov.srcB_DzIter_two_eq Ψ hΨ hz hθ
  simp only [Gsl]
  rw [h, h2]
  simp only [Work.Spaces.Dz, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  ring

/-- The one-dimensional angular estimate of the paper's §"General `ℋ^k` case", with the
dimension fixed: this is the type of `remov.slice_ang_gen k` after its `2 ≤ k` argument. -/
def OneD (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (iteratedDeriv j u θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))


end Work.FTS.EllipticEst.TT.ESW
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary angular bounds

`Sw θ = sin(2θ)^{η/2}` is bounded by `1` on the angular interval (its base `sin(2θ)` lies in
`[0,1]` and the exponent is nonnegative), so `|K · Sw| ≤ 3` there. -/

theorem Sw_le_one_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Sw θ ≤ 1 := by
  have h0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h2 : (0 : ℝ) ≤ Work.Spaces.eta / 2 := by norm_num [Work.Spaces.eta]
  have hle := Real.rpow_le_rpow h0 h1 h2
  rwa [Real.one_rpow] at hle

/-- On the angular interval, `|K(θ)·Sw θ| ≤ 3`. -/
theorem abs_K_mul_Sw_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Sw θ| ≤ 3 := by
  rw [abs_mul, abs_of_nonneg (K_nonneg_of_mem_Iθ hθ), abs_of_nonneg (Sw_nonneg_of_mem_Iθ hθ)]
  calc Work.Spaces.K θ * Sw θ ≤ 3 * 1 :=
        mul_le_mul (K_le_three_of_mem_Iθ hθ) (Sw_le_one_of_mem_Iθ hθ)
          (Sw_nonneg_of_mem_Iθ hθ) (by norm_num)
    _ = 3 := by norm_num

/-- The elementary bound `√x ≤ (1+x)/2` for `x ≥ 0` (AM–GM). -/
theorem sqrt_le_half_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ (1 + x) / 2 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  nlinarith [sq_nonneg (1 - x)]

/-! ## A.e. strong measurability on a closed interval from continuity on the open one -/

/-- A function continuous on the open interval `(a,b)` is a.e. strongly measurable for
`volume.restrict (Icc a b)`: the two intervals differ by the two null endpoints. -/
theorem aesm_Icc_of_continuousOn_Ioo {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo a b)) :
    AEStronglyMeasurable g (volume.restrict (Set.Icc a b)) := by
  have h1 : AEStronglyMeasurable g (volume.restrict (Set.Ioo a b)) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  have hset : (Set.Ioo a b) =ᵐ[volume] (Set.Icc a b) := MeasureTheory.Ioo_ae_eq_Icc
  have hmeas : volume.restrict (Set.Icc a b) = volume.restrict (Set.Ioo a b) :=
    (MeasureTheory.Measure.restrict_congr_set hset).symm
  rw [hmeas]
  exact h1

/-! ## The angular slice of the `L₁₂`-integrand is integrable

For `s > 0` the identity `K θ · F s θ / s = Wlam s · (K θ · Sw θ · Gaz F s θ)` converts the
slice of the density into the pairing of the angular profile `K·Sw` against the weighted datum
`Gaz F s = F s · w s / Sw`, which is dominated by `√(HkIntegrand α 4 F s ·)` on the angular
interval.  Since `|K·Sw| ≤ 3` there, the slice is dominated by the integrable function
`Wlam s · (3/2)·(1 + HkIntegrand α 4 F s ·)`. -/

/-- The pointwise domination on the angular interval. -/
theorem abs_K_mul_F_div_s_le {α s : ℝ} {F : ℝ → ℝ → ℝ} (hs : 0 < s) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * F s θ / s|
      ≤ Wlam s * (3 * (1 + Work.Spaces.HkIntegrand α 4 F s θ) / 2) := by
  have hx : 0 ≤ Work.Spaces.HkIntegrand α 4 F s θ := Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hb : |Work.Spaces.K θ * Sw θ * Gaz F s θ|
      ≤ 3 * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by
    rw [abs_mul]
    exact mul_le_mul (abs_K_mul_Sw_le_three hθ) (abs_Gaz_le_sqrt_HkIntegrand α F s θ)
      (abs_nonneg _) (by norm_num)
  have h3 : 3 * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)
      ≤ 3 * (1 + Work.Spaces.HkIntegrand α 4 F s θ) / 2 := by
    have h := sqrt_le_half_one_add hx
    linarith
  rw [K_mul_h_div_s_eq F hs θ hθ, abs_mul, abs_of_nonneg (Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left (le_trans hb h3) (Wlam_nonneg hs.le)

/-- **The angular slice of the `L₁₂`-integrand is integrable**, for every `s > 0`, from
`s ∈ ℋ⁴_α` alone (with `SmoothOpen F` only for the a.e. strong measurability of the slice). -/
theorem integrableOn_slice_of_SmoothOpen_HkMem {α s : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 4 F) (hs : 0 < s) :
    IntegrableOn (fun θ => Work.Spaces.K θ * F s θ / s) Work.Spaces.Iθ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hslice : ContinuousOn (fun θ => F s θ) (Set.Ioo 0 (π / 2)) :=
    (hF.curry_θ hs).continuousOn
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * F s θ / s)
      (volume.restrict Work.Spaces.Iθ) :=
    aesm_Icc_of_continuousOn_Ioo ((hcontK.continuousOn.mul hslice).div_const s)
  have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ :=
    hmem.1 s hs.le
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hdom : IntegrableOn
      (fun θ => Wlam s * (3 * (1 + Work.Spaces.HkIntegrand α 4 F s θ) / 2)) Work.Spaces.Iθ := by
    have h1 : IntegrableOn
        (fun θ => (Wlam s * (3 / 2)) * (1 + Work.Spaces.HkIntegrand α 4 F s θ)) Work.Spaces.Iθ :=
      (hconst.add hHk).const_mul _
    refine h1.congr_fun (fun θ _ => ?_) hIθ
    ring
  refine hdom.mono' haesm ?_
  rw [ae_restrict_iff' hIθ]
  exact Eventually.of_forall fun θ hθ => by
    rw [Real.norm_eq_abs]
    exact abs_K_mul_F_div_s_le (α := α) hs hθ

/-! ## The `L₁₂`-density is integrable

The density is the parametric integral `s ↦ ∫_θ K θ · F s θ / s`, so its a.e. strong
measurability comes from the joint continuity of the integrand on the open quadrant
(`Work.Spaces.aesm_of_continuousOn_Qd` + Fubini measurability of the partial integral), and
its integrability from the pointwise bound `cc.abs_L12dens_le` together with AM–GM against the
two square-integrable factors `Wlam` and `s ↦ √(∫_θ HkIntegrand α 4 F s θ)`. -/

/-- A.e. strong measurability of the `L₁₂`-density on `(0,∞)` for data smooth on the open
quadrant. -/
theorem aesm_L12dens_of_SmoothOpen {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    AEStronglyMeasurable (Work.Construction.L12dens F) (volume.restrict (Set.Ioi 0)) := by
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hF.continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hcontK.comp continuous_snd).continuousOn
  have hdiv : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hK.mul hFc).div continuousOn_fst (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1) hdiv
  have h := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
  have h3 : AEStronglyMeasurable (Work.Construction.L12dens F) (volume.restrict Work.Spaces.Iz) := by
    convert h using 1
    funext z
    rfl
  have hset : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz := MeasureTheory.Ioi_ae_eq_Ici
  rw [MeasureTheory.Measure.restrict_congr_set hset]
  exact h3

/-- **The `L₁₂`-density of an `ℋ⁴`-datum is integrable on `(0,∞)`.** -/
theorem integrableOn_L12dens_of_SmoothOpen_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 4 F) :
    IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := by
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hH_int : IntegrableOn H (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hH_int.aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) :=
    hH_int.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.div continuousOn_id ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro s hs
        have h1 : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs]
        exact pow_ne_zero 2 (ne_of_gt h1)
    exact (show ContinuousOn Wlam (Set.Ioi 0) from hc).aestronglyMeasurable measurableSet_Ioi
  have hWlam2_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlamA_int : IntegrableOn (fun s => Wlam s * A s) (Set.Ioi 0) := by
    refine (hWlam2_int.add hA2_int).mono' (hWlam_aesm.mul hA_aesm) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have h1 : 0 ≤ Wlam s := Wlam_nonneg hs.le
    have h2 : 0 ≤ A s := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2), Pi.add_apply]
    nlinarith [sq_nonneg (Wlam s - A s)]
  have hbd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      ‖Work.Construction.L12dens F s‖ ≤ BK * (Wlam s * A s) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := abs_L12dens_le α F hmem hs
    rw [Real.norm_eq_abs]
    calc |Work.Construction.L12dens F s| ≤ Wlam s * (BK * A s) := by
          simpa only [hA, hH] using hb
      _ = BK * (Wlam s * A s) := by ring
  exact (hWlamA_int.const_mul BK).mono' (aesm_L12dens_of_SmoothOpen hF) hbd

/-! ## The theorem -/

/-- Route.  Instantiate `Work.FTS.LocData.L12_add_mul` (with `c = 0`, `z = 0`) and derive its
four integrability inputs from `HkMem`:

* the θ-slice `θ ↦ K θ · h s θ / s` is `Wlam s • (θ ↦ K θ · Sw θ · Gaz h s θ)` and
  `|K θ Sw θ Gaz h s θ| ≤ |K θ Sw θ| · sqrt (HkIntegrand α 4 h s θ)`
  (`Work.FTS.GalBasis.cc.abs_Gaz_le_sqrt_HkIntegrand`), so Cauchy–Schwarz in θ with
  `K·Sw ∈ L²(Iθ)` (it is continuous) and `HkIntegrand α 4 h s · ∈ L¹(Iθ)` (`HkMem.1`) gives both
  the bound of `cc.abs_integral_K_S_Gaz_le` and the `L¹`-property of the slice;
* the density bound is `cc.abs_L12dens_le`, and its majorant `Wlam s · BK · sqrt(∫_θ HkIntegrand)`
  is `L¹((0,∞))` because `Wlam ∈ L²((0,∞))` and `s ↦ ∫_θ HkIntegrand α 4 h s θ ∈ L¹(Iz)`
  (`HkMem.2`), so `cc.integral_abs_L12dens_le` gives the density integrability (and also the
  `AEStronglyMeasurable` needed for `IntegrableOn`: the slices are continuous on the open
  quadrant, and the boundary lines are null).

`SmoothOpen` is used exactly for that a.e. strong measurability of the slices/densities. -/
theorem L12_add_of_HkMem {α : ℝ} {a b : Work.FTS.Galerkin.Fn}
    (hsa : Work.FTS.EllipticEst.SmoothOpen a) (hsb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    Work.Construction.L12 (fun z θ => a z θ + b z θ) 0
      = Work.Construction.L12 a 0 + Work.Construction.L12 b 0 :=
  (Work.FTS.LocData.L12_add_mul (c := 0) (z := 0)
    (fun s hs => integrableOn_slice_of_SmoothOpen_HkMem hsa hma hs)
    (fun s hs => integrableOn_slice_of_SmoothOpen_HkMem hsb hmb hs)
    (integrableOn_L12dens_of_SmoothOpen_HkMem hsa hma)
    (integrableOn_L12dens_of_SmoothOpen_HkMem hsb hmb)).1

end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.LocData.HkIntegrand_hLoc_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.FTS.LocData.HkIntegrand_hLoc_le` — the bump `hLoc` lies in `𝓗⁴` with a decaying weight

The localised bump `hLoc α z θ = φ(z)·Γ(θ)` (`φ = bumpZ = χ(4·-5)`, `Γ(θ) = (sinθcos²θ)^{α/3}`)
is the perturbation datum of the route.  This module proves the pointwise estimate

  `HkIntegrand α 4 (hLoc α) z θ ≤ K² · angMaj α θ / (1+z)²`   on `[0,∞) × [0,π/2]`,

with `K` depending only on `α ∈ (0,1]` — in fact only on the universal constant bounding the
`D_z`-iterates of the radial bump.

The argument is a term-by-term estimate of the finite sum defining `HkIntegrand`:

* `HlocFactor` separates every derivative, `D_z^j D_θ^i (φ·Γ) = (D_θ^i Γ)(0,·)·(T1^[j] φ)`;
* the radial factor is bounded by the universal constant `Cb` of `DzIter_bumpZ_bound`;
* the angular factor of the second block is bounded by `100000·Γ` (`DthIter_Gam_abs_le`) and
  `|Γ| ≤ 1` (`Gam_bounds`);
* the weight `w = (1+z)²/z²`, `w_θ = sin(2θ)^{-γ/2}` contribute exactly `w²·sin^{-η}`, resp.
  `w²·sin^{-γ}`, and the two angular weights are the two summands of `angMaj`;
* the factor `w(z)²` is absorbed into `1/(1+z)²` on the support `[3/4,7/4]` of the bump
  (`w_sq_le_on_support`), while off the support the integrand vanishes
  (`HkIntegrand_hLoc_eq_zero_off`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

/-! ## Elementary facts -/

/-- `sin(2θ) ≥ 0` on the angular interval. -/
private theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_mem_Icc
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `∑_{i<5} c = 5c`. -/
private theorem sum_range_five_const (c : ℝ) : (∑ _i ∈ Finset.range 5, c) = 5 * c := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num

/-! ## The two termwise bounds -/

/-- **The `D_z`-block of `HkIntegrand α 4 (hLoc α)`.**  The angular factor contributes `Γ²`, the
radial factor `(T1^[i] φ)² ≤ Cb²`, and the weight `w²·sin^{-η}`. -/
private theorem hLoc_term1_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (Cb : ℝ)
    (hCb : ∀ c ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ| ≤ Cb)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi : i ≤ 4) :
    (Work.Spaces.DzIter i (hLoc α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Cb ^ 2 * (Work.Spaces.w z) ^ 2
        * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hP : ((T1^[i]) bumpZ z) ^ 2 ≤ Cb ^ 2 := by
    have h := hCb i hi z hz θ
    rw [DzIter_bumpZ_eq i θ z] at h
    have h2 := pow_le_pow_left₀ (abs_nonneg ((T1^[i]) bumpZ z)) h 2
    simpa only [sq_abs] using h2
  have hw : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
      congr 1
      ring
    rw [div_eq_mul_inv, mul_pow, inv_pow, h1, ← Real.rpow_neg hs0]
  have hws : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  rw [congrFun (congrFun (DzIter_hLoc α i) z) θ]
  calc ((Work.Spaces.Gam α θ * (T1^[i]) bumpZ z)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((T1^[i]) bumpZ z) ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
    _ ≤ Cb ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [hw]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP (sq_nonneg _)) hws
    _ = Cb ^ 2 * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring

/-- **The mixed block of `HkIntegrand α 4 (hLoc α)`.**  The angular factor contributes at most
`(100000·Γ)²`, the radial factor `(T1^[j] φ)² ≤ Cb²`, and the weight `W = w·sin^{-γ/2}` gives
`w²·sin^{-γ}`. -/
private theorem hLoc_term2_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (Cb : ℝ)
    (hCb : ∀ c ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ| ≤ Cb)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {j i : ℕ}
    (hi : i ≤ 4) (hj : j ≤ 4) :
    (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2
        * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hA0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hAabs : |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * Work.Spaces.Gam α θ := DthIter_Gam_abs_le i hi α hα hα1 hθ
  have hA : (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10 : ℝ) ^ 10 * Work.Spaces.Gam α θ ^ 2 := by
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hAabs 2
    rw [sq_abs, mul_pow] at h2
    have h10 : ((100000 : ℝ)) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
    calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ (100000 : ℝ) ^ 2 * Work.Spaces.Gam α θ ^ 2 := h2
      _ = (10 : ℝ) ^ 10 * Work.Spaces.Gam α θ ^ 2 := by rw [h10]
  have hP : ((T1^[j]) bumpZ z) ^ 2 ≤ Cb ^ 2 := by
    have h := hCb j hj z hz θ
    rw [DzIter_bumpZ_eq j θ z] at h
    have h2 := pow_le_pow_left₀ (abs_nonneg ((T1^[j]) bumpZ z)) h 2
    simpa only [sq_abs] using h2
  have hWt : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
      congr 1
      ring
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h1]
  have hws : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  rw [congrFun (congrFun (mixed_hLoc α j i) z) θ]
  calc ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * (T1^[j]) bumpZ z)
        * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          * ((T1^[j]) bumpZ z) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ ((10 : ℝ) ^ 10 * Work.Spaces.Gam α θ ^ 2) * Cb ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [hWt]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hA hP (sq_nonneg _) (by positivity)) hws
    _ = (10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring

/-! ## The pointwise bound against the weight `w²` -/

/-- **The pointwise bound**: on the whole quadrant, `HkIntegrand α 4 (hLoc α) ≤ K·w²·angMaj`,
where `K = (5 + 25·10^10)·Cb²` counts the `5` terms of the `D_z`-block and the at most `25`
terms of the mixed block, and where `Cb` bounds the `D_z`-iterates of the radial bump. -/
private theorem hLoc_HkIntegrand_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (Cb : ℝ)
    (hCb : ∀ c ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ| ≤ Cb)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (hLoc α) z θ
      ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hCb2 : 0 ≤ Cb ^ 2 := sq_nonneg Cb
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hAng : angMaj α θ = Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1 :=
    angMaj_apply α θ
  have hB0 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  have hE0 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  set Bv := Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) with hBdef
  set Ev := Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hEdef
  have hAng' : angMaj α θ = Bv + Ev + 1 := by rw [hAng, hBdef, hEdef]
  have hBle : Bv ≤ angMaj α θ := by rw [hAng']; linarith [hE0]
  have hEle : Ev ≤ angMaj α θ := by rw [hAng']; linarith [hB0]
  have hsum1 : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (hLoc α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := by
    calc (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (hLoc α) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, (Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Ev) :=
          Finset.sum_le_sum (fun i hi => by
            rw [hEdef]
            exact hLoc_term1_le α hα hα1 Cb hCb hz hθ
              (by have h5 : i < 5 := Finset.mem_range.mp hi; omega))
      _ = 5 * (Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Ev) := sum_range_five_const _
      _ ≤ 5 * (Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEle (mul_nonneg hCb2 hw2))
            (by norm_num)
      _ = 5 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := by ring
  have hsum2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 25 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv) := by
    have hT : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]
        rw [hBdef]
        exact hLoc_term2_le α hα hα1 Cb hCb hz hθ
          (by have h5 : i < 5 := Finset.mem_range.mp hi; omega)
          (by have h5 : j < 5 := Finset.mem_range.mp hj; omega)
      · rw [if_neg hc]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCb2) hw2) hB0
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
            ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hT i hi))
      _ = 25 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv) := by
          have h1 : (∑ i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
                ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv))
              = ∑ _i ∈ Finset.range 5,
                (5 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv)) :=
            Finset.sum_congr rfl (fun i _ => sum_range_five_const _)
          rw [h1, sum_range_five_const]
          ring
  have hHk : Work.Spaces.HkIntegrand α 4 (hLoc α) z θ
      = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (hLoc α) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  calc Work.Spaces.HkIntegrand α 4 (hLoc α) z θ
      = _ := hHk
    _ ≤ 5 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ
          + 25 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv) :=
        add_le_add hsum1 hsum2
    _ ≤ 5 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ
          + 25 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ) := by
        refine add_le_add le_rfl ?_
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBle (by positivity))
          (by norm_num)
    _ = (5 + 25 * 10 ^ 10) * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := by ring

/-! ## The main estimate -/

theorem HkIntegrand_hLoc_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨Cb, hCb⟩ := DzIter_bumpZ_bound
  refine ⟨(5 + 25 * 10 ^ 10) * Cb ^ 2 * (1771561 / 1296 : ℝ) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2 * (1771561 / 1296 : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cb)) (by norm_num)
    linarith
  · intro z hz θ hθ
    have hA0 : 0 ≤ angMaj α θ := angMaj_nonneg hθ
    have hden : 0 ≤ (1 + z) ^ 2 := sq_nonneg _
    have hmain := hLoc_HkIntegrand_le α hα hα1 Cb hCb hz hθ
    by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
    · have hw := w_sq_le_on_support hsupp
      have hK0 : 0 ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg Cb)
      have hstep : (5 + 25 * 10 ^ 10) * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ
          ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2
              * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) * angMaj α θ := by
        refine mul_le_mul_of_nonneg_right ?_ hA0
        exact mul_le_mul_of_nonneg_left hw hK0
      set x := (5 + 25 * 10 ^ 10) * Cb ^ 2 * (1771561 / 1296 : ℝ) with hxdef
      have hx0 : 0 ≤ x := by
        rw [hxdef]
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cb)) (by norm_num)
      have hKle : x ≤ (x + 1) ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
      calc Work.Spaces.HkIntegrand α 4 (hLoc α) z θ
          ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := hmain
        _ ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2
              * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) * angMaj α θ := hstep
        _ = x * angMaj α θ / (1 + z) ^ 2 := by rw [hxdef]; ring
        _ ≤ (x + 1) ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ hden
            exact mul_le_mul_of_nonneg_right hKle hA0
    · have hzero : Work.Spaces.HkIntegrand α 4 (hLoc α) z θ = 0 :=
        HkIntegrand_hLoc_eq_zero_off hsupp θ
      rw [hzero]
      exact div_nonneg (mul_nonneg (sq_nonneg _) hA0) hden

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.ZfarFstar.ZFBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData
namespace ZFBase

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary angular facts -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## 2. `D_θ` of a product with a `z`-only factor -/

/-- `D_θ` is a derivation which, on a product `c(z)·g(z,θ)` with a factor depending only on `z`,
acts on the second factor only. -/
theorem DthIter_mul_left_z (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-! ## 3. `z`-slice smoothness -/

theorem contDiffOn_slice_oneSubChi (L : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 1 - Work.Stability.chi (z / L)) (Set.Ioi (-1)) :=
  (contDiff_const.sub (Work.Stability.chi_contDiff.comp (contDiff_id.div_const L))).contDiffOn

theorem contDiffOn_slice_FM_Fstar :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden
    (fun z hz => pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
  have hfun : (fun z : ℝ => Work.FM.Fstar z)
      = ((fun z : ℝ => 2 * z) / fun z : ℝ => (1 + z) ^ 2) := by
    funext z
    simp [Work.FM.Fstar, Pi.div_apply]
  rw [hfun]
  exact h

theorem contDiffOn_slice_Fstar (α : ℝ) (θ : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.Construction.Fstar α z θ)
      (Set.Ioi (-1)) := by
  have h := contDiffOn_slice_FM_Fstar.const_smul (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
  refine h.congr (fun z _ => ?_)
  rw [Work.Construction.Fstar]
  ring

/-- The `z`-slices of `D_θ^i F_*` are smooth: `D_θ^i F_* = (α/c)·D_θ^iΓ(0,θ)·φ(z)` with
`φ = FM.Fstar` a function of `z` only. -/
theorem contDiffOn_slice_DthIter_Fstar (α : ℝ) (i : ℕ) (θ : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Spaces.DthIter i (Work.Construction.Fstar α) z θ) (Set.Ioi (-1)) := by
  have hfun : (fun z : ℝ => Work.Spaces.DthIter i (Work.Construction.Fstar α) z θ)
      = fun z : ℝ => ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) * Work.FM.Fstar z := by
    funext z
    rw [congrFun (congrFun (DthIter_Fstar_eq α i) z) θ, DthIter_gamFn_z_indep α i z 0 θ]
    ring
  rw [hfun]
  have h := contDiffOn_slice_FM_Fstar.const_smul ((α / Work.Spaces.c α)
    * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
  simpa [smul_eq_mul] using h

/-! ## 4. The uniform bound on the derivatives of the cut-off factor

The iterated `D_z`-derivatives of `1 - χ(·/L)` are bounded by a constant *independent of `L`*:
by the Stirling expansion `D_z^c = ∑_k S(c,k) (z/L)^k ∂^k(·/L)` the derivatives of the
rescaled cut-off reduce to `(z/L)^k ∂^k(1-χ)(z/L)`, and those are bounded uniformly by
`OneSubChi_deriv_bound` of `Work.FTS.LocData.DzIter_oneSubChi_bound`. -/

theorem DzIter_oneSubChi_bound_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L → ∀ (c : ℕ), c ≤ 4 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ C := by
  obtain ⟨M, hM0, hMb⟩ := OneSubChi_deriv_bound
  have hM1 : 1 ≤ M := by
    have h := hMb 0 (by norm_num) (2 : ℝ)
    have h2 : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (2 : ℝ) = 1 := by
      rw [iteratedDeriv_zero, Work.Stability.chi_eq_zero (by norm_num)]
      norm_num
    simpa [h2] using h
  refine ⟨100 * M, by linarith, fun L hL c hc z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hsmg : ContDiff ℝ Work.Stability.smoothOrder (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have hsmL : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) :=
    hsmg.comp (contDiff_id.div_const L)
  -- 1. the θ-independent function is a `z`-only multiplier
  have h1 : Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ
      = Work.Coercivity.CommutZ.DzIterZ c
          (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z := by
    have h := congrFun (congrFun (Work.Coercivity.CommutZ.DzIter_mulZ c
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))) z) θ
    have hfun : Work.Coercivity.CommutZ.mulZ (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))
        = (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) := rfl
    rw [hfun] at h
    simpa only [Work.Coercivity.CommutZ.mulZ_apply] using h
  rw [h1]
  -- 2. the Stirling expansion
  have h2 : Work.Coercivity.CommutZ.DzIterZ c
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
      = ∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
          (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) := by
    simpa only [] using congrFun (DzIterZ_eq_sum_scoef
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) hsmL c) z
  rw [h2]
  -- 3. each summand is bounded by `M`
  have hb : ∀ k ≤ c, |z ^ k * iteratedDeriv k
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z| ≤ M := by
    intro k hk
    have hk4 : k ≤ 4 := le_trans hk hc
    have hrew : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
        = (L⁻¹) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) :=
      IteratedDeriv_comp_div (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) hsmg hLne k z
    have hzL : z ^ k * ((L⁻¹) ^ k *
          iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L))
        = (z / L) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) := by
      have hdiv : z / L = z * L⁻¹ := by rw [div_eq_mul_inv]
      rw [hdiv, mul_pow]
      ring
    rw [hrew, hzL]
    exact hMb k hk4 (z / L)
  have hsum := Work.Spaces.abs_sum_scoef_mul_le c M
    (fun k => z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) hb
  have hbell : (Work.Spaces.bell c : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le c hc
  calc |∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
        (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z)|
      ≤ (Work.Spaces.bell c : ℝ) * M := hsum
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right hbell hM0

/-! ## 5. The weighted derivatives of the profile -/

/-- `|D_z^a F_* · w| ≤ 4αΓ/z` for `z ≥ 1`, `a ≤ 4`: `D_z^a F_* = (α/c)Γ·Φ_a` and
`|w·Φ_a| ≤ 2/z` (`Phi_w_le`), while `(α/c)·2 ≤ 4α` because `1/c ≤ 5/3 ≤ 2` (`c ≥ 3/5`). -/
theorem DzIter_Fstar_w_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} (ha : a ≤ 4)
    {z : ℝ} (hz1 : 1 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DzIter a (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
      ≤ 4 * α * Work.Spaces.Gam α θ / z := by
  have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hz : 0 < z := by linarith
  have hPhi : |Work.Spaces.w z * Phi a z θ| ≤ 2 / z := Phi_w_le a ha hz1 θ
  have heq : Work.Spaces.DzIter a (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * Phi a z θ := by
    rw [congrFun (congrFun (DzIter_Fstar_eq α a) z) θ, PhiZ_eq a ha z θ]
  rw [heq]
  have hsplit : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * Phi a z θ * Work.Spaces.w z
      = ((α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
          * (Work.Spaces.w z * Phi a z θ) := by ring
  rw [hsplit, abs_mul]
  have hA : |(α / Work.Spaces.c α) * Work.Spaces.Gam α θ|
      = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ :=
    abs_of_nonneg (by positivity)
  rw [hA]
  have hmu : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z)
      ≤ 4 * α * Work.Spaces.Gam α θ / z := by
    have hcinv : (Work.Spaces.c α)⁻¹ ≤ 2 := by
      have h2 : (2 : ℝ)⁻¹ ≤ Work.Spaces.c α := by
        rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
        linarith
      exact (inv_le_comm₀ hcpos (by norm_num : (0 : ℝ) < 2)).mpr h2
    have hfact : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z)
        = (α * Work.Spaces.Gam α θ / z) * (2 * (Work.Spaces.c α)⁻¹) := by ring
    have hfact2 : 4 * α * Work.Spaces.Gam α θ / z
        = (α * Work.Spaces.Gam α θ / z) * 4 := by ring
    rw [hfact, hfact2]
    exact mul_le_mul_of_nonneg_left (by linarith [hcinv]) (by positivity)
  calc (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * |Work.Spaces.w z * Phi a z θ|
      ≤ (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z) :=
        mul_le_mul_of_nonneg_left hPhi (by positivity)
    _ ≤ 4 * α * Work.Spaces.Gam α θ / z := hmu

/-- `|D_z^j D_θ^i F_* · w| ≤ 4·10⁵·αΓ/z` for `z ≥ 1`, `i, j ≤ 4`, from
`mixed_Fstar_eq` (`mixed = (α/c)·D_θ^iΓ(0,θ)·Φ_j`), `|D_θ^iΓ| ≤ 10⁵Γ` (`DthIter_Gam_abs_le`)
and `|w·Φ_j| ≤ 2/z`. -/
theorem mixed_Fstar_w_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {a i : ℕ} (ha : a ≤ 4) (hi : i ≤ 4)
    {z : ℝ} (hz1 : 1 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed a i (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
      ≤ 400000 * α * Work.Spaces.Gam α θ / z := by
  have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hz : 0 < z := by linarith
  have hPhi : |Work.Spaces.w z * Phi a z θ| ≤ 2 / z := Phi_w_le a ha hz1 θ
  have hGam : |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * Work.Spaces.Gam α θ := DthIter_Gam_abs_le i hi α hα hα1 hθ
  have heq : Work.Spaces.mixed a i (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * Phi a z θ := by
    rw [congrFun (congrFun (mixed_Fstar_eq α i a) z) θ, PhiZ_eq a ha z θ]
  rw [heq]
  have hsplit : (α / Work.Spaces.c α)
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * Phi a z θ
        * Work.Spaces.w z
      = ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
        * (Work.Spaces.w z * Phi a z θ) := by ring
  rw [hsplit, abs_mul]
  have hA : |(α / Work.Spaces.c α)
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ (α / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hGam (by positivity)
  refine le_trans (mul_le_mul hA hPhi (abs_nonneg _) (by positivity)) ?_
  have hcinv : (Work.Spaces.c α)⁻¹ ≤ 2 := by
    have h2 : (2 : ℝ)⁻¹ ≤ Work.Spaces.c α := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      linarith
    exact (inv_le_comm₀ hcpos (by norm_num : (0 : ℝ) < 2)).mpr h2
  have hfact : (α / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) * (2 / z)
      = (α * Work.Spaces.Gam α θ / z) * (200000 * (Work.Spaces.c α)⁻¹) := by ring
  have hfact2 : 400000 * α * Work.Spaces.Gam α θ / z
      = (α * Work.Spaces.Gam α θ / z) * 400000 := by ring
  rw [hfact, hfact2]
  exact mul_le_mul_of_nonneg_left (by linarith [hcinv]) (by positivity)

/-! ## 6. Functions vanishing on a neighbourhood have vanishing `D`-derivatives

Below the cut-off (`z < L`) the far part `zfar L F_*` vanishes identically on a whole
neighbourhood of `z`, so every `D`-derivative of it vanishes at `z` as well — this is what
rescues the estimates there, where the radial weight `w(z) = (1+z)²/z²` blows up. -/

/-- `D_θ^i` of a function vanishing on a neighbourhood of `z` (in the `z`-variable, uniformly
in `θ`) vanishes there too. -/
theorem eventDthIter_zero {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) (i : ℕ) :
    ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, Work.Spaces.DthIter i f z' θ' = 0 := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rcases mem_nhds_iff.mp ih with ⟨U, hU, hUopen, hzU⟩
      filter_upwards [hUopen.mem_nhds hzU] with z' hz'
      intro θ'
      have hfun : (fun t : ℝ => Work.Spaces.DthIter i f z' t) = fun _ : ℝ => (0 : ℝ) :=
        funext (fun t => hU hz' t)
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [hfun, deriv_const, mul_zero]

/-- `D_z^i` of a function vanishing on a neighbourhood of `z` (uniformly in `θ`) vanishes
there too. -/
theorem eventDzIter_zero {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) (i : ℕ) :
    ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, Work.Spaces.DzIter i f z' θ' = 0 := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rcases mem_nhds_iff.mp ih with ⟨U, hU, hUopen, hzU⟩
      filter_upwards [hUopen.mem_nhds hzU] with z' hz'
      intro θ'
      have hev : (fun w : ℝ => Work.Spaces.DzIter i f w θ') =ᶠ[𝓝 z'] fun _ : ℝ => (0 : ℝ) :=
        Filter.eventually_of_mem (hUopen.mem_nhds hz') (fun w hw => hU hw θ')
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hev.deriv_eq, deriv_const, mul_zero]

/-- Every `D_z`-iterate of such a function vanishes at `z`. -/
theorem DzIter_eq_zero_of_eventually_zero {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) (i : ℕ) :
    Work.Spaces.DzIter i f z θ = 0 :=
  Filter.EventuallyEq.eq_of_nhds ((eventDzIter_zero h i).mono (fun z' hz' => hz' θ))

/-- Every mixed `D`-iterate of such a function vanishes at `z`. -/
theorem mixed_eq_zero_of_eventually_zero {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) (j i : ℕ) :
    Work.Spaces.mixed j i f z θ = 0 :=
  DzIter_eq_zero_of_eventually_zero (eventDthIter_zero h i) j

/-- The whole `ℋ^k`-integrand of such a function vanishes at `z`. -/
theorem HkIntegrand_eq_zero_of_eventually_zero {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have hD : ∀ i : ℕ, Work.Spaces.DzIter i f z θ = 0 :=
    fun i => DzIter_eq_zero_of_eventually_zero h i
  have hM : ∀ j i : ℕ, Work.Spaces.mixed j i f z θ = 0 :=
    fun j i => mixed_eq_zero_of_eventually_zero h j i
  rw [Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hD i]
    ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, hM j i]
      ring
    · rw [if_neg hc]
  rw [h1, h2, add_zero]

/-- The far part `zfar L F_*` vanishes identically on a neighbourhood of `z` whenever
`z < L` (`χ(z'/L) = 1` for `|z'| < L`). -/
theorem zfar_eventually_zero {α L z : ℝ} (hL : 0 < L) (hz0 : 0 ≤ z) (hz : z < L) :
    ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      Work.Stability.zfar L (Work.Construction.Fstar α) z' θ' = 0 := by
  have hzabs : |z| < L := by rw [abs_of_nonneg hz0]; exact hz
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hzabs] with z' hz'
  intro θ'
  have h1 : |z' / L| ≤ 1 := by
    rw [abs_div, abs_of_pos hL, div_le_one hL]
    exact le_of_lt hz'
  rw [Work.Stability.zfar_apply, Work.Stability.chi_eq_one h1]
  ring

end ZFBase
end Work.FTS.LocData
end
end
