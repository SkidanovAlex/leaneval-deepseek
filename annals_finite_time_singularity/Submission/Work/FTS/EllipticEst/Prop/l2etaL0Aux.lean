/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`0` (`η`-weighted) estimate: the auxiliary lemmas of the assembly

This is a verbatim copy (fresh namespace) of the auxiliary lemmas of
`Submission/Work/FTS/EllipticEst/TT/l2eta_weak.lean` (lines 89--242), which is the assembly of
the level-`0` estimate from the three analytic first-order steps.  The copy is needed because
the original module is above the build guard's per-file size limit; the assembly itself is in
`Prop/l2etaL0Asm.lean`.-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option maxHeartbeats 1000000

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.L0

set_option autoImplicit false

/-- **The `k = 0` shape of `HkSq`.**  At level `0` the mixed-derivative sum of `HkIntegrand` is
empty, so `HkSq α 0 g` is exactly the square of the `L²`-norm of
`g·w(z)/sin(2θ)^{η/2}`; this is the norm in which the `ℋ⁰`-integrals of the target are stated. -/
theorem HkSq_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
    Finset.sum_singleton]
  norm_num

/-- The same identity in `HkIntegrand` form, for rewriting integrands pointwise. -/
theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
    Finset.sum_singleton]
  norm_num

/-- **The level-`0` integrand vanishes on the boundary of the domain**: at `z = 0` (where
`w 0 = 0`) and at `θ = 0`, `θ = π/2` (where `sin(2θ) = 0`, so the weight `1/0 = 0`). -/
theorem HkIntegrand_zero_boundary (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) : Work.Spaces.HkIntegrand α 0 g z θ = 0 := by
  rcases h with h | h | h
  · subst h
    rw [HkIntegrand_zero_eq]
    have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · subst h
    rw [HkIntegrand_zero_eq]
    have h2 : 2 * (0 : ℝ) = 0 := by norm_num
    rw [h2, Real.sin_zero]
    have hz : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)
    rw [hz, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · subst h
    rw [HkIntegrand_zero_eq]
    have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [h2, Real.sin_pi]
    have hz : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)
    rw [hz, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- **Homogeneity of the level-`0` integrand** under multiplication by a constant. -/
theorem HkIntegrand_zero_const_mul (α c : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (fun z θ => c * g z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 0 g z θ := by
  rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq]
  ring

/-- **Homogeneity of `HkSq α 0`** under multiplication by a constant. -/
theorem HkSq_zero_const_mul (α c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (fun z θ => c * g z θ) = c ^ 2 * Work.Spaces.HkSq α 0 g := by
  rw [HkSq_zero_eq, HkSq_zero_eq]
  rw [show (fun z => ∫ θ in Work.Spaces.Iθ, (c * g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [← MeasureTheory.integral_const_mul]

/-- **`HkMem` is closed under multiplication by a constant** at level `0`. -/
theorem HkMem_zero_const_mul (α c : ℝ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 0 f) :
    Work.Spaces.HkMem α 0 (fun z θ => c * f z θ) := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α 0 (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 0 f z θ := HkIntegrand_zero_const_mul α c f
  constructor
  · intro z hz
    refine MeasureTheory.IntegrableOn.congr_fun ((h.1 z hz).const_mul (c ^ 2)) ?_
      measurableSet_Icc
    exact fun θ _ => (hpt z θ).symm
  · have h2 : MeasureTheory.IntegrableOn
        (fun z => c ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ))
        Work.Spaces.Iz := h.2.const_mul (c ^ 2)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z _
    show c ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (fun z θ => c * f z θ) z θ
    rw [← MeasureTheory.integral_const_mul]
    exact (MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => hpt z θ)).symm

/-- **Monotonicity of `HkSq α 0` under a pointwise domination of its integrand** by an arbitrary
majorant `M` (the majorant need not itself be an `HkIntegrand`); only the honesty of the majorant
is required. -/
theorem HkSq_zero_le_of_integrand_le (α : ℝ) {f M : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f)
    (hMθ : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 f z θ ≤ M z θ) :
    Work.Spaces.HkSq α 0 f ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, M z θ := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_mono_on hf.2 hMz measurableSet_Ici fun z hz => ?_
  exact MeasureTheory.setIntegral_mono_on (hf.1 z hz) (hMθ z hz) measurableSet_Icc
    (fun θ hθ => h z hz θ hθ)

/-- The elementary five-term Cauchy–Schwarz bound. -/
theorem sum_five_sq_le (x1 x2 x3 x4 x5 : ℝ) :
    (x1 + x2 + x3 + x4 + x5) ^ 2 ≤ 5 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2) := by
  nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4), sq_nonneg (x1 - x5),
    sq_nonneg (x2 - x3), sq_nonneg (x2 - x4), sq_nonneg (x2 - x5), sq_nonneg (x3 - x4),
    sq_nonneg (x3 - x5), sq_nonneg (x4 - x5)]

/-- The square-root form of `sum_five_sq_le`. -/
theorem sqrt_sum_five_le {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) :
    Real.sqrt (a + b + c + d + e)
      ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d + Real.sqrt e := by
  have h0 : 0 ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d + Real.sqrt e := by
    have := Real.sqrt_nonneg a; have := Real.sqrt_nonneg b; have := Real.sqrt_nonneg c
    have := Real.sqrt_nonneg d; have := Real.sqrt_nonneg e
    linarith
  rw [Real.sqrt_le_left h0]
  have ha' := Real.sq_sqrt ha
  have hb' := Real.sq_sqrt hb
  have hc' := Real.sq_sqrt hc
  have hd' := Real.sq_sqrt hd
  have he' := Real.sq_sqrt he
  have hab := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hac := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c)
  have had := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg d)
  have hae := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg e)
  have hbc := mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)
  have hbd := mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg d)
  have hbe := mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg e)
  have hcd := mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg d)
  have hce := mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg e)
  have hde := mul_nonneg (Real.sqrt_nonneg d) (Real.sqrt_nonneg e)
  nlinarith [sq_nonneg (Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d + Real.sqrt e)]

/-- Linearity of the set integral over a five-term sum of integrable functions. -/
theorem integral_five_eq {s : Set ℝ} {f1 f2 f3 f4 f5 : ℝ → ℝ}
    (h1 : MeasureTheory.IntegrableOn f1 s)
    (h2 : MeasureTheory.IntegrableOn f2 s)
    (h3 : MeasureTheory.IntegrableOn f3 s)
    (h4 : MeasureTheory.IntegrableOn f4 s)
    (h5 : MeasureTheory.IntegrableOn f5 s) :
    (∫ θ in s, f1 θ + f2 θ + f3 θ + f4 θ + f5 θ)
      = ((∫ θ in s, f1 θ) + (∫ θ in s, f2 θ)
          + (∫ θ in s, f3 θ) + (∫ θ in s, f4 θ)
          + (∫ θ in s, f5 θ)) := by
  rw [MeasureTheory.integral_add (f := fun θ => f1 θ + f2 θ + f3 θ + f4 θ) (g := f5)
    (((h1.add h2).add h3).add h4) h5]
  rw [MeasureTheory.integral_add (f := fun θ => f1 θ + f2 θ + f3 θ) (g := f4)
    ((h1.add h2).add h3) h4]
  rw [MeasureTheory.integral_add (f := fun θ => f1 θ + f2 θ) (g := f3) (h1.add h2) h3]
  rw [MeasureTheory.integral_add (f := f1) (g := f2) h1 h2]

end Work.FTS.EllipticEst.Prop.L0
