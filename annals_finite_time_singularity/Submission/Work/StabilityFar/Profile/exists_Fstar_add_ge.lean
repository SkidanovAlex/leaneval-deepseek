import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaPoincareDefs =====
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

/-- The `i`-th iterate of the angular operator `L = D_θ = sin(2θ) ∂_θ` acting on a
one-dimensional slice `u : ℝ → ℝ`. -/
def LopIter (i : ℕ) (u : ℝ → ℝ) : ℝ → ℝ := (Work.Spaces.Lop^[i]) u

/-- `u` is smooth on an open neighbourhood of the closed angular interval `Iθ`. -/
def SliceSmooth (u : ℝ → ℝ) : Prop := ContDiffOn ℝ ⊤ u (Set.Ioo (-1) (Real.pi / 2 + 1))

/-- The angular weight `sin(2θ)^{-η}` of the first sum of the `H^k`-norm. -/
def thEta (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The angular weight `sin(2θ)^{-γ}` of the mixed sum of the `H^k`-norm. -/
def thGam (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The second angular derivative `u''` of a slice. -/
def sliceV (u : ℝ → ℝ) : ℝ → ℝ := deriv (deriv u)



@[simp] theorem LopIter_zero (u : ℝ → ℝ) : LopIter 0 u = u := rfl
@[simp] theorem LopIter_succ (i : ℕ) (u : ℝ → ℝ) :
    LopIter (i + 1) u = Work.Spaces.Lop (LopIter i u) :=
  Function.iterate_succ_apply' Work.Spaces.Lop i u

/-! ## Elementary properties of `sin (2θ)` on `Iθ` -/

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- On `Iθ` the function `sin(2θ)` lies in `[0,1]`, so `θ ↦ sin(2θ)^p` is antitone in the
exponent `p` (for positive exponents; at `sin(2θ) = 0` the value `0^a = 0` for `0 < a`). -/
theorem sin_two_rpow_le_rpow {a b : ℝ} (ha : 0 < a) (hab : b ≤ a) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ a ≤ (Real.sin (2 * θ)) ^ b := by
  have hs0 := sin_two_nonneg hθ
  have hs1 := sin_two_le_one θ
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt ha)]
    exact Real.rpow_nonneg le_rfl b
  · exact Real.rpow_le_rpow_of_exponent_ge h hs1 hab

/-- `sin(2θ) ^ p ≤ 1` on `Iθ` for `p ≥ 0`. -/
theorem sin_two_rpow_le_one {p : ℝ} (hp : 0 ≤ p) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ p ≤ 1 := by
  rcases eq_or_lt_of_le hp with h | h
  · rw [← h, Real.rpow_zero]
  · calc (Real.sin (2 * θ)) ^ p ≤ (Real.sin (2 * θ)) ^ (0 : ℝ) :=
        sin_two_rpow_le_rpow h hp hθ
      _ = 1 := Real.rpow_zero _

/-! ## Positivity and integrability of the weights -/

theorem thEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ thEta θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

theorem thGam_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ thGam α θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

theorem integrableOn_thEta : IntegrableOn thEta Work.Spaces.Iθ ∧
    ∫ θ in Work.Spaces.Iθ, thEta θ ≤ 10000 := by
  have h := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
  have h' : (100 : ℝ) / (-(Work.Spaces.eta) + 1) = 10000 := by
    rw [Work.Spaces.eta]; norm_num
  refine ⟨?_, ?_⟩
  · change IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ
    exact h.1
  · change (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10000
    rw [h'] at h
    exact h.2

theorem integrableOn_sin_two_rpow {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p ≤ Real.pi / 2 := by
  have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ :=
    (Real.continuous_sin.comp_continuousOn
      (continuous_const.mul continuous_id).continuousOn).rpow_const
      (fun θ _ => Or.inr hp)
  refine ⟨hcont.integrableOn_compact isCompact_Icc, ?_⟩
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have h1 : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p)
      ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) := by
    refine integral_mono_of_nonneg ?_ hone ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.rpow_nonneg (sin_two_nonneg hθ) _
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact sin_two_rpow_le_one hp hθ
  have h2 : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Work.Spaces.Iθ,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    simp
  linarith [h1, h2.le]

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular bound `|D_θ^j (c2m)| ≤ 1000 · sin(2θ)²`, `1 ≤ j ≤ 4`

`Work.Construction.c2m θ = cos(2θ) - sin²θ = (3cos(2θ) - 1)/2` is the angular
coefficient multiplying the transport term of the linearised equation, and
`Work.Spaces.dthU = sin(2θ)·∂_θ` is the one-variable angular derivation `D_θ`.

Since `c2m` is a trigonometric polynomial of degree two, every iterate `D_θ^j c2m`
with `j ≥ 1` is `sin(2θ)²` times a polynomial in `cos(2θ)`, hence `O(sin(2θ)²)`.
For the four orders `1 ≤ j ≤ 4` needed here the closed forms are completely
explicit: writing `u = sin(2θ)`, `v = cos(2θ)`,

* `D_θ c2m = -3u²`,
* `D_θ² c2m = -12u²v`,
* `D_θ³ c2m = 24u⁴ - 48u²v²`,
* `D_θ⁴ c2m = 384u⁴v - 192u²v³`,

and each is bounded by `1000·u²` using only `u² + v² = 1` (the crude bounds are
`3`, `12`, `72` and `576`).

The closed forms are obtained by explicit differentiation: `c2m'(θ) = -3 sin(2θ)`,
and each subsequent step differentiates a polynomial in `u` and `v` with
`u' = 2v`, `v' = -2u`, so that `D_θ f = u·f'`.
-/

namespace Work.FTS.Nonlinear.FstarPkg

open scoped Real

/-! ## The derivative of `c2m` -/

/-- `c2m'(θ) = -3·sin(2θ)`, where `c2m θ = cos(2θ) - sin²θ`. -/
lemma dthU_c2m_deriv (θ : ℝ) : deriv Work.Construction.c2m θ = -3 * Real.sin (2 * θ) := by
  have hsub : HasDerivAt (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2)
      (-3 * Real.sin (2 * θ)) θ := by
    have h : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h.cos
    have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
        (2 * (Real.sin θ) ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
    have hfin : HasDerivAt (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2)
        (-Real.sin (2 * θ) * 2 - 2 * (Real.sin θ) ^ (2 - 1) * Real.cos θ) θ := hc.sub hs
    rw [show (-3 * Real.sin (2 * θ))
        = (-Real.sin (2 * θ) * 2 - 2 * (Real.sin θ) ^ (2 - 1) * Real.cos θ) from by
      rw [Real.sin_two_mul]; ring]
    exact hfin
  exact hsub.deriv

/-- The first iterate: `D_θ c2m = -3 sin(2θ)²`. -/
lemma dthU_c2m_eq : Work.Spaces.dthU Work.Construction.c2m
    = fun θ => -(3 : ℝ) * (Real.sin (2 * θ)) ^ 2 := by
  funext θ
  rw [Work.Spaces.dthU_apply, dthU_c2m_deriv θ]
  ring

/-! ## The derivatives of the successive closed forms -/

/-- `(θ ↦ -3 sin(2θ)²)'(θ) = -12 sin(2θ)cos(2θ)`. -/
lemma dthU_c2m_f1_deriv (θ : ℝ) :
    deriv (fun t : ℝ => -(3 : ℝ) * (Real.sin (2 * t)) ^ 2) θ
      = -12 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h.sin
  have hp : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc : HasDerivAt (fun t : ℝ => -(3 : ℝ) * (Real.sin (2 * t)) ^ 2)
      (-(3 : ℝ) * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hp.const_mul (-3)
  rw [hc.deriv]
  ring

/-- The second iterate: `D_θ² c2m = -12 sin(2θ)²cos(2θ)`. -/
lemma dthU_c2m_f1_eq : Work.Spaces.dthU (fun θ => -(3 : ℝ) * (Real.sin (2 * θ)) ^ 2)
    = fun θ => -(12 : ℝ) * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) := by
  funext θ
  rw [Work.Spaces.dthU_apply, dthU_c2m_f1_deriv θ]
  ring

/-- `(θ ↦ -12 sin(2θ)²cos(2θ))'(θ) = -48 sin(2θ)cos(2θ)² + 24 sin(2θ)³`. -/
lemma dthU_c2m_f2_deriv (θ : ℝ) :
    deriv (fun t : ℝ => -(12 : ℝ) * (Real.sin (2 * t)) ^ 2 * Real.cos (2 * t)) θ
      = -48 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 2 + 24 * (Real.sin (2 * θ)) ^ 3 := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h.cos
  have hp : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hm : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2 * Real.cos (2 * t))
      ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * (Real.cos (2 * θ))
        + (Real.sin (2 * θ)) ^ 2 * (-Real.sin (2 * θ) * 2)) θ := hp.mul hc
  have hfin : HasDerivAt (fun t : ℝ => -(12 : ℝ) * ((Real.sin (2 * t)) ^ 2 * Real.cos (2 * t)))
      (-(12 : ℝ) * ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * (Real.cos (2 * θ))
        + (Real.sin (2 * θ)) ^ 2 * (-Real.sin (2 * θ) * 2))) θ := hm.const_mul (-12)
  rw [show (fun t : ℝ => -(12 : ℝ) * (Real.sin (2 * t)) ^ 2 * Real.cos (2 * t))
      = (fun t : ℝ => -(12 : ℝ) * ((Real.sin (2 * t)) ^ 2 * Real.cos (2 * t))) from by
        ext t; ring,
    hfin.deriv]
  ring

/-- The third iterate: `D_θ³ c2m = 24 sin(2θ)⁴ - 48 sin(2θ)²cos(2θ)²`. -/
lemma dthU_c2m_f2_eq :
    Work.Spaces.dthU (fun θ => -(12 : ℝ) * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ))
      = fun θ => (24 : ℝ) * (Real.sin (2 * θ)) ^ 4
          - 48 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2 := by
  funext θ
  rw [Work.Spaces.dthU_apply, dthU_c2m_f2_deriv θ]
  ring

/-- `(θ ↦ 24 sin(2θ)⁴ - 48 sin(2θ)²cos(2θ)²)'(θ) = 384 sin(2θ)³cos(2θ) - 192 sin(2θ)cos(2θ)³`. -/
lemma dthU_c2m_f3_deriv (θ : ℝ) :
    deriv (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4
        - 48 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2) θ
      = 384 * (Real.sin (2 * θ)) ^ 3 * Real.cos (2 * θ)
        - 192 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 3 := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h.cos
  have hp4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hp2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hq2 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 2)
      (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 2
  have hA : HasDerivAt (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4)
      (24 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hp4.const_mul 24
  have hB : HasDerivAt (fun t : ℝ => (48 : ℝ) * ((Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2))
      (48 * ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * (Real.cos (2 * θ)) ^ 2
        + (Real.sin (2 * θ)) ^ 2 * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)))) θ :=
    (hp2.mul hq2).const_mul 48
  have hfin : HasDerivAt (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4
        - 48 * ((Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2))
      (24 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))
        - 48 * ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * (Real.cos (2 * θ)) ^ 2
          + (Real.sin (2 * θ)) ^ 2 * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)))) θ :=
    hA.sub hB
  rw [show (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4
        - 48 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2)
      = (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4
        - 48 * ((Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2)) from by ext t; ring,
    hfin.deriv]
  ring

/-- The fourth iterate: `D_θ⁴ c2m = 384 sin(2θ)⁴cos(2θ) - 192 sin(2θ)²cos(2θ)³`. -/
lemma dthU_c2m_f3_eq :
    Work.Spaces.dthU (fun θ => (24 : ℝ) * (Real.sin (2 * θ)) ^ 4
        - 48 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2)
      = fun θ => (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
          - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3 := by
  funext θ
  rw [Work.Spaces.dthU_apply, dthU_c2m_f3_deriv θ]
  ring

/-! ## The four iterates, as values -/

/-- `D_θ c2m θ = -3 sin(2θ)²`. -/
lemma dthU_c2m_iter_one (θ : ℝ) :
    (Work.Spaces.dthU^[1]) Work.Construction.c2m θ = -(3 : ℝ) * (Real.sin (2 * θ)) ^ 2 := by
  rw [Function.iterate_one, dthU_c2m_eq]

/-- `D_θ² c2m θ = -12 sin(2θ)²cos(2θ)`. -/
lemma dthU_c2m_iter_two (θ : ℝ) :
    (Work.Spaces.dthU^[2]) Work.Construction.c2m θ
      = -(12 : ℝ) * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
    dthU_c2m_eq, dthU_c2m_f1_eq]

/-- `D_θ³ c2m θ = 24 sin(2θ)⁴ - 48 sin(2θ)²cos(2θ)²`. -/
lemma dthU_c2m_iter_three (θ : ℝ) :
    (Work.Spaces.dthU^[3]) Work.Construction.c2m θ
      = (24 : ℝ) * (Real.sin (2 * θ)) ^ 4
        - 48 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
    dthU_c2m_eq, dthU_c2m_f1_eq, dthU_c2m_f2_eq]

/-- `D_θ⁴ c2m θ = 384 sin(2θ)⁴cos(2θ) - 192 sin(2θ)²cos(2θ)³`. -/
lemma dthU_c2m_iter_four (θ : ℝ) :
    (Work.Spaces.dthU^[4]) Work.Construction.c2m θ
      = (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
        - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
    dthU_c2m_eq, dthU_c2m_f1_eq, dthU_c2m_f2_eq, dthU_c2m_f3_eq]

/-! ## The four pointwise bounds -/

/-- `|D_θ c2m θ| ≤ 1000 sin(2θ)²`. -/
lemma dthU_c2m_iter_one_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[1]) Work.Construction.c2m θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_one]
  rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have h3 : |(-(3 : ℝ))| = 3 := by norm_num
  rw [h3]
  nlinarith [sq_nonneg (Real.sin (2 * θ))]

/-- `|D_θ² c2m θ| ≤ 1000 sin(2θ)²`. -/
lemma dthU_c2m_iter_two_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[2]) Work.Construction.c2m θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_two]
  have hv : |Real.cos (2 * θ)| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith [sq_nonneg (Real.sin (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have h12 : |(-(12 : ℝ))| = 12 := by norm_num
  rw [h12]
  nlinarith [sq_nonneg (Real.sin (2 * θ)), hv, abs_nonneg (Real.cos (2 * θ))]

/-- `|D_θ³ c2m θ| ≤ 1000 sin(2θ)²`. -/
lemma dthU_c2m_iter_three_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[3]) Work.Construction.c2m θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_three]
  have hu2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  have hv2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  have hkey : (24 : ℝ) * (Real.sin (2 * θ)) ^ 4 - 48 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
      = (Real.sin (2 * θ)) ^ 2 * (24 * (Real.sin (2 * θ)) ^ 2 - 48 * (Real.cos (2 * θ)) ^ 2) := by
    ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hX : |24 * (Real.sin (2 * θ)) ^ 2 - 48 * (Real.cos (2 * θ)) ^ 2| ≤ 1000 := by
    rw [abs_le]
    constructor <;> nlinarith
  calc (Real.sin (2 * θ)) ^ 2
        * |24 * (Real.sin (2 * θ)) ^ 2 - 48 * (Real.cos (2 * θ)) ^ 2|
      ≤ (Real.sin (2 * θ)) ^ 2 * 1000 := mul_le_mul_of_nonneg_left hX (sq_nonneg _)
    _ = 1000 * (Real.sin (2 * θ)) ^ 2 := by ring

/-- `|D_θ⁴ c2m θ| ≤ 1000 sin(2θ)²`. -/
lemma dthU_c2m_iter_four_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[4]) Work.Construction.c2m θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_four]
  have hu2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  have hkey : (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
        - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      = (Real.sin (2 * θ)) ^ 2
        * (384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) - 192 * (Real.cos (2 * θ)) ^ 3) := by
    ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hv : |Real.cos (2 * θ)| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith [sq_nonneg (Real.sin (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  have hA : |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)| ≤ 384 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
    have h384 : |(384 : ℝ)| = 384 := by norm_num
    rw [h384]
    have hm : (Real.sin (2 * θ)) ^ 2 * |Real.cos (2 * θ)| ≤ 1 := by
      nlinarith [hu2, hv, sq_nonneg (Real.sin (2 * θ)), abs_nonneg (Real.cos (2 * θ))]
    nlinarith [hm, sq_nonneg (Real.sin (2 * θ)), abs_nonneg (Real.cos (2 * θ))]
  have hB : |192 * (Real.cos (2 * θ)) ^ 3| ≤ 192 := by
    rw [abs_mul, abs_pow]
    have h192 : |(192 : ℝ)| = 192 := by norm_num
    rw [h192]
    have hm : |Real.cos (2 * θ)| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hv
    nlinarith [hm, abs_nonneg (Real.cos (2 * θ))]
  have htri : |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) - 192 * (Real.cos (2 * θ)) ^ 3|
      ≤ |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)| + |192 * (Real.cos (2 * θ)) ^ 3| := by
    have h := abs_add_le (384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ))
      (-(192 * (Real.cos (2 * θ)) ^ 3))
    simpa [sub_eq_add_neg] using h
  have hX : |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) - 192 * (Real.cos (2 * θ)) ^ 3|
      ≤ 1000 := by
    linarith
  calc (Real.sin (2 * θ)) ^ 2
        * |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) - 192 * (Real.cos (2 * θ)) ^ 3|
      ≤ (Real.sin (2 * θ)) ^ 2 * 1000 := mul_le_mul_of_nonneg_left hX (sq_nonneg _)
    _ = 1000 * (Real.sin (2 * θ)) ^ 2 := by ring

/-- **The angular bound for the iterated `D_θ`-derivatives of `c2m`.**  For `1 ≤ j ≤ 4`
and every `θ : ℝ`, `|D_θ^j (c2m) θ| ≤ 1000 · sin(2θ)²`. -/
theorem dthU_c2m_bound (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) (θ : ℝ) :
    |(Work.Spaces.dthU^[j] Work.Construction.c2m) θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  interval_cases j
  · exact dthU_c2m_iter_one_bound θ
  · exact dthU_c2m_iter_two_bound θ
  · exact dthU_c2m_iter_three_bound θ
  · exact dthU_c2m_iter_four_bound θ

end Work.FTS.Nonlinear.FstarPkg
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.FK_pointwise_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise `L²(θ)`-bound for the angular moment `FK`

`FK g z = ∫_θ g z θ · K θ` with `K θ = 3 sin θ cos²θ` and `Iθ = [0,π/2]`.  Since
`0 ≤ K θ ≤ 3` on `Iθ` and `|Iθ| = π/2`, Cauchy–Schwarz gives

  `|FK g z| ≤ ‖g z ·‖_{L²(Iθ)} · ‖K‖_{L²(Iθ)} ≤ 3√(π/2) · √(∫_θ (g z θ)²)`,

which is the claimed inequality.  Concretely: `‖∫f‖ ≤ ∫‖f‖`, `|g z θ · K θ| = |g z θ| · K θ` on
`Iθ` (as `K ≥ 0` there), the `L²`-pairing step `|∫ f g| ≤ √(∫f²)·√(∫g²)` is the workspace lemma
`Work.Blocks.IMC.cs_integral_mul_le`, and the kernel factor is bounded by `9·(π/2)` for `∫K²`:
`K² ≤ 9` pointwise on `Iθ` and `∫_{Iθ} 1 = π/2`.

The only measurability input needed for Cauchy–Schwarz is `AEStronglyMeasurable (g z ·)`, and it
does *not* follow from square-integrability alone for a general real function; what follows is
`AEStronglyMeasurable (|g z ·|)`, because `|g z θ| = √((g z θ)²)` is a continuous function of
the square-integrable `(g z ·)²`.  That is enough, since `∫ |g z| · K = ∫ |g z · K|`.

The hypothesis `hint` (integrability of `θ ↦ g z θ · K θ`) is not needed for the estimate itself
— `‖∫f‖ ≤ ∫‖f‖` is unconditional — but it is what makes the statement meaningful: it guarantees
that `FK g z` is the genuine Bochner integral of `g z · K` rather than the junk value `0` of a
non-integrable integral.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools

-- The integrability hypothesis `hint` of `FK_pointwise_le` is part of the requested statement but
-- is not needed for the estimate itself (see the file docstring), whence the linter option.
set_option linter.unusedVariables false

/-- `K(θ) = 3 sin θ cos²θ ≥ 0` on `Iθ`. -/
theorem K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  positivity

/-- `K(θ) = 3 sin θ cos²θ ≤ 3` for every `θ` (hence on `Iθ`). -/
theorem K_le_three (θ : ℝ) : Work.Spaces.K θ ≤ 3 := by
  rw [Work.Spaces.K]
  have h1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have h3 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    simpa using mul_le_mul h1 h2 (sq_nonneg (Real.cos θ)) (by norm_num : (0 : ℝ) ≤ 1)
  calc 3 * Real.sin θ * Real.cos θ ^ 2 = 3 * (Real.sin θ * Real.cos θ ^ 2) := by ring
    _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = 3 := by ring

/-- `K` is continuous. -/
theorem continuous_K : Continuous fun θ : ℝ => Work.Spaces.K θ := by
  unfold Work.Spaces.K
  fun_prop





end Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12_tendsto_of_dominated =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem L12_tendsto_of_dominated {f : ℕ → ℝ → ℝ → ℝ} {g : ℝ → ℝ → ℝ} {M : ℝ → ℝ} {ρ : ℝ}
    (hmeas : ∀ n : ℕ,
      MeasureTheory.AEStronglyMeasurable (fun s => Work.FM.L12dens Work.Spaces.K (f n) s)
        (MeasureTheory.volume.restrict (Set.Ioi ρ)))
    (hconv : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi ρ)),
      Filter.Tendsto (fun n : ℕ => Work.FM.L12dens Work.Spaces.K (f n) s) Filter.atTop
        (nhds (Work.FM.L12dens Work.Spaces.K g s)))
    (hbdd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi ρ)),
      ∀ n : ℕ, ‖Work.FM.L12dens Work.Spaces.K (f n) s‖ ≤ M s)
    (hM : MeasureTheory.Integrable M (MeasureTheory.volume.restrict (Set.Ioi ρ))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (f n) ρ) Filter.atTop
      (nhds (Work.Construction.L12 g ρ)) := by
  -- Swap the order of the quantifiers in the domination hypothesis: the `∀ n` sits
  -- outside the `∀ᵐ s` in `tendsto_integral_of_dominated_convergence`.
  have hbound : ∀ n : ℕ, ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi ρ)),
      ‖Work.FM.L12dens Work.Spaces.K (f n) s‖ ≤ M s :=
    fun n => hbdd.mono fun s hs => hs n
  -- `Work.Construction.L12 (f n) ρ = Work.FM.L12 Spaces.K (f n) ρ
  --    = ∫ s in Ioi ρ, L12dens Spaces.K (f n) s
  --    = ∫ s, L12dens Spaces.K (f n) s ∂(volume.restrict (Ioi ρ))`,
  -- so this is literally the dominated convergence theorem for the measure
  -- `volume.restrict (Ioi ρ)`.
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict (Set.Ioi ρ))
    (F := fun (n : ℕ) (s : ℝ) => Work.FM.L12dens Work.Spaces.K (f n) s)
    (f := fun s : ℝ => Work.FM.L12dens Work.Spaces.K g s)
    M hmeas hM hbound hconv
  simpa only [Work.Construction.L12, Work.FM.L12] using h

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.continuousOn_integral_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- The tail integral `z ↦ ∫ s in Ioi z, g s` of a function integrable on `Ioi 0` is
continuous on `Ici 0`.  This is the instance `a₀ = 0` of
`MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ioi`. -/
theorem continuousOn_integral_Ioi {g : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0)) :
    ContinuousOn (fun z => ∫ s in Set.Ioi z, g s) (Set.Ici 0) :=
  hint.continuousOn_Ici_primitive_Ioi

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false

/-- The angular profile of `N₄^{g*} + N₅^{g*}`: `a θ = -(α/c α)·(D_θΓ(θ) + 2 sin²θ·Γ(θ))`. -/
def aProf (α : ℝ) (θ : ℝ) : ℝ :=
  -(α / Work.Spaces.c α) *
    (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
      + 2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ)

/-- The radial profile of `N₄^{g*} + N₅^{g*}`: `r z = FK g z · hKer z`, `hKer z = z/(1+z)²`. -/
def rProf (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  Work.Construction.FK g z * Work.Spaces.hKer z

/-- The angular majorant of the `D_θ`-iterates of `aProf`: `Γ(α + sin 2θ) + sin(2θ)^{α/5}`. -/
def Gprof (α : ℝ) (θ : ℝ) : ℝ :=
  Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) + (Real.sin (2 * θ)) ^ (α / 5)

end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.PieceDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.PieceDefs` — one-variable forms of `D_z` and `D_θ`

The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` of `Work.Spaces` act on functions of two
variables.  Every function occurring in `explicit_piece_bounds` is a finite sum of products
`A(z)·B(θ)` of a function of `z` alone with a function of `θ` alone, and on such a product the
two operators act separately:

  `D_z^j D_θ^i (A·B) (z,θ) = (ZIter j A z)·(TIter i B θ)`,

where `ZIter j A = (z d/dz)^j A` and `TIter i B = (sin(2θ) d/dθ)^i B` are the one-variable
versions.  This file sets up `ZIter`, `TIter` and proves that splitting
(`DzIter_sep`, `DthIter_sep`, `mixed_sep`); the bounds on the individual one-variable factors
are the lemmas `ZIter_*` (in `piece_z_bounds`) and `TIter_*` (in `piece_t_bounds`).

Note that `deriv_const_mul_field` and `deriv_mul_const_field` are *unconditional* in Lean
(`deriv` is totalised), so the splitting needs no differentiability hypotheses at all.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-- `(z ∂_z)^j A`, the one-variable version of the radial operator `D_z`. -/
def ZIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, A => A
  | j + 1, A => fun z => z * deriv (ZIter j A) z

/-- `(sin(2θ) ∂_θ)^i B`, the one-variable version of the angular operator `D_θ`. -/
def TIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, B => B
  | i + 1, B => fun θ => Real.sin (2 * θ) * deriv (TIter i B) θ

@[simp] theorem ZIter_zero (A : ℝ → ℝ) : ZIter 0 A = A := rfl

@[simp] theorem ZIter_succ (j : ℕ) (A : ℝ → ℝ) :
    ZIter (j + 1) A = fun z => z * deriv (ZIter j A) z := rfl

@[simp] theorem TIter_zero (B : ℝ → ℝ) : TIter 0 B = B := rfl

@[simp] theorem TIter_succ (i : ℕ) (B : ℝ → ℝ) :
    TIter (i + 1) B = fun θ => Real.sin (2 * θ) * deriv (TIter i B) θ := rfl

theorem ZIter_succ_apply (j : ℕ) (A : ℝ → ℝ) (z : ℝ) :
    ZIter (j + 1) A z = z * deriv (ZIter j A) z := rfl


/-- Constants pass through `ZIter`. -/
theorem ZIter_const_mul (c : ℝ) (A : ℝ → ℝ) (j : ℕ) :
    ZIter j (fun z => c * A z) = fun z => c * ZIter j A z := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [ZIter_succ, ih, ZIter_succ]
      funext z
      rw [deriv_const_mul_field]
      ring

/-- `D_z^j` of a product `A(z)·C(θ)` only sees the radial factor. -/
theorem DzIter_sep (j : ℕ) (A C : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A z * C θ) = fun z θ => ZIter j A z * C θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp only [ZIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_mul_const_field]
      ring

/-- `D_θ^i` of a product `A(z)·B(θ)` only sees the angular factor. -/
theorem DthIter_sep (i : ℕ) (A B : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => A z * B θ) = fun z θ => A z * TIter i B θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [TIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-- **The mixed jets of a separable datum split.**  For `A·B : (z,θ) ↦ A z * B θ`,

  `D_z^j D_θ^i (A·B) z θ = (ZIter j A z) · (TIter i B θ)`.

This is the identity in which every pointwise estimate of `explicit_piece_bounds` is applied. -/
theorem mixed_sep (j i : ℕ) (A B : ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => A z * B θ) = fun z θ => ZIter j A z * TIter i B θ := by
  rw [Work.Spaces.mixed, DthIter_sep i A B, DzIter_sep j A (TIter i B)]

end Work.FTS_RegExport.RXT.SysAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.logcoord_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

/-- `sin (2 * arctan t) / 2 = t / (1 + t²)`: the elementary trigonometric identity behind the
change of coordinate `θ = arctan (e^ψ)`. -/
lemma sin_two_arctan_div_two (t : ℝ) : Real.sin (2 * Real.arctan t) / 2 = t / (1 + t ^ 2) := by
  have hD : (0 : ℝ) ≤ 1 + t ^ 2 := by positivity
  have h2 : Real.sin (Real.arctan t) * Real.cos (Real.arctan t) = t / (1 + t ^ 2) := by
    rw [Real.sin_arctan, Real.cos_arctan, div_mul_div_comm, mul_one, Real.mul_self_sqrt hD]
  rw [Real.sin_two_mul]
  rw [show (2 : ℝ) * Real.sin (Real.arctan t) * Real.cos (Real.arctan t) / 2
        = Real.sin (Real.arctan t) * Real.cos (Real.arctan t) by ring]
  exact h2

/-- `|cos (2θ) - sin²θ| ≤ 2`: both summands lie in `[-1,1]`. -/
lemma abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ ≤ 2 := by
        have h1 := Real.abs_cos_le_one (2 * θ)
        have h2 : |Real.sin θ ^ 2| ≤ 1 := by
          rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
          exact Real.sin_sq_le_one θ
        linarith

/-- Elementary facts about the logarithmic angular coordinate `ψ ↦ θ = arctan(e^ψ)`, which maps
`ℝ` onto the open interval `(0, π/2)`:

* `0 < arctan (e^ψ) < π/2` for every `ψ`;
* `d/dψ arctan(e^ψ) = sin (2·arctan(e^ψ))/2 = e^ψ/(1+e^{2ψ})`; in particular the derivative is
  positive, so `sin (2·arctan(e^ψ)) > 0`;
* every `z > 0` is `e^s` for some `s`, and every `θ ∈ (0,π/2)` is `arctan(e^ψ)` for some `ψ`
  (namely `ψ = log (tan θ)`);
* `0 < sin (2θ)` for `0 < θ < π/2`;
* `|c2m θ| ≤ 2` where `c2m θ = cos 2θ − sin²θ` (`Work.Construction.c2m`). -/
theorem logcoord_facts :
    (∀ ψ : ℝ, 0 < Real.arctan (Real.exp ψ) ∧ Real.arctan (Real.exp ψ) < Real.pi / 2) ∧
    (∀ ψ : ℝ, 0 < Real.sin (2 * Real.arctan (Real.exp ψ))) ∧
    (∀ ψ : ℝ, HasDerivAt (fun ψ' => Real.arctan (Real.exp ψ'))
      (Real.sin (2 * Real.arctan (Real.exp ψ)) / 2) ψ) ∧
    (∀ z : ℝ, 0 < z → ∃ s : ℝ, Real.exp s = z) ∧
    (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → ∃ ψ : ℝ, Real.arctan (Real.exp ψ) = θ) ∧
    (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → 0 < Real.sin (2 * θ)) ∧
    (∀ θ : ℝ, |Work.Construction.c2m θ| ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ
    exact ⟨(Real.arctan_pos).mpr (Real.exp_pos ψ), Real.arctan_lt_pi_div_two (Real.exp ψ)⟩
  · intro ψ
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact mul_pos two_pos ((Real.arctan_pos).mpr (Real.exp_pos ψ))
    · nlinarith [Real.arctan_lt_pi_div_two (Real.exp ψ), Real.pi_pos]
  · intro ψ
    have h := (Real.hasDerivAt_arctan (Real.exp ψ)).comp ψ (Real.hasDerivAt_exp ψ)
    have hv : (1 / (1 + (Real.exp ψ) ^ 2)) * Real.exp ψ
        = Real.sin (2 * Real.arctan (Real.exp ψ)) / 2 := by
      rw [sin_two_arctan_div_two]
      rw [one_div, inv_mul_eq_div]
    rw [hv] at h
    exact h
  · intro z hz
    exact ⟨Real.log z, Real.exp_log hz⟩
  · intro θ h1 h2
    refine ⟨Real.log (Real.tan θ), ?_⟩
    rw [Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two h1 h2)]
    exact Real.arctan_tan (by linarith [Real.pi_pos]) h2
  · intro θ h1 h2
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · linarith
    · linarith [Real.pi_pos]
  · exact abs_c2m_le_two

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.velPertAux.thetaJetsTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Jet convergence of the singular part `Θ = (1/(4α)) sin(2θ) L₁₂(F)`

The function `Θ` (`Work.Construction.Theta`) is a product of a function of `z` alone,
`L₁₂ F`, and a function of `θ` alone, `(1/(4α)) sin(2θ)`.  The operators `D_z = z ∂_z` and
`D_θ = sin(2θ) ∂_θ` respect this splitting: `D_z` differentiates only the `z`-factor and `D_θ`
only the `θ`-factor.  Hence for every `j, i`

  `mixed j i (Θ α F) z θ = (D_θ^i ((1/(4α)) sin(2·))) θ · (D_z^j (L₁₂ F)) (z, 0)`,

the angular factor being independent of the family `F`.  Consequently, if the `j`-th `D_z`-jets
of `L₁₂ (F n)` converge to those of `L₁₂ G` for `j ≤ 3` (the hypothesis `hL12`), then all mixed
jets `mixed j i (Θ α (F n)) z θ` with `j + i ≤ 3` converge as well: the `n`-dependence sits
entirely in the second factor.

The proof of the factorisation goes through the one-variable iterates `DzIter1`, `DthIter1` of
`z ∂_z` and `sin(2θ) ∂_θ` (the type of a one-variable function is enough once the other variable
is known to be untouched), exactly as in `GalBasis/cc/psiCut_mixed_factor.lean`.
-/

namespace Work.FTS_RegExport.RXT.velPertAux

open Filter

noncomputable section

/-! ## The one-variable operators `z ∂_z` and `sin(2θ) ∂_θ` -/

/-- The `j`-th iterate of the one-variable operator `f ↦ (z ↦ z f'(z))`, the `z`-part of `D_z`. -/
def DzIter1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => fun z => z * deriv (DzIter1 n f) z

/-- The `i`-th iterate of the one-variable operator `f ↦ (θ ↦ sin(2θ) f'(θ))`, the `θ`-part of
`D_θ`. -/
def DthIter1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => fun θ => Real.sin (2 * θ) * deriv (DthIter1 n f) θ

/-! ## `D_z^j` and `D_θ^i` of a function of a single variable -/

/-- `D_z^j` applied to a function of `z` alone is the one-variable iterate `DzIter1`. -/
theorem DzIter_const (j : ℕ) (a : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') = fun z _ => DzIter1 j a z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rfl

/-- `D_θ^i` applied to a function of `θ` alone is the one-variable iterate `DthIter1`. -/
theorem DthIter_const (i : ℕ) (b : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun (_ : ℝ) θ' => b θ') = fun _ θ => DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rfl

/-! ## `D_z^j` and `D_θ^i` of a separated product -/

/-- `D_z^j` of a separated product only differentiates the `z`-factor. -/
theorem DzIter_mul_sep (j : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => a z * b θ) = fun z θ => DzIter1 j a z * b θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [deriv_mul_const_field]
    simp only [DzIter1]
    ring

/-- `D_θ^i` of a separated product only differentiates the `θ`-factor. -/
theorem DthIter_mul_sep (i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => a z * b θ) = fun z θ => a z * DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const_mul_field]
    simp only [DthIter1]
    ring

/-- The mixed jets of a separated product `(z,θ) ↦ a z * b θ` factorise. -/
theorem mixed_mul_sep (j i : ℕ) (a b : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => a z * b θ) z θ
      = DthIter1 i b θ * Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') z 0 := by
  have h4 : Work.Spaces.DthIter i (fun z θ => a z * b θ) = fun z θ => a z * DthIter1 i b θ :=
    DthIter_mul_sep i a b
  have h3 : Work.Spaces.DzIter j (fun z θ => a z * DthIter1 i b θ)
      = fun z θ => DzIter1 j a z * DthIter1 i b θ := DzIter_mul_sep j a (DthIter1 i b)
  have h1 : Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') z 0 = DzIter1 j a z :=
    congrFun (congrFun (DzIter_const j a) z) 0
  change Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => a z * b θ)) z θ = _
  rw [h4, h3, h1]
  ring

/-- `Θ α F` is the separated product of `L₁₂ F` (in `z`) and `(1/(4α)) sin(2θ)` (in `θ`). -/
theorem theta_eq_sep (α : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Construction.Theta α F
      = fun z θ => Work.Construction.L12 F z * ((1 / (4 * α)) * Work.Construction.s2 θ) := by
  funext z θ
  simp only [Work.Construction.Theta]
  ring

/-- The factorisation of the mixed jets of `Θ`: the angular factor is `F`-independent and the
`F`-dependence is the pure radial jet of `L₁₂ F`. -/
theorem theta_mixed_factor (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (Work.Construction.Theta α F) z θ
      = DthIter1 i (fun θ => (1 / (4 * α)) * Work.Construction.s2 θ) θ
        * Work.Spaces.DzIter j (fun z' (_ : ℝ) => Work.Construction.L12 F z') z 0 := by
  rw [theta_eq_sep α F,
    mixed_mul_sep j i (fun z => Work.Construction.L12 F z)
      (fun θ => (1 / (4 * α)) * Work.Construction.s2 θ)]

/-! ## The convergence theorem -/


end

end Work.FTS_RegExport.RXT.velPertAux
end
-- ===== merged: Submission.Work.Spaces.DthIter_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.Spaces


end Work.Spaces
end
-- ===== merged: Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A lower bound for `|F_* + g|` on the domain

The paper's far-field/dichotomy argument needs a point `(z,θ) ∈ I_z × I_θ` at which the
reference profile `F_* = α (Γ(θ)/c) F_{*,rad}(z)` is not cancelled by a perturbation `g`
that is uniformly small, `|g| ≤ α/200`.

The witness is `(z,θ) = (1, π/4)`:

* `F_{*,rad}(1) = 2·1/(1+1)² = 1/2` is the maximum of `F_{*,rad}`;
* `Γ(π/4) = (sin(π/4)·cos²(π/4))^{α/3} = (√2/4)^{α/3} ≥ √2/4 ≥ 3/10`
  (the base `√2/4` lies in `(0,1]` and `α/3 ≤ 1`);
* `c(α) ≤ 10` (`Work.Spaces.c_bounds`), hence `Γ(π/4)/c ≥ (3/10)/10 = 3/100`.

Therefore `F_*(1, π/4) ≥ α · (3/100) · (1/2) = 3α/200`, so that at this point
`F_*(1,π/4) + g(1,π/4) ≥ 3α/200 - α/200 = α/100 > 0`, giving the claim.
-/

namespace Work.StabilityFar.Profile

open scoped Real Topology



end Work.StabilityFar.Profile
end
