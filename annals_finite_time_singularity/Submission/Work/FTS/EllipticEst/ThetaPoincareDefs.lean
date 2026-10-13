/-
Copyright: work module for the Elgindi finite-time singularity project.

# The one-dimensional (angular) vocabulary of the `θ`-Poincaré estimate `theta_poincare_Hk`

The target `Work.FTS.EllipticEst.theta_poincare_Hk` compares the weighted `H^k`-norm of a
function `f` (and of its angular derivative `∂_θ f`) with the weighted `H^k`-norm of
`∂_θ² f`, for functions vanishing on the two angular boundaries.  Since the weights of
`Work.Spaces` depend only on `θ` and the radial operator `D_z = z ∂_z` acts inside each
angular slice, the whole estimate splits into *one-dimensional* statements about a single
slice `u : ℝ → ℝ`.

This file fixes the vocabulary of those slice statements:

* `LopIter i u` is the `i`-th iterate of `L = D_θ = sin(2θ) ∂_θ`;
* `thEta θ = sin(2θ)^{-η}` and `thGam α θ = sin(2θ)^{-γ}` are the two angular weights
  (`η = eta = 99/100`, `γ = gam α = 1 + α/10`);
* `sliceV u = u''` is the second angular derivative of the slice;
* `sliceA u = ∫_{Iθ} (u'')² sin(2θ)^{-η}` is the (finite) constant measuring the data;
* `slicePhi α K u` is the dominating function by which the slice estimates bound the
  quantities `u² sin(2θ)^{-η}` and `(D_θ^i u)² sin(2θ)^{-γ}`, `1 ≤ i ≤ K`.

The two slice estimates themselves are proved in the sibling files `slice_f_bound` (the
`∂_θ²`-case: `u` vanishing at both endpoints) and `slice_d_bound` (the `∂_θ`-case:
`∂_θ u`); they are the analytic core of `theta_poincare_Hk`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.sin_two_rpow

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

/-- The constant `A(u) = ∫_{Iθ} (u'')² sin(2θ)^{-η}` carried by the slice estimates. -/
def sliceA (u : ℝ → ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ

/-- The dominating function of the slice estimates: the data term `(u'')² sin(2θ)^{-η}`,
the higher angular derivatives of the data `(D_θ^m u'')² sin(2θ)^{-γ}`, `1 ≤ m ≤ K`, and
the fixed integrable terms produced by the boundary conditions, controlled by `A(u)`. -/
def slicePhi (α : ℝ) (K : ℕ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (sliceV u θ) ^ 2 * thEta θ
    + (∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
    + sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))

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
