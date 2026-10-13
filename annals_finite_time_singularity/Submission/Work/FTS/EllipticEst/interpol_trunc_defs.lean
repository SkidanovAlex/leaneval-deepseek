/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the truncation argument of `interpol_mixed_weighted_of_compact`

This module collects the definitions used to reduce the mixed weighted interpolation
estimate to its compactly supported case:

* `sig θ = sin(2θ)^{-η}` (`η = 99/100`) is the angular weight of the estimate;
* `cut n` is the `n`-th radial cut-off: a smooth function of `z` with
  `cut n = 0` for `z ≤ 1/(n+1)`, `cut n = 0` for `z ≥ 3(n+1)`, and `cut n = 1` on
  `[2/(n+1), 2(n+1)]`; the functions `z ↦ z (cut n)'(z)` and
  `z ↦ z (z (cut n)')'(z)` are uniformly bounded in `n` (they are what appears when the
  scale-invariant derivative `D_z = z ∂_z` acts on `G · cut n`);
* `trunc G n = G · cut n` is the truncation of `G`, supported in `[1/(n+1), 3(n+1)]`.

The estimates are all stated through the weight `sig` so that they can be rewritten
into the four functionals `mixInt`, `ddInt`, `ttInt`, `dInt` of
`Submission/Work/FTS/EllipticEst/interpol_defs.lean`.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.Cutoff

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

/-! ## The angular weight `σ_η` -/

/-- The angular weight `σ_η(θ) = sin(2θ)^{-η}` of the mixed weighted interpolation
estimate, with `η = 99/100`. -/
def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

theorem sig_apply (θ : ℝ) : sig θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig θ := by
  rw [sig_apply]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

theorem sig_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < sig θ := by
  rw [sig_apply]
  exact Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

theorem one_le_sig {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h0 : θ ≠ 0) (hπ : θ ≠ Real.pi / 2) :
    1 ≤ sig θ := by
  have h2θ0 : 0 < 2 * θ := by
    rcases lt_or_eq_of_le hθ.1 with h | h
    · linarith
    · exact absurd h.symm h0
  have h2θπ : 2 * θ < Real.pi := by
    rcases lt_or_eq_of_le hθ.2 with h | h
    · linarith
    · exact absurd h hπ
  rw [sig_apply]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (Real.sin_pos_of_pos_of_lt_pi h2θ0 h2θπ) (Real.sin_le_one _)
    (by rw [neg_nonpos]; exact le_of_lt Work.Spaces.eta_pos)

theorem sig_measurable : Measurable sig := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

theorem sig_continuousOn : ContinuousOn sig (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (0 : ℝ) (Real.pi / 2))
  refine ContinuousOn.rpow_const ?_ ?_
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  · intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))

theorem integrable_sig : IntegrableOn sig Work.Spaces.Iθ := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
  rw [show sig = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) by
    funext θ; rw [sig_apply]]
  exact h

theorem integral_sig_le : (∫ θ in Work.Spaces.Iθ, sig θ) ≤ 10000 := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).2
  have h' : (∫ θ in Work.Spaces.Iθ, sig θ)
      = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [show sig = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) by
      funext θ; rw [sig_apply]]
  rw [h']
  refine le_trans h (le_of_eq ?_)
  norm_num [Work.Spaces.eta]

/-! ## The radial cut-offs `cut n` and the truncation `trunc G n` -/

/-- The `n`-th radial cut-off of the truncation argument:
`cut n z = smoothTransition ((n+1) z - 1) · (1 - smoothTransition (z/(n+1) - 2))`.
It equals `1` for `z ∈ [2/(n+1), 2(n+1)]` and vanishes for `z ≤ 1/(n+1)` and for
`z ≥ 3(n+1)`. -/
def cut (n : ℕ) (z : ℝ) : ℝ :=
  Real.smoothTransition ((n + 1 : ℝ) * z - 1) * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))

/-- The truncation of `G` by the `n`-th cut-off, `trunc G n = G · cut n`. -/
def trunc (G : ℝ → ℝ → ℝ) (n : ℕ) : ℝ → ℝ → ℝ := fun z θ => G z θ * cut n z

theorem cut_nonneg (n : ℕ) (z : ℝ) : 0 ≤ cut n z :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem cut_le_one (n : ℕ) (z : ℝ) : cut n z ≤ 1 := by
  have h1 : Real.smoothTransition ((n + 1 : ℝ) * z - 1) ≤ 1 := Real.smoothTransition.le_one _
  have h2 : (0 : ℝ) ≤ 1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2) :=
    sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have h3 : (1 : ℝ) - Real.smoothTransition (z / (n + 1 : ℝ) - 2) ≤ 1 := by
    linarith [Real.smoothTransition.nonneg (z / (n + 1 : ℝ) - 2)]
  have h4 : (0 : ℝ) ≤ Real.smoothTransition ((n + 1 : ℝ) * z - 1) :=
    Real.smoothTransition.nonneg _
  calc cut n z
      = Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)) := rfl
    _ ≤ 1 * 1 := mul_le_mul h1 h3 h2 (by norm_num)
    _ = 1 := by ring

theorem cut_apply_zero_of_le (n : ℕ) {z : ℝ} (h : z ≤ 1 / (n + 1)) : cut n z = 0 := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hz : (n + 1 : ℝ) * z - 1 ≤ 0 := by
    have h' : (n + 1 : ℝ) * z ≤ 1 := by
      have := (le_div_iff₀ hn).mp h
      linarith [this]
    linarith
  rw [cut, Real.smoothTransition.zero_of_nonpos hz, zero_mul]

theorem cut_apply_zero_of_ge (n : ℕ) {z : ℝ} (h : 3 * (n + 1) ≤ z) : cut n z = 0 := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hz : 1 ≤ z / (n + 1 : ℝ) - 2 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hn]
    linarith
  rw [cut, Real.smoothTransition.one_of_one_le hz, sub_self, mul_zero]

/-- The cut-off is genuinely `C^∞` (the order `⊤ : ℕ∞ω` is analyticity, which a cut-off can
never have), so smoothness is stated with `Work.Stability.smoothOrder`. -/
theorem cut_contDiff (n : ℕ) : ContDiff ℝ Work.Stability.smoothOrder (cut n) := by
  have hρ : ContDiff ℝ Work.Stability.smoothOrder Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := ⊤)
  have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => (n + 1 : ℝ) * z - 1) :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => z / (n + 1 : ℝ) - 2) :=
    (contDiff_id.div_const _).sub contDiff_const
  show ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ =>
    Real.smoothTransition ((n + 1 : ℝ) * z - 1)
    * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)))
  exact (hρ.comp h1).mul (contDiff_const.sub (hρ.comp h2))

/-- The cut-off is strictly positive on the open slab `1/(n+1) < z < 3(n+1)`. -/
theorem cut_pos_of_mem (n : ℕ) {z : ℝ} (h1 : 1 / (n + 1 : ℝ) < z)
    (h2 : z < 3 * (n + 1 : ℝ)) : 0 < cut n z := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hz1 : 0 < (n + 1 : ℝ) * z - 1 := by
    have := (div_lt_iff₀ hn).mp h1
    linarith
  have hz2 : z / (n + 1 : ℝ) - 2 < 1 := by
    have h3 : z / (n + 1 : ℝ) < 3 := by
      rw [div_lt_iff₀ hn]
      linarith
    linarith
  rw [cut]
  exact mul_pos (Real.smoothTransition.pos_of_pos hz1)
    (by linarith [Real.smoothTransition.lt_one_of_lt_one hz2])

theorem cut_eq_one_of_mem (n : ℕ) {z : ℝ} (h1 : 2 / (n + 1) ≤ z) (h2 : z ≤ 2 * (n + 1)) :
    cut n z = 1 := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hz1 : 1 ≤ (n + 1 : ℝ) * z - 1 := by
    have := (div_le_iff₀ hn).mp h1
    linarith
  have hz2 : z / (n + 1 : ℝ) - 2 ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ hn]
    linarith
  rw [cut, Real.smoothTransition.one_of_one_le hz1, Real.smoothTransition.zero_of_nonpos hz2]
  ring

theorem trunc_apply (G : ℝ → ℝ → ℝ) (n : ℕ) (z θ : ℝ) : trunc G n z θ = G z θ * cut n z := rfl

/-- `trunc G n` is supported in `z ∈ [1/(n+1), 3(n+1)]`. -/
theorem trunc_eq_zero_of_notMem (G : ℝ → ℝ → ℝ) (n : ℕ) {z : ℝ}
    (h : z ∉ Set.Icc (1 / (n + 1 : ℝ)) (3 * (n + 1 : ℝ))) (θ : ℝ) : trunc G n z θ = 0 := by
  rw [trunc_apply]
  rcases le_or_gt z (1 / (n + 1 : ℝ)) with h1 | h1
  · rw [cut_apply_zero_of_le n h1, mul_zero]
  · have h2 : 3 * (n + 1 : ℝ) ≤ z := by
      by_contra hc
      push_neg at hc
      exact h ⟨le_of_lt h1, le_of_lt hc⟩
    rw [cut_apply_zero_of_ge n h2, mul_zero]

end Work.FTS.EllipticEst
