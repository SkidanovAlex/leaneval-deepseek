import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.gammaFactorLogDerivReLe
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_supply
import Submission.Work.LinnikAreas.OtherCharRepel.one_div_le_winSum
import Submission.Work.LinnikAreas.OtherCharRepel.winSum_nonneg

/-!
# Sharp off-axis bounds for the log-derivative of a primitive `L`-function

There is an absolute constant `C > 0` such that for every primitive non-principal character `χ`
modulo `N`:

* on the segment `1 < Re s ≤ 5/4`, `|Im s| ≤ 12`, the real part of `-L'/L` is at most
  `(1/2) log N + C` (the sharp `log N`-coefficient of the Hadamard partial-fraction bound);
* at a point `σ + i·Im u` directly "below" (same imaginary part as) a zero `u` of `L(s,χ)` with
  `|Im u| ≤ 12` and `1 < σ ≤ 5/4`, the single zero `u` contributes its exact kernel
  `-1/(σ - Re u)` and the rest is again at most `(1/2) log N + C`.

## Route

The main input is `Work.LinnikAreas.DhRepel.shape` (Heath-Brown's Lemma 3.1 in window form,
proved by the symmetric Hadamard partial fraction and the archimedean estimate):

`-Re (L'/L)(s) + winSum χ s δ ≤ (1/2) log N + log π / 2 + (1/2)(log (2 + |Im s|) + 8)`,

where `winSum χ s δ` is the sum over the zeros `v` of `Λ(·,χ)` in the ball `|v| ≤ |Im s| + 2`
that lie within distance `δ` of `1 + i·Im s`, of `mult(v) · Re (1/(s-v))`.

* Every summand of `winSum` is non-negative (`winSum_nonneg`): the multiplicities are
  non-negative and `Re 1/(s-v) ≥ 0` because `0 < Re v < 1 < Re s`. So `winSum ≥ 0` and the first
  part follows once `log π/2 + (1/2)(log (2 + |Im s|) + 8) ≤ 7` for `|Im s| ≤ 12`.
* If `u` is a zero of `L(·,χ)` with `0 < Re u < 1`, then taking `δ = 1 - Re u/2 ∈ (0,1)` puts `u`
  inside the window (the distance to the centre is `|1 - Re u|` because the imaginary parts
  coincide), and its multiplicity is at least `1`; hence `winSum ≥ 1/(σ - Re u)` and the extra
  `-1/(σ - Re u)` can be extracted (`one_div_le_winSum`).
* If `Re u ≤ 0` (a *trivial* zero of `L`), then `u` is far from the centre of the window and the
  window gain is unavailable, but `1/(σ - Re u) ≤ 1/σ < 1`, so the plain bound of the first part
  suffices.
-/

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex Metric
open scoped Classical BigOperators

noncomputable section

set_option maxHeartbeats 800000

/-! ## Extracting a single zero from the window sum -/

/-- The window `‖1 + i·Im s - u‖ ≤ 1 - Re u/2` contains the zero `u` when `u.im = s.im` and
`0 < u.re < 1`. -/
private theorem norm_window_close {s u : ℂ} (hum : u.im = s.im) (h0 : 0 < u.re) (h1 : u.re < 1) :
    ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ 1 - u.re/2 := by
  have hval : (1 : ℂ) + (s.im : ℂ) * Complex.I - u = ((1 - u.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.sub_re, Complex.add_re]
    · simp [Complex.sub_im, Complex.add_im, hum]
  rw [hval]
  have hnorm : ‖((1 - u.re : ℝ) : ℂ)‖ = 1 - u.re :=
    (RCLike.norm_ofReal (1 - u.re)).trans (abs_of_pos (by linarith))
  rw [hnorm]
  linarith

/-! ## The additive constant -/

/-- `log π / 2 + (1/2)(log (2 + |τ|) + 8) ≤ 7` for `|τ| ≤ 12`. -/
private theorem shapeConst_bound {τ : ℝ} (hτ : |τ| ≤ 12) :
    Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |τ|) + 8) ≤ 7 := by
  have hlogpi : Real.log Real.pi / 2 ≤ 1 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  have hlog : Real.log (2 + |τ|) ≤ 4 := by
    have h1 : (2:ℝ) + |τ| ≤ 16 := by linarith [abs_nonneg τ]
    have h2 : Real.log (2 + |τ|) ≤ Real.log 16 := Real.log_le_log (by positivity) h1
    have h3 : Real.log (16:ℝ) = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
    have h4 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  linarith

/-! ## The main theorem -/

theorem sharpPrimitiveOffAxis : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
    (∀ σ τ : ℝ, 1 < σ → σ ≤ 5 / 4 → |τ| ≤ 12 →
      (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
        (1 / 2) * Real.log (N : ℝ) + C) ∧
    (∀ u : ℂ, DirichletCharacter.LFunction χ u = 0 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 → |u.im| ≤ 12 →
        (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (u.im : ℂ) * Complex.I)).re ≤
          -1 / (σ - u.re) + (1 / 2) * Real.log (N : ℝ) + C) := by
  refine ⟨8, by norm_num, ?_⟩
  intro N _inst χ hχ hχprim
  -- the bound of `shape` with the additive constant absorbed into `7`
  have hshape_bound : ∀ {s : ℂ}, 1 < s.re → s.re ≤ 5/4 → |s.im| ≤ 12 →
      (-logDeriv (DirichletCharacter.LFunction χ) s).re ≤ (1/2) * Real.log (N:ℝ) + 7 := by
    intro s hs1 hs2 him
    have hshape := Work.LinnikAreas.DhRepel.shape χ hχ hχprim (s := s) hs1 (by linarith)
      (δ := (1:ℝ)/2) (by norm_num) (by norm_num)
    have hwin : 0 ≤ Work.LinnikAreas.DhRepel.winSum χ s (1/2) :=
      winSum_nonneg χ hχ hχprim hs1 (1/2)
    have hK := shapeConst_bound him
    rw [Complex.neg_re]
    linarith
  constructor
  · intro σ τ hσ1 hσ2 hτ
    have h := hshape_bound (s := (σ : ℂ) + (τ : ℂ) * Complex.I)
      (by simp; linarith) (by simp; linarith) (by simpa using hτ)
    linarith
  · intro u hu σ hσ1 hσ2 huim
    -- every zero of `L(·,χ)` has real part `< 1`
    have hure1 : u.re < 1 := by
      by_contra h
      push Not at h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hu
    have hsim : |(((σ : ℂ) + (u.im : ℂ) * Complex.I)).im| ≤ 12 := by simpa using huim
    by_cases hure : 0 < u.re
    · -- a non-trivial zero: extract its kernel from the window sum
      have hδ0 : (0:ℝ) < 1 - u.re/2 := by linarith
      have hδ1 : (1:ℝ) - u.re/2 < 1 := by linarith
      have hwin_raw : ‖(1 : ℂ) + (((σ : ℂ) + (u.im : ℂ) * Complex.I).im : ℂ) * Complex.I - u‖
          ≤ 1 - u.re/2 :=
        norm_window_close (s := (σ : ℂ) + (u.im : ℂ) * Complex.I) (by simp) hure hure1
      have hext' := one_div_le_winSum χ hχ hχprim
        (s := (σ : ℂ) + (u.im : ℂ) * Complex.I) (u := u) (δ := 1 - u.re/2)
        (by simp; linarith) hu (by simp) hure hwin_raw
      have hext'' : 1 / (σ - u.re) ≤
          Work.LinnikAreas.DhRepel.winSum χ ((σ : ℂ) + (u.im : ℂ) * Complex.I) (1 - u.re/2) := by
        simpa using hext'
      have hshape := Work.LinnikAreas.DhRepel.shape χ hχ hχprim
        (s := (σ : ℂ) + (u.im : ℂ) * Complex.I) (by simp; linarith) (by simp; linarith)
        (δ := 1 - u.re/2) hδ0 hδ1
      have hshape' : -(logDeriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (u.im : ℂ) * Complex.I)).re
          + Work.LinnikAreas.DhRepel.winSum χ ((σ : ℂ) + (u.im : ℂ) * Complex.I) (1 - u.re/2) ≤
          (1/2) * Real.log (N:ℝ) + 7 := by
        have hK : Real.log Real.pi / 2
            + (1/2) * (Real.log (2 + |(((σ : ℂ) + (u.im : ℂ) * Complex.I)).im|) + 8) ≤ 7 := by
          simpa using shapeConst_bound huim
        linarith
      rw [Complex.neg_re, neg_div]
      linarith
    · -- a trivial zero (`u.re ≤ 0`): the plain bound suffices since `1/(σ - u.re) ≤ 1`
      push Not at hure
      have h := hshape_bound (s := (σ : ℂ) + (u.im : ℂ) * Complex.I)
        (by simp; linarith) (by simp; linarith) hsim
      have hpos : (0:ℝ) < σ - u.re := by linarith
      have hle : 1/(σ - u.re) ≤ 1 := by rw [div_le_one hpos]; linarith
      rw [neg_div]
      linarith

end

end Work.LinnikAreas.OtherCharRepel
