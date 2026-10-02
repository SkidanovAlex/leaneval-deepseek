import Mathlib
import Submission.Work.LinnikAreas.logDeriv_completedRiemannZeta_eq
import Submission.Work.LinnikAreas.zeta_logDeriv_negHalf_bound

namespace Work.LinnikAreas

open MeasureTheory

noncomputable section

/-!
# Integrability of `(Λ'/Λ)·Φ` on the two vertical edges of the strip `[-1/2, 2]`

Let `Λ = completedRiemannZeta` and `Φ = tentPhi (11/2) (3/10) q`.  We show that both

  `t ↦ logDeriv Λ (2 + i t)  * Φ (2 + i t)`   and
  `t ↦ logDeriv Λ (-1/2 + i t) * Φ (-1/2 + i t)`

are Lebesgue-integrable on `ℝ`.

The two ingredients are:

* the tent kernel decays like `1/(1+t²)` uniformly on `Re s ≤ 2`
  (`Commons.NumberTheory.Linnik.exists_norm_tentPhi_bound`), and
* `logDeriv Λ` grows only logarithmically along the two edges, because `Λ = Γℝ · ζ` there
  (`Work.LinnikAreas.logDeriv_completedRiemannZeta_eq`), with `‖(Γℝ'/Γℝ)(s)‖ ≲ log(2+|t|)`
  (`Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_two`,
  `…norm_logDeriv_gammaFactor_left`) and `‖ζ'/ζ(s)‖` bounded on `Re s = 2`
  (`…logDeriv_LFunction_re_ge_three_halves_bound`) and logarithmic on `Re s = -1/2`
  (`Work.LinnikAreas.zeta_logDeriv_negHalf_bound`).

The product of a logarithmically growing function with a `1/(1+t²)`-decaying kernel is
integrable; this is packaged as `Commons.NumberTheory.Linnik.integrable_mul_tentPhi_of_bound`.
-/

/-- The archimedean gamma factor of the (unique) Dirichlet character mod `1` is `Gammaℝ`. -/
private lemma gammaFactor_one_eq :
    DirichletCharacter.gammaFactor (1 : DirichletCharacter ℂ 1) = Complex.Gammaℝ := by
  funext s
  have h : (1 : DirichletCharacter ℂ 1).Even := by
    show (1 : DirichletCharacter ℂ 1) (-1) = 1
    exact map_one _
  exact DirichletCharacter.Even.gammaFactor_def h s

/-- **The logarithmic derivative of `Λ` on `Re s = 2` is `O(log(2+|t|))`.**

Since `ζ` does not vanish on `Re s = 2` (`riemannZeta_ne_zero_of_one_le_re`), `Λ = Γℝ·ζ`
there, and both factors have the required logarithmic growth. -/
private lemma logDeriv_completedRiemannZeta_line_two_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv completedRiemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (Real.log (2 + |t|) + 1) := by
  refine ⟨33, by norm_num, ?_⟩
  intro t
  set s : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = 2 := by simp [hs, Complex.add_re, Complex.mul_re]
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; norm_num)
  have hsplit := Work.LinnikAreas.logDeriv_completedRiemannZeta_eq hs0 hs1
    (by rw [hsre]; norm_num) hζ
  have hΓ : ‖logDeriv Complex.Gammaℝ s‖ ≤ 13 * (Real.log (2 + |t|) + 1) := by
    have h := Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_two
      (1 : DirichletCharacter ℂ 1) t
    rw [gammaFactor_one_eq] at h
    rwa [hs]
  have hZ : ‖logDeriv riemannZeta s‖ ≤ 20 := by
    have h32 : (3 : ℝ) / 2 ≤ s.re := by rw [hsre]; norm_num
    have h := Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_re_ge_three_halves_bound
      (1 : DirichletCharacter ℂ 1) (s := s) h32
    simpa using h
  have hlog : (1 : ℝ) ≤ Real.log (2 + |t|) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |t| by linarith [abs_nonneg t])
    linarith
  rw [hsplit]
  calc ‖logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s‖
      ≤ ‖logDeriv Complex.Gammaℝ s‖ + ‖logDeriv riemannZeta s‖ := norm_add_le _ _
    _ ≤ 13 * (Real.log (2 + |t|) + 1) + 20 := add_le_add hΓ hZ
    _ ≤ 33 * (Real.log (2 + |t|) + 1) := by nlinarith [hlog]

/-- `ζ` does not vanish on the line `Re s = -1/2`.

If `ζ w = 0` for `w = -1/2 + i t`, the functional equation
`ζ(1-w) = 2·(2π)^{-w}·Γ(w)·cos(πw/2)·ζ(w)` forces `ζ(1-w) = 0`; but `Re (1-w) = 3/2 ≥ 1`,
where `ζ` has no zeros. -/
private lemma riemannZeta_ne_zero_leftHalf (t : ℝ) :
    riemannZeta (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h0
  set w : ℂ := ((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hw
  have hwre : w.re = -1/2 := by simp [hw, Complex.add_re, Complex.mul_re]
  have h1 : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hn
    have hn' : (n : ℝ) = 1/2 := by
      have h := congrArg Complex.re hn
      rw [hwre] at h
      simp at h
      linarith
    have h2 : ((2 * n : ℕ) : ℝ) = 1 := by push_cast; linarith
    have h3 : (2 * n : ℕ) = 1 := by exact_mod_cast h2
    omega
  have hw1 : w ≠ 1 := by
    intro hh; have := congrArg Complex.re hh; rw [hwre] at this; norm_num at this
  have hfe := riemannZeta_one_sub h1 hw1
  have hzero : riemannZeta (1 - w) = 0 := by rw [hfe, h0]; ring
  have hre : (1 - w).re = 3/2 := by rw [Complex.sub_re, Complex.one_re, hwre]; norm_num
  exact riemannZeta_ne_zero_of_one_le_re (by rw [hre]; norm_num) hzero

/-- **The logarithmic derivative of `Λ` on `Re s = -1/2` is `O(log(2+|t|))`.**

`ζ` does not vanish on this line, so `Λ = Γℝ·ζ` there; the gamma factor is `O(log(2+|t|))`
and `ζ'/ζ` is `O(log(|t|+2))` by `Work.LinnikAreas.zeta_logDeriv_negHalf_bound`. -/
private lemma logDeriv_completedRiemannZeta_line_left_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv completedRiemannZeta (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (Real.log (2 + |t|) + 1) := by
  obtain ⟨Cz, hCzpos, hCzb⟩ := Work.LinnikAreas.zeta_logDeriv_negHalf_bound
  have hconv : ∀ t : ℝ, (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = (-(1/2) : ℂ) + (t : ℂ) * Complex.I := by
    intro t; push_cast; ring
  refine ⟨13 + 2 * Cz, by positivity, ?_⟩
  intro t
  set w : ℂ := ((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hw
  have hwre : w.re = -1/2 := by simp [hw, Complex.add_re, Complex.mul_re]
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hwre] at this; norm_num at this
  have hw1 : w ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hwre] at this; norm_num at this
  have hζ : riemannZeta w ≠ 0 := by
    rw [hw]; exact riemannZeta_ne_zero_leftHalf t
  have hsplit := Work.LinnikAreas.logDeriv_completedRiemannZeta_eq hw0 hw1
    (by rw [hwre]; norm_num) hζ
  have hΓ : ‖logDeriv Complex.Gammaℝ w‖ ≤ 13 * (Real.log (2 + |t|) + 1) := by
    have h := Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_left
      (1 : DirichletCharacter ℂ 1) t
    rw [gammaFactor_one_eq] at h
    rwa [hw]
  have hZ : ‖logDeriv riemannZeta w‖ ≤ Cz * (1 + Real.log (|t| + 2)) := by
    have h := hCzb t
    rw [hw, hconv t]
    exact h
  have hlog : (1 : ℝ) ≤ Real.log (2 + |t|) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |t| by linarith [abs_nonneg t])
    linarith
  have hlogeq : Real.log (|t| + 2) = Real.log (2 + |t|) := by ring_nf
  rw [hsplit]
  calc ‖logDeriv Complex.Gammaℝ w + logDeriv riemannZeta w‖
      ≤ ‖logDeriv Complex.Gammaℝ w‖ + ‖logDeriv riemannZeta w‖ := norm_add_le _ _
    _ ≤ 13 * (Real.log (2 + |t|) + 1) + Cz * (1 + Real.log (|t| + 2)) := add_le_add hΓ hZ
    _ = 13 * (Real.log (2 + |t|) + 1) + Cz * (1 + Real.log (2 + |t|)) := by rw [hlogeq]
    _ ≤ (13 + 2 * Cz) * (Real.log (2 + |t|) + 1) := by nlinarith [hlog, hCzpos]

/-- `t ↦ logDeriv Λ (σ + i t)` is (a.e.) strongly measurable: `logDeriv Λ = Λ'/Λ`, `Λ'` is
Borel by `measurable_deriv`, and `Λ = Λ₀ - 1/s - 1/(1-s)` with `Λ₀` entire is Borel. -/
private lemma aestronglyMeasurable_logDeriv_completedRiemannZeta_line (σ : ℝ) :
    AEStronglyMeasurable
      (fun t : ℝ => logDeriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) volume := by
  have hΛ : Measurable completedRiemannZeta := by
    have h0 : Measurable completedRiemannZeta₀ :=
      differentiable_completedZeta₀.continuous.measurable
    have h : completedRiemannZeta = fun s : ℂ => completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹ := by
      funext s; rw [completedRiemannZeta_eq]; ring
    rw [h]
    exact (h0.sub measurable_inv).sub (measurable_inv.comp (by fun_prop))
  have h1 : Measurable
      (fun t : ℝ => deriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    (measurable_deriv completedRiemannZeta).comp (by fun_prop)
  have h2 : Measurable
      (fun t : ℝ => completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    hΛ.comp (by fun_prop)
  have he : (fun t : ℝ => logDeriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
      = fun t : ℝ => deriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
          completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    funext t; rw [logDeriv_apply]
  rw [he]
  exact (h1.div h2).aestronglyMeasurable

/-- Generic assembly: on the vertical line `Re s = σ` with `σ ≤ 2`, a logarithmically bounded
`logDeriv Λ` times the decaying tent kernel `Φ` is integrable. -/
private lemma integrable_line {q : ℕ} (hq : 2 ≤ q) {σ : ℝ} (hσ : σ ≤ 2) {C : ℝ} (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => logDeriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) volume)
    (hb : ∀ t : ℝ,
      ‖logDeriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (Real.log (2 + |t|) + 1)) :
    MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
        Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
          ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
  Commons.NumberTheory.Linnik.integrable_mul_tentPhi_of_bound
    (L := (11/2 : ℝ)) (K := (3/10 : ℝ)) (by norm_num) (by norm_num) (Q := q) hq
    (σ := σ) hσ hmeas hC hb

theorem integrable_logDeriv_completedRiemannZeta_strip {q : ℕ} (hq : 2 ≤ q) :
    MeasureTheory.Integrable (fun t : ℝ =>
        logDeriv completedRiemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q ((2 : ℂ) + (t : ℂ) * Complex.I)) ∧
    MeasureTheory.Integrable (fun t : ℝ =>
        logDeriv completedRiemannZeta (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨C₂, hC₂pos, hC₂b⟩ := logDeriv_completedRiemannZeta_line_two_bound
  obtain ⟨Cₗ, hCₗpos, hCₗb⟩ := logDeriv_completedRiemannZeta_line_left_bound
  refine ⟨?_, ?_⟩
  · have h := integrable_line (q := q) hq (σ := (2 : ℝ)) (by norm_num) hC₂pos.le
      (aestronglyMeasurable_logDeriv_completedRiemannZeta_line 2) hC₂b
    simpa using h
  · exact integrable_line (q := q) hq (σ := (-1/2 : ℝ)) (by norm_num) hCₗpos.le
      (aestronglyMeasurable_logDeriv_completedRiemannZeta_line (-1/2)) hCₗb

end

end Work.LinnikAreas
