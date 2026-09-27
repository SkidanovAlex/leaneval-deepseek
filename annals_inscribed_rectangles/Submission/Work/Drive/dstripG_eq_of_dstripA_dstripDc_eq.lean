import Mathlib
import Submission.Work.Drive.stripData
import Submission.Work.Drive.dcOf_inj

/-!
# `(A, Dᶜ)` determines the strip map `G`

The strip data of the descent is

* `dstripA M W α τ = ‖M (e^{iα}, τ)‖² + τ ‖W (e^{iα}, τ)‖²`,
* `dstripD M W α τ = M (e^{iα}, τ) / √(dstripA M W α τ)`,
* `dstripDc M W α τ = √2 · (D/‖D‖) · √(1 - ‖D‖²/2)`,
* `dstripG M W (α, τ) = (M (e^{iα}, τ), dstripA M W α τ)`.

The quantity `dstripDc` keeps the argument of `D` and replaces its modulus `ρ` by `√(2 - ρ²)`; on the
band `4 |τ| ‖W‖² < ‖M‖²` (`τ < 0`) one has `ρ² = ‖M‖²/A ∈ (1, 4/3)`, and at `τ = 0` one has `ρ = 1`.
In either case `ρ² < 2`, so `dstripDc` is injective in `D` (see `Work.Drive.dcOf_inj`), and
`(dstripA, dstripDc)` therefore determines `dstripG`.

The content of the file is the numeric lemma `dstripA_pos_and_normSq_dstripD` (the strip bounds
`0 < A`, `D ≠ 0`, `‖D‖² < 2`) and the assembly on top of `dcOf_inj`.
-/

namespace Work.Drive

/-- **Strip bounds.** For `τ ∈ [-c, 0]` and on the unit circle `‖e^{iα}‖ = 1`, the band inequality
gives `0 < dstripA M W α τ` and `1 ≤ ‖dstripD M W α τ‖² < 2`; in particular `dstripD ≠ 0`.

At `τ = 0` the value is exactly `‖dstripD‖² = 1`; for `τ < 0` it lies in `(1, 4/3)`. The bound
`‖dstripD‖² < 2` is exactly what makes `dstripDc` injective in `dstripD`. -/
lemma dstripA_pos_and_normSq_dstripD {M W : ℂ × ℝ → ℂ} {c : ℝ}
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    {α τ : ℝ} (hτ : τ ∈ Set.Icc (-c) 0) :
    0 < dstripA M W α τ ∧ dstripD M W α τ ≠ 0 ∧
      Complex.normSq (dstripD M W α τ) < 2 := by
  have hx : ‖dstripU α‖ = 1 := norm_dstripU α
  have h1 : (1 : ℝ) / 8 ≤ ‖dstripU α‖ := by rw [hx]; norm_num
  have h2 : ‖dstripU α‖ ≤ 2 := by rw [hx]; norm_num
  rcases lt_or_eq_of_le hτ.2 with hlt | heq
  · -- the open strip `τ < 0`: the band inequality gives `1 < ‖D‖² < 4/3`
    have hWn : W (dstripU α, τ) ≠ 0 := hWne _ _ h1 h2 hτ.1 hlt
    set m : ℝ := ‖M (dstripU α, τ)‖ ^ 2 with hm
    set w : ℝ := ‖W (dstripU α, τ)‖ ^ 2 with hw
    have hwpos : 0 < w := by rw [hw]; exact pow_pos (norm_pos_iff.mpr hWn) 2
    have hb : 4 * |τ| * w < m := by rw [hm, hw]; exact hband _ _ h1 h2 hτ.1 hlt
    have habs : |τ| = -τ := abs_of_neg hlt
    have hτw : 0 < |τ| * w := mul_pos (abs_pos.mpr (ne_of_lt hlt)) hwpos
    have hmpos : 0 < m := by nlinarith [hb, hτw]
    have htw : τ * w = -(|τ| * w) := by rw [habs]; ring
    have hAform : dstripA M W α τ = m + τ * w := by
      rw [dstripA, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← hm, ← hw]
    have hApos : 0 < dstripA M W α τ := by rw [hAform, htw]; nlinarith
    have hDnorm : Complex.normSq (dstripD M W α τ) = m / dstripA M W α τ := by
      rw [dstripD, Complex.normSq_div, Complex.normSq_ofReal,
        Real.mul_self_sqrt (le_of_lt hApos), Complex.normSq_eq_norm_sq, ← hm]
    have h2A : m < 2 * dstripA M W α τ := by rw [hAform, htw]; nlinarith
    have hlt2 : m / dstripA M W α τ < 2 := (div_lt_iff₀ hApos).mpr h2A
    refine ⟨hApos, ?_, ?_⟩
    · intro h0
      have hz : Complex.normSq (dstripD M W α τ) = 0 := by rw [h0]; simp
      rw [hDnorm] at hz
      exact absurd hz (ne_of_gt (div_pos hmpos hApos))
    · rw [hDnorm]; exact hlt2
  · -- the boundary `τ = 0`: `A = ‖M‖²` and `‖D‖² = 1`
    subst heq
    have hm0 : M (dstripU α, 0) ≠ 0 := hM0 _ (by rw [hx]; norm_num) (by rw [hx])
    set m : ℝ := Complex.normSq (M (dstripU α, 0)) with hm
    have hmpos : 0 < m := by rw [hm]; exact Complex.normSq_pos.mpr hm0
    have hA : dstripA M W α 0 = m := by rw [dstripA, ← hm]; ring
    have hApos : 0 < dstripA M W α 0 := by rw [hA]; exact hmpos
    have hDnorm : Complex.normSq (dstripD M W α 0) = 1 := by
      rw [dstripD, Complex.normSq_div, Complex.normSq_ofReal,
        Real.mul_self_sqrt (le_of_lt hApos), hA, ← hm]
      exact div_self (ne_of_gt hmpos)
    refine ⟨hApos, ?_, ?_⟩
    · intro h0
      rw [h0] at hDnorm
      simp at hDnorm
    · rw [hDnorm]; norm_num

/-- **The strip map `G` is a function of `(A, Dᶜ)`.** The pair `(dstripA, dstripDc)` determines
`dstripG`: `dstripA` alone determines the modulus `√A` of `M`, `dstripDc` determines the direction
and the norm of `D = M/√A` (via `Work.Drive.dcOf_inj`, using the strip bound `‖D‖² < 2`), and hence
`M = √A · D`. -/
theorem dstripG_eq_of_dstripA_dstripDc_eq {M W : ℂ × ℝ → ℂ} {c : ℝ}
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    {α α' τ τ' : ℝ} (hτ : τ ∈ Set.Icc (-c) 0) (hτ' : τ' ∈ Set.Icc (-c) 0)
    (hA : dstripA M W α τ = dstripA M W α' τ')
    (hDc : dstripDc M W α τ = dstripDc M W α' τ') :
    dstripG M W (α, τ) = dstripG M W (α', τ') := by
  obtain ⟨hApos, hDne, hDlt⟩ := dstripA_pos_and_normSq_dstripD hband hWne hM0 hτ
  obtain ⟨hApos', hDne', hDlt'⟩ := dstripA_pos_and_normSq_dstripD hband hWne hM0 hτ'
  have hsq : ((Real.sqrt (dstripA M W α τ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hApos))
  have hsq' : ((Real.sqrt (dstripA M W α' τ') : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hApos'))
  have e1 : dstripD M W α τ * ((Real.sqrt (dstripA M W α τ) : ℝ) : ℂ)
      = M (dstripU α, τ) := by
    rw [dstripD]; exact div_mul_cancel₀ _ hsq
  have e2 : dstripD M W α' τ' * ((Real.sqrt (dstripA M W α' τ') : ℝ) : ℂ)
      = M (dstripU α', τ') := by
    rw [dstripD]; exact div_mul_cancel₀ _ hsq'
  have hD : dstripD M W α τ = dstripD M W α' τ' := by
    refine dcOf_inj (D₁ := dstripD M W α τ) (D₂ := dstripD M W α' τ')
      hDne hDne' hDlt hDlt' ?_
    simpa only [dstripDc] using hDc
  have hM : M (dstripU α, τ) = M (dstripU α', τ') := by
    rw [← e1, ← e2, hD, hA]
  simp only [dstripG]
  exact Prod.ext hM hA

end Work.Drive
