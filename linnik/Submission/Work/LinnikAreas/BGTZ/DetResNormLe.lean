/-
# The residue term of the BGTZ zero-detector: its norm is bounded by `detResBound`

The BGTZ detector's contour shift produces, besides the shifted-line integral `detJ`, the
residue of the integrand

`L(χ,ρ+s) L(χχ₁,ρ+s) G(ρ+s,χ) N^s / (s(s+1))`

at its pole `s = 1 - ρ`.  That residue is `detRes χ₁ χ R θw N ρ` (`DetContourDefs`), and
`detResBound` (`DetectorDefs`) is the explicit quantity it is compared with in the contour
inequality `DetectorContour`.

The two structural facts used here (both elementary, and independent of the sieve weights):

* the residue is `detA (1-ρ) / ((1-ρ)(2-ρ))`, where `detA` is the numerator with the pole
  divided out and the removable `s = 0` singularity killed by the zero hypothesis;
* at `s = 1 - ρ` the numerator `detA` vanishes unless one of `χ`, `χχ₁` is principal, and
  otherwise equals `LFunctionTrivChar₁ q 1 · L(χ₁,1) · G(1,χ₀) · N^{1-ρ}`: the two `L`-factors
  collapse to the single `L(χ₁,1)` because in the remaining case `χ = χ₁`, and the sieve function
  is the same at `1` and at `χ₁` (`DetSieveLocalTriv`).  Since
  `‖LFunctionTrivChar₁ q 1‖ = ∏_{p | q}(1 - p⁻¹) = φ(q)/q`, this matches `detResBound` exactly.

This file is deliberately independent of `DetectorContourCore` (it only imports the
definitions `DetContourDefs`/`DetectorDefs` and the local-factor identity `DetSieveLocalTriv`),
so that it can be rebuilt while the contour-shift development is still moving.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetContourDefs
import Submission.Work.LinnikAreas.BGTZ.DetSieveLocalTriv

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

/-! ## Three elementary facts about `detA`, reproduced here to keep this module's dependency
closure to the definitions only. -/

/-- `LFunctionTrivChar₁ q` is `(s-1)·L(s,χ₀)` away from `s = 1`. -/
private lemma LFunctionTrivChar₁_of_ne_aux {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar₁ q s
      = (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s := by
  simp only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs]

/-- The numerator of `detInt`, i.e. `detInt s · s(s+1)`. -/
private def detNumAux {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ)
    (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ (ρ + s) * DirichletCharacter.LFunction (χ * χ₁) (ρ + s)
    * sieveG χ₁ R θw (ρ + s) χ * (N : ℂ) ^ s

/-- `detA s = (s-(1-ρ))·(numerator of detInt)` away from the pole `s = 1-ρ`. -/
private lemma detA_eq_mul_aux {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ)
    (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ) {s : ℂ} (hs : s ≠ 1 - ρ) :
    detA χ₁ χ R θw N ρ s = (s - (1 - ρ)) * detNumAux χ₁ χ R θw N ρ s := by
  unfold detA detNumAux
  by_cases hB : χ = 1 ∨ χ * χ₁ = 1
  · rw [if_pos hB]
    have hρs : ρ + s ≠ 1 := by
      intro hcon
      exact hs (by linear_combination hcon)
    rw [LFunctionTrivChar₁_of_ne_aux (q := q) hρs]
    rcases hB with h | h
    · have hother : detOther χ₁ χ = χ * χ₁ := by simp only [detOther, if_pos h]
      rw [hother, h, one_mul]
      ring
    · have hother : detOther χ₁ χ = χ := by
        by_cases h1 : χ = 1
        · subst h1
          simp only [detOther, if_pos rfl]
          exact h
        · simp only [detOther, if_neg h1]
      rw [hother, h]
      ring
  · rw [if_neg hB]
    ring

/-- The numerator `detA` vanishes at `s = 0` when `ρ` is a zero of `L(·,χ)` or `L(·,χχ₁)`. -/
private lemma detA_zero_aux {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ)
    (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) : detA χ₁ χ R θw N ρ 0 = 0 := by
  have h0u : (0 : ℂ) ≠ 1 - ρ := by
    intro hcon
    exact hρ1 (sub_eq_zero.mp hcon.symm).symm
  rw [detA_eq_mul_aux χ₁ χ R θw N ρ h0u]
  have hnum : detNumAux χ₁ χ R θw N ρ 0 = 0 := by
    unfold detNumAux
    rcases hzero with h | h
    · rw [show ρ + 0 = ρ by ring, h]; ring
    · rw [show ρ + 0 = ρ by ring, h]; ring
  rw [hnum]
  ring

/-! ## The residue, its value at the pole, and the trivial-character factor -/

/-- `detRes` is `detA (1-ρ)` divided by the two linear factors `(1-ρ)` and `(2-ρ)`: the residue
of the detector integrand at its pole, with the removable `s = 0` singularity divided out. -/
lemma detRes_eq_detA_div {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ)
    (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) :
    detRes χ₁ χ R θw N ρ = detA χ₁ χ R θw N ρ (1 - ρ) / ((1 - ρ) * (2 - ρ)) := by
  have hne : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hsub := sub_smul_dslope (detA χ₁ χ R θw N ρ) 0 (1 - ρ)
  rw [sub_zero, smul_eq_mul] at hsub
  have h0 := detA_zero_aux χ₁ χ R θw N ρ hzero hρ1
  rw [h0, sub_zero] at hsub
  have hds : dslope (detA χ₁ χ R θw N ρ) 0 (1 - ρ) = detA χ₁ χ R θw N ρ (1 - ρ) / (1 - ρ) := by
    rw [eq_div_iff hne, mul_comm]
    exact hsub
  unfold detRes detM
  rw [hds]
  have h2 : (1 : ℂ) - ρ + 1 = 2 - ρ := by ring
  rw [h2]
  field_simp

/-- The value of `detA` at the pole `s = 1 - ρ`: it vanishes unless one of the two `L`-factors is
the principal character, in which case it is the divided-out numerator's value
`LFunctionTrivChar₁ q 1 · L(χ₁,1) · G(1,χ₀) · N^{1-ρ}`. -/
lemma detA_apply_one_sub {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ)
    (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ) (hχ₁ : χ₁ ^ 2 = 1) (hχ₁ne : χ₁ ≠ 1) :
    detA χ₁ χ R θw N ρ (1 - ρ)
      = (if χ = 1 ∨ χ * χ₁ = 1 then
          DirichletCharacter.LFunctionTrivChar₁ q 1 * DirichletCharacter.LFunction χ₁ 1
            * sieveG χ₁ R θw 1 1 * (N : ℂ) ^ (1 - ρ)
        else 0) := by
  unfold detA
  by_cases hB : χ = 1 ∨ χ * χ₁ = 1
  · rw [if_pos hB, if_pos hB]
    have hρs : ρ + (1 - ρ) = 1 := by ring
    rw [hρs]
    rcases hB with hχ | hχ
    · subst hχ
      have hother : detOther χ₁ (1 : DirichletCharacter ℂ q) = χ₁ := by
        simp [detOther]
      rw [hother]
    · have hne1 : χ ≠ 1 := by
        intro h; rw [h] at hχ; simp at hχ; exact hχ₁ne hχ
      have hother : detOther χ₁ χ = χ := by
        simp only [detOther, if_neg hne1]
      have hχeq : χ = χ₁ := by
        calc χ = χ * 1 := by rw [mul_one]
          _ = χ * (χ₁ * χ₁) := by rw [← pow_two, hχ₁]
          _ = (χ * χ₁) * χ₁ := by rw [mul_assoc]
          _ = 1 * χ₁ := by rw [hχ]
          _ = χ₁ := by rw [one_mul]
      rw [hother, hχeq, ← DetSieveLocalTriv χ₁ hχ₁ R θw 1]
  · rw [if_neg hB, if_neg hB]
    ring

/-- Euler's product formula for the totient function, in the real form used here. -/
private lemma totient_div_eq_prod {q : ℕ} [NeZero q] :
    (q.totient : ℝ) / (q : ℝ) = ∏ p ∈ q.primeFactors, (1 - ((p : ℝ))⁻¹) := by
  have hQ := Nat.totient_eq_mul_prod_factors q
  have hR : (q.totient : ℝ) = (q : ℝ) * ∏ p ∈ q.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) hQ
    push_cast at h
    simpa using h
  rw [hR, div_eq_iff (Nat.cast_ne_zero.mpr (NeZero.ne q))]
  exact mul_comm _ _

/-- Each factor `1 - p⁻¹` of the Euler product, read in `ℂ`, has norm `1 - p⁻¹` in `ℝ`
(nonnegative because `p ≥ 2`). -/
private lemma norm_one_sub_inv {p : ℕ} (hp : 2 ≤ p) :
    ‖(1 : ℂ) - (p : ℂ)⁻¹‖ = 1 - ((p : ℝ))⁻¹ := by
  have hcast : (1 : ℂ) - (p : ℂ)⁻¹ = ((1 - ((p : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; ring
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hle : ((p : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hp0]; exact_mod_cast (by omega : 1 ≤ p)
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- The `LFunctionTrivChar₁ q` factor at `s = 1` is exactly `φ(q)/q = ∏_{p | q}(1 - p⁻¹)`. -/
lemma norm_LFunctionTrivChar₁_apply_one_le {q : ℕ} [NeZero q] :
    ‖DirichletCharacter.LFunctionTrivChar₁ q (1 : ℂ)‖ ≤ (q.totient : ℝ) / (q : ℝ) := by
  rw [show DirichletCharacter.LFunctionTrivChar₁ q (1 : ℂ)
        = ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) by
    simp [DirichletCharacter.LFunctionTrivChar₁]]
  rw [norm_prod,
    Finset.prod_congr rfl (fun p hp =>
      norm_one_sub_inv (Nat.prime_of_mem_primeFactors hp).two_le)]
  exact le_of_eq (totient_div_eq_prod (q := q)).symm

theorem DetResNormLe {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₁ne : χ₁ ≠ 1) {R : ℕ} (θw : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N)
    {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hρ1 : ρ ≠ 1) (hρ2 : ρ.re < 1) :
    ‖Work.LinnikAreas.BGTZ.detRes χ₁ χ R θw N ρ‖
      ≤ Work.LinnikAreas.BGTZ.detResBound χ₁ χ R θw N ρ := by
  have hdetRes := detRes_eq_detA_div χ₁ χ R θw N ρ hzero hρ1
  have hdetA := detA_apply_one_sub χ₁ χ R θw N ρ hχ₁ hχ₁ne
  have hL := norm_LFunctionTrivChar₁_apply_one_le (q := q)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [hdetRes, norm_div]
  unfold detResBound
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  rw [hdetA]
  by_cases hB : χ = 1 ∨ χ * χ₁ = 1
  · rw [if_pos hB]
    simp only [norm_mul]
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) from (Complex.ofReal_natCast N).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    have h0 : (0 : ℝ) ≤ ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (1 - ρ.re) := Real.rpow_nonneg (by positivity) _
    calc ‖DirichletCharacter.LFunctionTrivChar₁ q (1 : ℂ)‖
            * ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
            * ‖sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)‖ * (N : ℝ) ^ (1 - ρ.re)
        ≤ ((q.totient : ℝ) / (q : ℝ)) * ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
            * ‖sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)‖ * (N : ℝ) ^ (1 - ρ.re) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL h0) h1) h2
      _ = ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ * ((q.totient : ℝ) / (q : ℝ))
            * ‖sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)‖ * (N : ℝ) ^ (1 - ρ.re) := by
          rw [mul_comm ((q.totient : ℝ) / (q : ℝ)) ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖]
  · rw [if_neg hB]
    simp only [norm_zero]
    have h0 : (0 : ℝ) ≤ ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (1 - ρ.re) := Real.rpow_nonneg (by positivity) _
    have h3 : (0 : ℝ) ≤ (q.totient : ℝ) / (q : ℝ) := by
      have hqpos : 0 < q := NeZero.pos q
      have hφ : (0 : ℝ) < (q.totient : ℝ) := by
        exact_mod_cast (Nat.totient_pos.mpr hqpos)
      exact div_nonneg (le_of_lt hφ) (by positivity)
    exact mul_nonneg (mul_nonneg (mul_nonneg h0 h3) h1) h2

end

end Work.LinnikAreas.BGTZ
