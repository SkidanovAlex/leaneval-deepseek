import Mathlib
import Submission.Work.BMF.vk_L_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lower bound for `L(1 + h + it, χ)`

For a Dirichlet character `χ` modulo `N`, `0 < h ≤ 1` and real `t`,

  `h / 2 ≤ ‖L(1 + h + i t, χ)‖`.

The point is that `L` does not vanish near the line `Re s = 1`: the elementary Euler-product
inequality `Work.BMF.vk_L_lower` gives `1 ≤ ‖L(s,χ)‖ · ζ(Re s)` for `Re s > 1`, and the
classical bound `ζ(σ) ≤ 1 + 1/(σ-1)` for `σ > 1` (proved here from scratch by the integral
test for the Dirichlet series of `ζ`) turns this into `‖L(s,χ)‖ ≥ 1/ζ(σ) ≥ σ - 1 = h` at
`s = 1 + h + it`; we only record the slightly weaker constant `h/2`.
-/

namespace Work.BMF

open MeasureTheory

/-- The `n`-th term of the `L`-series of the constant sequence `1` at a real point `σ ≠ 0` is
the complex number `(n : ℝ)^{-σ}` (for `n = 0` both sides vanish). -/
private lemma term_one_eq_ofReal (σ : ℝ) (hσ : σ ≠ 0) (n : ℕ) :
    LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    have h0 : (((0 : ℕ) : ℝ)) = (0 : ℝ) := Nat.cast_zero
    rw [h0, Real.zero_rpow (neg_ne_zero.mpr hσ)]
    simp
  · rw [LSeries.term_of_ne_zero hn]
    simp only [Pi.one_apply, one_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ), Complex.ofReal_neg, Complex.cpow_neg]
    simp

/-- On the real axis to the right of `1`, the Riemann zeta function equals its classical
Dirichlet series: `ζ(σ) = ∑_{n ≥ 1} n^{-σ}` for `σ > 1` (the `n = 0` term of the `ℕ`-indexed
sum vanishes because `-σ ≠ 0`). -/
private lemma riemannZeta_re_eq_tsum_rpow (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
  have hσc : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hsum : Summable (LSeries.term (1 : ℕ → ℂ) (σ : ℂ)) := LSeriesSummable_one_iff.mpr hσc
  have h1 : LSeries (1 : ℕ → ℂ) (σ : ℂ) = ∑' n : ℕ, LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n := rfl
  rw [← LSeries_one_eq_riemannZeta (s := (σ : ℂ)) hσc, h1, Complex.re_tsum hsum]
  exact tsum_congr (fun n => by rw [term_one_eq_ofReal σ (by linarith) n, Complex.ofReal_re])

/-- The real sequence `n ↦ n^{-σ}` is summable for `σ > 1`. -/
private lemma summable_nat_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
  have h := (Real.summable_nat_rpow_inv (p := σ)).mpr hσ
  refine h.congr (fun n => ?_)
  exact (Real.rpow_neg (Nat.cast_nonneg n) σ).symm

/-- Integral-test bound for the real zeta series: `∑_{n ≥ 1} n^{-σ} ≤ 1 + 1/(σ-1)` for
`σ > 1`.  The tail `∑_{n ≥ 2} n^{-σ}` is compared with `∫_1^∞ x^{-σ} dx = 1/(σ-1)`. -/
private lemma tsum_rpow_le_one_add (σ : ℝ) (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hσpos : 0 < σ := by linarith
  have hσ0 : σ ≠ 0 := ne_of_gt hσpos
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := summable_nat_rpow_neg hσ
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici (1 : ℝ)) := by
    refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono ?_
    intro x hx
    show (0 : ℝ) < x
    exact lt_of_lt_of_le zero_lt_one hx
  have hint : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) one_pos
  have hnn : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ t ^ (-σ) :=
    fun t ht => Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-σ)) 1
    (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hint)
    (by simpa only [Nat.cast_one] using hnn)
  have hintval : ∫ x in Set.Ioi (↑(1 : ℕ) : ℝ), x ^ (-σ) = 1 / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) (by norm_num : (0 : ℝ) < ↑(1 : ℕ))]
    rw [show (↑(1 : ℕ) : ℝ) = 1 by norm_num, Real.one_rpow]
    rw [div_eq_div_iff (by linarith : (-σ + 1) ≠ 0) (by linarith : (σ - 1) ≠ 0)]
    ring
  have hsum_g : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-σ)) :=
    (summable_nat_add_iff 1).2 hsum
  have hsplit : ∑' n : ℕ, (((n + 1 : ℕ) : ℝ)) ^ (-σ)
      = 1 + ∑' n : ℕ, (((n + 1 + 1 : ℕ) : ℝ)) ^ (-σ) := by
    rw [hsum_g.tsum_eq_zero_add]
    have h0 : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
    rw [h0, Real.one_rpow]
  have hsplit1 : ∑' n : ℕ, (n : ℝ) ^ (-σ)
      = 1 + ∑' n : ℕ, (((n + 1 + 1 : ℕ) : ℝ)) ^ (-σ) := by
    have h0 : (((0 : ℕ) : ℝ)) = (0 : ℝ) := Nat.cast_zero
    rw [hsum.tsum_eq_zero_add, h0, Real.zero_rpow (neg_ne_zero.mpr hσ0), zero_add, hsplit]
  rw [hsplit1]
  have := htail
  rw [hintval] at this
  linarith

/-- `ζ(σ) ≤ 1 + 1/(σ-1)` for real `σ > 1`. -/
private lemma riemannZeta_re_le_one_add (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re ≤ 1 + 1 / (σ - 1) := by
  rw [riemannZeta_re_eq_tsum_rpow σ hσ]
  exact tsum_rpow_le_one_add σ hσ

/-- `ζ(σ) > 0` for real `σ > 1` (the Dirichlet series has nonnegative terms and `1` as its
first term). -/
private lemma riemannZeta_re_pos (σ : ℝ) (hσ : 1 < σ) : 0 < (riemannZeta (σ : ℂ)).re := by
  rw [riemannZeta_re_eq_tsum_rpow σ hσ]
  have hsum := summable_nat_rpow_neg hσ
  have hle : ((1 : ℕ) : ℝ) ^ (-σ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) :=
    hsum.le_tsum 1 (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have h1 : ((1 : ℕ) : ℝ) ^ (-σ) = 1 := by simp [Real.one_rpow]
  linarith

/-- **Lower bound for `L` just to the right of the line `Re s = 1`.**
For `χ ≠ 1` mod `N`, `0 < h ≤ 1` and real `t`, `‖L(1 + h + it, χ)‖ ≥ h/2`. -/
theorem LFunction_lower_one_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (h t : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    h / 2 ≤ ‖DirichletCharacter.LFunction χ (((1 + h : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set s : ℂ := ((1 + h : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = 1 + h := by simp [hs]
  have hσ : 1 < s.re := by rw [hsre]; linarith
  have hσ1h : (1 : ℝ) < 1 + h := by linarith
  have hlow : 1 ≤ ‖DirichletCharacter.LFunction χ s‖ * (riemannZeta (((1 + h : ℝ)) : ℂ)).re := by
    have h := vk_L_lower χ (s := s) hσ
    rwa [hsre] at h
  have hζpos : 0 < (riemannZeta (((1 + h : ℝ)) : ℂ)).re := riemannZeta_re_pos (1 + h) hσ1h
  have hζle : (riemannZeta (((1 + h : ℝ)) : ℂ)).re ≤ 2 / h := by
    have hb := riemannZeta_re_le_one_add (1 + h) hσ1h
    have h1 : (1 : ℝ) + h - 1 = h := by ring
    rw [h1] at hb
    have h2 : (1 : ℝ) + 1 / h ≤ 2 / h := by
      have h3 : (1 : ℝ) ≤ 1 / h := by rw [le_div_iff₀ hh, one_mul]; exact hh1
      have h4 : (2 : ℝ) / h = 1 / h + 1 / h := by ring
      linarith
    linarith
  have hhalf : h / 2 ≤ 1 / (riemannZeta (((1 + h : ℝ)) : ℂ)).re := by
    have h5 := one_div_le_one_div_of_le hζpos hζle
    have h6 : 1 / (2 / h) = h / 2 := by rw [one_div, inv_div]
    linarith
  have hdiv : 1 / (riemannZeta (((1 + h : ℝ)) : ℂ)).re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    rw [div_le_iff₀ hζpos]
    exact hlow
  linarith

end Work.BMF
