import Mathlib
import Submission.Work.LinnikAreas.Zeta1Aux.CommonsImports

namespace Work.LinnikAreas.Zeta1Aux

/-- `riemannZeta₁ w = (w - 1) * riemannZeta w` away from the pole `w = 1`. -/
private lemma riemannZeta₁_eq_mul_sub (w : ℂ) (hw : w ≠ 1) :
    riemannZeta₁ w = (w - 1) * riemannZeta w := by
  have h := riemannZeta_eq_inv_sub_mul (s := w) hw
  calc
    riemannZeta₁ w = (w - 1) * ((w - 1)⁻¹ * riemannZeta₁ w) := by
      rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hw), one_mul]
    _ = (w - 1) * riemannZeta w := by rw [h]

/-- **Growth of `ζ₁` on the disk `‖w - (2 + i t)‖ ≤ 6` at height `|t| ≥ 7`.**

There is `G > 0` such that for every `t` with `7 ≤ |t|` and every `w` with
`‖w - (2 + i t)‖ ≤ 6` one has `‖ζ₁ w‖ ≤ G * (|t| + 9)^13`.

Route: `‖w - c‖ ≤ 6` gives `w.re ∈ [-4, 8]` and `|w.im - t| ≤ 6`, so `|w.im| ≥ 1`
and `|w.im| + 3 ≤ |t| + 9`; also `‖w - 1‖ ≤ ‖w‖ + 1 ≤ |t| + 9` and `w ≠ 1`
(so `‖ζ₁ w‖ = ‖w - 1‖ · ‖ζ w‖`).  For `ζ` itself split on `w.re`:
`hgrowth` for `w.re ∈ [-4, -1]`, `Commons.NumberTheory.Zeta.zeta_strip_polyGrowth`
for `w.re ∈ [-1, 3]` (its quartic factor is `≤ (|t|+9)^12` since `|t| + 9 ≥ 1`), and
`Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re` for `w.re ≥ 3`. -/
lemma zeta1_growth_disk6
    (hgrowth : ∃ Cg : ℝ, 0 < Cg ∧ ∀ σ t : ℝ, -4 ≤ σ → σ ≤ -1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ Cg * (|t| + 3) ^ 12) :
    ∃ G : ℝ, 0 < G ∧ ∀ t : ℝ, 7 ≤ |t| → ∀ w : ℂ,
      ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ 6 →
        ‖riemannZeta₁ w‖ ≤ G * (|t| + 9) ^ 13 := by
  rcases hgrowth with ⟨Cg, hCgpos, hCg⟩
  rcases Commons.NumberTheory.Zeta.zeta_strip_polyGrowth with ⟨Cpg, hCpgpos, hCpg⟩
  rcases Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re with ⟨C3, hC3pos, hC3⟩
  let K : ℝ := max (max Cg Cpg) C3
  have hKpos : 0 < K := by
    dsimp [K]
    exact lt_max_of_lt_left (lt_max_of_lt_left hCgpos)
  have hCgK : Cg ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left Cg Cpg) (le_max_left _ _)
  have hCpgK : Cpg ≤ K := by
    dsimp [K]
    exact le_trans (le_max_right Cg Cpg) (le_max_left _ _)
  have hC3K : C3 ≤ K := by
    dsimp [K]
    exact le_max_right _ _
  refine ⟨K, hKpos, ?_⟩
  intro t ht w hw
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hw' : ‖w - c‖ ≤ 6 := hw
  -- geometry of the disk
  have hre_abs : |w.re - 2| ≤ ‖w - c‖ := by
    simpa [c] using Complex.abs_re_le_norm (w - c)
  have him_abs : |w.im - t| ≤ ‖w - c‖ := by
    simpa [c] using Complex.abs_im_le_norm (w - c)
  have hre_lo : -4 ≤ w.re := by
    have h := (abs_le.mp (le_trans hre_abs hw')).1
    linarith
  have him_dist6 : |w.im - t| ≤ 6 := le_trans him_abs hw'
  have him_up : |w.im| ≤ |t| + 6 := by
    have h : t + (w.im - t) = w.im := by ring
    calc
      |w.im| = |t + (w.im - t)| := by rw [h]
      _ ≤ |t| + |w.im - t| := abs_add_le t (w.im - t)
      _ ≤ |t| + 6 := by linarith
  have him_lo : 1 ≤ |w.im| := by
    have hdec : w.im + (t - w.im) = t := by ring
    have h1 : |t| ≤ |w.im| + |t - w.im| := by
      calc
        |t| = |w.im + (t - w.im)| := by rw [hdec]
        _ ≤ |w.im| + |t - w.im| := abs_add_le _ _
    have h2 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
    rw [h2] at h1
    linarith
  have htri : |w.im| + 3 ≤ |t| + 9 := by linarith
  have hw1le : ‖w - 1‖ ≤ |t| + 9 := by
    have hc1 : ‖c - 1‖ ≤ 1 + |t| := by
      have heq : c - 1 = (1 : ℂ) + Complex.I * (t : ℂ) := by
        simp [c]
        ring
      rw [heq]
      calc
        ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ :=
          norm_add_le _ _
        _ = 1 + |t| := by simp
    have hsum : (w - c) + (c - 1) = w - 1 := by ring
    calc
      ‖w - 1‖ = ‖(w - c) + (c - 1)‖ := by rw [hsum]
      _ ≤ ‖w - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 6 + (1 + |t|) := add_le_add hw' hc1
      _ ≤ |t| + 9 := by linarith
  have hwne : w ≠ 1 := by
    intro h
    have h0 : w.im = 0 := by rw [h]; simp
    rw [h0] at him_lo
    simp at him_lo
    exact absurd him_lo (by norm_num)
  have hnorm_eq : ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := by
    rw [riemannZeta₁_eq_mul_sub w hwne, norm_mul]
  have hX1 : (1 : ℝ) ≤ |t| + 9 := by
    have := abs_nonneg t
    linarith
  have hXpow_nonneg : 0 ≤ (|t| + 9) ^ 12 := by positivity
  -- bound for `ζ w`
  have hzK : ‖riemannZeta w‖ ≤ K * (|t| + 9) ^ 12 := by
    have hwform : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by
      apply Complex.ext <;> simp
    rw [hwform]
    by_cases hcase1 : w.re ≤ -1
    · have hb := hCg w.re w.im hre_lo hcase1 him_lo
      have hpow : (|w.im| + 3) ^ 12 ≤ (|t| + 9) ^ 12 :=
        pow_le_pow_left₀ (by positivity) htri 12
      calc
        ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ ≤
            Cg * (|w.im| + 3) ^ 12 := hb
        _ ≤ Cg * (|t| + 9) ^ 12 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCgpos)
        _ ≤ K * (|t| + 9) ^ 12 := mul_le_mul_of_nonneg_right hCgK hXpow_nonneg
    · have hcase1' : -1 ≤ w.re := by linarith
      by_cases hcase2 : w.re ≤ 3
      · have hb := hCpg w.re w.im hcase1' hcase2 him_lo
        have h4 : (|w.im| + 3) ^ 4 ≤ (|t| + 9) ^ 4 :=
          pow_le_pow_left₀ (by positivity) htri 4
        have h412 : (|t| + 9) ^ 4 ≤ (|t| + 9) ^ 12 :=
          pow_le_pow_right₀ hX1 (by norm_num)
        calc
          ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ ≤
              Cpg * (|w.im| + 3) ^ 4 := hb
          _ ≤ Cpg * (|t| + 9) ^ 4 := mul_le_mul_of_nonneg_left h4 (le_of_lt hCpgpos)
          _ ≤ Cpg * (|t| + 9) ^ 12 := mul_le_mul_of_nonneg_left h412 (le_of_lt hCpgpos)
          _ ≤ K * (|t| + 9) ^ 12 := mul_le_mul_of_nonneg_right hCpgK hXpow_nonneg
      · have hcase2' : 3 ≤ w.re := by linarith
        have hbre : ((w.re : ℂ) + Complex.I * (w.im : ℂ)).re = w.re := by simp
        have hb := hC3 ((w.re : ℂ) + Complex.I * (w.im : ℂ)) (by rw [hbre]; exact hcase2')
        have h12 : (1 : ℝ) ≤ (|t| + 9) ^ 12 := one_le_pow₀ hX1
        calc
          ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ ≤ C3 := hb
          _ = C3 * 1 := by ring
          _ ≤ C3 * (|t| + 9) ^ 12 := mul_le_mul_of_nonneg_left h12 (le_of_lt hC3pos)
          _ ≤ K * (|t| + 9) ^ 12 := mul_le_mul_of_nonneg_right hC3K hXpow_nonneg
  calc
    ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := hnorm_eq
    _ ≤ (|t| + 9) * (K * (|t| + 9) ^ 12) :=
      mul_le_mul hw1le hzK (norm_nonneg _) (by positivity)
    _ = K * (|t| + 9) ^ 13 := by ring

end Work.LinnikAreas.Zeta1Aux
