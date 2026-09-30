import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.num_est15_arch2
import Submission.Work.BW.num_est15_slacks

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## Assembly of BW (15) at level `J`: the arithmetic core

The Archimedean accounting lemma `num_est15_arch2` bounds three weighted differences by the
three budget terms `0.018`, `0.075`, `0.1` (in the units `(d-1)·S·D/d`), and `num_est15_slacks`
bounds `(D₀+1)` by `0.007·D·(57rd)/d`.  Here these are combined into the single inequality that
`est15` uses: the whole Archimedean bound `estCi` (multiplied by `(1/m)(d-m)`) is dominated by
`(d-1)h(T'+t₀)` plus the three budgets plus the leftover `|s|`-term.

Since `estCi` is the sum of five explicit summands, each is handled separately:
* `T'(1+log(1+Λ/T'))`: `num_est15_arch2` part 1 applied at `T' = estTp t`, plus `m⁻¹(d-m) ≤ d-1`;
* `t₀ log u(h)`: `num_est15_arch2` part 4;
* `(D₀+1)h(1+log μ+1/μ) + (D₀+1)h/μ` (`μ = 57rd`): `num_est15_arch2` part 3;
* `(D₀+1)(2^{-J}|s|)/μ`: `num_est15_slacks` part 3 gives `(D₀+1)/μ ≤ 0.007·D/d`, and
  `m⁻¹(d-m) ≤ d-1 ≤ d`.
-/

/-- If `(d - m)·X ≤ B` with `m ≥ 1` and `B ≥ 0`, then `m⁻¹(d - m)X ≤ B`. -/
private lemma est15_scale (d m X B : ℝ) (hm1 : 1 ≤ m) (hB : 0 ≤ B)
    (h : (d - m) * X ≤ B) : (1 / m) * (d - m) * X ≤ B := by
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
  have h1 : (1 / m) * ((d - m) * X) ≤ (1 / m) * B :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : (1 / m) * B ≤ B := by
    rw [one_div, inv_mul_le_iff₀ hm0]
    nlinarith [hB, hm1]
  have e : (1 / m) * ((d - m) * X) = (1 / m) * (d - m) * X := by ring
  linarith [h1, h2, e.le, e.ge]

/-- `m⁻¹(d - m) ≤ d - 1` for `1 ≤ m` and `1 ≤ d`. -/
private lemma est15_hQle (d m : ℝ) (hm1 : 1 ≤ m) (hd1 : 1 ≤ d) :
    (1 / m) * (d - m) ≤ d - 1 := by
  have hdn : 0 ≤ d - 1 := by linarith
  have h2 : (1 / m) * (d - m) ≤ (1 / m) * (d - 1) :=
    mul_le_mul_of_nonneg_left (by linarith : d - m ≤ d - 1) (by positivity)
  have h3 : (1 / m) * (d - 1) ≤ d - 1 := by
    have h4 : (d - 1) / m ≤ (d - 1) / 1 :=
      div_le_div_of_nonneg_left hdn (by norm_num) hm1
    have e1 : (d - 1) / (1 : ℝ) = d - 1 := by ring
    have e2 : (d - 1) / m = (1 / m) * (d - 1) := by ring
    linarith [h4, e1.le, e1.ge, e2.le, e2.ge]
  linarith

theorem est15_arith_core {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ) (Tst : ℝ)
    (m : ℝ) (hTst : Tst ≤ acT K σ) (hTst0 : 0 ≤ Tst) (ht0 : (t0 : ℝ) ≤ Tst)
    (htp : estTp t ≤ Tst) (hm1 : 1 ≤ m) (hmd : m ≤ (dK K : ℝ)) :
    (1 / m) * ((dK K : ℝ) - m) * estCi K b v σ J t0 t s
      ≤ ((dK K : ℝ) - 1) * ((acH K b v : ℝ) * (estTp t + (t0 : ℝ)))
        + ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ))
        + ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ))
        + ((dK K : ℝ) - 1) * (0.1 * acS K r b v * acD K σ / (dK K : ℝ))
        + 0.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ := by
  classical
  -- ## basic facts about the parameters
  have hr : 2 ≤ r := H.hr
  have hd1 : 1 ≤ dK K := Module.finrank_pos
  have hdR : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < (dK K : ℝ) := by linarith
  have hdnn : (0 : ℝ) ≤ (dK K : ℝ) - 1 := by linarith
  have hrR : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (by omega : 0 < r)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
  have hdm0 : (0 : ℝ) ≤ (dK K : ℝ) - m := by linarith
  have hdle : (dK K : ℝ) - m ≤ (dK K : ℝ) - 1 := by linarith
  have hh0 : (0 : ℝ) ≤ (acH K b v : ℝ) := by positivity
  have hSnn : (0 : ℝ) ≤ acS K r b v := by simp only [acS]; positivity
  have hDpos : (0 : ℝ) < acD K σ := pD_pos hr hd1 σ (fun j => sigma_ge H j)
  have hDnn : (0 : ℝ) ≤ acD K σ := le_of_lt hDpos
  have hTp0 : (0 : ℝ) ≤ estTp t := by simp only [estTp]; positivity
  have hzz0 : (0 : ℝ) ≤ ((|s| : ℤ) : ℝ) / 2 ^ J := by positivity
  have hmu0 : (0 : ℝ) < mu57 K r := by simp only [mu57]; positivity
  have hQle : (1 / m) * ((dK K : ℝ) - m) ≤ (dK K : ℝ) - 1 :=
    est15_hQle _ _ hm1 hdR
  have hD0p_nn : (0 : ℝ) ≤ ((pD0 r (dK K) σ : ℕ) : ℝ) + 1 := by positivity
  -- ## the numeric inputs
  obtain ⟨hA1, hA2, hA3, hA4⟩ := num_est15_arch2 H Tst hTst hTst0 t0 ht0 m hm1 hmd
  have hsl := (num_est15_slacks H J).2.2.1
  -- ## positivity of the budgets
  have hB1nn : (0 : ℝ) ≤ ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ)) :=
    mul_nonneg hdnn (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hSnn) hDnn) (le_of_lt hdpos))
  have hB2nn : (0 : ℝ) ≤ ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ)) :=
    mul_nonneg hdnn (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hSnn) hDnn) (le_of_lt hdpos))
  have hB3nn : (0 : ℝ) ≤ ((dK K : ℝ) - 1) * (0.1 * acS K r b v * acD K σ / (dK K : ℝ)) :=
    mul_nonneg hdnn (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hSnn) hDnn) (le_of_lt hdpos))
  -- ## piece 1: the `Π`-term
  have hP1 : (1 / m) * ((dK K : ℝ) - m) *
      (estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)))
      ≤ ((dK K : ℝ) - 1) * ((acH K b v : ℝ) * estTp t)
        + ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ)) := by
    have hX := hA1 (estTp t) hTp0 htp
    have hkey : ((dK K : ℝ) - m) * (estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)))
        ≤ ((dK K : ℝ) - m) * ((acH K b v : ℝ) * estTp t)
          + ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ)) := by
      linarith [hX]
    have hBnn : (0 : ℝ) ≤ ((dK K : ℝ) - m) * ((acH K b v : ℝ) * estTp t)
          + ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ)) :=
      add_nonneg (mul_nonneg hdm0 (mul_nonneg hh0 hTp0)) hB1nn
    have hs := est15_scale ((dK K : ℝ)) m
      (estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)))
      (((dK K : ℝ) - m) * ((acH K b v : ℝ) * estTp t)
        + ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ)))
      hm1 hBnn hkey
    have hcm : ((dK K : ℝ) - m) * ((acH K b v : ℝ) * estTp t)
        ≤ ((dK K : ℝ) - 1) * ((acH K b v : ℝ) * estTp t) :=
      mul_le_mul_of_nonneg_right hdle (mul_nonneg hh0 hTp0)
    linarith [hs, hcm]
  -- ## piece 2: the `u(h)^{t₀}`-term
  have hP2 : (1 / m) * ((dK K : ℝ) - m) * ((t0 : ℝ) * Real.log (ulcm (acH K b v)))
      ≤ ((dK K : ℝ) - 1) * ((acH K b v : ℝ) * (t0 : ℝ))
        + ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ)) := by
    have ht0nn : (0 : ℝ) ≤ (t0 : ℝ) := Nat.cast_nonneg _
    have hkey : ((dK K : ℝ) - m) * ((t0 : ℝ) * Real.log (ulcm (acH K b v)))
        ≤ ((dK K : ℝ) - m) * ((acH K b v : ℝ) * (t0 : ℝ))
          + ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ)) := by
      linarith [hA4]
    have hBnn : (0 : ℝ) ≤ ((dK K : ℝ) - m) * ((acH K b v : ℝ) * (t0 : ℝ))
          + ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ)) :=
      add_nonneg (mul_nonneg hdm0 (mul_nonneg hh0 ht0nn)) hB2nn
    have hs := est15_scale ((dK K : ℝ)) m
      ((t0 : ℝ) * Real.log (ulcm (acH K b v)))
      (((dK K : ℝ) - m) * ((acH K b v : ℝ) * (t0 : ℝ))
        + ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ)))
      hm1 hBnn hkey
    have hcm : ((dK K : ℝ) - m) * ((acH K b v : ℝ) * (t0 : ℝ))
        ≤ ((dK K : ℝ) - 1) * ((acH K b v : ℝ) * (t0 : ℝ)) :=
      mul_le_mul_of_nonneg_right hdle (mul_nonneg hh0 ht0nn)
    linarith [hs, hcm]
  -- ## piece 3: the `Θ`-term
  have hP3 : (1 / m) * ((dK K : ℝ) - m) *
      ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) *
            (1 + Real.log (mu57 K r) + 1 / mu57 K r)
          + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) / mu57 K r)
      ≤ ((dK K : ℝ) - 1) * (0.1 * acS K r b v * acD K σ / (dK K : ℝ)) := by
    have h3 := est15_scale ((dK K : ℝ)) m
      ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) *
            (1 + Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 1 / (57 * (r : ℝ) * (dK K : ℝ)))
          + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) /
              (57 * (r : ℝ) * (dK K : ℝ)))
      (((dK K : ℝ) - 1) * (0.1 * acS K r b v * acD K σ / (dK K : ℝ)))
      hm1 hB3nn hA3
    simp only [mu57] at h3 ⊢
    exact h3
  -- ## piece 4: the leftover `|s|`-term
  have hD0mu : (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) / mu57 K r ≤ 0.007 * acD K σ / (dK K : ℝ) := by
    have h57 : (0 : ℝ) < 57 * (r : ℝ) * (dK K : ℝ) := by positivity
    rw [mu57]
    rw [div_le_iff₀ h57]
    have heq : 0.007 * acD K σ / (dK K : ℝ) * (57 * (r : ℝ) * (dK K : ℝ))
        = 0.007 * acD K σ * (57 * (r : ℝ) * (dK K : ℝ)) / (dK K : ℝ) := by ring
    rw [heq]
    exact hsl
  have hP4 : (1 / m) * ((dK K : ℝ) - m) *
      ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (((|s| : ℤ) : ℝ) / 2 ^ J) / mu57 K r)
      ≤ 0.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ := by
    have h50 : (1 / m) * ((dK K : ℝ) - m) * ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) / mu57 K r)
        ≤ 0.007 * acD K σ := by
      have h2 := mul_le_mul hQle hD0mu (div_nonneg hD0p_nn (le_of_lt hmu0)) hdnn
      have h5 : (0 : ℝ) ≤ 0.007 * acD K σ := by positivity
      have h4 : ((dK K : ℝ) - 1) / (dK K : ℝ) ≤ 1 := by
        rw [div_le_one hdpos]; linarith
      have h3 : ((dK K : ℝ) - 1) * (0.007 * acD K σ / (dK K : ℝ)) ≤ 0.007 * acD K σ := by
        calc ((dK K : ℝ) - 1) * (0.007 * acD K σ / (dK K : ℝ))
            = 0.007 * acD K σ * (((dK K : ℝ) - 1) / (dK K : ℝ)) := by ring
          _ ≤ 0.007 * acD K σ * 1 := mul_le_mul_of_nonneg_left h4 h5
          _ = 0.007 * acD K σ := by ring
      linarith [h2, h3]
    have h6 : (1 / m) * ((dK K : ℝ) - m) *
          ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (((|s| : ℤ) : ℝ) / 2 ^ J) / mu57 K r)
        = ((1 / m) * ((dK K : ℝ) - m) * ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) / mu57 K r))
            * (((|s| : ℤ) : ℝ) / 2 ^ J) := by ring
    rw [h6]
    have h7 := mul_le_mul_of_nonneg_right h50 hzz0
    linarith [h7]
  -- ## assembly
  rw [estCi]
  linarith [hP1, hP2, hP3, hP4]

end Work.BW
