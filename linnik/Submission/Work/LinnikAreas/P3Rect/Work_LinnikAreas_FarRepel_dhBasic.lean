import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.FarRepel.zeroMult_beta_one_le
import Submission.Work.LinnikAreas.FarRepel.WtDiffBounds

open DirichletCharacter Complex Filter
open scoped Classical BigOperators Topology

noncomputable section

namespace Work.LinnikAreas.FarRepel


/-! ## The zero multiplicity of `ζ_K = ζ·L(·,χ)` and the two-point weight -/

/-- The multiplicity of `u` as a non-trivial zero of `ζ_K = ζ·L(·,χ)`: the vanishing order of the
completed Riemann zeta function at `u` plus `Work.LinnikContract.zeroMult χ u`. -/
def multZ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℂ) : ℕ :=
  analyticOrderNatAt completedRiemannZeta u + Work.LinnikContract.zeroMult χ u

/-- The two-point Deuring–Heilbronn weight `Re (1/(c-u)^{2j}) + Re (1/(c+iγ'-u)^{2j})`. -/
def Wt (c γ' : ℝ) (j : ℕ) (u : ℂ) : ℝ :=
  ((1 / ((c : ℂ) - u)) ^ (2 * j)).re
    + ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u)) ^ (2 * j)).re

/-- At a **real** point `ω < c` the two-point weight is non-negative (this is the "trivial zeros
contribute `≥ 0`" step of Kadiri–Ng–Wong §2). -/
lemma Wt_nonneg_of_im_eq_zero {c γ' : ℝ} {ω : ℂ} (hω : ω.im = 0) (hcω : ω.re < c) (j : ℕ) :
    0 ≤ Wt c γ' j ω := by
  have hx : 0 < c - ω.re := by linarith
  set x : ℝ := c - ω.re with hxdef
  have hωeq : ω = ((ω.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hω
  rw [hωeq, Wt]
  have h1 : (1 / ((c : ℂ) - ((ω.re : ℝ) : ℂ))) ^ (2 * j) = (((1 / x) ^ (2 * j) : ℝ) : ℂ) := by
    have hsub : (c : ℂ) - ((ω.re : ℝ) : ℂ) = (x : ℂ) := by
      rw [hxdef]; push_cast; ring
    rw [hsub, one_div, ← Complex.ofReal_inv, ← Complex.ofReal_pow, one_div]
  rw [h1, Complex.ofReal_re]
  have h2 : -((1 / x) ^ (2 * j)) ≤
      ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - ((ω.re : ℝ) : ℂ))) ^ (2 * j)).re := by
    have hsub2 : (c : ℂ) + Complex.I * (γ' : ℂ) - ((ω.re : ℝ) : ℂ)
        = (x : ℂ) + Complex.I * (γ' : ℂ) := by
      rw [hxdef]; push_cast; ring
    rw [hsub2]
    set w : ℂ := (x : ℂ) + Complex.I * (γ' : ℂ) with hw
    have hwre : w.re = x := by simp [hw]
    have hwnorm : x ≤ ‖w‖ := by
      have h := Complex.re_le_norm w
      rwa [hwre] at h
    have hwnormpos : 0 < ‖w‖ := lt_of_lt_of_le hx hwnorm
    have hle : (1 : ℝ) / ‖w‖ ≤ 1 / x := one_div_le_one_div_of_le hx hwnorm
    have hkey : ‖(1 / w) ^ (2 * j)‖ ≤ (1 / x) ^ (2 * j) := by
      rw [norm_pow, norm_div, norm_one]
      exact pow_le_pow_left₀ (by positivity) hle (2 * j)
    have habs : |((1 / w) ^ (2 * j)).re| ≤ (1 / x) ^ (2 * j) :=
      le_trans (Complex.abs_re_le_norm _) hkey
    have := neg_abs_le (((1 / w) ^ (2 * j)).re)
    linarith [habs, this]
  linarith [h2]

/-- Real part of the multiplicity-weighted zero sum: the coefficient is the multiplicity. -/
lemma re_tsum_multZ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (j : ℕ)
    (hsumm : Summable (fun u : ℂ => (multZ χ u : ℂ) * (1 / (s - u)) ^ (2 * j))) :
    (∑' u : ℂ, (multZ χ u : ℂ) * (1 / (s - u)) ^ (2 * j)).re
      = ∑' u : ℂ, (multZ χ u : ℝ) * ((1 / (s - u)) ^ (2 * j)).re := by
  rw [Complex.re_tsum hsumm]
  exact tsum_congr fun u => by
    rw [Complex.mul_re]
    simp

/-- The trivial-zero series are invariant under taking real parts termwise. -/
lemma re_tsum_triv (d j : ℕ) (s : ℂ)
    (h : Summable (fun n : ℕ => (1 / (s + ((d + 2 * n : ℕ) : ℂ))) ^ (2 * j))) :
    (∑' n : ℕ, (1 / (s + ((d + 2 * n : ℕ) : ℂ))) ^ (2 * j)).re
      = ∑' n : ℕ, ((1 / (s + ((d + 2 * n : ℕ) : ℂ))) ^ (2 * j)).re :=
  Complex.re_tsum h

/-- **The trivial zeros contribute `≥ 0` at the two evaluation points.**  For any `d : ℕ` (the
trivial zeros of `ζ_K` are `-d-2n`, `n ≥ 0`, with `d ∈ {0,1,2,…}`) the two-point real part of the
trivial-zero series is non-negative.  This is the step "trivial zeros contribute `≥ 0`" of
Kadiri–Ng–Wong §2. -/
lemma trivSeries_nonneg {c γ' : ℝ} {j : ℕ} (hc : 0 < c) (hj : 1 ≤ j) (d : ℕ) :
    0 ≤ (∑' n : ℕ, (1 / ((c : ℂ) + ((d + 2 * n : ℕ) : ℂ))) ^ (2 * j)).re
      + (∑' n : ℕ, (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) + ((d + 2 * n : ℕ) : ℂ))) ^ (2 * j)).re := by
  set X : ℕ → ℂ := fun n => (c : ℂ) + ((d + 2 * n : ℕ) : ℂ) with hX
  set Y : ℕ → ℂ := fun n => (c : ℂ) + Complex.I * (γ' : ℂ) + ((d + 2 * n : ℕ) : ℂ) with hY
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * j))⁻¹) := by
    have h := (Real.summable_nat_rpow_inv (p := ((2 * j : ℕ) : ℝ))).mpr (by
      exact_mod_cast (by omega : 1 < 2 * j))
    exact h.congr fun n => by rw [Real.rpow_natCast]
  have key : ∀ (Z : ℕ → ℂ), (∀ n, (Z n).re = c + (d : ℝ) + 2 * n) →
      Summable (fun n => (1 / Z n) ^ (2 * j)) := by
    intro Z hZ
    refine Summable.of_norm_bounded_eventually_nat hbase ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hge : (n : ℝ) ≤ ‖Z n‖ := by
      have h := Complex.re_le_norm (Z n)
      rw [hZ n] at h
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
      linarith
    have hpos : (0:ℝ) < (n:ℝ) := by
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have hZne : Z n ≠ 0 := by
      intro h0
      have : ‖Z n‖ = 0 := by rw [h0]; simp
      linarith
    rw [one_div, norm_pow, norm_inv, inv_pow]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_left₀ (by positivity) hge (2 * j))
  have hsumX : Summable (fun n : ℕ => (1 / X n) ^ (2 * j)) :=
    key X (fun n => by simp [hX, Complex.add_re]; ring)
  have hsumY : Summable (fun n : ℕ => (1 / Y n) ^ (2 * j)) :=
    key Y (fun n => by simp [hY, Complex.add_re]; ring)
  have hreX : Summable (fun n : ℕ => ((1 / X n) ^ (2 * j)).re) :=
    Summable.of_norm_bounded hsumX.norm fun n => by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have hreY : Summable (fun n : ℕ => ((1 / Y n) ^ (2 * j)).re) :=
    Summable.of_norm_bounded hsumY.norm fun n => by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  rw [Complex.re_tsum hsumX, Complex.re_tsum hsumY, ← Summable.tsum_add hreX hreY]
  refine tsum_nonneg fun n => ?_
  have hωpos : (0 : ℝ) ≤ (d + 2 * n : ℕ) := Nat.cast_nonneg _
  have := Wt_nonneg_of_im_eq_zero (c := c) (γ' := γ')
    (ω := -(((d + 2 * n : ℕ) : ℝ) : ℂ)) (by simp) (by
      simp only [Complex.neg_re, Complex.ofReal_re]
      linarith) j
  simpa [Wt, hX, hY, sub_neg_eq_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this

/-- **Final numerical step of the Deuring–Heilbronn inequality.**  From the two-point bound
`∑' u, mult_u · W(u) ≤ 1/(c-1)^{2j} + Re 1/(c+iγ'-1)^{2j}` for the multiplicity-weighted zero sum of
`ζ_K = ζ·L(·,χ)` and the summability of that sum, the target inequality follows: the exceptional
zero `β₁` is subtracted (its multiplicity is `≥ 1`, so the subtraction does not increase the sum)
and the two differences against the pole at `1` are estimated by `WtDiffBounds`. -/
lemma final_step {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {j : ℕ} {c γ' β₁ : ℝ} (hc : 5 ≤ c) (hβ₁ : β₁ < 1)
    (hz₁ : DirichletCharacter.completedLFunction χ (β₁ : ℂ) = 0)
    (hsumm : Summable (fun u : ℂ => (multZ χ u : ℝ) * Wt c γ' j u))
    (hkey : (∑' u : ℂ, (multZ χ u : ℝ) * Wt c γ' j u)
      ≤ 1 / (c - 1) ^ (2 * j)
        + ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - 1)) ^ (2 * j)).re) :
    4 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) ≥
      (∑' u : ℂ, (multZ χ u : ℝ) * Wt c γ' j u)
        - (multZ χ (β₁ : ℂ) : ℝ) * Wt c γ' j (β₁ : ℂ) := by
  have hc1 : 1 < c := by linarith
  -- the multiplicity of the exceptional zero is at least one
  have hmult : (1 : ℝ) ≤ (multZ χ (β₁ : ℂ) : ℝ) := by
    have h1 : 1 ≤ Work.LinnikContract.zeroMult χ (β₁ : ℂ) :=
      zeroMult_beta_one_le χ hχ hprim hβ₁ hz₁
    have h2 : (1 : ℕ) ≤ multZ χ (β₁ : ℂ) := by
      simp only [multZ]
      omega
    exact_mod_cast h2
  have hβc : β₁ < c := by linarith
  have hWβ : 0 ≤ Wt c γ' j (β₁ : ℂ) :=
    Wt_nonneg_of_im_eq_zero (by simp) (by simpa using hβc) j
  -- write the weight at the real point `β₁` in elementary form
  have hWbeta : Wt c γ' j (β₁ : ℂ)
      = 1 / (c - β₁) ^ (2 * j)
        + ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - (β₁ : ℂ))) ^ (2 * j)).re := by
    rw [Wt]
    congr 1
    have hsub : (c : ℂ) - (β₁ : ℂ) = ((c - β₁ : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, one_div, ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re,
      ← one_div_pow, one_div]
  -- the two difference estimates
  obtain ⟨hd1, hd2⟩ := WtDiffBounds (c := c) (γ' := γ') (β := β₁) hβ₁ hc1 j
  rw [abs_le] at hd1 hd2
  -- compare
  have hstep : (∑' u : ℂ, (multZ χ u : ℝ) * Wt c γ' j u)
      - (multZ χ (β₁ : ℂ) : ℝ) * Wt c γ' j (β₁ : ℂ)
      ≤ (1 / (c - 1) ^ (2 * j) + ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - 1)) ^ (2 * j)).re)
        - Wt c γ' j (β₁ : ℂ) := by
    have hFβ : Wt c γ' j (β₁ : ℂ) ≤ (multZ χ (β₁ : ℂ) : ℝ) * Wt c γ' j (β₁ : ℂ) :=
      le_mul_of_one_le_left hWβ hmult
    linarith
  refine le_trans hstep ?_
  rw [hWbeta]
  have hsum : 2 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1)
      + 2 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1)
      = 4 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) := by ring
  linarith [hd1.2, hd2.2, hsum]


end Work.LinnikAreas.FarRepel
