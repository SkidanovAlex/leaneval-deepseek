import Mathlib

namespace Work.LinnikAreas.DhExplicit

/-- Auxiliary: for a real `r > 0` and a complex `z` with `z.re = r`, the real part of the
power `(1/z)^k` is bounded below by `-r^{-k}` while `Re (1/r)^k = r^{-k}`, hence
`Re (1/r)^k + Re (1/z)^k ≥ 0`. -/
lemma trivialPartBoundOdd_aux_re (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z.re = r) (k : ℕ) :
    0 ≤ ((1 / (r : ℂ)) ^ k).re + ((1 / z) ^ k).re := by
  have hA : ((1 / (r : ℂ)) ^ k).re = ‖1 / (r : ℂ)‖ ^ k := by
    rw [one_div, ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re,
        Complex.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hB : -‖1 / z‖ ^ k ≤ ((1 / z) ^ k).re := by
    have h := Complex.abs_re_le_norm ((1 / z) ^ k)
    rw [abs_le] at h
    calc -‖1 / z‖ ^ k = -‖(1 / z) ^ k‖ := by rw [norm_pow]
      _ ≤ ((1 / z) ^ k).re := h.1
  have hle : ‖1 / z‖ ≤ ‖1 / (r : ℂ)‖ := by
    have hzr : r ≤ ‖z‖ := by rw [← hz]; exact Complex.re_le_norm z
    have h1 : ‖1 / z‖ ≤ r⁻¹ := by
      rw [one_div, norm_inv]
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hr hzr
    have h2 : ‖1 / (r : ℂ)‖ = r⁻¹ := by
      rw [one_div, ← Complex.ofReal_inv, Complex.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    rw [h2]; exact h1
  have hpow : ‖1 / z‖ ^ k ≤ ‖1 / (r : ℂ)‖ ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) hle k
  linarith [hA, hB, hpow]

/-- Auxiliary, complex form: if `x` is a positive real (i.e. `x.im = 0`, `0 < x.re`) and
`z.re = x.re`, then `Re (1/x)^k + Re (1/z)^k ≥ 0`. -/
lemma trivialPartBoundOdd_aux (x z : ℂ) (hxim : x.im = 0) (hx : 0 < x.re)
    (hz : z.re = x.re) (k : ℕ) :
    0 ≤ ((1 / x) ^ k).re + ((1 / z) ^ k).re := by
  have hxreal : x = (x.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hxim
  rw [hxreal]
  exact trivialPartBoundOdd_aux_re x.re hx z hz k

/-- **Elementary sign of the "trivial-zero" (Γ) part of the explicit formula, odd character.**

For `j ≥ 1`, `c > 0`, `γ' ∈ ℝ`, with `w = c + iγ'` and the four Γ-series summable,

`Re (1/c^{2j}) + Re (1/w^{2j}) ≤ Σ'_n Re (1/(c+2n))^{2j} + Σ'_n Re (1/(w+2n))^{2j}
                             + Σ'_n Re (1/(c+1+2n))^{2j} + Σ'_n Re (1/(w+1+2n))^{2j}`.

PROOF ROUTE (elementary): the RHS groups as
`[Re(1/c^{2j}) + Σ_{m≥1}Re(1/(c+m))^{2j}] + [Re(1/w^{2j}) + Σ_{m≥1}Re(1/(w+m))^{2j}]`
(the even `m = 2n` and odd `m = 2n+1` parts), so `RHS − LHS = Σ_{m≥1}Re(1/(c+m))^{2j} +
Σ_{m≥1}Re(1/(w+m))^{2j}`, and the second sum dominates the negative of the first termwise because
`Re(w+m) = c+m > 0` gives `Re(1/(w+m)^{2j}) ≥ -|w+m|^{-2j} ≥ -(c+m)^{-2j}`. -/
theorem trivialPartBoundOdd (j : ℕ) (hj : 1 ≤ j) {c γ' : ℝ} (hc : 0 < c)
    (h1 : Summable (fun n : ℕ => (1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)))
    (h2 : Summable (fun n : ℕ => (1 / (1 + ((c : ℂ) + ((2 * n : ℕ) : ℂ)))) ^ (2 * j)))
    (h3 : Summable (fun n : ℕ => (1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)))
    (h4 : Summable (fun n : ℕ => (1 / (1 + (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ)))) ^ (2 * j))) :
    (1 / ((c : ℂ) ^ (2 * j))).re + (1 / (((c : ℂ) + Complex.I * (γ' : ℂ))) ^ (2 * j)).re
      ≤ (∑' n : ℕ, ((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re)
        + (∑' n : ℕ, ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re)
        + (∑' n : ℕ, ((1 / (1 + ((c : ℂ) + ((2 * n : ℕ) : ℂ)))) ^ (2 * j)).re)
        + (∑' n : ℕ, ((1 / (1 + (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ)))) ^ (2 * j)).re) := by
  let w : ℂ := (c : ℂ) + Complex.I * (γ' : ℂ)
  let A : ℕ → ℝ := fun n => ((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re
  let B : ℕ → ℝ := fun n => ((1 / (1 + ((c : ℂ) + ((2 * n : ℕ) : ℂ)))) ^ (2 * j)).re
  let C : ℕ → ℝ := fun n => ((1 / (w + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re
  let D : ℕ → ℝ := fun n => ((1 / (1 + (w + ((2 * n : ℕ) : ℂ)))) ^ (2 * j)).re
  show (1 / ((c : ℂ) ^ (2 * j))).re + (1 / (((c : ℂ) + Complex.I * (γ' : ℂ))) ^ (2 * j)).re
      ≤ (∑' n, A n) + (∑' n, C n) + (∑' n, B n) + (∑' n, D n)
  have hA : Summable A := h1.map Complex.reCLM Complex.reCLM.continuous
  have hB : Summable B := h2.map Complex.reCLM Complex.reCLM.continuous
  have hC : Summable C := h3.map Complex.reCLM Complex.reCLM.continuous
  have hD : Summable D := h4.map Complex.reCLM Complex.reCLM.continuous
  have hA0 : (1 / ((c : ℂ) ^ (2 * j))).re = A 0 := by
    show (1 / ((c : ℂ) ^ (2 * j))).re = ((1 / ((c : ℂ) + ((2 * 0 : ℕ) : ℂ))) ^ (2 * j)).re
    simp only [Nat.mul_zero, Nat.cast_zero, add_zero]
    rw [one_div_pow]
  have hC0 : (1 / (((c : ℂ) + Complex.I * (γ' : ℂ))) ^ (2 * j)).re = C 0 := by
    show (1 / (((c : ℂ) + Complex.I * (γ' : ℂ))) ^ (2 * j)).re
       = ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * 0 : ℕ) : ℂ))) ^ (2 * j)).re
    simp only [Nat.mul_zero, Nat.cast_zero, add_zero]
    rw [one_div_pow]
  have hL : (1 / ((c : ℂ) ^ (2 * j))).re + (1 / (((c : ℂ) + Complex.I * (γ' : ℂ))) ^ (2 * j)).re
      = A 0 + C 0 := by rw [hA0, hC0]
  rw [hL]
  have e1 : (∑' n, A n) = A 0 + ∑' n, A (n+1) := Summable.tsum_eq_zero_add hA
  have e2 : (∑' n, C n) = C 0 + ∑' n, C (n+1) := Summable.tsum_eq_zero_add hC
  have hA' : Summable (fun n => A (n+1)) := (summable_nat_add_iff (f := A) 1).mpr hA
  have hC' : Summable (fun n => C (n+1)) := (summable_nat_add_iff (f := C) 1).mpr hC
  have e3 : (∑' n, A (n+1)) + (∑' n, C (n+1)) = ∑' n, (A (n+1) + C (n+1)) :=
    (hA'.tsum_add hC').symm
  have e4 : (∑' n, B n) + (∑' n, D n) = ∑' n, (B n + D n) := (hB.tsum_add hD).symm
  have p1 : (0:ℝ) ≤ ∑' n, (A (n+1) + C (n+1)) := by
    apply tsum_nonneg
    intro n
    exact trivialPartBoundOdd_aux ((c : ℂ) + ((2 * (n+1) : ℕ) : ℂ))
      (w + ((2 * (n+1) : ℕ) : ℂ))
      (by simp)
      (by simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
          have h2 : (0:ℝ) ≤ ((2*(n+1):ℕ):ℝ) := Nat.cast_nonneg _
          linarith)
      (by simp only [Complex.add_re, Complex.mul_re, w, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re]; ring)
      (2*j)
  have p2 : (0:ℝ) ≤ ∑' n, (B n + D n) := by
    apply tsum_nonneg
    intro n
    exact trivialPartBoundOdd_aux (1 + ((c : ℂ) + ((2 * n : ℕ) : ℂ)))
      (1 + (w + ((2 * n : ℕ) : ℂ)))
      (by simp)
      (by simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re, Complex.one_re]
          have h2 : (0:ℝ) ≤ ((2*n:ℕ):ℝ) := Nat.cast_nonneg _
          linarith)
      (by simp only [Complex.add_re, Complex.mul_re, w, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re]; ring)
      (2*j)
  linarith [e1, e2, e3, e4, p1, p2]

end Work.LinnikAreas.DhExplicit
