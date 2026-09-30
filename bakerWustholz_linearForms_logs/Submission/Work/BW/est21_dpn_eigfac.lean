import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est_gamma_log

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Analytic input of `est21_dpn_eigfac`: if `‖a·g‖ ≤ e^{h+1}·D` and `D ≥ 0`, then the
normalised power `a^t/t! · g^t` is bounded by `e^{h·t + e·D}`.  Indeed
`‖a^t/t!·g^t‖ = ‖a g‖^t/t! ≤ (e^{h+1}D)^t/t! = e^{h t}·((e D)^t/t!) ≤ e^{h t}·e^{e D}`,
the last step being the exponential series (`Real.pow_div_factorial_le_exp`). -/
private lemma norm_pow_div_fact_mul_le {h D : ℝ} (hD : 0 ≤ D) {a g : ℂ} {t : ℕ}
    (ha : ‖a * g‖ ≤ Real.exp (h + 1) * D) :
    ‖a ^ t / ((t.factorial : ℂ)) * g ^ t‖ ≤ Real.exp (h * (t : ℝ) + Real.exp 1 * D) := by
  have h1 : ‖a ^ t / ((t.factorial : ℂ)) * g ^ t‖ = ‖a * g‖ ^ t / ((t.factorial : ℝ)) := by
    simp only [norm_mul, norm_div, norm_inv, norm_pow, Complex.norm_natCast, mul_pow]
    ring
  rw [h1]
  have h2 : ‖a * g‖ ^ t / ((t.factorial : ℝ)) ≤
      (Real.exp (h + 1) * D) ^ t / ((t.factorial : ℝ)) := by
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg t.factorial)
    exact pow_le_pow_left₀ (norm_nonneg _) ha t
  have h3 : (Real.exp (h + 1) * D) ^ t = Real.exp (h * (t : ℝ)) * (Real.exp 1 * D) ^ t := by
    have hassoc : (Real.exp h * Real.exp 1) * D = Real.exp h * (Real.exp 1 * D) := by ring
    rw [Real.exp_add, hassoc, mul_pow, ← Real.exp_nat_mul, mul_comm (t : ℝ) h]
  have h5 : Real.exp (h * (t : ℝ)) * (Real.exp 1 * D) ^ t / ((t.factorial : ℝ))
      = Real.exp (h * (t : ℝ)) * ((Real.exp 1 * D) ^ t / ((t.factorial : ℝ))) := by ring
  have h4 : (Real.exp 1 * D) ^ t / ((t.factorial : ℝ)) ≤ Real.exp (Real.exp 1 * D) :=
    Real.pow_div_factorial_le_exp (Real.exp 1 * D) (mul_nonneg (Real.exp_pos 1).le hD) t
  have hB : (Real.exp (h + 1) * D) ^ t / ((t.factorial : ℝ))
      ≤ Real.exp (h * (t : ℝ)) * ((Real.exp 1 * D) ^ t / ((t.factorial : ℝ))) := by
    rw [h3]
    exact h5.le
  have hC : Real.exp (h * (t : ℝ)) * ((Real.exp 1 * D) ^ t / ((t.factorial : ℝ)))
      ≤ Real.exp (h * (t : ℝ) + Real.exp 1 * D) :=
    (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le).trans
      (le_of_eq (Real.exp_add (h * (t : ℝ)) (Real.exp 1 * D)).symm)
  exact (h2.trans hB).trans hC

theorem est21_dpn_eigfac {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (lm : Fin r → ℕ)
    (hlm : ∀ j, lm j ≤ pDj r (dK K) σ j) (t' : Fin n → ℕ) :
    ‖∏ i, ((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
        ((t' i).factorial : ℂ) * (gam b k L i lm) ^ (t' i))‖
      ≤ Real.exp ((acH K b v : ℝ) * ((∑ i, t' i : ℕ) : ℝ) + (n : ℝ) * Real.exp 1 * acD K σ) := by
  classical
  have hBH : BH φ α b v c r L α' σ := H.hBH
  obtain ⟨hLI, hbspan, hα'ne, hKum, hσpos, hα'hmod, hrow, hkapp⟩ := hBH
  have hst : Standing φ α b k c := H.hst
  obtain ⟨hn2, hαne, hlogind, hgcd, hbk, hmhle, hXbw, hexp1c, hlogc⟩ := hst
  have hr : 2 ≤ r := H.hr
  have hd : 0 < (dK K : ℝ) := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast h
  have hd1 : 1 ≤ dK K := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.cast_pos.mp hd))
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hDnn : 0 ≤ acD K σ := by
    show 0 ≤ pD r (dK K) σ
    simp only [pD]
    have hlog : 0 ≤ Real.log (2 * ↑r * ↑(dK K)) := by
      apply Real.log_nonneg
      have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      have h2 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
      nlinarith
    have hp : 0 ≤ ∏ j : Fin r, σ j := Finset.prod_nonneg (fun j _ => (hσpos j).le)
    have h1 : (0 : ℝ) ≤ 2 * (r : ℝ) ^ r := by positivity
    have h2 : (0 : ℝ) ≤ (32 * (dK K : ℝ)) ^ (r + 1) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hlog) hp
  have hbkabs : (1 : ℝ) ≤ |((b k : ℤ) : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hbk)
  have hstep : ∀ i : Fin n,
      ‖((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
        ((t' i).factorial : ℂ) * (gam b k L i lm) ^ (t' i))‖
      ≤ Real.exp ((acH K b v : ℝ) * (t' i : ℝ) + Real.exp 1 * acD K σ) := by
    intro i
    have hg := (est_gamma_log H i lm hlm).2
    have hAnorm : ‖(((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ))‖
        = (((2 : ℝ) ^ v)⁻¹ * ‖Complex.log (φ (α i))‖) / |((b k : ℤ) : ℝ)| := by
      rw [norm_div, norm_mul, norm_inv, norm_pow, Complex.norm_two, Complex.norm_intCast]
    have hc : ((2 : ℝ) ^ v)⁻¹ / |((b k : ℤ) : ℝ)| ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le zero_lt_one hbkabs)]
      exact le_trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) hbkabs
    have hlogg : ‖Complex.log (φ (α i))‖ * ‖gam b k L i lm‖
        ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ := by
      calc ‖Complex.log (φ (α i))‖ * ‖gam b k L i lm‖
          = ‖Complex.log (φ (α i)) * (gam b k L i lm)‖ := (norm_mul _ _).symm
        _ = ‖(gam b k L i lm) * Complex.log (φ (α i))‖ := by
              rw [mul_comm (Complex.log (φ (α i)))]
        _ ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ := hg
    have hAG : ‖(((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) * (gam b k L i lm)‖
        ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ := by
      rw [norm_mul, hAnorm]
      calc ((((2 : ℝ) ^ v)⁻¹ * ‖Complex.log (φ (α i))‖) / |((b k : ℤ) : ℝ)|)
            * ‖gam b k L i lm‖
          = (((2 : ℝ) ^ v)⁻¹ / |((b k : ℤ) : ℝ)|)
              * (‖Complex.log (φ (α i))‖ * ‖gam b k L i lm‖) := by ring
        _ ≤ 1 * (‖Complex.log (φ (α i))‖ * ‖gam b k L i lm‖) :=
            mul_le_mul_of_nonneg_right hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖Complex.log (φ (α i))‖ * ‖gam b k L i lm‖ := by rw [one_mul]
        _ ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ := hlogg
    exact norm_pow_div_fact_mul_le hDnn hAG
  have hnorm : ‖∏ i, ((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
        ((t' i).factorial : ℂ) * (gam b k L i lm) ^ (t' i))‖
      = ∏ i, ‖((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
        ((t' i).factorial : ℂ) * (gam b k L i lm) ^ (t' i))‖ := by
    simpa using (norm_prod (Finset.univ : Finset (Fin n))
      (fun i => ((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
        ((t' i).factorial : ℂ) * (gam b k L i lm) ^ (t' i))))
  have hexp : (∑ i : Fin n, ((acH K b v : ℝ) * (t' i : ℝ) + Real.exp 1 * acD K σ))
      = (acH K b v : ℝ) * ((∑ i, t' i : ℕ) : ℝ) + (n : ℝ) * Real.exp 1 * acD K σ := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Nat.cast_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  calc ‖∏ i, ((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
        ((t' i).factorial : ℂ) * (gam b k L i lm) ^ (t' i))‖
      = ∏ i, ‖((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
        ((t' i).factorial : ℂ) * (gam b k L i lm) ^ (t' i))‖ := hnorm
    _ ≤ ∏ i, Real.exp ((acH K b v : ℝ) * (t' i : ℝ) + Real.exp 1 * acD K σ) :=
        Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => norm_nonneg _)
          (fun i _ => hstep i)
    _ = Real.exp (∑ i : Fin n, ((acH K b v : ℝ) * (t' i : ℝ) + Real.exp 1 * acD K σ)) :=
        (Real.exp_sum Finset.univ _).symm
    _ = Real.exp ((acH K b v : ℝ) * ((∑ i, t' i : ℕ) : ℝ) + (n : ℝ) * Real.exp 1 * acD K σ) := by
        rw [hexp]

end Work.BW
