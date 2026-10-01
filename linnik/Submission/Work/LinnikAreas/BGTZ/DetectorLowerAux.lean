import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorAux
import Submission.Work.LinnikAreas.BGTZ.principal_apply_facts

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

variable {q : ℕ} [NeZero q]

/-- The `n`-th summand of the BGTZ detector `detector χ₁ χ N θ ρ`. -/
def dTerm (χ₁ χ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (ρ : ℂ) (n : ℕ) : ℂ :=
  (aCoeff χ₁ n : ℂ) * (χ n) * ((∑ d ∈ n.divisors, (θ d : ℂ)) ^ 2) * ((n : ℂ) ^ (-ρ))
    * (1 - (n : ℂ) / (N : ℂ))

/-- The real "principal-character" per-term weight of the detector:
`a(n)·1(n)·(Σ_{d|n}θ_d)²·n^{-σ}·(1-n/N)`. -/
def bTerm (χ₁ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  aCoeff χ₁ n * ((1 : DirichletCharacter ℂ q) n).re * (∑ d ∈ n.divisors, θ d) ^ 2
    * (n : ℝ) ^ (-σ) * (1 - (n : ℝ) / (N : ℝ))

lemma detector_eq_sum_dTerm (χ₁ χ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (ρ : ℂ) :
    detector χ₁ χ N θ ρ = ∑ n ∈ Finset.Icc 1 N, dTerm χ₁ χ N θ ρ n := rfl

lemma dTerm_one (χ₁ χ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (hθ1 : θ 1 = 1)
    (ρ : ℂ) : dTerm χ₁ χ N θ ρ 1 = ((1 - 1 / (N : ℝ) : ℝ) : ℂ) := by
  simp only [dTerm, aCoeff_one χ₁, Nat.divisors_one, Finset.sum_singleton, hθ1, Nat.cast_one,
    MulChar.map_one, one_cpow, one_mul]
  push_cast
  ring_nf

lemma bTerm_one (χ₁ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (σ : ℝ) (hθ1 : θ 1 = 1) :
    bTerm χ₁ N θ σ 1 = 1 - 1 / (N : ℝ) := by
  simp only [bTerm, aCoeff_one χ₁, Nat.divisors_one, Finset.sum_singleton, hθ1, Nat.cast_one,
    MulChar.map_one (1 : DirichletCharacter ℂ q), Real.one_rpow, Complex.one_re, one_mul]
  push_cast
  ring


/-- Norm of the real-cast of a real number. -/
lemma norm_ofReal_re (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- **The real part of the principal-character detector is the sum of `bTerm`.** -/
lemma detector_principal_re (χ₁ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (β₁ : ℝ) :
    (detector χ₁ 1 N θ (β₁ : ℂ)).re = ∑ n ∈ Finset.Icc 1 N, bTerm χ₁ N θ β₁ n := by
  rw [detector_eq_sum_dTerm, Complex.re_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hprin : ((1 : DirichletCharacter ℂ q) n)
      = ((((1 : DirichletCharacter ℂ q) n).re : ℝ) : ℂ) := by
    have := (principal_apply_facts (1 : DirichletCharacter ℂ q) n).1
    exact Complex.ext rfl this
  have hsum : ((∑ d ∈ n.divisors, (θ d : ℂ)) : ℂ)
      = (((∑ d ∈ n.divisors, θ d : ℝ)) : ℂ) := (Complex.ofReal_sum _ _).symm
  have hpow : ((∑ d ∈ n.divisors, (θ d : ℂ)) ^ 2)
      = (((∑ d ∈ n.divisors, θ d) ^ 2 : ℝ) : ℂ) := by
    rw [hsum, ← Complex.ofReal_pow]
  have hcpow : ((n : ℂ) ^ (-(β₁ : ℂ))) = (((n : ℝ) ^ (-β₁) : ℝ) : ℂ) := by
    have h1 : (n : ℂ) = (((n : ℝ)) : ℂ) := by simp
    rw [h1]
    have h2 : (-(β₁ : ℂ)) = ((-β₁ : ℝ) : ℂ) := by simp
    rw [h2, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  have hlast : (1 - (n : ℂ) / (N : ℂ)) = (((1 - (n : ℝ) / (N : ℝ)) : ℝ) : ℂ) := by
    push_cast; ring
  simp only [dTerm, bTerm]
  rw [hprin, hpow, hcpow, hlast]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Per-term norm bound**: the modulus of the `n`-th detector summand is at most `bTerm`. -/
lemma norm_dTerm_le_bTerm (χ₁ χ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (ρ : ℂ)
    (hsq : χ₁ ^ 2 = 1) {n : ℕ} (hn : n ∈ Finset.Icc 2 N) :
    ‖dTerm χ₁ χ N θ ρ n‖ ≤ bTerm χ₁ N θ ρ.re n := by
  rw [Finset.mem_Icc] at hn
  obtain ⟨hn2, hnN⟩ := hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsum : ((∑ d ∈ n.divisors, (θ d : ℂ)) : ℂ)
      = (((∑ d ∈ n.divisors, θ d : ℝ)) : ℂ) := (Complex.ofReal_sum _ _).symm
  have hlast : (1 - (n : ℂ) / (N : ℂ)) = (((1 - (n : ℝ) / (N : ℝ)) : ℝ) : ℂ) := by
    push_cast; ring
  have hnormc : ‖dTerm χ₁ χ N θ ρ n‖
      = aCoeff χ₁ n * ‖χ n‖ * (∑ d ∈ n.divisors, θ d) ^ 2 * (n : ℝ) ^ (-ρ.re)
        * (1 - (n : ℝ) / (N : ℝ)) := by
    simp only [dTerm]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    rw [hsum, norm_pow]
    rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n) (-ρ), Complex.neg_re]
    rw [hlast]
    simp only [norm_ofReal_re]
    rw [abs_of_nonneg (aCoeff_nonneg χ₁ hsq n), sq_abs,
      abs_of_nonneg (by rw [sub_nonneg, div_le_one hN0]; exact_mod_cast hnN)]
  have h1 : 0 ≤ aCoeff χ₁ n := aCoeff_nonneg χ₁ hsq n
  have h2 : 0 ≤ (∑ d ∈ n.divisors, θ d) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (n : ℝ) ^ (-ρ.re) := Real.rpow_nonneg hn0.le _
  have h4 : 0 ≤ 1 - (n : ℝ) / (N : ℝ) := by
    rw [sub_nonneg, div_le_one hN0]; exact_mod_cast hnN
  have hle : ‖χ n‖ ≤ ((1 : DirichletCharacter ℂ q) n).re := (principal_apply_facts χ n).2.2.2
  rw [hnormc, bTerm]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle h1) h2) h3) h4

/-- **Monotonicity of `bTerm` in the real exponent `σ`.** -/
lemma bTerm_mono (χ₁ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (hsq : χ₁ ^ 2 = 1)
    {σ σ' : ℝ} (h : σ ≤ σ') {n : ℕ} (hn : n ∈ Finset.Icc 2 N) :
    bTerm χ₁ N θ σ n ≤ (N : ℝ) ^ (σ' - σ) * bTerm χ₁ N θ σ' n := by
  rw [Finset.mem_Icc] at hn
  obtain ⟨hn2, hnN⟩ := hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hc : 0 ≤ aCoeff χ₁ n * ((1 : DirichletCharacter ℂ q) n).re * (∑ d ∈ n.divisors, θ d) ^ 2
      * (1 - (n : ℝ) / (N : ℝ)) := by
    have h1 : 0 ≤ aCoeff χ₁ n := aCoeff_nonneg χ₁ hsq n
    have h2 : 0 ≤ ((1 : DirichletCharacter ℂ q) n).re := (principal_apply_facts χ₁ n).2.1
    have h3 : 0 ≤ (∑ d ∈ n.divisors, θ d) ^ 2 := sq_nonneg _
    have h4 : 0 ≤ 1 - (n : ℝ) / (N : ℝ) := by
      rw [sub_nonneg, div_le_one hN0]; exact_mod_cast hnN
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have hleN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hrpow : (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (σ' - σ) * (n : ℝ) ^ (-σ') := by
    have hsplit : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ') * (n : ℝ) ^ (σ' - σ) := by
      rw [← Real.rpow_add hn0]; ring_nf
    rw [hsplit]
    calc (n : ℝ) ^ (-σ') * (n : ℝ) ^ (σ' - σ) ≤ (n : ℝ) ^ (-σ') * (N : ℝ) ^ (σ' - σ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hn0.le hleN (by linarith : (0:ℝ) ≤ σ' - σ))
            (Real.rpow_pos_of_pos hn0 _).le
      _ = (N : ℝ) ^ (σ' - σ) * (n : ℝ) ^ (-σ') := by ring
  rw [bTerm, bTerm]
  calc aCoeff χ₁ n * ((1 : DirichletCharacter ℂ q) n).re * (∑ d ∈ n.divisors, θ d) ^ 2
        * (n : ℝ) ^ (-σ) * (1 - (n : ℝ) / (N : ℝ))
      = (aCoeff χ₁ n * ((1 : DirichletCharacter ℂ q) n).re * (∑ d ∈ n.divisors, θ d) ^ 2
          * (1 - (n : ℝ) / (N : ℝ))) * (n : ℝ) ^ (-σ) := by ring
    _ ≤ (aCoeff χ₁ n * ((1 : DirichletCharacter ℂ q) n).re * (∑ d ∈ n.divisors, θ d) ^ 2
          * (1 - (n : ℝ) / (N : ℝ))) * ((N : ℝ) ^ (σ' - σ) * (n : ℝ) ^ (-σ')) :=
        mul_le_mul_of_nonneg_left hrpow hc
    _ = (N : ℝ) ^ (σ' - σ) * (aCoeff χ₁ n * ((1 : DirichletCharacter ℂ q) n).re
          * (∑ d ∈ n.divisors, θ d) ^ 2 * (n : ℝ) ^ (-σ') * (1 - (n : ℝ) / (N : ℝ))) := by ring

/-- **The detector lower bound.**  The `n = 1` term of the detector plus the (non-negative)
principal-character detector controls the remaining terms: for `ρ.re ≤ β₁`,
`‖detector χ₁ χ N θ ρ‖ ≥ (1-1/N) - N^{β₁-ρ.re}·((detector χ₁ 1 N θ β₁).re - (1-1/N))`. -/
theorem detector_lower_bound {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q)
    (N : ℕ) (θ : ℕ → ℝ) (ρ : ℂ) (β₁ : ℝ)
    (hsq : χ₁ ^ 2 = 1) (hθ1 : θ 1 = 1) (hN : 2 ≤ N) (hre : ρ.re ≤ β₁) :
    (1 - 1 / (N : ℝ)) - (N : ℝ) ^ (β₁ - ρ.re)
        * ((detector χ₁ 1 N θ (β₁ : ℂ)).re - (1 - 1 / (N : ℝ)))
      ≤ ‖detector χ₁ χ N θ ρ‖ := by
  have hnotin : (1 : ℕ) ∉ Finset.Icc 2 N := by simp only [Finset.mem_Icc]; omega
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hpre : (detector χ₁ 1 N θ (β₁ : ℂ)).re
      = (∑ n ∈ Finset.Icc 2 N, bTerm χ₁ N θ β₁ n) + (1 - 1 / (N : ℝ)) := by
    rw [detector_principal_re, hsplit, Finset.sum_insert hnotin, bTerm_one χ₁ N θ β₁ hθ1]
    ring
  have hper : ∀ n ∈ Finset.Icc 2 N,
      ‖dTerm χ₁ χ N θ ρ n‖ ≤ (N : ℝ) ^ (β₁ - ρ.re) * bTerm χ₁ N θ β₁ n := fun n hn =>
    (norm_dTerm_le_bTerm χ₁ χ N θ ρ hsq hn).trans (bTerm_mono χ₁ N θ hsq hre hn)
  have hsum2 : (∑ n ∈ Finset.Icc 2 N, ‖dTerm χ₁ χ N θ ρ n‖)
      ≤ (N : ℝ) ^ (β₁ - ρ.re) * ∑ n ∈ Finset.Icc 2 N, bTerm χ₁ N θ β₁ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hper
  have hS : detector χ₁ χ N θ ρ
      = dTerm χ₁ χ N θ ρ 1 + ∑ n ∈ Finset.Icc 2 N, dTerm χ₁ χ N θ ρ n := by
    rw [detector_eq_sum_dTerm, hsplit, Finset.sum_insert hnotin]
  have hD1 : dTerm χ₁ χ N θ ρ 1 = (((1 - 1 / (N : ℝ)) : ℝ) : ℂ) := dTerm_one χ₁ χ N θ hθ1 ρ
  have hone : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < (N : ℝ))]
    exact_mod_cast (by omega : 1 ≤ N)
  have hD1norm : ‖dTerm χ₁ χ N θ ρ 1‖ = 1 - 1 / (N : ℝ) := by
    rw [hD1, norm_ofReal_re, abs_of_nonneg hone]
  have hrest : ‖∑ n ∈ Finset.Icc 2 N, dTerm χ₁ χ N θ ρ n‖
      ≤ ∑ n ∈ Finset.Icc 2 N, ‖dTerm χ₁ χ N θ ρ n‖ := norm_sum_le _ _
  have htri : 1 - 1 / (N : ℝ) - (N : ℝ) ^ (β₁ - ρ.re)
        * ((detector χ₁ 1 N θ (β₁ : ℂ)).re - (1 - 1 / (N : ℝ)))
      ≤ ‖detector χ₁ χ N θ ρ‖ := by
    rw [hS]
    have haux : ‖dTerm χ₁ χ N θ ρ 1‖ - ‖∑ n ∈ Finset.Icc 2 N, dTerm χ₁ χ N θ ρ n‖
        ≤ ‖dTerm χ₁ χ N θ ρ 1 + ∑ n ∈ Finset.Icc 2 N, dTerm χ₁ χ N θ ρ n‖ := by
      have h3 := norm_add_le
        (dTerm χ₁ χ N θ ρ 1 + ∑ n ∈ Finset.Icc 2 N, dTerm χ₁ χ N θ ρ n)
        (-(∑ n ∈ Finset.Icc 2 N, dTerm χ₁ χ N θ ρ n))
      simp only [add_neg_cancel_right, norm_neg] at h3
      linarith
    rw [hD1norm] at haux
    have hb : (N : ℝ) ^ (β₁ - ρ.re) * ((detector χ₁ 1 N θ (β₁ : ℂ)).re - (1 - 1 / (N : ℝ)))
        = (N : ℝ) ^ (β₁ - ρ.re) * ∑ n ∈ Finset.Icc 2 N, bTerm χ₁ N θ β₁ n := by
      rw [hpre]; ring
    rw [hb]
    have hc : (N : ℝ) ^ (β₁ - ρ.re) * ∑ n ∈ Finset.Icc 2 N, bTerm χ₁ N θ β₁ n
        ≥ ‖∑ n ∈ Finset.Icc 2 N, dTerm χ₁ χ N θ ρ n‖ := hrest.trans hsum2
    linarith [haux, hc]
  exact htri

end
end Work.LinnikAreas.BGTZ
