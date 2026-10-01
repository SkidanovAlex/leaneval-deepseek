/-
# Pointwise strip bounds and the horizontal-segment vanishing

The pieces needed to make the two horizontal segments of the contour shift to the critical line
`Re s = 1/2 - β` tend to zero.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.LoneLowerDefs
import Submission.Work.LinnikAreas.primeFactors_prod_one_add_rpow_le
import Submission.Work.LinnikAreas.contour_errors_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Work.Sieve.sum_Icc_rpow_neg_half_le

open DirichletCharacter Complex Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace Work.LinnikAreas.BGTZ.CoeffSum

open Work.LinnikAreas

set_option maxHeartbeats 1000000

/-- `‖(r : ℂ)‖ = |r|`. -/
lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

lemma norm_add_mul_I_le' (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + |t| := by
  refine le_trans (norm_add_le _ _) (le_of_eq ?_)
  rw [norm_ofReal_eq_abs, abs_of_nonneg hσ, norm_mul, norm_ofReal_eq_abs]
  simp

/-- The Euler-product factor over the prime divisors of `N` is `≤ exp((log N)^{3/4}) + 1`. -/
lemma prod_primeFactors_le (N : ℕ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (-σ))
      ≤ Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1 := by
  by_cases h : 3 ≤ N
  · have h1 := primeFactors_prod_one_add_rpow_le N h hσ
    linarith [Real.exp_pos ((Real.log N) ^ (3 / 4 : ℝ))]
  · have hN2 : N ≤ 2 := by omega
    have hterm : ∀ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (-σ)) ≤ 2 := by
      intro p hp
      have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
      have h3 : (p : ℝ) ^ (-σ) ≤ 1 := by
        rw [← Real.rpow_zero (p : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      linarith
    have hcard : N.primeFactors.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' : a = 2 := by
        have hpp : a.Prime := Nat.prime_of_mem_primeFactors ha
        have hpd : a ∣ N := Nat.dvd_of_mem_primeFactors ha
        have h2 : 2 ≤ a := hpp.two_le
        have hposN : 0 < N := by
          rcases Nat.eq_zero_or_pos N with h0 | h
          · rw [h0] at ha; simp at ha
          · exact h
        have hle : a ≤ N := Nat.le_of_dvd hposN hpd
        omega
      have hb' : b = 2 := by
        have hpp : b.Prime := Nat.prime_of_mem_primeFactors hb
        have hpd : b ∣ N := Nat.dvd_of_mem_primeFactors hb
        have h2 : 2 ≤ b := hpp.two_le
        have hposN : 0 < N := by
          rcases Nat.eq_zero_or_pos N with h0 | h
          · rw [h0] at ha; simp at ha
          · exact h
        have hle : b ≤ N := Nat.le_of_dvd hposN hpd
        omega
      rw [ha', hb']
    have hprod2 : ∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (-σ)) ≤ 2 := by
      calc ∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (-σ))
          ≤ ∏ _p ∈ N.primeFactors, (2 : ℝ) :=
              Finset.prod_le_prod₀ (fun p _ => by
                have h1 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg p
                have h2 : (0:ℝ) ≤ (p:ℝ) ^ (-σ) := Real.rpow_nonneg h1 _
                linarith) hterm
        _ = (2 : ℝ) ^ N.primeFactors.card := by rw [Finset.prod_const]
        _ ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hcard
        _ = 2 := by norm_num
    have hexp1 : (1 : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · rw [h0]; simp
      · exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hpos)) _
    linarith

/-- `‖ζ(σ + it)‖ ≤ 8√(N+1)` for `1/2 ≤ σ ≤ 1`, `|t| ≥ 1` and `N ≥ |t| + 3`. -/
private lemma zeta_em_bound (σ t : ℝ) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1) (ht : 1 ≤ |t|)
    (N : ℕ) (hN : 1 ≤ N) (hNt : |t| + 3 ≤ (N : ℝ)) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 8 * (((N : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hs0 : 0 < s.re := by rw [hsre]; linarith
  have hsne : s ≠ 1 := by
    intro h
    have h1 : s.im = 0 := by rw [h]; simp
    rw [hsim] at h1
    have h2 : |t| = 0 := by rw [h1]; simp
    linarith [abs_nonneg t]
  obtain ⟨hsum, hbound⟩ := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN s hs0 hsne
  set TT : ℂ := ∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
      (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))) with hTdef
  set H : ℂ := ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)) with hHdef
  set M : ℂ := ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) with hMdef
  have hid : riemannZeta s = H + M + TT := by
    have h := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hsne N hN
    rw [h]
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0le : (0 : ℝ) ≤ (N : ℝ) := hN0.le
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1p : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hhead : ‖H‖ ≤ 2 * (((N : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
    have h1 : ‖H‖ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [hHdef]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have heq : ‖(((n : ℕ) : ℂ) ^ (-s))‖ = (n : ℝ) ^ (-σ) := by
        rw [← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
        rw [show (-s).re = -s.re from Complex.neg_re s, hsre]
      rw [heq]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)
    have h2 := Work.Sieve.sum_Icc_rpow_neg_half_le N hN
    linarith
  have hpole : ‖M‖ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hden : |t| ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, hsim] at h
      simpa using h
    have hden1 : (1 : ℝ) ≤ ‖s - 1‖ := le_trans ht hden
    have hdenpos : (0 : ℝ) < ‖s - 1‖ := lt_of_lt_of_le zero_lt_one hden1
    have hnum : ‖((N : ℕ) : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - σ) := by
      rw [← Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
      rw [show (1 - s).re = 1 - s.re from Complex.sub_re 1 s, hsre]
    rw [hMdef, norm_div, hnum]
    have hstep : (N : ℝ) ^ (1 - σ) / ‖s - 1‖ ≤ (N : ℝ) ^ (1 - σ) := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [Real.rpow_nonneg hN0le (1 - σ), hden1]
    have hstep2 : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    linarith
  have htail : ‖TT‖ ≤ 2 * (((N : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
    have h1 : ‖TT‖ ≤ (‖s‖ / s.re) * ((N : ℝ) ^ (-s.re)) := by
      refine le_trans ?_ hbound
      rw [hTdef]
      exact norm_tsum_le_tsum_norm hsum.norm
    rw [hsre] at h1
    have h3 : ‖s‖ ≤ (N : ℝ) := by
      have h4 : ‖s‖ ≤ σ + |t| := by
        rw [hs]; exact norm_add_mul_I_le' σ t (by linarith)
      have h5 : σ + |t| ≤ (N : ℝ) := by linarith
      linarith
    have h6 : ‖s‖ / σ ≤ 2 * (N : ℝ) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < σ)]
      nlinarith [h3, hσ1]
    have h7 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h8 : (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (N : ℝ) ^ (1 / 2 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hN0]
      norm_num
    have h11 : (‖s‖ / σ) * ((N : ℝ) ^ (-σ)) ≤ (2 * (N : ℝ)) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul h6 h7 (Real.rpow_nonneg hN0le _) (by linarith)
    have h12 : (2 * (N : ℝ)) * ((N : ℝ) ^ (-(1 / 2 : ℝ)))
        ≤ 2 * (((N : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
      rw [show (2 * (N : ℝ)) * ((N : ℝ) ^ (-(1 / 2 : ℝ)))
          = 2 * ((N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ))) by ring, h8]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hN0le (by linarith) (by norm_num)) (by norm_num)
    linarith
  have htri : ‖H + M + TT‖ ≤ ‖H‖ + ‖M‖ + ‖TT‖ := by
    have h1 : ‖H + M + TT‖ ≤ ‖H + M‖ + ‖TT‖ := norm_add_le (H + M) TT
    have h2 : ‖H + M‖ ≤ ‖H‖ + ‖M‖ := norm_add_le H M
    linarith
  have hp : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (((N : ℝ) + 1) ^ (1 / 2 : ℝ)) :=
    Real.rpow_le_rpow hN0le (by linarith) (by norm_num)
  have hsq : (0 : ℝ) ≤ (((N : ℝ) + 1) ^ (1 / 2 : ℝ)) := Real.rpow_nonneg hN1p.le _
  calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = ‖riemannZeta s‖ := by simp [hs]
    _ = ‖H + M + TT‖ := by rw [hid]
    _ ≤ ‖H‖ + ‖M‖ + ‖TT‖ := htri
    _ ≤ 8 * (((N : ℝ) + 1) ^ (1 / 2 : ℝ)) := by linarith

/-- `‖ζ(σ+it)‖ ≤ C(1+|t|)^{1/2}` for `1/2 ≤ σ ≤ 2` and `|t| ≥ 1`. -/
lemma zeta_half_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨CZ, hCZpos, hCZ⟩ := Work.LinnikAreas.zeta_strip_uniform
  refine ⟨max 100 (32 * CZ), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro σ t hσ1 hσ2 ht
  have hbase : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hbpos : (0 : ℝ) < 1 + |t| := by linarith
  have hCJle : CZ ≤ max 100 (32 * CZ) := by
    have : CZ ≤ 32 * CZ := by linarith
    exact le_trans this (le_max_right _ _)
  have h100 : (100 : ℝ) ≤ max 100 (32 * CZ) := le_max_left _ _
  by_cases h : (5 / 8 : ℝ) ≤ σ
  · calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16) := hCZ σ t h (by linarith) ht
      _ ≤ CZ * (1 + |t|) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase (by norm_num))
            hCZpos.le
      _ ≤ max 100 (32 * CZ) * (1 + |t|) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hCJle (Real.rpow_nonneg hbpos.le _)
  · have hσlt : σ < 5 / 8 := not_le.mp h
    have hN1 : 1 ≤ Nat.floor |t| + 4 := by omega
    have hNt : |t| + 3 ≤ ((Nat.floor |t| + 4 : ℕ) : ℝ) := by
      have hfl := Nat.lt_floor_add_one |t|
      push_cast
      linarith
    have hb := zeta_em_bound σ t hσ1 (by linarith) ht (Nat.floor |t| + 4) hN1 hNt
    have hNle : (((Nat.floor |t| + 4 : ℕ) : ℝ) + 1) ≤ 6 * (1 + |t|) := by
      have hfl := Nat.floor_le (abs_nonneg t)
      push_cast
      linarith
    have hsq : (((Nat.floor |t| + 4 : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ)
        ≤ 3 * (1 + |t|) ^ (1 / 2 : ℝ) := by
      calc (((Nat.floor |t| + 4 : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ)
          ≤ (6 * (1 + |t|)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) hNle (by norm_num)
        _ = (6 : ℝ) ^ (1 / 2 : ℝ) * (1 + |t|) ^ (1 / 2 : ℝ) :=
            Real.mul_rpow (by norm_num) hbpos.le
        _ ≤ 3 * (1 + |t|) ^ (1 / 2 : ℝ) := by
            have h6 : (6 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 := by
              rw [← Real.sqrt_eq_rpow]
              nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
            exact mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hbpos.le _)
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 8 * ((((Nat.floor |t| + 4 : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ)) := hb
      _ ≤ 24 * (1 + |t|) ^ (1 / 2 : ℝ) := by linarith [hsq]
      _ ≤ max 100 (32 * CZ) * (1 + |t|) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hbpos.le _)

/-- The majorant for the `L`-function on the strip `1/2 ≤ σ ≤ 2`. -/
def Lmaj (N : ℕ) (t : ℝ) : ℝ :=
  (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
      * (Real.log ((N : ℝ) * (2 + |t|)) + 2)
    + (Real.log (2 * (N : ℝ)) + Real.log (2 + |t|) + 6)


/-- The strip bound for the (possibly imprimitive) Dirichlet `L`-function on `1/2 ≤ σ ≤ 2`. -/
lemma L_half_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 →
      ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Lmaj N t := by
  refine ⟨Real.exp 6 + 1, by positivity, ?_⟩
  intro N _inst ψ hψ σ t hσ1 hσ2 ht
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h2t : (0 : ℝ) < 2 + |t| := by linarith [abs_nonneg t]
  have hNt1 : (1 : ℝ) ≤ (N : ℝ) * (2 + |t|) := by nlinarith
  have hstuff : (0 : ℝ) ≤ (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
      * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
      * (Real.log ((N : ℝ) * (2 + |t|)) + 2) := by
    have h4 : (0 : ℝ) ≤ ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    have h8 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
      have h9 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (2 + |t|)) := Real.log_nonneg hNt1
      linarith
    positivity
  have hlog2N : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hlog2t : (0 : ℝ) ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases hσ : σ ≤ 1
  · haveI hcond : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
    have hprim : ψ.primitiveCharacter.IsPrimitive :=
      DirichletCharacter.primitiveCharacter_isPrimitive ψ
    have hprimne : ψ.primitiveCharacter ≠ 1 :=
      Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one ψ hψ
    have hred := Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le ψ hψ
      (σ := σ) hσ1 (t := t)
    have hprod := prod_primeFactors_le N hσ1
    have hconv := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
      ψ.primitiveCharacter hprimne hprim (σ := σ) (T := t) (by linarith) hσ
    rw [show ((σ : ℂ) + Complex.I * (t : ℂ)) = ((σ : ℂ) + (t : ℂ) * Complex.I) by ring] at hconv
    have hNcpos : (0 : ℝ) < (ψ.conductor : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ψ.conductor)
    have hNcq : (ψ.conductor : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos N) ψ.conductor_dvd_level
    have hNc1 : (1 : ℝ) ≤ (ψ.conductor : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne ψ.conductor)
    have hbpos : (0 : ℝ) < (ψ.conductor : ℝ) * (2 + |t|) := mul_pos hNcpos h2t
    have hlc : (0 : ℝ) < Real.log ((ψ.conductor : ℝ) * (2 + |t|)) + 2 := by
      have h1 : (1 : ℝ) ≤ (ψ.conductor : ℝ) * (2 + |t|) := by nlinarith [hNc1, ht]
      have := Real.log_nonneg h1
      linarith
    have hE : Real.exp (((1 - σ) / 2) * (Real.log (ψ.conductor : ℝ) + Real.log (2 + |t|))
        + Real.log (Real.log ((ψ.conductor : ℝ) * (2 + |t|)) + 2) + 6)
        = Real.exp 6 * ((((ψ.conductor : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2))
            * (Real.log ((ψ.conductor : ℝ) * (2 + |t|)) + 2)) := by
      rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos hbpos, Real.exp_log hlc,
        Real.log_mul (ne_of_gt hNcpos) (ne_of_gt h2t)]
      ring_nf
    have hnorm : ‖DirichletCharacter.LFunction ψ.primitiveCharacter
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Real.exp (((1 - σ) / 2) * (Real.log (ψ.conductor : ℝ) + Real.log (2 + |t|))
            + Real.log (Real.log ((ψ.conductor : ℝ) * (2 + |t|)) + 2) + 6) := by
      have hnn : (0 : ℝ) ≤ ‖DirichletCharacter.LFunction ψ.primitiveCharacter
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
      rcases eq_or_lt_of_le hnn with h0 | hpos
      · rw [← h0]; exact (Real.exp_pos _).le
      · exact (Real.log_le_iff_le_exp hpos).mp hconv
    have hbnd : ‖DirichletCharacter.LFunction ψ.primitiveCharacter
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
            * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by
      rw [hE] at hnorm
      refine hnorm.trans ?_
      have hp1 : ((ψ.conductor : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2)
          ≤ ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ) := by
        calc ((ψ.conductor : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2)
            ≤ ((ψ.conductor : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by nlinarith [hNc1, ht]) (by linarith)
          _ ≤ ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ) :=
              Real.rpow_le_rpow (mul_pos hNcpos h2t).le
                (mul_le_mul_of_nonneg_right hNcq h2t.le) (by norm_num)
      have hp2 : Real.log ((ψ.conductor : ℝ) * (2 + |t|)) + 2
          ≤ Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
        have := Real.log_le_log (mul_pos hNcpos h2t)
          (mul_le_mul_of_nonneg_right hNcq h2t.le)
        linarith
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hp1 hp2 hlc.le (Real.rpow_nonneg (mul_pos hNpos h2t).le _))
        (Real.exp_pos 6).le
    calc ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (-σ)))
            * ‖DirichletCharacter.LFunction ψ.primitiveCharacter
                ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hred
      _ ≤ (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
            * (Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
              * (Real.log ((N : ℝ) * (2 + |t|)) + 2))) :=
          mul_le_mul hprod hbnd (norm_nonneg _) (by positivity)
      _ ≤ (Real.exp 6 + 1) * Lmaj N t := by
          have hswap : (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
              * (Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
                * (Real.log ((N : ℝ) * (2 + |t|)) + 2)))
              = Real.exp 6 * ((Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
                * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
                * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by ring
          rw [hswap, Lmaj]
          have h1 : Real.exp 6 * ((Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
                * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
                * (Real.log ((N : ℝ) * (2 + |t|)) + 2))
              ≤ (Real.exp 6 + 1) * ((Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
                * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
                * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by
            apply mul_le_mul_of_nonneg_right _ hstuff
            linarith [Real.exp_pos 6]
          have h2 : (Real.exp 6 + 1) * ((Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
                * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
                * (Real.log ((N : ℝ) * (2 + |t|)) + 2))
              ≤ (Real.exp 6 + 1) * ((Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
                * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
                * (Real.log ((N : ℝ) * (2 + |t|)) + 2)
                + (Real.log (2 * (N : ℝ)) + Real.log (2 + |t|) + 6)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [hlog2N, hlog2t]
          linarith
  · have hσ' : (1 : ℝ) ≤ σ := (not_le.mp hσ).le
    have h := Work.LinnikAreas.LFunction_log_bound ψ hψ ((σ : ℂ) + (t : ℂ) * Complex.I)
      (by simp; linarith)
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [him] at h
    refine h.trans ?_
    simp only [Lmaj]
    have h3 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) + Real.log (2 + |t|) + 6 := by linarith
    have hexp6 : (1 : ℝ) ≤ Real.exp 6 + 1 := by linarith [Real.exp_pos 6]
    nlinarith [hstuff, h3, hexp6]

/-- Pointwise bound for `triFun` on the horizontal segment `Im s = t`, `Re s = u ∈ [1/2-β, 1]`. -/
lemma norm_triFun_horiz_half :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 →
      ∀ {β x u t : ℝ}, 1 / 2 < β → β < 1 → 0 < x → 1 ≤ |t| →
        1 / 2 - β ≤ u → u ≤ 1 →
      ‖triFun ψ β x ((u : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t * (x + x ^ (-(1 / 2 : ℝ))) / t ^ 2 := by
  obtain ⟨Cz, hCzpos, hZ⟩ := zeta_half_strip
  obtain ⟨CL, hCLpos, hL⟩ := L_half_strip
  refine ⟨Cz * CL, by positivity, ?_⟩
  intro N _inst ψ hψ β x u t hβ hβ1 hx ht hu hu'
  set s : ℂ := (u : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = u := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hsp : s + (β : ℂ) = ((u + β : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    rw [hs]; push_cast; ring
  have hσ1 : (1 / 2 : ℝ) ≤ u + β := by linarith
  have hσ2 : u + β ≤ 2 := by linarith
  have htne : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht; linarith
  have ht2pos : (0 : ℝ) < t ^ 2 := by positivity
  have htbase : (0 : ℝ) < 1 + |t| := by linarith [abs_nonneg t]
  have hζ : ‖riemannZeta (s + (β : ℂ))‖ ≤ Cz * (1 + |t|) ^ (1 / 2 : ℝ) := by
    rw [hsp]; exact hZ (u + β) t hσ1 hσ2 ht
  have hLb : ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖ ≤ CL * Lmaj N t := by
    rw [hsp]; exact hL N ψ hψ (u + β) t hσ1 hσ2 ht
  have hxrpow : ‖(x : ℂ) ^ s‖ = x ^ u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx s, hsre]
  have hden : t ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    have h1 : |t| ≤ ‖s‖ := by
      have h := Complex.abs_im_le_norm s
      rwa [hsim] at h
    have h2 : |t| ≤ ‖s + 1‖ := by
      have h := Complex.abs_im_le_norm (s + 1)
      rw [Complex.add_im, hsim] at h
      simpa using h
    nlinarith [h1, h2, sq_abs t, abs_nonneg t, norm_nonneg s, norm_nonneg (s + 1)]
  have hxu : x ^ u ≤ x + x ^ (-(1 / 2 : ℝ)) := by
    have hβu : (-(1 / 2 : ℝ)) ≤ u := by linarith
    by_cases hx1 : (1 : ℝ) ≤ x
    · have h1 : x ^ u ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hu'
      rw [Real.rpow_one] at h1
      have h2 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
      linarith
    · have hxle : x ≤ 1 := le_of_lt (not_le.mp hx1)
      have h1 : x ^ u ≤ x ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hx hxle hβu
      have h2 : (0 : ℝ) ≤ x := hx.le
      linarith
  have hLmajnn : (0 : ℝ) ≤ Lmaj N t := by
    simp only [Lmaj]
    have h3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
      have h4 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (2 + |t|)) :=
        Real.log_nonneg (by
          have : (1 : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
          nlinarith [abs_nonneg t])
      linarith
    have h5 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) + Real.log (2 + |t|) + 6 := by
      have h6 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_nonneg (by
          have : (1 : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
          linarith)
      have h7 : (0 : ℝ) ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith)
      linarith
    have h2 : (0 : ℝ) ≤ ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    have h1 : (0 : ℝ) ≤ (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) := by positivity
    positivity
  have hCnn : (0 : ℝ) ≤ Cz * CL * (1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t
      * (x + x ^ (-(1 / 2 : ℝ))) := by
    have h1 : (0 : ℝ) ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.rpow_nonneg htbase.le _
    have h4 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
    positivity
  have hmain : ‖triFun ψ β x s‖
      = ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
          * ‖(x : ℂ) ^ s‖ / ‖s * (s + 1)‖ := by
    simp only [triFun, zlFun, norm_div, norm_mul]
  have hnum : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
        * x ^ u
      ≤ Cz * CL * (1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t * (x + x ^ (-(1 / 2 : ℝ))) := by
    have h1 : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
        ≤ (Cz * CL) * ((1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t) := by
      have h2 : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
          ≤ (Cz * (1 + |t|) ^ (1 / 2 : ℝ)) * (CL * Lmaj N t) :=
        mul_le_mul hζ hLb (norm_nonneg _) (by positivity)
      calc ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
          ≤ (Cz * (1 + |t|) ^ (1 / 2 : ℝ)) * (CL * Lmaj N t) := h2
        _ = (Cz * CL) * ((1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t) := by ring
    have h3 : (0 : ℝ) ≤ (Cz * CL) * ((1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t) := by
      have h1 : (0 : ℝ) ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.rpow_nonneg htbase.le _
      positivity
    calc ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖ * x ^ u
        ≤ ((Cz * CL) * ((1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t)) * (x + x ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul h1 hxu (Real.rpow_nonneg hx.le u) h3
      _ = Cz * CL * (1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t * (x + x ^ (-(1 / 2 : ℝ))) := by ring
  rw [hmain, hxrpow, div_le_div_iff₀ (lt_of_lt_of_le ht2pos hden) ht2pos]
  exact mul_le_mul hnum hden ht2pos.le hCnn


/-- **The two horizontal segments of the contour shift tend to zero.** -/
theorem horizSegTendstoZero {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    {β x : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hx : 0 < x) :
    Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I))))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hC⟩ := norm_triFun_horiz_half
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set B₁ : ℝ := 5 * (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * (3 * (N : ℝ)) ^ (1 / 4 : ℝ)
        * (Real.log (3 * (N : ℝ)) + 2) + (Real.log (2 * (N : ℝ)) + 8) + 4 with hBdef
  have hLmajB : ∀ {t : ℝ}, 1 ≤ |t| → Lmaj N t ≤ B₁ * |t| ^ (1 / 2 : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
    have hlogt : Real.log |t| ≤ 4 * |t| ^ (1 / 4 : ℝ) := by
      have h := Real.log_le_rpow_div (x := |t|) (ε := (1 / 4 : ℝ)) (abs_nonneg t) (by norm_num)
      have h2 : |t| ^ (1 / 4 : ℝ) / (1 / 4) = 4 * |t| ^ (1 / 4 : ℝ) := by ring
      linarith [h, h2]
    have hy14le : |t| ^ (1 / 4 : ℝ) ≤ |t| ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
    have hy14nn : (0 : ℝ) ≤ |t| ^ (1 / 4 : ℝ) := Real.rpow_nonneg (abs_nonneg t) _
    have hy12nn : (0 : ℝ) ≤ |t| ^ (1 / 2 : ℝ) := Real.rpow_nonneg (abs_nonneg t) _
    have hy12ge1 : (1 : ℝ) ≤ |t| ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_zero |t|]
      exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
    have hsq : |t| ^ (1 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ) = |t| ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add ht0]; norm_num
    have hlog30 : (0 : ℝ) ≤ Real.log (3 * (N : ℝ)) + 2 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 3 * (N : ℝ)); linarith
    have hlog31 : (1 : ℝ) ≤ Real.log (3 * (N : ℝ)) + 2 := by
      have h1 : (1 : ℝ) ≤ Real.log (3 * (N : ℝ)) := by
        have h2 : Real.log 3 ≤ Real.log (3 * (N : ℝ)) :=
          Real.log_le_log (by norm_num) (by nlinarith [hN1])
        have h3 : (1 : ℝ) ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
          exact le_of_lt Real.exp_one_lt_three
        linarith
      linarith
    have hlog20 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) + 8 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (N : ℝ)); linarith
    have henn : (0 : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1 := by positivity
    have h3Npos : (0 : ℝ) < 3 * (N : ℝ) := by linarith
    have hp1 : ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
        ≤ (3 * (N : ℝ)) ^ (1 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ) := by
      have hbase0 : (0 : ℝ) ≤ (N : ℝ) * (2 + |t|) := by positivity
      have hbase : (N : ℝ) * (2 + |t|) ≤ 3 * (N : ℝ) * |t| := by nlinarith [hN1, ht]
      calc ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ) ≤ (3 * (N : ℝ) * |t|) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow hbase0 hbase (by norm_num)
        _ = (3 * (N : ℝ)) ^ (1 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ) :=
            Real.mul_rpow h3Npos.le (abs_nonneg t)
    have hstep1 : (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
          * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
          * (Real.log ((N : ℝ) * (2 + |t|)) + 2)
        ≤ 5 * (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * (3 * (N : ℝ)) ^ (1 / 4 : ℝ)
          * (Real.log (3 * (N : ℝ)) + 2) * |t| ^ (1 / 2 : ℝ) := by
      have hx0 : (0 : ℝ) < (N : ℝ) * (2 + |t|) := by positivity
      have hbase : (N : ℝ) * (2 + |t|) ≤ 3 * (N : ℝ) * |t| := by nlinarith [hN1, ht]
      have hlogNt : Real.log ((N : ℝ) * (2 + |t|)) ≤ Real.log (3 * (N : ℝ)) + Real.log |t| := by
        have h := Real.log_le_log hx0 hbase
        rw [Real.log_mul (ne_of_gt h3Npos) (ne_of_gt ht0)] at h
        exact h
      have h2b : Real.log ((N : ℝ) * (2 + |t|)) + 2
          ≤ (Real.log (3 * (N : ℝ)) + 2) * (1 + 4 * |t| ^ (1 / 4 : ℝ)) := by
        have h4a : 4 * |t| ^ (1 / 4 : ℝ) ≤ 4 * |t| ^ (1 / 4 : ℝ) * (Real.log (3 * (N : ℝ)) + 2) :=
          le_mul_of_one_le_right (by positivity) hlog31
        nlinarith [hlogNt, hlogt, hlog30, h4a, hy14nn]
      have hmid : (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
            * ((3 * (N : ℝ)) ^ (1 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ))
            * ((Real.log (3 * (N : ℝ)) + 2) * (1 + 4 * |t| ^ (1 / 4 : ℝ)))
          ≤ 5 * (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * (3 * (N : ℝ)) ^ (1 / 4 : ℝ)
            * (Real.log (3 * (N : ℝ)) + 2) * |t| ^ (1 / 2 : ℝ) := by
        have hkey : |t| ^ (1 / 4 : ℝ) * (1 + 4 * |t| ^ (1 / 4 : ℝ)) ≤ 5 * |t| ^ (1 / 2 : ℝ) := by
          nlinarith [hsq, hy14le, hy14nn]
        have hc : (0 : ℝ) ≤ (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * (3 * (N : ℝ)) ^ (1 / 4 : ℝ)
            * (Real.log (3 * (N : ℝ)) + 2) :=
          mul_nonneg (mul_nonneg henn (Real.rpow_nonneg h3Npos.le _)) hlog30
        calc (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
              * ((3 * (N : ℝ)) ^ (1 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ))
              * ((Real.log (3 * (N : ℝ)) + 2) * (1 + 4 * |t| ^ (1 / 4 : ℝ)))
            = ((Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * (3 * (N : ℝ)) ^ (1 / 4 : ℝ)
                * (Real.log (3 * (N : ℝ)) + 2))
              * (|t| ^ (1 / 4 : ℝ) * (1 + 4 * |t| ^ (1 / 4 : ℝ))) := by ring
          _ ≤ ((Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * (3 * (N : ℝ)) ^ (1 / 4 : ℝ)
                * (Real.log (3 * (N : ℝ)) + 2)) * (5 * |t| ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hkey hc
          _ = 5 * (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * (3 * (N : ℝ)) ^ (1 / 4 : ℝ)
                * (Real.log (3 * (N : ℝ)) + 2) * |t| ^ (1 / 2 : ℝ) := by ring
      have hcnn : (0 : ℝ) ≤ Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
        have h1 : (1 : ℝ) ≤ (N : ℝ) * (2 + |t|) := by nlinarith [hN1, abs_nonneg t]
        have h2 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (2 + |t|)) := Real.log_nonneg h1
        linarith
      have hbnn : (0 : ℝ) ≤ (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
          * ((3 * (N : ℝ)) ^ (1 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ)) := by positivity
      calc (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
            * ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ)
            * (Real.log ((N : ℝ) * (2 + |t|)) + 2)
          ≤ (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1)
            * ((3 * (N : ℝ)) ^ (1 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ))
            * ((Real.log (3 * (N : ℝ)) + 2) * (1 + 4 * |t| ^ (1 / 4 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hp1 henn) h2b hcnn hbnn
        _ ≤ _ := hmid
    have hstep2 : Real.log (2 * (N : ℝ)) + Real.log (2 + |t|) + 6
        ≤ ((Real.log (2 * (N : ℝ)) + 8) + 4) * |t| ^ (1 / 2 : ℝ) := by
      have h2a : Real.log (2 + |t|) ≤ Real.log (3 * |t|) :=
        Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
      have h2b : Real.log (3 * |t|) = Real.log 3 + Real.log |t| :=
        Real.log_mul (by norm_num) (ne_of_gt ht0)
      have h2c : Real.log 3 ≤ 2 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith
      nlinarith [h2a, h2b, h2c, hlogt, hy14le, hy12ge1, hlog20]
    rw [Lmaj, hBdef]
    linarith [hstep1, hstep2]
  have hKxnn : (0 : ℝ) ≤ x + x ^ (-(1 / 2 : ℝ)) := by
    have h2 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
    linarith
  have hBnn : (0 : ℝ) ≤ B₁ := by
    rw [hBdef]
    have h1 : (0 : ℝ) ≤ Real.log (3 * (N : ℝ)) + 2 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 3 * (N : ℝ)); linarith
    have h2 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) + 8 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (N : ℝ)); linarith
    have h5 : (0 : ℝ) ≤ (3 * (N : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
    have h6 : (0 : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1 := by positivity
    have h7 : (0 : ℝ) ≤ 5 * (Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1) * (3 * (N : ℝ)) ^ (1 / 4 : ℝ)
        * (Real.log (3 * (N : ℝ)) + 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h6) h5) h1
    linarith
  have hKnn : (0 : ℝ) ≤ C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁) := by
    have h2 : (0 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
    positivity
  have hpt : ∀ {u t : ℝ}, 1 / 2 - β ≤ u → u ≤ 1 → 1 ≤ |t| →
      ‖triFun ψ β x ((u : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * |t| ^ (-(1 / 4 : ℝ)) := by
    intro u t hu hu' ht
    have h1 := hC N ψ hψ hβ hβ1 hx ht hu hu'
    have hLm := hLmajB ht
    have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
    have htne : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht; linarith
    have hb : (1 + |t|) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) * |t| ^ (1 / 2 : ℝ) := by
      calc (1 + |t|) ^ (1 / 2 : ℝ) ≤ (2 * |t|) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith [abs_nonneg t]) (by linarith) (by norm_num)
        _ = 2 ^ (1 / 2 : ℝ) * |t| ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) (abs_nonneg t)
    have hq : |t| ^ (1 / 2 : ℝ) * |t| ^ (1 / 2 : ℝ) = |t| := by
      rw [← Real.rpow_add ht0]; norm_num
    have h2 : (1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t / t ^ 2 ≤ 2 ^ (1 / 2 : ℝ) * B₁ / |t| := by
      have hpos : (0 : ℝ) < t ^ 2 := by positivity
      have hLmajnn : (0 : ℝ) ≤ Lmaj N t := by
        rw [Lmaj]
        have h6 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
          have h7 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (2 + |t|)) :=
            Real.log_nonneg (by nlinarith [hN1, abs_nonneg t])
          linarith
        have h8 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) + Real.log (2 + |t|) + 6 := by
          have h9 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
          have h10 : (0 : ℝ) ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
          linarith
        have h11 : (0 : ℝ) ≤ ((N : ℝ) * (2 + |t|)) ^ (1 / 4 : ℝ) :=
          Real.rpow_nonneg (by positivity) _
        have h12 : (0 : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) + 1 := by positivity
        positivity
      have h3 : (1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t / t ^ 2
          ≤ (2 ^ (1 / 2 : ℝ) * |t| ^ (1 / 2 : ℝ)) * (B₁ * |t| ^ (1 / 2 : ℝ)) / t ^ 2 := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact mul_le_mul hb hLm hLmajnn (by positivity)
      have h4 : (2 ^ (1 / 2 : ℝ) * |t| ^ (1 / 2 : ℝ)) * (B₁ * |t| ^ (1 / 2 : ℝ)) / t ^ 2
          = 2 ^ (1 / 2 : ℝ) * B₁ / |t| := by
        have htne' : |t| ≠ 0 := ne_of_gt ht0
        rw [(sq_abs t).symm,
          show (2 ^ (1 / 2 : ℝ) * |t| ^ (1 / 2 : ℝ)) * (B₁ * |t| ^ (1 / 2 : ℝ))
            = 2 ^ (1 / 2 : ℝ) * B₁ * (|t| ^ (1 / 2 : ℝ) * |t| ^ (1 / 2 : ℝ)) by ring, hq]
        field_simp
      linarith [h3, h4.le]
    have h5 : 2 ^ (1 / 2 : ℝ) * B₁ / |t| ≤ 2 ^ (1 / 2 : ℝ) * B₁ * |t| ^ (-(1 / 4 : ℝ)) := by
      rw [show 2 ^ (1 / 2 : ℝ) * B₁ / |t| = 2 ^ (1 / 2 : ℝ) * B₁ * |t| ^ (-(1 : ℝ)) by
        rw [Real.rpow_neg_one]; ring]
      have hB' : (0 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) * B₁ := by
        have h2 : (0 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
        positivity
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by norm_num)) hB'
    refine h1.trans ?_
    calc C * (1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t * (x + x ^ (-(1 / 2 : ℝ))) / t ^ 2
        = C * (x + x ^ (-(1 / 2 : ℝ))) * ((1 + |t|) ^ (1 / 2 : ℝ) * Lmaj N t / t ^ 2) := by ring
      _ ≤ C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁ / |t|) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁ * |t| ^ (-(1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁) * |t| ^ (-(1 / 4 : ℝ)) := by ring
  have hLx : (1 / 2 - β : ℝ) ≤ 1 := by linarith
  have hbnd : ∀ T : ℝ, 1 ≤ T →
      ‖(1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I)))‖
      ≤ 4 * (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)) := by
    intro T hT
    have hT1 : (1 : ℝ) ≤ |T| := by rw [abs_of_nonneg (by linarith)]; exact hT
    have hT1' : (1 : ℝ) ≤ |-T| := by rwa [abs_neg]
    have hVal : (1 : ℝ) ≤ |1 - (1 / 2 - β : ℝ)| := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have hVal2 : |1 - (1 / 2 - β : ℝ)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have hI1 : ‖(∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I))‖
        ≤ (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)) * 2 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 - β : ℝ)) (b := 1)
        (C := (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)))
        (f := fun u : ℝ => triFun ψ β x ((u : ℂ) + T * Complex.I))
        (fun u hu => by
          rw [Set.uIoc_of_le hLx] at hu
          simpa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)] using hpt hu.1.le hu.2 hT1)
      calc _ ≤ ((C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)))
            * |1 - (1 / 2 - β : ℝ)| := h
        _ ≤ ((C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ))) * 2 := by
            have h3 : (0 : ℝ) ≤ (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)) := by
              have h4 : (0 : ℝ) ≤ T ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
              positivity
            exact mul_le_mul_of_nonneg_left hVal2 h3
    have hI2 : ‖(∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I))‖
        ≤ (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)) * 2 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 - β : ℝ)) (b := 1)
        (C := (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)))
        (f := fun u : ℝ => triFun ψ β x ((u : ℂ) - T * Complex.I))
        (fun u hu => by
          rw [Set.uIoc_of_le hLx] at hu
          have h' := hpt (t := -T) hu.1.le hu.2 hT1'
          rw [show ((u : ℂ) - (T : ℂ) * Complex.I)
            = ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) by push_cast; ring]
          simpa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)] using h')
      calc _ ≤ ((C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)))
            * |1 - (1 / 2 - β : ℝ)| := h
        _ ≤ ((C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ))) * 2 := by
            have h3 : (0 : ℝ) ≤ (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)) := by
              have h4 : (0 : ℝ) ≤ T ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
              positivity
            exact mul_le_mul_of_nonneg_left hVal2 h3
    have hnormc : ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ ≤ 1 := by
      have hden : ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
        have hp : ‖((Real.pi : ℂ))‖ = Real.pi :=
          (norm_ofReal_eq_abs Real.pi).trans (abs_of_nonneg Real.pi_pos.le)
        calc ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖
            = ‖((2 : ℂ))‖ * ‖((Real.pi : ℂ))‖ * ‖(Complex.I)‖ := by rw [norm_mul, norm_mul]
          _ = 2 * Real.pi := by rw [Complex.norm_two, hp, Complex.norm_I, mul_one]
      rw [norm_div, hden, norm_one, div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
      linarith [Real.pi_gt_three]
    calc ‖(1 / (2 * Real.pi * Complex.I)) *
          ((∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I))
           - (∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I)))‖
        = ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ *
            ‖(∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I))
             - (∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I))‖ :=
          norm_mul _ _
      _ ≤ 1 * (‖(∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I))‖
             + ‖(∫ u in ((1 / 2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I))‖) := by
          apply mul_le_mul hnormc (norm_sub_le _ _) (by positivity) (by norm_num)
      _ ≤ 1 * (((C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)) * 2)
             + ((C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)) * 2)) := by
          apply mul_le_mul_of_nonneg_left (by linarith [hI1, hI2]) (by norm_num)
      _ = 4 * (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)) * T ^ (-(1 / 4 : ℝ)) := by ring
  have hlim : Filter.Tendsto (fun T : ℝ => 4 * (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁))
      * T ^ (-(1 / 4 : ℝ))) Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    simpa using h.const_mul (4 * (C * (x + x ^ (-(1 / 2 : ℝ))) * (2 ^ (1 / 2 : ℝ) * B₁)))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _))
    (Filter.eventually_atTop.mpr ⟨1, fun T hT => hbnd T hT⟩) hlim


end Work.LinnikAreas.BGTZ.CoeffSum
