import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.P231.ReducedDefs
import Submission.Work.FIArea7.P231.LBilinStar_reindex
import Submission.Work.FIArea7.P231M.Coprime
import Submission.Work.FIArea7.P231M.divisorsTauWeight
import Submission.Work.FIArea7.P231M.prodInvSqLeRad
import Submission.Work.FIArea7.P231.card_divisors_mul_le

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea7.P231M

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. `(log x)^A ≤ C x^ε` for `x ≥ 2` -/

theorem logPowLeConstRpow (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → (Real.log x) ^ A ≤ C * x ^ ε := by
  rcases eq_or_lt_of_le hA with h0 | hpos
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [← h0, Real.rpow_zero]
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have : (1 : ℝ) ≤ x ^ ε := Real.one_le_rpow hx1 hε.le
    simpa using this
  · set r : ℝ := ε / (2 * A) with hr
    have hr0 : 0 < r := by rw [hr]; positivity
    refine ⟨r ^ (-A), by positivity, fun x hx => ?_⟩
    have hx0 : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have h1 : Real.log x ≤ x ^ r / r := Real.log_le_rpow_div (le_of_lt hx0) hr0
    have h2 : (Real.log x) ^ A ≤ (x ^ r / r) ^ A := Real.rpow_le_rpow hlog0 h1 hA
    have h3 : (x ^ r / r) ^ A = x ^ (ε / 2) * r ^ (-A) := by
      rw [div_eq_mul_inv]
      rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt hx0) r)
        (by positivity : (0 : ℝ) ≤ r⁻¹), Real.inv_rpow (le_of_lt hr0)]
      rw [Real.rpow_neg (le_of_lt hr0) A]
      have hAne : A ≠ 0 := ne_of_gt hpos
      have hrA : r * A = ε / 2 := by
        rw [hr]; field_simp; try ring
      rw [(Real.rpow_mul (le_of_lt hx0) r A).symm, hrA]
    rw [h3] at h2
    refine h2.trans ?_
    calc x ^ (ε / 2) * r ^ (-A) ≤ x ^ ε * r ^ (-A) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) (by positivity)
      _ = r ^ (-A) * x ^ ε := by ring

/-! ## 2. The `c`-smooth divisor sum -/

theorem smoothTauSumLe (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℕ, 1 ≤ c → ∀ M : ℕ,
      (∑ a ∈ (Finset.Icc 1 M).filter (Work.FIArea7.P231.IsSmooth c),
          (((a.divisors.card : ℕ) : ℝ)) * (a : ℝ) ^ (-(11 / 12 : ℝ)))
        ≤ K * (c : ℝ) ^ ε := by
  obtain ⟨K1, hK1pos, hK1⟩ := prodInvSqLeRad ε hε
  refine ⟨K1, hK1pos, ?_⟩
  intro c hc M
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    have hemp : (Finset.Icc 1 0).filter (Work.FIArea7.P231.IsSmooth c) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      omega
    rw [hemp, Finset.sum_empty]
    positivity
  · have hsub : (Finset.Icc 1 M).filter (Work.FIArea7.P231.IsSmooth c)
        ⊆ (c ^ M).divisors := by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      obtain ⟨⟨ha1, haM⟩, haS⟩ := ha
      have ha0 : a ≠ 0 := by omega
      refine Nat.mem_divisors.mpr ⟨?_, pow_ne_zero M (by omega)⟩
      exact (Work.FIArea7.P231.isSmooth_dvd_pow ha0 haS).trans (Nat.pow_dvd_pow c haM)
    have hcM : 1 ≤ c ^ M := Nat.one_le_pow M c hc
    calc (∑ a ∈ (Finset.Icc 1 M).filter (Work.FIArea7.P231.IsSmooth c),
            (((a.divisors.card : ℕ) : ℝ)) * (a : ℝ) ^ (-(11 / 12 : ℝ)))
        ≤ ∑ a ∈ (c ^ M).divisors,
            (((a.divisors.card : ℕ) : ℝ)) * (a : ℝ) ^ (-(11 / 12 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun a _ _ => by positivity)
      _ ≤ ∏ p ∈ (c ^ M).primeFactors,
            ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹ := divisorsTauWeight (c ^ M) hcM
      _ = ∏ p ∈ c.primeFactors, ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹ := by
          rw [Nat.primeFactors_pow c (by omega : M ≠ 0)]
      _ ≤ K1 * (∏ p ∈ c.primeFactors, (p : ℝ)) ^ ε := hK1 c hc
      _ ≤ K1 * (c : ℝ) ^ ε := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hK1pos)
          refine Real.rpow_le_rpow (by positivity) ?_ hε.le
          have hdvd : (∏ p ∈ c.primeFactors, p) ∣ c := Nat.prod_primeFactors_dvd c
          have hle : (∏ p ∈ c.primeFactors, p) ≤ c := Nat.le_of_dvd (by omega) hdvd
          have hle' : ((∏ p ∈ c.primeFactors, p : ℕ) : ℝ) ≤ (c : ℝ) := Nat.cast_le.mpr hle
          simpa using hle'

/-! ## 3. `ReducedBound ⟹ CoprimeBoundEps ε` -/

/-- The weight `τ(a)·a^{-11/12}` of the `c`-smooth divisor sum. -/
def tauWeight (a : ℕ) : ℝ := (((a.divisors.card : ℕ) : ℝ)) * (a : ℝ) ^ (-(11 / 12 : ℝ))

/-- The summand of the `c`-smooth decomposition of `L∗(M,N)`: for `a`, `b` `c`-smooth, the
restricted form with modulus `a b c` and coefficients dilated by `a`, `b`, restricted to the
`c`-coprime parts. -/
def redSummand (M N c : ℕ) (ψ : GaussianInt → ℂ) (α β : ℕ → ℂ) (a b : ℕ) : ℂ :=
  if Nat.Coprime a b then
    Work.FIArea7.LBilinStar (M / a) (N / b) (a * b * c) ψ
      (fun m' => if Nat.Coprime m' c then α (a * m') else 0)
      (fun n' => if Nat.Coprime n' c then β (b * n') else 0)
  else 0

lemma redSummand_apply (M N c : ℕ) (ψ : GaussianInt → ℂ) (α β : ℕ → ℂ) (a b : ℕ) :
    redSummand M N c ψ α β a b
      = if Nat.Coprime a b then
          Work.FIArea7.LBilinStar (M / a) (N / b) (a * b * c) ψ
            (fun m' => if Nat.Coprime m' c then α (a * m') else 0)
            (fun n' => if Nat.Coprime n' c then β (b * n') else 0)
        else 0 := rfl

lemma lbilinStar_reindex_summand {c M N : ℕ} (hc : 1 ≤ c) (ψ : GaussianInt → ℂ)
    (α β : ℕ → ℂ) :
    Work.FIArea7.LBilinStar M N c ψ α β
      = ∑ a ∈ (Finset.Icc 1 M).filter (Work.FIArea7.P231.IsSmooth c),
          ∑ b ∈ (Finset.Icc 1 N).filter (Work.FIArea7.P231.IsSmooth c),
            redSummand M N c ψ α β a b := by
  rw [Work.FIArea7.P231.LBilinStar_reindex hc ψ α β]
  rfl

lemma sum_sum_factor (s t : Finset ℕ) (P : ℝ) (u v : ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, P * (u a * v b)) = P * ((∑ a ∈ s, u a) * (∑ b ∈ t, v b)) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mul_sum]

theorem coprimeBound_of_reduced (hR : Work.FIArea7.ReducedBound) :
    ∀ ε : ℝ, 0 < ε → CoprimeBoundEps ε := by
  intro ε hε
  obtain ⟨C_R, A_R, hCR, hAR, hbound⟩ := hR
  obtain ⟨K1, hK1pos, hK1⟩ := smoothTauSumLe (ε / 4) (by linarith)
  obtain ⟨K2, hK2pos, hK2⟩ := logPowLeConstRpow A_R (ε / 2) hAR.le (by linarith)
  refine ⟨C_R * K1 ^ 2 * K2, by positivity, ?_⟩
  intro M N c k χ α β hc hM hN hχ hχmul hα hβ
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMN0 : (0 : ℝ) ≤ (M : ℝ) * (N : ℝ) := by positivity
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  set A : ℝ := ((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12) with hA
  set B : ℝ := ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12) with hB
  set Lb : ℝ := ((M : ℝ) * (N : ℝ) + (c : ℝ) + 2) with hLb
  set τc : ℝ := (((c.divisors.card : ℕ) : ℝ)) with hτc
  set LM : ℝ := (Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ A_R with hLM
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hLb0 : 0 ≤ Lb := by rw [hLb]; positivity
  have hLbpos : (0 : ℝ) < Lb := by rw [hLb]; linarith [hMN0, hc0]
  have hLM0 : 0 ≤ LM := by
    rw [hLM]
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith [hMN0])) A_R
  have hτc0 : 0 ≤ τc := by rw [hτc]; positivity
  set ψ : GaussianInt → ℂ := Work.FIArea7.grossenChar χ k with hψ
  have hP0 : 0 ≤ C_R * τc * A * B * LM := by
    have h1 : (0 : ℝ) ≤ C_R * τc * A * B := by
      have h3 : (0 : ℝ) ≤ C_R * τc := mul_nonneg (le_of_lt hCR) hτc0
      have h4 : (0 : ℝ) ≤ C_R * τc * A := mul_nonneg h3 hA0
      exact mul_nonneg h4 hB0
    exact mul_nonneg h1 hLM0
  set SM : Finset ℕ := (Finset.Icc 1 M).filter (Work.FIArea7.P231.IsSmooth c) with hSM
  set SN : Finset ℕ := (Finset.Icc 1 N).filter (Work.FIArea7.P231.IsSmooth c) with hSN
  rw [lbilinStar_reindex_summand hc ψ α β, ← hSM, ← hSN]
  have hstep : ∀ a ∈ SM, ∀ b ∈ SN,
      ‖redSummand M N c ψ α β a b‖
        ≤ (C_R * τc * A * B * LM) * (tauWeight a * tauWeight b) := by
    intro a ha b hb
    rw [hSM] at ha
    rw [hSN] at hb
    rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
    obtain ⟨⟨ha1, haM'⟩, haS⟩ := ha
    obtain ⟨⟨hb1, hbN'⟩, hbS⟩ := hb
    have hapos : 0 < a := ha1
    have hbpos : 0 < b := hb1
    have hMa : 1 ≤ M / a := (Nat.one_le_div_iff hapos).mpr haM'
    have hNb : 1 ≤ N / b := (Nat.one_le_div_iff hbpos).mpr hbN'
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
    have ha1R : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have hb1R : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    by_cases hab : Nat.Coprime a b
    · rw [redSummand_apply, if_pos hab]
      have hcab : 1 ≤ a * b * c := by
        refine Nat.one_le_iff_ne_zero.mpr ?_
        exact Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega)
      have hαg : ∀ m, m ∈ Finset.Icc 1 (M / a) →
          ‖(fun m' => if Nat.Coprime m' c then α (a * m') else 0) m‖ ≤ 1 := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        obtain ⟨hm1, hm2⟩ := hm
        by_cases hmc : Nat.Coprime m c
        · have hv : (fun m' => if Nat.Coprime m' c then α (a * m') else 0) m = α (a * m) := by
            simp [hmc]
          rw [hv]
          have hmem : a * m ∈ Finset.Icc 1 M := by
            rw [Finset.mem_Icc]
            refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
            calc a * m ≤ a * (M / a) := Nat.mul_le_mul_left a hm2
              _ ≤ M := Nat.mul_div_le M a
          exact hα _ hmem
        · have hv : (fun m' => if Nat.Coprime m' c then α (a * m') else 0) m = 0 := by
            simp [hmc]
          rw [hv, norm_zero]; norm_num
      have hαc : ∀ m, m ∈ Finset.Icc 1 (M / a) →
          (fun m' => if Nat.Coprime m' c then α (a * m') else 0) m ≠ 0 →
          Nat.Coprime m (a * b * c) := by
        intro m hm hne
        have hmc : Nat.Coprime m c := by
          by_contra hcon
          refine hne ?_
          dsimp only
          rw [if_neg hcon]
        have hma : Nat.Coprime m a := Work.FIArea7.P231.coprime_of_isSmooth_coprime hc haS hmc
        have hmb : Nat.Coprime m b := Work.FIArea7.P231.coprime_of_isSmooth_coprime hc hbS hmc
        exact (hma.mul_right hmb).mul_right hmc
      have hβg : ∀ n, n ∈ Finset.Icc 1 (N / b) →
          ‖(fun n' => if Nat.Coprime n' c then β (b * n') else 0) n‖ ≤ 1 := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        obtain ⟨hn1, hn2⟩ := hn
        by_cases hnc : Nat.Coprime n c
        · have hv : (fun n' => if Nat.Coprime n' c then β (b * n') else 0) n = β (b * n) := by
            simp [hnc]
          rw [hv]
          have hmem : b * n ∈ Finset.Icc 1 N := by
            rw [Finset.mem_Icc]
            refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
            calc b * n ≤ b * (N / b) := Nat.mul_le_mul_left b hn2
              _ ≤ N := Nat.mul_div_le N b
          exact hβ _ hmem
        · have hv : (fun n' => if Nat.Coprime n' c then β (b * n') else 0) n = 0 := by
            simp [hnc]
          rw [hv, norm_zero]; norm_num
      have hβc : ∀ n, n ∈ Finset.Icc 1 (N / b) →
          (fun n' => if Nat.Coprime n' c then β (b * n') else 0) n ≠ 0 →
          Nat.Coprime n (a * b * c) := by
        intro n hn hne
        have hnc : Nat.Coprime n c := by
          by_contra hcon
          refine hne ?_
          dsimp only
          rw [if_neg hcon]
        have hna : Nat.Coprime n a := Work.FIArea7.P231.coprime_of_isSmooth_coprime hc haS hnc
        have hnb : Nat.Coprime n b := Work.FIArea7.P231.coprime_of_isSmooth_coprime hc hbS hnc
        exact (hna.mul_right hnb).mul_right hnc
      have hb' := hbound (M / a) (N / b) (a * b * c) k χ
        (fun m' => if Nat.Coprime m' c then α (a * m') else 0)
        (fun n' => if Nat.Coprime n' c then β (b * n') else 0)
        hcab hMa hNb hχ hχmul hαg hαc hβg hβc
      have hS1 : (((a * b * c).divisors.card : ℕ) : ℝ)
          ≤ τc * ((((a.divisors.card : ℕ) : ℝ)) * (((b.divisors.card : ℕ) : ℝ))) := by
        rw [hτc]
        have h1 := Work.FIArea7.P231.card_divisors_mul_le c (a * b)
        have h2 := Work.FIArea7.P231.card_divisors_mul_le a b
        have h3 : (a * b * c).divisors.card ≤ c.divisors.card * (a.divisors.card * b.divisors.card) := by
          have h1' : (a * b * c).divisors.card ≤ c.divisors.card * (a * b).divisors.card := by
            rw [mul_comm (a * b) c]; exact h1
          exact h1'.trans (Nat.mul_le_mul_left _ h2)
        have h3' : ((a * b * c).divisors.card : ℝ)
            ≤ ((c.divisors.card : ℕ) : ℝ)
              * (((a.divisors.card : ℕ) : ℝ) * ((b.divisors.card : ℕ) : ℝ)) := by
          exact_mod_cast h3
        exact h3'
      have hS2 : (((M / a : ℕ) : ℝ) + ((N / b : ℕ) : ℝ)) ^ ((1 : ℝ) / 12) ≤ A := by
        rw [hA]
        have h1 : ((M / a : ℕ) : ℝ) ≤ (M : ℝ) := by
          have h := Nat.cast_div_le (α := ℝ) (m := M) (n := a)
          refine le_trans (by simpa using h) ?_
          rw [div_le_iff₀ ha0]
          nlinarith [hM1, ha1R]
        have h2 : ((N / b : ℕ) : ℝ) ≤ (N : ℝ) := by
          have h := Nat.cast_div_le (α := ℝ) (m := N) (n := b)
          refine le_trans (by simpa using h) ?_
          rw [div_le_iff₀ hb0]
          nlinarith [hN1, hb1R]
        refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
        linarith
      have hS3 : (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ)) ^ ((11 : ℝ) / 12)
          ≤ B * ((a : ℝ) ^ (-(11 / 12 : ℝ)) * (b : ℝ) ^ (-(11 / 12 : ℝ))) := by
        rw [hB]
        have h1 : ((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ)
            ≤ ((M : ℝ) * (N : ℝ)) * (((a : ℝ) * (b : ℝ))⁻¹) := by
          have hMa' : ((M / a : ℕ) : ℝ) ≤ (M : ℝ) / (a : ℝ) := Nat.cast_div_le
          have hNb' : ((N / b : ℕ) : ℝ) ≤ (N : ℝ) / (b : ℝ) := Nat.cast_div_le
          calc ((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ)
              ≤ ((M : ℝ) / (a : ℝ)) * ((N : ℝ) / (b : ℝ)) :=
                mul_le_mul hMa' hNb' (by positivity) (by positivity)
            _ = ((M : ℝ) * (N : ℝ)) * (((a : ℝ) * (b : ℝ))⁻¹) := by
                rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]; ring
        have h2 : (((M : ℝ) * (N : ℝ)) * (((a : ℝ) * (b : ℝ))⁻¹)) ^ ((11 : ℝ) / 12)
            = ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12)
              * (((a : ℝ) * (b : ℝ)) ^ (-(11 / 12 : ℝ))) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
            ← Real.rpow_neg (by positivity) (11 / 12)]
        have h3 : (((a : ℝ) * (b : ℝ)) ^ (-(11 / 12 : ℝ)))
            = (a : ℝ) ^ (-(11 / 12 : ℝ)) * (b : ℝ) ^ (-(11 / 12 : ℝ)) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
        calc (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ)) ^ ((11 : ℝ) / 12)
            ≤ (((M : ℝ) * (N : ℝ)) * (((a : ℝ) * (b : ℝ))⁻¹)) ^ ((11 : ℝ) / 12) :=
              Real.rpow_le_rpow (by positivity) h1 (by norm_num)
          _ = ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12)
              * (((a : ℝ) * (b : ℝ)) ^ (-(11 / 12 : ℝ))) := h2
          _ = ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12)
              * ((a : ℝ) ^ (-(11 / 12 : ℝ)) * (b : ℝ) ^ (-(11 / 12 : ℝ))) := by rw [h3]
      have hS4 : (Real.log (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) + 2)) ^ A_R ≤ LM := by
        rw [hLM]
        have hma0 : (0 : ℝ) ≤ ((M / a : ℕ) : ℝ) := Nat.cast_nonneg _
        have hnb0 : (0 : ℝ) ≤ ((N / b : ℕ) : ℝ) := Nat.cast_nonneg _
        have hprod0 : (0 : ℝ) ≤ ((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) :=
          mul_nonneg hma0 hnb0
        have h1 : ((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) ≤ (M : ℝ) * (N : ℝ) := by
          have hMa' : ((M / a : ℕ) : ℝ) ≤ (M : ℝ) / (a : ℝ) := Nat.cast_div_le
          have hNb' : ((N / b : ℕ) : ℝ) ≤ (N : ℝ) / (b : ℝ) := Nat.cast_div_le
          have hab1 : (1 : ℝ) ≤ (a : ℝ) * (b : ℝ) := by nlinarith [ha1R, hb1R]
          have hab0 : (0 : ℝ) < (a : ℝ) * (b : ℝ) := by nlinarith [ha1R, hb1R]
          have h2 : ((M : ℝ) / (a : ℝ)) * ((N : ℝ) / (b : ℝ)) ≤ (M : ℝ) * (N : ℝ) := by
            rw [div_mul_div_comm, div_le_iff₀ hab0]
            have h4 : (M : ℝ) * (N : ℝ) ≤ (M : ℝ) * (N : ℝ) * ((a : ℝ) * (b : ℝ)) := by
              have h5 := mul_le_mul_of_nonneg_left hab1 hMN0
              simpa using h5
            exact h4
          exact le_trans (mul_le_mul hMa' hNb' (by positivity) (by positivity)) h2
        have h2 : Real.log (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) + 2)
            ≤ Real.log ((M : ℝ) * (N : ℝ) + 2) :=
          Real.log_le_log (by linarith [hprod0]) (by linarith [h1])
        have h3 : 0 ≤ Real.log (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) + 2) :=
          Real.log_nonneg (by linarith [hprod0])
        exact Real.rpow_le_rpow h3 h2 hAR.le
      have hlogMa : (0 : ℝ) ≤ Real.log (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) + 2) := by
        have hma0 : (0 : ℝ) ≤ ((M / a : ℕ) : ℝ) := Nat.cast_nonneg _
        have hnb0 : (0 : ℝ) ≤ ((N / b : ℕ) : ℝ) := Nat.cast_nonneg _
        have hpr : (0 : ℝ) ≤ ((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) := mul_nonneg hma0 hnb0
        exact Real.log_nonneg (by linarith)
      have hlogPow0 : (0 : ℝ)
          ≤ (Real.log (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) + 2)) ^ A_R :=
        Real.rpow_nonneg hlogMa A_R
      have hgoal : C_R * (((a * b * c).divisors.card : ℕ) : ℝ)
            * (((M / a : ℕ) : ℝ) + ((N / b : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
            * (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ)) ^ ((11 : ℝ) / 12)
            * (Real.log (((M / a : ℕ) : ℝ) * ((N / b : ℕ) : ℝ) + 2)) ^ A_R
          ≤ C_R * (τc * ((((a.divisors.card : ℕ) : ℝ)) * (((b.divisors.card : ℕ) : ℝ))))
              * A * (B * ((a : ℝ) ^ (-(11 / 12 : ℝ)) * (b : ℝ) ^ (-(11 / 12 : ℝ)))) * LM := by
        gcongr
      refine hb'.trans (hgoal.trans ?_)
      refine le_of_eq ?_
      simp only [tauWeight]
      ring
    · rw [redSummand_apply, if_neg hab, norm_zero]
      have h1 : (0 : ℝ) ≤ (a : ℝ) ^ (-(11 / 12 : ℝ)) := by positivity
      have h2 : (0 : ℝ) ≤ (b : ℝ) ^ (-(11 / 12 : ℝ)) := by positivity
      have h3 : (0 : ℝ) ≤ ((a.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
      have h4 : (0 : ℝ) ≤ ((b.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
      have h5 : (0 : ℝ) ≤ tauWeight a := by simp only [tauWeight]; positivity
      have h6 : (0 : ℝ) ≤ tauWeight b := by simp only [tauWeight]; positivity
      exact mul_nonneg hP0 (mul_nonneg h5 h6)
  have hfinal : ‖∑ a ∈ SM, ∑ b ∈ SN, redSummand M N c ψ α β a b‖
      ≤ (C_R * K1 ^ 2 * K2) * τc * A * B * Lb ^ ε := by
    have hSM' : (∑ a ∈ SM, tauWeight a) ≤ K1 * (c : ℝ) ^ (ε / 4) := by
      rw [hSM]; simp only [tauWeight]; exact hK1 c hc M
    have hSN' : (∑ b ∈ SN, tauWeight b) ≤ K1 * (c : ℝ) ^ (ε / 4) := by
      rw [hSN]; simp only [tauWeight]; exact hK1 c hc N
    calc ‖∑ a ∈ SM, ∑ b ∈ SN, redSummand M N c ψ α β a b‖
        ≤ ∑ a ∈ SM, ∑ b ∈ SN, (C_R * τc * A * B * LM) * (tauWeight a * tauWeight b) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a ha => ?_))
          exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun b hb => hstep a ha b hb))
      _ = (C_R * τc * A * B * LM) * ((∑ a ∈ SM, tauWeight a) * (∑ b ∈ SN, tauWeight b)) :=
          sum_sum_factor SM SN _ _ _
      _ ≤ (C_R * τc * A * B * LM)
            * ((K1 * (c : ℝ) ^ (ε / 4)) * (K1 * (c : ℝ) ^ (ε / 4))) := by
          have hSb0 : (0 : ℝ) ≤ ∑ b ∈ SN, tauWeight b := by
            refine Finset.sum_nonneg (fun b hb => ?_)
            simp only [tauWeight]; positivity
          refine mul_le_mul_of_nonneg_left ?_ hP0
          exact mul_le_mul hSM' hSN' hSb0 (by positivity)
      _ ≤ (C_R * K1 ^ 2 * K2) * τc * A * B * Lb ^ ε := by
          have hx2 : (2 : ℝ) ≤ (M : ℝ) * (N : ℝ) + 2 := by linarith [hMN0]
          have hlm : (Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ A_R
              ≤ K2 * (((M : ℝ) * (N : ℝ) + 2) ^ (ε / 2)) := hK2 _ hx2
          have hxLb : ((M : ℝ) * (N : ℝ) + 2) ≤ Lb := by rw [hLb]; linarith
          have hcLb : (c : ℝ) ≤ Lb := by rw [hLb]; linarith
          have hpowL : ((M : ℝ) * (N : ℝ) + 2) ^ (ε / 2) ≤ Lb ^ (ε / 2) :=
            Real.rpow_le_rpow (by positivity) hxLb (by linarith)
          have hpowc : (c : ℝ) ^ (ε / 2) ≤ Lb ^ (ε / 2) :=
            Real.rpow_le_rpow (by positivity) hcLb (by linarith)
          have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
          have hK1sq : (K1 * (c : ℝ) ^ (ε / 4)) * (K1 * (c : ℝ) ^ (ε / 4))
              = K1 ^ 2 * (c : ℝ) ^ (ε / 2) := by
            have hc4 : (c : ℝ) ^ (ε / 4) * (c : ℝ) ^ (ε / 4) = (c : ℝ) ^ (ε / 2) := by
              rw [← Real.rpow_add hcpos]
              congr 1
              ring
            rw [← hc4]; ring
          rw [hK1sq, hLM]
          have hlmc : (Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ A_R * (c : ℝ) ^ (ε / 2)
              ≤ K2 * Lb ^ ε := by
            have h2 : ε / 2 + ε / 2 = ε := by ring
            calc (Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ A_R * (c : ℝ) ^ (ε / 2)
                ≤ (K2 * ((M : ℝ) * (N : ℝ) + 2) ^ (ε / 2)) * (c : ℝ) ^ (ε / 2) :=
                  mul_le_mul_of_nonneg_right hlm (by positivity)
              _ ≤ (K2 * Lb ^ (ε / 2)) * Lb ^ (ε / 2) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hpowL (le_of_lt hK2pos)) hpowc
                    (by positivity) (by positivity)
              _ = K2 * Lb ^ ε := by
                  have hLb2 : Lb ^ (ε / 2) * Lb ^ (ε / 2) = Lb ^ ε := by
                    rw [← Real.rpow_add hLbpos, h2]
                  rw [← hLb2]; ring
          calc (C_R * τc * A * B * (Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ A_R)
                * (K1 ^ 2 * (c : ℝ) ^ (ε / 2))
              = (C_R * τc * A * B) * K1 ^ 2
                * ((Real.log ((M : ℝ) * (N : ℝ) + 2)) ^ A_R * (c : ℝ) ^ (ε / 2)) := by ring
            _ ≤ (C_R * τc * A * B) * K1 ^ 2 * (K2 * Lb ^ ε) :=
                mul_le_mul_of_nonneg_left hlmc (by positivity)
            _ = (C_R * K1 ^ 2 * K2) * τc * A * B * Lb ^ ε := by ring
  exact hfinal

end

end Work.FIArea7.P231M
