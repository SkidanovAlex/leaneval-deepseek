import Mathlib
import Submission.Work.FIArea4.S15_energy_defs
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le
import Submission.Commons.NumberTheory.DivisorSum.tau_pow_eight_le_sum_dvd_cube
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea4.S15box
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sqKernel_sq_dvd

open Finset
open scoped BigOperators

namespace Work.FIArea4

private lemma pow17_ge (e : ℕ) (he : 1 ≤ e) : (2*e+1)^10 * 2 ≤ (e+1)^17 := by
  rcases eq_or_lt_of_le he with h | h
  · subst h; norm_num
  · have hle : 2*e+1 ≤ 2*(e+1) := by omega
    have h10 : (2*e+1)^10 ≤ (2*(e+1))^10 := Nat.pow_le_pow_left hle 10
    have h2e : (2*(e+1))^10 = 2^10 * (e+1)^10 := by rw [Nat.mul_pow]
    have hstep : (2*e+1)^10 * 2 ≤ 2^11 * (e+1)^10 := by
      calc (2*e+1)^10 * 2 ≤ (2*(e+1))^10 * 2 := Nat.mul_le_mul_right 2 h10
        _ = 2^10 * (e+1)^10 * 2 := by rw [h2e]
        _ = 2^11 * (e+1)^10 := by ring
    have h3 : 3 ≤ e + 1 := by omega
    have h217 : (2:ℕ)^11 ≤ (e+1)^7 := by
      calc (2:ℕ)^11 ≤ 3^7 := by norm_num
        _ ≤ (e+1)^7 := Nat.pow_le_pow_left h3 7
    calc (2*e+1)^10 * 2 ≤ 2^11 * (e+1)^10 := hstep
      _ ≤ (e+1)^7 * (e+1)^10 := Nat.mul_le_mul_right _ h217
      _ = (e+1)^17 := by rw [← pow_add]

private lemma tau_sq_pow_le_nat (b : ℕ) (hb : 1 ≤ b) :
    ((b^2).divisors.card)^10 * 2^(b.primeFactors).card ≤ (b.divisors.card)^17 := by
  have hb0 : b ≠ 0 := by omega
  have hb20 : b^2 ≠ 0 := by positivity
  rw [Nat.card_divisors hb20, Nat.primeFactors_pow b (by norm_num : (2:ℕ) ≠ 0),
      Nat.card_divisors hb0]
  have hfac : ∀ x, (b^2).factorization x = 2 * b.factorization x := by
    intro x
    rw [Nat.factorization_pow]
    simp [Finsupp.smul_apply, smul_eq_mul]
  simp only [hfac]
  rw [← Finset.prod_pow, ← Finset.prod_pow, (Finset.prod_const (2:ℕ)).symm,
      ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro x hx; positivity
  · intro x hx
    have hpx : x.Prime := Nat.prime_of_mem_primeFactors hx
    have hxdvd : x ∣ b := Nat.dvd_of_mem_primeFactors hx
    have hpos : 1 ≤ b.factorization x := hpx.factorization_pos_of_dvd hb0 hxdvd
    exact pow17_ge (b.factorization x) hpos

private lemma tau_sq_pow_le (b : ℕ) (hb : 1 ≤ b) :
    ((((b^2).divisors.card : ℕ) : ℝ))^10 * (2:ℝ)^(b.primeFactors).card
      ≤ ((((b.divisors.card : ℕ) : ℝ)))^17 := by
  have h := tau_sq_pow_le_nat b hb
  exact_mod_cast h

private lemma summand_le (d : ℕ) (hd : 1 ≤ d) :
    (((d.divisors.card : ℝ))^10 * (2:ℝ)^(d.primeFactors).card
        * ((Work.FIArea4.S15d2 d : ℕ):ℝ) / (d:ℝ))
      ≤ (((((d / (Work.FIArea4.S15d2 d)^2).divisors.card : ℕ):ℝ))^11
            / ((d / (Work.FIArea4.S15d2 d)^2 : ℕ):ℝ))
        * (((((Work.FIArea4.S15d2 d).divisors.card : ℕ):ℝ))^17
            / ((Work.FIArea4.S15d2 d : ℕ):ℝ)) := by
  set b : ℕ := Work.FIArea4.S15d2 d with hb
  set a : ℕ := d / b ^ 2 with ha
  have hb2dvd0 : (Work.FIArea4.S15d2 d)^2 ∣ d := by
    simpa [Work.FIArea4.S15d2] using Commons.NumberTheory.FriedlanderIwaniec.sqKernel_sq_dvd d
  have hb2dvd : b^2 ∣ d := by rw [hb]; exact hb2dvd0
  have hdpos : 0 < d := hd
  have hb2pos : 0 < b^2 := Nat.pos_of_dvd_of_pos hb2dvd hdpos
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hb2pos; simp at hb2pos
    · exact h
  have hb2le : b^2 ≤ d := Nat.le_of_dvd hdpos hb2dvd
  have hapos : 0 < a := by rw [ha]; exact Nat.div_pos hb2le hb2pos
  have hda : a * b^2 = d := by rw [ha, Nat.div_mul_cancel hb2dvd]
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast hapos
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hbpos
  have hd_eq : (d:ℝ) = (a:ℝ)*(b:ℝ)^2 := by rw [← hda]; push_cast; ring
  have hτd : ((d.divisors.card : ℝ)) ≤ ((a.divisors.card : ℝ)) * (((b^2).divisors.card : ℝ)) := by
    have h := Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le a (b^2)
    rw [hda] at h
    exact_mod_cast h
  have hpf : d.primeFactors = a.primeFactors ∪ b.primeFactors := by
    rw [← hda, Nat.primeFactors_mul hapos.ne' (pow_ne_zero 2 hbpos.ne'),
        Nat.primeFactors_pow b (by norm_num : (2:ℕ) ≠ 0)]
  have hcard : (d.primeFactors).card ≤ (a.primeFactors).card + (b.primeFactors).card := by
    rw [hpf]; exact Finset.card_union_le _ _
  have h2ω : (2:ℝ)^(d.primeFactors).card
      ≤ (2:ℝ)^(a.primeFactors).card * (2:ℝ)^(b.primeFactors).card := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hcard
  have h2ωa : (2:ℝ)^(a.primeFactors).card ≤ (a.divisors.card : ℝ) := by
    have h := Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors hapos
    exact_mod_cast h
  have hstep1 : ((d.divisors.card : ℝ))^10 * (2:ℝ)^(d.primeFactors).card * (b:ℝ) / (d:ℝ)
      ≤ (((a.divisors.card : ℝ) * ((b^2).divisors.card : ℝ))^10
          * ((2:ℝ)^(a.primeFactors).card * (2:ℝ)^(b.primeFactors).card)) * (b:ℝ) / (d:ℝ) := by
    apply div_le_div_of_nonneg_right _ hdR.le
    apply mul_le_mul _ le_rfl (by positivity) (by positivity)
    apply mul_le_mul _ h2ω (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) hτd 10
  have hstep2 : (((a.divisors.card : ℝ) * ((b^2).divisors.card : ℝ))^10
          * ((2:ℝ)^(a.primeFactors).card * (2:ℝ)^(b.primeFactors).card)) * (b:ℝ) / (d:ℝ)
      = (((a.divisors.card : ℝ))^10 * (2:ℝ)^(a.primeFactors).card / (a:ℝ))
        * ((((b^2).divisors.card : ℝ))^10 * (2:ℝ)^(b.primeFactors).card / (b:ℝ)) := by
    rw [hd_eq]
    field_simp
  have hstep3 : (((a.divisors.card : ℝ))^10 * (2:ℝ)^(a.primeFactors).card / (a:ℝ))
        * ((((b^2).divisors.card : ℝ))^10 * (2:ℝ)^(b.primeFactors).card / (b:ℝ))
      ≤ (((a.divisors.card : ℝ))^11 / (a:ℝ)) * (((b.divisors.card : ℝ))^17 / (b:ℝ)) := by
    apply mul_le_mul
    · apply div_le_div_of_nonneg_right _ haR.le
      calc ((a.divisors.card : ℝ))^10 * (2:ℝ)^(a.primeFactors).card
          ≤ ((a.divisors.card : ℝ))^10 * ((a.divisors.card : ℝ)) :=
            mul_le_mul_of_nonneg_left h2ωa (by positivity)
        _ = ((a.divisors.card : ℝ))^11 := by ring
    · apply div_le_div_of_nonneg_right _ hbR.le
      exact tau_sq_pow_le b hbpos
    · positivity
    · positivity
  have hmain : ((d.divisors.card : ℝ))^10 * (2:ℝ)^(d.primeFactors).card * (b:ℝ) / (d:ℝ)
      ≤ (((a.divisors.card : ℝ))^11 / (a:ℝ)) * (((b.divisors.card : ℝ))^17 / (b:ℝ)) :=
    le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  exact le_trans hmain (le_of_eq (by ring))

private lemma core (Y : ℕ) (_hY : 1 ≤ Y) :
    (∑ d ∈ Finset.Icc 1 Y,
        ((d.divisors.card : ℝ))^10 * (2:ℝ)^(d.primeFactors).card
          * ((Work.FIArea4.S15d2 d : ℕ):ℝ) / (d:ℝ))
      ≤ (∑ a ∈ Finset.Icc 1 Y, ((a.divisors.card : ℝ))^11 / (a:ℝ))
        * (∑ b ∈ Finset.Icc 1 Y, ((b.divisors.card : ℝ))^17 / (b:ℝ)) := by
  have hsq : ∀ d : ℕ, (Work.FIArea4.S15d2 d)^2 ∣ d := fun d => by
    simpa [Work.FIArea4.S15d2] using Commons.NumberTheory.FriedlanderIwaniec.sqKernel_sq_dvd d
  let φ : ℕ → ℕ × ℕ := fun d => (d / (Work.FIArea4.S15d2 d)^2, Work.FIArea4.S15d2 d)
  let Gp : ℕ × ℕ → ℝ := fun p => ((((p.1.divisors.card : ℕ):ℝ))^11 / ((p.1 : ℕ):ℝ))
      * ((((p.2.divisors.card : ℕ):ℝ))^17 / ((p.2 : ℕ):ℝ))
  have hpt : ∀ d ∈ Finset.Icc 1 Y,
      ((d.divisors.card : ℝ))^10 * (2:ℝ)^(d.primeFactors).card
          * ((Work.FIArea4.S15d2 d : ℕ):ℝ) / (d:ℝ) ≤ Gp (φ d) :=
    fun d hd => summand_le d (Finset.mem_Icc.mp hd).1
  have hinj : Set.InjOn φ (↑(Finset.Icc 1 Y) : Set ℕ) := by
    intro d _ d' _ heq
    have hb : Work.FIArea4.S15d2 d = Work.FIArea4.S15d2 d' := congrArg Prod.snd heq
    have ha : d / (Work.FIArea4.S15d2 d)^2 = d' / (Work.FIArea4.S15d2 d')^2 := congrArg Prod.fst heq
    calc d = d / (Work.FIArea4.S15d2 d)^2 * (Work.FIArea4.S15d2 d)^2 :=
          (Nat.div_mul_cancel (hsq d)).symm
      _ = d' / (Work.FIArea4.S15d2 d')^2 * (Work.FIArea4.S15d2 d')^2 := by rw [ha, hb]
      _ = d' := Nat.div_mul_cancel (hsq d')
  have hsub : (Finset.Icc 1 Y).image φ ⊆ (Finset.Icc 1 Y) ×ˢ (Finset.Icc 1 Y) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    show (d / (Work.FIArea4.S15d2 d)^2, Work.FIArea4.S15d2 d)
        ∈ (Finset.Icc 1 Y) ×ˢ (Finset.Icc 1 Y)
    rw [Finset.mem_product]
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdD : d ≤ Y := (Finset.mem_Icc.mp hd).2
    have h2dvd : (Work.FIArea4.S15d2 d)^2 ∣ d := hsq d
    have h2pos : 0 < (Work.FIArea4.S15d2 d)^2 := Nat.pos_of_dvd_of_pos h2dvd (by omega)
    have h2le : (Work.FIArea4.S15d2 d)^2 ≤ d := Nat.le_of_dvd (by omega) h2dvd
    have hbpos : 0 < Work.FIArea4.S15d2 d := by
      rcases Nat.eq_zero_or_pos (Work.FIArea4.S15d2 d) with h | h
      · rw [h] at h2pos; simp at h2pos
      · exact h
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos h2le h2pos, le_trans (Nat.div_le_self d _) hdD⟩
    · rw [Finset.mem_Icc]
      refine ⟨hbpos, ?_⟩
      have hle1 : Work.FIArea4.S15d2 d ≤ (Work.FIArea4.S15d2 d)^2 := by
        have := Nat.le_mul_of_pos_right (Work.FIArea4.S15d2 d) hbpos
        simpa [pow_two] using this
      exact le_trans (le_trans hle1 h2le) hdD
  calc
    (∑ d ∈ Finset.Icc 1 Y,
        ((d.divisors.card : ℝ))^10 * (2:ℝ)^(d.primeFactors).card
          * ((Work.FIArea4.S15d2 d : ℕ):ℝ) / (d:ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 Y, Gp (φ d) := Finset.sum_le_sum hpt
    _ = ∑ p ∈ (Finset.Icc 1 Y).image φ, Gp p := (Finset.sum_image (f := Gp) hinj).symm
    _ ≤ ∑ p ∈ (Finset.Icc 1 Y) ×ˢ (Finset.Icc 1 Y), Gp p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by simp only [Gp]; positivity)
    _ = (∑ a ∈ Finset.Icc 1 Y, ((a.divisors.card : ℝ))^11 / (a:ℝ))
        * (∑ b ∈ Finset.Icc 1 Y, ((b.divisors.card : ℝ))^17 / (b:ℝ)) := by
          simp only [Gp]; rw [Finset.sum_product, Finset.sum_mul_sum]


/-- **The divisor sum `Σ_{d ≤ Y} τ(d)^10 · 2^ω(d) · d₂(d)/d ≪ (log Y)^B`** with an explicit
`B ≤ 9·10^5`.  Writing `d = a·b²` with `b = d₂(d)` (so that `b²` is the largest square divisor of
`d` and `a` is squarefree), the summand factorises as

  `τ(d)^10 2^ω(d) d₂(d)/d ≤ (τ(a)^10 2^ω(a)/a) · (τ(b²)^10 2^ω(b)/b)`

and each factor is controlled by the divisor-sum mean value `Σ_{n ≤ x} τ(n)^k/n ≪ (log x)^{2^k}`
(`Commons.NumberTheory.Divisors.sum_tau_pow_div_le`): the first uses `2^ω(a) ≤ τ(a)` (exponent
`2^11`) and the second uses the pointwise bound `τ(b²)^10 · 2^ω(b) ≤ τ(b)^17` (exponent `2^17`).
Hence `B = 2^11 + 2^17 = 133120 ≤ 9·10^5`. -/
theorem S15_tau10_d2_sum :
    ∃ C B : ℝ, 0 < C ∧ B ≤ 900000 ∧ ∀ Y : ℕ,
      (∑ d ∈ Finset.Icc 1 Y,
          ((d.divisors.card : ℝ) ^ (10 : ℕ)) * (2 : ℝ) ^ (Nat.primeFactors d).card
            * ((Work.FIArea4.S15d2 d : ℕ) : ℝ) / (d : ℝ))
        ≤ C * (Real.log ((Y : ℝ) + 2)) ^ B := by
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 11
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 17
  refine ⟨max (C1 * C2) 1, ((2 ^ 11 : ℕ) : ℝ) + ((2 ^ 17 : ℕ) : ℝ), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (mul_pos hC1pos hC2pos) (le_max_left _ _)
  · norm_num
  · intro Y
    rcases Nat.eq_zero_or_pos Y with hY | hYpos
    · subst hY
      have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
        rw [Finset.Icc_eq_empty_iff]; norm_num
      rw [hempty, Finset.sum_empty]
      apply mul_nonneg (le_of_lt _)
        (Real.rpow_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ ((0:ℕ):ℝ) + 2)) _)
      exact lt_of_lt_of_le (mul_pos hC1pos hC2pos) (le_max_left _ _)
    · have hY1 : 1 ≤ Y := hYpos
      have hlogpos : 0 < Real.log ((Y:ℝ) + 2) := by
        apply Real.log_pos
        have hY0 : (0:ℝ) ≤ (Y:ℝ) := Nat.cast_nonneg Y
        linarith
      have hcore := core Y hY1
      have hbA := hC1 Y hY1
      have hbB := hC2 Y hY1
      have h1 : (∑ a ∈ Finset.Icc 1 Y, ((a.divisors.card : ℝ))^11 / (a:ℝ))
            * (∑ b ∈ Finset.Icc 1 Y, ((b.divisors.card : ℝ))^17 / (b:ℝ))
          ≤ (C1 * (Real.log ((Y:ℝ)+2))^(2^11)) * (C2 * (Real.log ((Y:ℝ)+2))^(2^17)) :=
        mul_le_mul hbA hbB
          (Finset.sum_nonneg (fun b _ => div_nonneg (by positivity) (Nat.cast_nonneg _)))
          (mul_nonneg (le_of_lt hC1pos) (pow_nonneg hlogpos.le _))
      have hrp : (Real.log ((Y:ℝ)+2))^(2^11) * (Real.log ((Y:ℝ)+2))^(2^17)
          = (Real.log ((Y:ℝ)+2))^(((2^11:ℕ):ℝ) + ((2^17:ℕ):ℝ)) := by
        rw [← Real.rpow_natCast (Real.log ((Y:ℝ)+2)) (2^11),
            ← Real.rpow_natCast (Real.log ((Y:ℝ)+2)) (2^17),
            ← Real.rpow_add hlogpos]
      have h2 : (C1 * (Real.log ((Y:ℝ)+2))^(2^11)) * (C2 * (Real.log ((Y:ℝ)+2))^(2^17))
          = C1 * C2 * (Real.log ((Y:ℝ)+2))^(((2^11:ℕ):ℝ) + ((2^17:ℕ):ℝ)) := by
        rw [← hrp]; ring
      have h3 : C1 * C2 * (Real.log ((Y:ℝ)+2))^(((2^11:ℕ):ℝ) + ((2^17:ℕ):ℝ))
          ≤ max (C1 * C2) 1 * (Real.log ((Y:ℝ)+2))^(((2^11:ℕ):ℝ) + ((2^17:ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hlogpos.le _)
      exact le_trans hcore (le_trans h1 (le_trans (le_of_eq h2) h3))

end Work.FIArea4
