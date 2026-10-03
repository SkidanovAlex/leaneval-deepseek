import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Assembly

namespace Work.FIArea4.L14

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Elementary helpers -/

/-- For odd `n`, the odd part of `n` is `n`. -/
lemma oddPart_eq_self_of_odd {n : ℕ} (hn : Odd n) : Work.FIPlan.oddPart n = n := by
  have h2 : ¬ (2 ∣ n) := fun h => (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr h)
  rw [Work.FIPlan.oddPart, Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, Nat.div_one]

/-- If the Jacobi symbol `(r | b)` is nonzero then `r` is coprime to `b` (for `b ≠ 0`). -/
lemma coprime_of_jacobiSym_ne_zero {r b : ℕ} (hb : b ≠ 0)
    (h : jacobiSym (r : ℤ) b ≠ 0) : Nat.Coprime r b := by
  by_contra hg
  apply h
  rw [jacobiSym.eq_zero_iff]
  exact ⟨hb, by
    rw [Int.gcd_natCast_natCast]
    intro hcon
    exact hg (Nat.coprime_iff_gcd_eq_one.mpr hcon)⟩

/-- Reindex the even numbers of `[1,R]` as `2k`, `k ∈ [1, R/2]`. -/
lemma sum_Icc_filter_even (R : ℕ) (g : ℕ → ℝ) :
    ∑ r ∈ (Finset.Icc 1 R).filter Even, g r
      = ∑ k ∈ Finset.Icc 1 (R / 2), g (2 * k) := by
  refine Finset.sum_bij (fun r _ => r / 2) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨h1, h2⟩, hev⟩ := hr
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right h2⟩
    have h2r : 2 ≤ r := by rcases hev with ⟨c, hc⟩; omega
    exact Nat.div_pos h2r (by norm_num)
  · intro r1 hr1 r2 hr2 heq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr1 hr2
    have e1 := Nat.two_mul_div_two_of_even hr1.2
    have e2 := Nat.two_mul_div_two_of_even hr2.2
    rw [← e1, ← e2, heq]
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨2 * k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, ⟨k, by ring⟩⟩
      have : k * 2 ≤ R := (Nat.le_div_iff_mul_le (by norm_num)).mp hk.2
      omega
    · exact Nat.mul_div_cancel_left k (by norm_num)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    congr 1
    exact (Nat.two_mul_div_two_of_even hr.2).symm

/-- Splitting the full sum of `(r|b)` over `r ≤ R` into its odd part plus `(2|b)` times the
sum over `r ≤ R/2`. -/
lemma sum_full_eq_odd_add (b R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) b : ℝ))
      = (∑ r ∈ (Finset.Icc 1 R).filter Odd, (jacobiSym (r : ℤ) b : ℝ))
        + (jacobiSym (2 : ℤ) b : ℝ)
            * (∑ k ∈ Finset.Icc 1 (R / 2), (jacobiSym (k : ℤ) b : ℝ)) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 R) Odd
        (fun r => (jacobiSym (r : ℤ) b : ℝ))]
  congr 1
  have hfilter : (Finset.Icc 1 R).filter (fun r => ¬ Odd r) = (Finset.Icc 1 R).filter Even :=
    Finset.filter_congr (fun r _ => Nat.not_odd_iff_even)
  rw [hfilter, sum_Icc_filter_even R (fun r => (jacobiSym (r : ℤ) b : ℝ)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  show (jacobiSym ((2 * k : ℕ) : ℤ) b : ℝ)
      = (jacobiSym (2 : ℤ) b : ℝ) * (jacobiSym (k : ℤ) b : ℝ)
  have hk2 : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; ring
  rw [hk2, jacobiSym.mul_left]
  push_cast
  ring

/-- Algebra: distributing a factor `2` over a double sum. -/
lemma double_sum_mul_add {ι κ : Type*}
    (s : Finset ι) (t : ι → Finset κ) (w A B : ι → κ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t a, w a b * (2 * (A a b + B a b)))
      = 2 * ((∑ a ∈ s, ∑ b ∈ t a, w a b * A a b)
           + (∑ a ∈ s, ∑ b ∈ t a, w a b * B a b)) := by
  have h1 : (∑ a ∈ s, ∑ b ∈ t a, w a b * (2 * (A a b + B a b)))
      = (∑ a ∈ s, ∑ b ∈ t a, 2 * (w a b * A a b))
        + (∑ a ∈ s, ∑ b ∈ t a, 2 * (w a b * B a b)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have h2 : (∑ a ∈ s, ∑ b ∈ t a, 2 * (w a b * A a b))
      = 2 * (∑ a ∈ s, ∑ b ∈ t a, w a b * A a b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
  have h3 : (∑ a ∈ s, ∑ b ∈ t a, 2 * (w a b * B a b))
      = 2 * (∑ a ∈ s, ∑ b ∈ t a, w a b * B a b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
  rw [h1, h2, h3]
  ring

/-- **Per-pair reduction.** For `d₁, d₂ ≥ 1` and `b = d₁' d₂'` (`dᵢ' = oddPart dᵢ`), the square
of the coprimality-restricted character sum is bounded by `2` times the sum of the squares of the
two full character sums (up to `R` and up to `R/2`). -/
lemma pair_reduction (d1 d2 R : ℕ) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) :
    Complex.normSq (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ))
      ≤ 2 * ((∑ r ∈ Finset.Icc 1 R,
            (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ)) ^ 2
          + (∑ r ∈ Finset.Icc 1 (R / 2),
            (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ)) ^ 2) := by
  set b := Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 with hb
  have hd1nz : d1 ≠ 0 := by omega
  have hd2nz : d2 ≠ 0 := by omega
  have hb0 : b ≠ 0 := by
    rw [hb]; exact mul_ne_zero (oddPart_ne_zero hd1nz) (oddPart_ne_zero hd2nz)
  have hbodd : Odd b := by
    rw [hb]; exact Odd.mul (oddPart_odd hd1nz) (oddPart_odd hd2nz)
  set FR := ∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) b : ℝ) with hFR
  set FH := ∑ r ∈ Finset.Icc 1 (R / 2), (jacobiSym (r : ℤ) b : ℝ) with hFH
  have hGcomplex : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) b : ℂ))
      = (((∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) b : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro r hr
    push_cast
    ring
  have hnorm : Complex.normSq (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) b : ℂ))
      = (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) b : ℝ)) ^ 2 := by
    rw [hGcomplex, Complex.normSq_ofReal]
    ring
  rw [hnorm]
  have hbound : |∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) b : ℝ)| ≤ |FR| + |FH| := by
    by_cases hodd : Odd (d1 * d2)
    · have hd1o : Odd d1 := Nat.Odd.of_mul_left hodd
      have hd2o : Odd d2 := Nat.Odd.of_mul_right hodd
      have hb_eq : b = d1 * d2 := by
        rw [hb, oddPart_eq_self_of_odd hd1o, oddPart_eq_self_of_odd hd2o]
      have hG_eq : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
            (jacobiSym (r : ℤ) b : ℝ)) = FR := by
        rw [hFR]
        refine Finset.sum_filter_of_ne (fun r hr hne => ?_)
        have hJ : jacobiSym (r : ℤ) b ≠ 0 := by
          intro hz; exact hne (by rw [hz]; norm_num)
        have := coprime_of_jacobiSym_ne_zero hb0 hJ
        rw [← hb_eq]; exact this
      rw [hG_eq]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · have heven : Even (d1 * d2) := Nat.not_odd_iff_even.mp hodd
      set e := d1.factorization 2 + d2.factorization 2 with he
      have hfac : d1 * d2 = 2 ^ e * b := by
        have h1 : 2 ^ (d1.factorization 2) * Work.FIPlan.oddPart d1 = d1 :=
          oddPart_mul_two_pow d1
        have h2 : 2 ^ (d2.factorization 2) * Work.FIPlan.oddPart d2 = d2 :=
          oddPart_mul_two_pow d2
        calc d1 * d2
            = (2 ^ (d1.factorization 2) * Work.FIPlan.oddPart d1)
                * (2 ^ (d2.factorization 2) * Work.FIPlan.oddPart d2) := by rw [h1, h2]
          _ = 2 ^ e * b := by rw [hb, he, pow_add]; ring
      have hepos : 0 < e := by
        by_contra h
        have he0 : e = 0 := by omega
        have : Odd (d1 * d2) := by rw [hfac, he0, pow_zero, one_mul]; exact hbodd
        exact (Nat.not_odd_iff_even.mpr heven) this
      have hcop : ∀ r, Nat.Coprime r (d1 * d2) ↔ Odd r ∧ Nat.Coprime r b := by
        intro r
        rw [hfac, Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff hepos,
          Nat.coprime_two_right]
      have hG_eq : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
            (jacobiSym (r : ℤ) b : ℝ))
          = ∑ r ∈ (Finset.Icc 1 R).filter Odd, (jacobiSym (r : ℤ) b : ℝ) := by
        have h1 : (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2))
            = (Finset.Icc 1 R).filter (fun r => Odd r ∧ Nat.Coprime r b) :=
          Finset.filter_congr (fun r _ => hcop r)
        rw [h1, ← Finset.filter_filter]
        exact Finset.sum_filter_of_ne (fun r hr hne => by
          have hJ : jacobiSym (r : ℤ) b ≠ 0 := by
            intro hz; exact hne (by rw [hz]; norm_num)
          exact coprime_of_jacobiSym_ne_zero hb0 hJ)
      have hFR_eq : FR = (∑ r ∈ (Finset.Icc 1 R).filter Odd, (jacobiSym (r : ℤ) b : ℝ))
            + (jacobiSym (2 : ℤ) b : ℝ) * FH := by
        rw [hFR, hFH]
        exact sum_full_eq_odd_add b R
      have hc_le : |(jacobiSym (2 : ℤ) b : ℝ)| ≤ 1 := by
        rcases jacobiSym.trichotomy (2 : ℤ) b with h | h | h <;> rw [h] <;> norm_num
      have hG_eq2 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
            (jacobiSym (r : ℤ) b : ℝ)) = FR - (jacobiSym (2 : ℤ) b : ℝ) * FH := by
        rw [hG_eq, hFR_eq]; ring
      rw [hG_eq2]
      calc |FR - (jacobiSym (2 : ℤ) b : ℝ) * FH|
          ≤ |FR| + |(jacobiSym (2 : ℤ) b : ℝ) * FH| := by
            rw [sub_eq_add_neg]
            simpa using abs_add_le FR (-((jacobiSym (2 : ℤ) b : ℝ) * FH))
        _ = |FR| + |(jacobiSym (2 : ℤ) b : ℝ)| * |FH| := by rw [abs_mul]
        _ ≤ |FR| + 1 * |FH| := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc_le (abs_nonneg FH))
        _ = |FR| + |FH| := by ring
  have hmain : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) b : ℝ)) ^ 2 ≤ 2 * (FR ^ 2 + FH ^ 2) := by
    have h1 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) b : ℝ)) ^ 2
        = |∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) b : ℝ)| ^ 2 := (sq_abs _).symm
    have h2 := sq_abs FR
    have h3 := sq_abs FH
    nlinarith [hbound, abs_nonneg (∑ r ∈ (Finset.Icc 1 R).filter
      (fun r => Nat.Coprime r (d1 * d2)), (jacobiSym (r : ℤ) b : ℝ)),
      abs_nonneg FR, abs_nonneg FH, sq_nonneg (|FR| - |FH|)]
  exact hmain


/-- Reduction of the target double sum of Lemma 11.4 to the two "full character sum" second
moments `T' R' = Σ_{d₁,d₂ ≤ D, d₁'d₂' ≠ □} [d₁,d₂]^{-1} |Σ_{r ≤ R'} (r | d₁'d₂')|²`
(with `R' = R` and `R' = R/2`): replace `Complex.normSq` of the coprimality-restricted sum by
the square of the real sum, and use `|Σ_{r ≤ R, (r,d₁d₂)=1} (r|b)| ≤ |Σ_{r ≤ R} (r|b)| +
|Σ_{r ≤ R/2} (r|b)|` (`b = d₁'d₂'`; the coprimality condition only removes even `r` from the
full character sum, since the Jacobi symbol already vanishes off `(r,b) = 1` and
`(2k|b) = (2|b)(k|b)`). -/
theorem reduce_to_T :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R : ℕ), 1 ≤ D → 1 ≤ R →
      (∑ d1 ∈ Finset.Icc 1 D,
        ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
            Complex.normSq (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
              (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)))
      ≤ C * (
        (∑ d1 ∈ Finset.Icc 1 D,
          ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
              (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2)
        + (∑ d1 ∈ Finset.Icc 1 D,
          ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
              (∑ r ∈ Finset.Icc 1 (R/2), (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2))
    := by
  refine ⟨2, by norm_num, fun D R hD hR => ?_⟩
  have hsplit := double_sum_mul_add (Finset.Icc 1 D)
      (fun d1 => (Finset.Icc 1 D).filter
          (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                      ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2))
      (fun d1 d2 => ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹)
      (fun d1 d2 => (∑ r ∈ Finset.Icc 1 R,
          (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ)) ^ 2)
      (fun d1 d2 => (∑ r ∈ Finset.Icc 1 (R / 2),
          (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ)) ^ 2)
  refine le_trans ?_ (le_of_eq hsplit)
  apply Finset.sum_le_sum
  intro d1 hd1
  apply Finset.sum_le_sum
  intro d2 hd2
  have hd1' : 1 ≤ d1 := (Finset.mem_Icc.mp hd1).1
  have hd2' : 1 ≤ d2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd2).1).1
  have hw : 0 ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ := by
    rw [inv_nonneg]; positivity
  exact mul_le_mul_of_nonneg_left (pair_reduction d1 d2 R hd1' hd2') hw

end

end Work.FIArea4.L14
