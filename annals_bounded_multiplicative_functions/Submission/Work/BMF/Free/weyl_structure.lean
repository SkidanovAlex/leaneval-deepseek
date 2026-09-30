import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.Free.weyl_inverse
import Submission.Work.BMF.weyl_coeff_shift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.FreeWS

open Polynomial Finset Real

/-- **Descent arithmetic for the inverse-Weyl base-point shift.**  Let `q > 0`, `1 ≤ M`,
`|d| ≤ A·M` with `A ≥ 0`, and suppose each coefficient `a j` (`1 ≤ j ≤ k`) of a polynomial is
within `C'/M^j` of a rational of denominator `q`.  Then for each `1 ≤ l ≤ k`, the number
`Σ_{l ≤ i ≤ k} a i · d^{i-l} · C(i,l)` is within `2^k (k+1) (A+1)^k |C'| / M^l` of a rational of
denominator `q`.  Indeed writing `q·a i = m_i + e_i` with `|e_i| ≤ C'/M^i`, the `m_i`-part is an
integer (as `d^{i-l} ∈ ℤ`), and
`Σ_i |e_i| |d|^{i-l} C(i,l) ≤ Σ_i (C'/M^i)(AM)^{i-l} 2^k = (2^k C'/M^l) Σ_{j≤k-l} A^j`. -/
lemma weyl_descent_bound (k : ℕ) (C' A : ℝ) (hA : 0 ≤ A) (M : ℕ) (hM : 1 ≤ M)
    (q : ℕ) (d : ℤ) (a : ℕ → ℝ) (hd : |(d : ℝ)| ≤ A * M)
    (hm : ∀ j ∈ Finset.Icc 1 k, ∃ m : ℤ,
        |(q : ℝ) * a j - (m : ℝ)| ≤ C' / (M : ℝ) ^ j) :
    ∀ l ∈ Finset.Icc 1 k, ∃ m : ℤ,
      |(q : ℝ) * (∑ i ∈ Finset.Icc l k, a i * ((d : ℝ) ^ (i - l)) * (i.choose l : ℝ))
        - (m : ℝ)| ≤ ((2 : ℝ) ^ k * ((k : ℝ) + 1) * (A + 1) ^ k * |C'|) / (M : ℝ) ^ l := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  intro l hl
  rw [Finset.mem_Icc] at hl
  obtain ⟨hl1, hlk⟩ := hl
  have hsub : ∀ i, i ∈ Finset.Icc l k → i ∈ Finset.Icc 1 k := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact Finset.mem_Icc.mpr ⟨le_trans hl1 hi.1, hi.2⟩
  have hm2 : ∀ i, ∃ m : ℤ, i ∈ Finset.Icc l k →
      |(q : ℝ) * a i - (m : ℝ)| ≤ C' / (M : ℝ) ^ i := by
    intro i
    by_cases hi : i ∈ Finset.Icc l k
    · exact ⟨Classical.choose (hm i (hsub i hi)), fun _ => Classical.choose_spec (hm i (hsub i hi))⟩
    · exact ⟨0, fun h => absurd h hi⟩
  classical
  let mm : ℕ → ℤ := fun i => Classical.choose (hm2 i)
  have hmm : ∀ i (hi : i ∈ Finset.Icc l k),
      |(q : ℝ) * a i - (mm i : ℝ)| ≤ C' / (M : ℝ) ^ i := by
    intro i hi
    exact (Classical.choose_spec (hm2 i)) hi
  refine ⟨∑ i ∈ Finset.Icc l k, mm i * d ^ (i - l) * (i.choose l), ?_⟩
  have hcast : (((∑ i ∈ Finset.Icc l k, mm i * d ^ (i - l) * (i.choose l)) : ℤ) : ℝ)
      = ∑ i ∈ Finset.Icc l k, ((mm i : ℝ) * ((d : ℝ) ^ (i - l)) * (i.choose l : ℝ)) := by
    push_cast
    rfl
  have hqS : (q : ℝ) * (∑ i ∈ Finset.Icc l k, a i * ((d : ℝ) ^ (i - l)) * (i.choose l : ℝ))
      = ∑ i ∈ Finset.Icc l k, ((q : ℝ) * a i) * ((d : ℝ) ^ (i - l)) * (i.choose l : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hdiff : (q : ℝ) * (∑ i ∈ Finset.Icc l k, a i * ((d : ℝ) ^ (i - l)) * (i.choose l : ℝ))
      - (((∑ i ∈ Finset.Icc l k, mm i * d ^ (i - l) * (i.choose l)) : ℤ) : ℝ)
      = ∑ i ∈ Finset.Icc l k,
          (((q : ℝ) * a i - (mm i : ℝ)) * ((d : ℝ) ^ (i - l)) * (i.choose l : ℝ)) := by
    rw [hqS, hcast, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hdiff]
  calc |∑ i ∈ Finset.Icc l k,
          ((q : ℝ) * a i - (mm i : ℝ)) * ((d : ℝ) ^ (i - l)) * (i.choose l : ℝ)|
      ≤ ∑ i ∈ Finset.Icc l k,
          |((q : ℝ) * a i - (mm i : ℝ)) * ((d : ℝ) ^ (i - l)) * (i.choose l : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.Icc l k,
          |(q : ℝ) * a i - (mm i : ℝ)| * |(d : ℝ)| ^ (i - l) * (i.choose l : ℝ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hC : |((i.choose l : ℕ) : ℝ)| = ((i.choose l : ℕ) : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg _)
        rw [abs_mul, abs_mul, abs_pow, hC]
    _ ≤ ∑ i ∈ Finset.Icc l k,
          (|C'| / (M : ℝ) ^ l) * ((A + 1) ^ k * (2 : ℝ) ^ k) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [Finset.mem_Icc] at hi
        obtain ⟨hil, hik⟩ := hi
        have hiIcc : i ∈ Finset.Icc l k := Finset.mem_Icc.mpr ⟨hil, hik⟩
        have h1 : |(q : ℝ) * a i - (mm i : ℝ)| ≤ |C'| / (M : ℝ) ^ i :=
          le_trans (hmm i hiIcc)
            (div_le_div_of_nonneg_right (le_abs_self C') (pow_nonneg hMpos.le i))
        have h2 : |(d : ℝ)| ^ (i - l) ≤ (A * (M : ℝ)) ^ (i - l) :=
          pow_le_pow_left₀ (abs_nonneg _) hd (i - l)
        have h3nn : (0 : ℝ) ≤ (i.choose l : ℝ) := Nat.cast_nonneg _
        have hkey : (M : ℝ) ^ i = (M : ℝ) ^ (i - l) * (M : ℝ) ^ l := by
          rw [← pow_add, Nat.sub_add_cancel hil]
        have hstep : (|C'| / (M : ℝ) ^ i) * (A * (M : ℝ)) ^ (i - l) * (i.choose l : ℝ)
            = (|C'| / (M : ℝ) ^ l) * ((A : ℝ) ^ (i - l) * (i.choose l : ℝ)) := by
          rw [mul_pow, hkey]
          have e1 : (M : ℝ) ^ (i - l) ≠ 0 := pow_ne_zero _ hMne
          have e2 : (M : ℝ) ^ l ≠ 0 := pow_ne_zero _ hMne
          field_simp
          try ring
        calc |(q : ℝ) * a i - (mm i : ℝ)| * |(d : ℝ)| ^ (i - l) * (i.choose l : ℝ)
            ≤ (|C'| / (M : ℝ) ^ i) * (A * (M : ℝ)) ^ (i - l) * (i.choose l : ℝ) := by
              apply mul_le_mul_of_nonneg_right _ h3nn
              exact mul_le_mul h1 h2 (pow_nonneg (abs_nonneg _) _)
                (div_nonneg (abs_nonneg _) (pow_nonneg hMpos.le i))
          _ = (|C'| / (M : ℝ) ^ l) * ((A : ℝ) ^ (i - l) * (i.choose l : ℝ)) := hstep
          _ ≤ (|C'| / (M : ℝ) ^ l) * ((A + 1) ^ k * (2 : ℝ) ^ k) := by
              apply mul_le_mul_of_nonneg_left _
                (div_nonneg (abs_nonneg _) (pow_nonneg hMpos.le l))
              apply mul_le_mul
              · calc (A : ℝ) ^ (i - l) ≤ (A + 1) ^ (i - l) :=
                      pow_le_pow_left₀ hA (by linarith) _
                  _ ≤ (A + 1) ^ k :=
                      pow_le_pow_right₀ (by linarith) (le_trans (Nat.sub_le i l) hik)
              · calc (i.choose l : ℝ) ≤ (2 : ℝ) ^ i := by
                      exact_mod_cast Nat.choose_le_two_pow i l
                  _ ≤ (2 : ℝ) ^ k :=
                      pow_le_pow_right₀ (by norm_num) hik
              · positivity
              · positivity
    _ = ((Finset.Icc l k).card : ℝ) *
          ((|C'| / (M : ℝ) ^ l) * ((A + 1) ^ k * (2 : ℝ) ^ k)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) * ((|C'| / (M : ℝ) ^ l) * ((A + 1) ^ k * (2 : ℝ) ^ k)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Nat.card_Icc]
        have hle : (k + 1 - l : ℕ) ≤ k + 1 := Nat.sub_le _ _
        calc ((k + 1 - l : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (k : ℝ) + 1 := by push_cast; ring
    _ = ((2 : ℝ) ^ k * ((k : ℝ) + 1) * (A + 1) ^ k * |C'|) / (M : ℝ) ^ l := by
        ring

/-- **Structured inverse-Weyl inequality at a base point.** Fix `k` (degree), a scale constant `A ≥ 0`
and a strength `δ > 0`. There are `Q` and `C` such that: if `R` is a real polynomial of degree `≤ k`,
`b, n₀ : ℕ` are two base points at distance `≤ A * M`, `M ≥ 1`, and the exponential sum
`∑_{b ≤ m ≤ b+M-1} eC (R(m))` has modulus at least `δ * M`, then there is `1 ≤ q ≤ Q` such that for
every `l ≤ k` the `l`-th Taylor coefficient of `R` at `n₀` is within `C / M^l` of a rational with
denominator `q`.

Route: apply `weyl_inverse` (N2, `Submission.Work.BMF.weyl_inverse`) to the shifted polynomial
`Polynomial.taylor b R` summed over `[0, M)`, then undo the shift `n₀ - b` with binomial
coefficients, picking up the factor `(A+1)^k`. -/
theorem weyl_structure (k : ℕ) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (R : Polynomial ℝ) (b n₀ : ℕ) (M : ℕ),
      R ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ) → 1 ≤ M →
      |((n₀ : ℝ) - (b : ℝ))| ≤ A * M →
      δ * M ≤ ‖∑ m ∈ Finset.Icc b (b + M - 1), Work.BMF.eC (Polynomial.eval (m : ℝ) R)‖ →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧
        ∀ l ∈ Finset.range (k + 1), ∃ m : ℤ,
          |(q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R).coeff l - m| ≤ C / (M : ℝ) ^ l := by
  obtain ⟨C', hC'pos, hC'⟩ := Work.BMF.SD.FreeW.weyl_inverse k δ hδ
  refine ⟨⌈C'⌉₊, max 1 ((2 : ℝ) ^ k * ((k : ℝ) + 1) * (A + 1) ^ k * |C'|), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro R b n₀ M hdeg hM hdb hsum
  have hnd : R.natDegree ≤ k :=
    Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hdeg)
  have hreindex : ∑ m ∈ Finset.Icc b (b + M - 1), Work.BMF.eC (Polynomial.eval (m : ℝ) R)
      = ∑ n ∈ Finset.range M, Work.BMF.eC (Polynomial.eval ((b + n : ℕ) : ℝ) R) := by
    have himg : (Finset.range M).image (fun n => b + n) = Finset.Icc b (b + M - 1) := by
      ext m
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨n, hn, rfl⟩
        omega
      · intro hm
        exact ⟨m - b, by omega, by omega⟩
    rw [← himg]
    apply Finset.sum_image
    intro x _ y _ hxy
    exact Nat.add_left_cancel hxy
  have heval : ∀ n : ℕ,
      Polynomial.eval ((b + n : ℕ) : ℝ) R
        = ∑ j ∈ Finset.range (k + 1), (Polynomial.taylor (b : ℝ) R).coeff j * (n : ℝ) ^ j := by
    intro n
    have h1 : Polynomial.eval ((b + n : ℕ) : ℝ) R = Polynomial.eval ((n : ℝ) + (b : ℝ)) R := by
      congr 1
      push_cast
      ring
    rw [h1, ← Polynomial.taylor_eval (b : ℝ) R (n : ℝ)]
    exact Polynomial.eval_eq_sum_range' (p := Polynomial.taylor (b : ℝ) R) (n := k + 1)
      (by rw [Polynomial.natDegree_taylor]; omega) (n : ℝ)
  have hsumEq : (∑ m ∈ Finset.Icc b (b + M - 1), Work.BMF.eC (Polynomial.eval (m : ℝ) R))
      = ∑ n ∈ Finset.range M, Work.BMF.eC
          (∑ j ∈ Finset.range (k + 1), (Polynomial.taylor (b : ℝ) R).coeff j * (n : ℝ) ^ j) := by
    rw [hreindex]
    exact Finset.sum_congr rfl (fun n _ => by rw [heval n])
  have hsum' : δ * M ≤ ‖∑ n ∈ Finset.range M, Work.BMF.eC
      (∑ j ∈ Finset.range (k + 1), (Polynomial.taylor (b : ℝ) R).coeff j * (n : ℝ) ^ j)‖ := by
    rw [← hsumEq]
    exact hsum
  obtain ⟨q, hq1, hqle, hcoeff⟩ := hC' M hM (fun j => (Polynomial.taylor (b : ℝ) R).coeff j) hsum'
  refine ⟨q, hq1, ?_, ?_⟩
  · calc (q : ℝ) ≤ C' := hqle
      _ ≤ (⌈C'⌉₊ : ℝ) := Nat.le_ceil C'
  · intro l hl
    rw [Finset.mem_range] at hl
    rcases Nat.eq_zero_or_pos l with hl0 | hlpos
    · subst hl0
      refine ⟨⌊(q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R).coeff 0⌋, ?_⟩
      have hlt : |(q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R).coeff 0
          - ((⌊(q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R).coeff 0⌋ : ℤ) : ℝ)| < 1 := by
        rw [abs_of_nonneg (by
          linarith [Int.floor_le ((q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R).coeff 0)])]
        linarith [Int.lt_floor_add_one ((q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R).coeff 0)]
      calc |(q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R).coeff 0
            - ((⌊(q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R).coeff 0⌋ : ℤ) : ℝ)|
          ≤ 1 := le_of_lt hlt
        _ ≤ max 1 ((2 : ℝ) ^ k * ((k : ℝ) + 1) * (A + 1) ^ k * |C'|) := le_max_left _ _
        _ = max 1 ((2 : ℝ) ^ k * ((k : ℝ) + 1) * (A + 1) ^ k * |C'|) / (M : ℝ) ^ 0 := by
            rw [pow_zero, div_one]
    · have hlk : l ≤ k := by omega
      have hlIcc : l ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hlpos, hlk⟩
      have hdcast : (((n₀ : ℤ) - (b : ℤ) : ℤ) : ℝ) = (n₀ : ℝ) - (b : ℝ) := by
        push_cast; ring
      obtain ⟨m, hm⟩ := weyl_descent_bound k C' A hA M hM q ((n₀ : ℤ) - (b : ℤ))
        (fun i => (Polynomial.taylor (b : ℝ) R).coeff i)
        (by rw [hdcast]; exact hdb) hcoeff l hlIcc
      refine ⟨m, ?_⟩
      have hident : (Polynomial.taylor (n₀ : ℝ) R).coeff l
          = ∑ i ∈ Finset.Icc l k, (Polynomial.taylor (b : ℝ) R).coeff i *
              ((((n₀ : ℤ) - (b : ℤ) : ℤ) : ℝ) ^ (i - l)) * (i.choose l : ℝ) := by
        rw [weyl_coeff_shift R k b n₀ l hnd]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hdcast]
      rw [hident]
      refine le_trans hm ?_
      apply div_le_div_of_nonneg_right _ (pow_nonneg (by exact_mod_cast (Nat.zero_le M)) l)
      exact le_max_right _ _

end Work.BMF.FreeWS
