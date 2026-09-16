import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.PSeries
import Submission.Commons.Analysis.InfiniteSum.summable_prod_mul
import Submission.Commons.Analysis.InfiniteSum.tsum_prod_mul_of_nonneg
import Submission.Commons.NumberTheory.Zeta.tsum_rpow_neg_dvd
import Submission.Commons.NumberTheory.Zeta.norm_lcm_inv_cpow_le

open scoped BigOperators
open Commons.Analysis.InfiniteSum

namespace Commons.NumberTheory.Zeta

/-- The triple-indexed kernel `φ(k)·d^{−(1+c)}·d'^{−(1+e)}` cut off by `k ∣ d ∧ k ∣ d'`. -/
private noncomputable def tripleKernel (c e : ℝ) (q : (ℕ × ℕ) × ℕ) : ℝ :=
  if q.1.1 ≠ 0 ∧ q.1.2 ≠ 0 ∧ q.2 ∣ q.1.1 ∧ q.2 ∣ q.1.2
    then (Nat.totient q.2 : ℝ) * (q.1.1 : ℝ) ^ (-(1 + c)) * (q.1.2 : ℝ) ^ (-(1 + e))
    else 0

/-- The `gcd`-majorant `gcd(d,d')·d^{−(1+c)}·d'^{−(1+e)}`. -/
private noncomputable def zhangMajorant (c e : ℝ) (p : ℕ × ℕ) : ℝ :=
  (Nat.gcd p.1 p.2 : ℝ) * (p.1 : ℝ) ^ (-(1 + c)) * (p.2 : ℝ) ^ (-(1 + e))

private lemma tripleKernel_nonneg (c e : ℝ) (q : (ℕ × ℕ) × ℕ) : 0 ≤ tripleKernel c e q := by
  rw [tripleKernel]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_refl 0

private lemma summable_nat_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
  (Real.summable_nat_rpow).2 (by linarith)

private lemma dvd_indicator_nonneg (k : ℕ) (s : ℝ) (n : ℕ) :
    0 ≤ (if k ∣ n then (n : ℝ) ^ (-s) else 0) := by
  by_cases h : k ∣ n
  · simp only [h, if_true]; exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · simp only [h, if_false]; exact le_refl 0

private lemma summable_dvd_indicator {k : ℕ} {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => if k ∣ n then (n : ℝ) ^ (-s) else 0) := by
  refine Summable.of_nonneg_of_le (fun n => dvd_indicator_nonneg k s n) (fun n => ?_)
    (summable_nat_rpow_neg hs)
  by_cases h : k ∣ n
  · simp only [h, if_true]; exact le_refl _
  · simp only [h, if_false]; exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem summable_lcm_inv_cpow {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Summable (fun x : ℕ × ℕ =>
      ‖(((Nat.lcm x.1 x.2 : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖) := by
  have ha1 : (1 : ℝ) < 1 + a.re := by linarith
  have hb1 : (1 : ℝ) < 1 + b.re := by linarith
  have hab1 : (1 : ℝ) < 1 + a.re + b.re := by linarith
  have hsa : Summable (fun m : ℕ => (m : ℝ) ^ (-(1 + a.re))) := summable_nat_rpow_neg ha1
  have hsb : Summable (fun m : ℕ => (m : ℝ) ^ (-(1 + b.re))) := summable_nat_rpow_neg hb1
  have hSa_nn : 0 ≤ ∑' m : ℕ, (m : ℝ) ^ (-(1 + a.re)) :=
    tsum_nonneg (fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hSb_nn : 0 ≤ ∑' m : ℕ, (m : ℝ) ^ (-(1 + b.re)) :=
    tsum_nonneg (fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _)
  -- Step (i): inner summability over `p` for each `k`.
  have hInner : ∀ k : ℕ, Summable (fun p : ℕ × ℕ => tripleKernel a.re b.re (p, k)) := by
    intro k
    have hbase : Summable (fun p : ℕ × ℕ =>
        (p.1 : ℝ) ^ (-(1 + a.re)) * (p.2 : ℝ) ^ (-(1 + b.re))) :=
      summable_prod_mul hsa hsb
        (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hmaj : Summable (fun p : ℕ × ℕ =>
        (Nat.totient k : ℝ) * (p.1 : ℝ) ^ (-(1 + a.re)) * (p.2 : ℝ) ^ (-(1 + b.re))) := by
      simpa only [mul_assoc] using hbase.mul_left (Nat.totient k : ℝ)
    refine Summable.of_nonneg_of_le (fun p => tripleKernel_nonneg a.re b.re (p, k))
      (fun p => ?_) hmaj
    rw [tripleKernel]
    split_ifs with h
    · rfl
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  -- Step (ii): summability of `k ↦ ∑' p, tripleKernel (p,k)`.
  have hT : Summable (fun k : ℕ => ∑' p : ℕ × ℕ, tripleKernel a.re b.re (p, k)) := by
    have hgm : Summable (fun k : ℕ =>
        (k : ℝ) ^ (-(1 + a.re + b.re)) *
          ((∑' m : ℕ, (m : ℝ) ^ (-(1 + a.re))) * (∑' m : ℕ, (m : ℝ) ^ (-(1 + b.re))))) :=
      (summable_nat_rpow_neg hab1).mul_right _
    refine Summable.of_nonneg_of_le
      (fun k => tsum_nonneg (fun p => tripleKernel_nonneg a.re b.re (p, k))) (fun k => ?_) hgm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hzero : (∑' p : ℕ × ℕ, tripleKernel a.re b.re (p, 0)) = 0 := by
        rw [show (∑' p : ℕ × ℕ, tripleKernel a.re b.re (p, 0))
              = ∑' p : ℕ × ℕ, (0 : ℝ) from
            tsum_congr (fun p => by
              rw [tripleKernel]
              by_cases hp : p.1 = 0
              · simp [hp]
              · simp [hp, zero_dvd_iff])]
        exact tsum_zero
      rw [hzero]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg 0) _) (mul_nonneg hSa_nn hSb_nn)
    · -- main case k ≥ 1
      have hAn : Summable (fun n : ℕ => if k ∣ n then (n : ℝ) ^ (-(1 + a.re)) else 0) :=
        summable_dvd_indicator ha1
      have hBn : Summable (fun n : ℕ => if k ∣ n then (n : ℝ) ^ (-(1 + b.re)) else 0) :=
        summable_dvd_indicator hb1
      have hterm : ∀ p : ℕ × ℕ,
          tripleKernel a.re b.re (p, k) ≤
            (Nat.totient k : ℝ) *
              ((if k ∣ p.1 then (p.1 : ℝ) ^ (-(1 + a.re)) else 0) *
               (if k ∣ p.2 then (p.2 : ℝ) ^ (-(1 + b.re)) else 0)) := by
        intro p
        rw [tripleKernel]
        by_cases h : (p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ k ∣ p.1 ∧ k ∣ p.2)
        · rw [if_pos h, if_pos h.2.2.1, if_pos h.2.2.2, mul_assoc]
        · rw [if_neg h]
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (dvd_indicator_nonneg k (1 + a.re) p.1)
              (dvd_indicator_nonneg k (1 + b.re) p.2))
      have hmaj : Summable (fun p : ℕ × ℕ =>
          (Nat.totient k : ℝ) *
            ((if k ∣ p.1 then (p.1 : ℝ) ^ (-(1 + a.re)) else 0) *
             (if k ∣ p.2 then (p.2 : ℝ) ^ (-(1 + b.re)) else 0))) :=
        (summable_prod_mul hAn hBn
          (fun n => dvd_indicator_nonneg k (1 + a.re) n)
          (fun n => dvd_indicator_nonneg k (1 + b.re) n)).mul_left (Nat.totient k : ℝ)
      have hle := Summable.tsum_le_tsum hterm (hInner k) hmaj
      refine le_trans hle ?_
      rw [tsum_mul_left]
      rw [tsum_prod_mul_of_nonneg hAn hBn
            (fun n => dvd_indicator_nonneg k (1 + a.re) n)
            (fun n => dvd_indicator_nonneg k (1 + b.re) n)]
      rw [tsum_rpow_neg_dvd hk (1 + a.re), tsum_rpow_neg_dvd hk (1 + b.re)]
      -- arithmetic: φ(k)·(k^{−(1+c)}Sa)·(k^{−(1+e)}Sb) ≤ k^{−(1+c+e)}·(Sa·Sb)
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      have hphi : (Nat.totient k : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Nat.totient_le k)
      have hsplit : (k : ℝ) ^ (-(1 + a.re)) * (k : ℝ) ^ (-(1 + b.re))
          = (k : ℝ) ^ (-(2 + a.re + b.re)) := by
        rw [← Real.rpow_add hkpos]; congr 1; ring
      have hmerge : (k : ℝ) * (k : ℝ) ^ (-(2 + a.re + b.re))
          = (k : ℝ) ^ (-(1 + a.re + b.re)) := by
        nth_rewrite 1 [← Real.rpow_one (k : ℝ)]
        rw [← Real.rpow_add hkpos]; congr 1; ring
      have hk2nn : 0 ≤ (k : ℝ) ^ (-(2 + a.re + b.re)) :=
        Real.rpow_nonneg (Nat.cast_nonneg k) _
      have hSSnn : 0 ≤ (∑' m : ℕ, (m : ℝ) ^ (-(1 + a.re))) *
          (∑' m : ℕ, (m : ℝ) ^ (-(1 + b.re))) := mul_nonneg hSa_nn hSb_nn
      have hkey : (Nat.totient k : ℝ) * ((k : ℝ) ^ (-(1 + a.re)) * (k : ℝ) ^ (-(1 + b.re)))
          ≤ (k : ℝ) ^ (-(1 + a.re + b.re)) := by
        rw [hsplit, ← hmerge]
        exact mul_le_mul_of_nonneg_right hphi hk2nn
      have hkey2 : (Nat.totient k : ℝ) * ((k : ℝ) ^ (-(1 + a.re)) * (k : ℝ) ^ (-(1 + b.re)))
            * ((∑' m : ℕ, (m : ℝ) ^ (-(1 + a.re))) * (∑' m : ℕ, (m : ℝ) ^ (-(1 + b.re))))
          ≤ (k : ℝ) ^ (-(1 + a.re + b.re)) *
            ((∑' m : ℕ, (m : ℝ) ^ (-(1 + a.re))) * (∑' m : ℕ, (m : ℝ) ^ (-(1 + b.re)))) :=
        mul_le_mul_of_nonneg_right hkey hSSnn
      nlinarith [hkey2]
  -- Step (iii): assemble summability of the triple kernel.
  have hswap : Summable (fun q : ℕ × (ℕ × ℕ) => tripleKernel a.re b.re (q.2, q.1)) :=
    (summable_prod_of_nonneg (f := fun q : ℕ × (ℕ × ℕ) => tripleKernel a.re b.re (q.2, q.1))
      (fun q => tripleKernel_nonneg a.re b.re (q.2, q.1))).2 ⟨hInner, hT⟩
  have hΦ : Summable (tripleKernel a.re b.re) :=
    (Equiv.summable_iff (f := tripleKernel a.re b.re)
      (Equiv.prodComm (ℕ × ℕ) ℕ).symm).1 hswap
  -- Step (iv): apply Tonelli in the original order.
  have hprod := (summable_prod_of_nonneg
    (f := tripleKernel a.re b.re) (fun q => tripleKernel_nonneg a.re b.re q)).1 hΦ
  have hG : Summable (fun p : ℕ × ℕ => ∑' k : ℕ, tripleKernel a.re b.re (p, k)) := hprod.2
  -- Step (v): `F ≤ G` pointwise.
  have hFG : ∀ p : ℕ × ℕ,
      zhangMajorant a.re b.re p ≤ ∑' k : ℕ, tripleKernel a.re b.re (p, k) := by
    rintro ⟨d, d'⟩
    by_cases hd : d = 0
    · subst hd
      have hF0 : zhangMajorant a.re b.re (0, d') = 0 := by
        simp only [zhangMajorant, Nat.cast_zero,
          Real.zero_rpow (by linarith : -(1 + a.re) ≠ 0), mul_zero, zero_mul]
      rw [hF0]
      exact tsum_nonneg (fun k => tripleKernel_nonneg a.re b.re ((0, d'), k))
    by_cases hd' : d' = 0
    · subst hd'
      have hF0 : zhangMajorant a.re b.re (d, 0) = 0 := by
        simp only [zhangMajorant, Nat.cast_zero,
          Real.zero_rpow (by linarith : -(1 + b.re) ≠ 0), mul_zero, zero_mul]
      rw [hF0]
      exact tsum_nonneg (fun k => tripleKernel_nonneg a.re b.re ((d, 0), k))
    -- d, d' ≥ 1
    have hdiv : ∀ k ∈ (Nat.gcd d d').divisors,
        tripleKernel a.re b.re ((d, d'), k)
          = (Nat.totient k : ℝ) * (d : ℝ) ^ (-(1 + a.re)) * (d' : ℝ) ^ (-(1 + b.re)) := by
      intro k hk
      rw [Nat.mem_divisors] at hk
      obtain ⟨hkg, -⟩ := hk
      rw [tripleKernel, if_pos]
      exact ⟨hd, hd', hkg.trans (Nat.gcd_dvd_left d d'), hkg.trans (Nat.gcd_dvd_right d d')⟩
    have hsum_eq : (∑ k ∈ (Nat.gcd d d').divisors, tripleKernel a.re b.re ((d, d'), k))
        = zhangMajorant a.re b.re (d, d') := by
      rw [Finset.sum_congr rfl hdiv]
      rw [show (∑ k ∈ (Nat.gcd d d').divisors,
              (Nat.totient k : ℝ) * (d : ℝ) ^ (-(1 + a.re)) * (d' : ℝ) ^ (-(1 + b.re)))
            = ((∑ k ∈ (Nat.gcd d d').divisors, (Nat.totient k : ℝ))
                * (d : ℝ) ^ (-(1 + a.re))) * (d' : ℝ) ^ (-(1 + b.re)) by
          rw [← Finset.sum_mul, ← Finset.sum_mul]]
      rw [show (∑ k ∈ (Nat.gcd d d').divisors, (Nat.totient k : ℝ)) = (Nat.gcd d d' : ℝ) by
          rw [← Nat.cast_sum, Nat.sum_totient]]
      simp only [zhangMajorant]
    rw [← hsum_eq]
    exact Summable.sum_le_tsum _ (fun k _ => tripleKernel_nonneg a.re b.re ((d, d'), k))
      (hprod.1 (d, d'))
  have hFnn : ∀ p : ℕ × ℕ, 0 ≤ zhangMajorant a.re b.re p := by
    rintro ⟨d, d'⟩
    simp only [zhangMajorant]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hF : Summable (zhangMajorant a.re b.re) := Summable.of_nonneg_of_le hFnn hFG hG
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hF
  exact norm_lcm_inv_cpow_le ha hb x.1 x.2

end Commons.NumberTheory.Zeta