import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.SelbergWeights

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Pointwise bound for the optimal Selberg weights

For `d ∈ selbergT D P` (i.e. `d ≤ D`, `d ∣ P`) the optimal Selberg weight satisfies

  `|λ d| ≤ ∏_{p ∣ d} (p - 1)/(p - 2)`.

The proof is the classical pointwise estimate.  Unfolding the definition,
`λ d = φ(d) · Σ_{l ∈ T, d ∣ l} μ(l/d) y_l` with `y_l = μ(l)/(w l · G)`, `w l = ∏_{p|l}(p-2)`
and `G = Σ_{l ∈ T} 1/w l`.  Since `P` is squarefree with odd prime factors, every `l ∣ P` is odd
and squarefree and `w l > 0`.  Writing `l = d · m` with `m = l/d` (coprime to `d` because `l` is
squarefree) gives `w l = w d · w m`, so

  `Σ_{l ∈ T, d ∣ l} |y_l| ≤ (1/G) · Σ_{l} 1/w l = (1/(G · w d)) · Σ_{m ∈ A} 1/w m
   ≤ (1/(G · w d)) · G = 1/w d`,

where `A = {l/d : l ∈ T, d ∣ l} ⊆ T`.  Hence `|λ d| ≤ φ(d)/w d = ∏_{p ∣ d} (p-1)/(p-2)`.
-/

/-- Membership in `selbergT D P`. -/
private lemma absle_mem_selbergT {D P d : ℕ} :
    d ∈ selbergT D P ↔ 1 ≤ d ∧ d ≤ D ∧ d ∣ P := by
  rw [selbergT, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- `1` belongs to `selbergT D P` when `1 ≤ D`. -/
private lemma absle_one_mem_selbergT (D P : ℕ) (hD : 1 ≤ D) : (1 : ℕ) ∈ selbergT D P := by
  rw [absle_mem_selbergT]
  exact ⟨le_rfl, hD, one_dvd P⟩

/-- `w l = ∏_{p ∣ l}(p - 2)` is positive whenever `l ∣ P` and the prime factors of `P` are `≥ 3`. -/
private lemma absle_selbergWt_pos {P l : ℕ} (hodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (hP0 : P ≠ 0)
    (hlP : l ∣ P) : 0 < selbergWt l := by
  rw [selbergWt]
  refine Finset.prod_pos (fun p hp => ?_)
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hodd p (Nat.primeFactors_mono hlP hP0 hp)
  linarith

/-- The Selberg constant `G` is positive (the term `l = 1` contributes `1`). -/
private lemma absle_selbergG_pos {P : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (hodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (hP0 : P ≠ 0) : 0 < selbergG D P := by
  have hmem : (1 : ℕ) ∈ selbergT D P := absle_one_mem_selbergT D P hD
  have hterm : ∀ l ∈ selbergT D P, 0 ≤ 1 / selbergWt l := fun l hl =>
    div_nonneg zero_le_one
      (le_of_lt (absle_selbergWt_pos hodd hP0 (absle_mem_selbergT.mp hl).2.2))
  have h1 : 1 / selbergWt 1 ≤ selbergG D P := Finset.single_le_sum hterm hmem
  have h2 : (1 : ℝ) ≤ selbergG D P := by
    simpa [selbergWt, Nat.primeFactors_one] using h1
  linarith

/-- For squarefree `l` and `d ∣ l`, the quotient `l/d` is coprime to `d`. -/
private lemma absle_coprime_div {d l : ℕ} (hl : Squarefree l) (hdl : d ∣ l) :
    d.Coprime (l / d) := by
  rw [← Nat.mul_div_cancel' hdl] at hl
  exact Nat.coprime_iff_isRelPrime.mpr (squarefree_mul_iff.mp hl).1

/-- `w` is multiplicative on coprime arguments. -/
private lemma absle_wt_mul {d m : ℕ} (h : d.Coprime m) :
    selbergWt (d * m) = selbergWt d * selbergWt m := by
  rw [selbergWt, selbergWt, selbergWt, Nat.Coprime.primeFactors_mul h,
    Finset.prod_union (Nat.Coprime.disjoint_primeFactors h)]

/-- The Möbius function is bounded by `1` in absolute value. -/
private lemma absle_moebius_abs_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
  split <;> norm_num

theorem selbergLam_abs_le (D P d : ℕ) (hD : 1 ≤ D) (hPsq : Squarefree P)
    (hodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hd : d ∈ Work.NumberTheory.Chen.BTermCount.selbergT D P) :
    |Work.NumberTheory.Chen.BTermCount.selbergLam D P d|
      ≤ ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  obtain ⟨hd1, hdD, hdP⟩ := absle_mem_selbergT.mp hd
  have hP0 : P ≠ 0 := hPsq.ne_zero
  have hdsq : Squarefree d := hPsq.squarefree_of_dvd hdP
  have hGpos : 0 < selbergG D P := absle_selbergG_pos D hD hodd hP0
  have hwdpos : 0 < selbergWt d := absle_selbergWt_pos hodd hP0 hdP
  -- unfold `selbergLam`
  have hlam : selbergLam D P d
      = (Nat.totient d : ℝ) * ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l),
          (ArithmeticFunction.moebius (l / d) : ℝ) * selbergY D P l := by
    rw [selbergLam, if_pos hd]
    congr 1
    exact (Finset.sum_filter (s := selbergT D P) (p := fun l : ℕ => d ∣ l)
      (f := fun l : ℕ => (ArithmeticFunction.moebius (l / d) : ℝ) * selbergY D P l)).symm
  -- termwise bound
  have hterm : ∀ l ∈ (selbergT D P).filter (fun l => d ∣ l),
      |(ArithmeticFunction.moebius (l / d) : ℝ) * selbergY D P l|
        ≤ 1 / (selbergWt l * selbergG D P) := by
    intro l hl
    obtain ⟨hlT, hdl⟩ := Finset.mem_filter.mp hl
    obtain ⟨hl1, hlD, hlP⟩ := absle_mem_selbergT.mp hlT
    have hlw : 0 < selbergWt l := absle_selbergWt_pos hodd hP0 hlP
    have hy : |selbergY D P l|
        = |(ArithmeticFunction.moebius l : ℝ)| / (selbergWt l * selbergG D P) := by
      rw [selbergY, if_pos hlD, abs_div, abs_div, abs_of_pos hlw, abs_of_pos hGpos, div_div]
    calc |(ArithmeticFunction.moebius (l / d) : ℝ) * selbergY D P l|
        = |(ArithmeticFunction.moebius (l / d) : ℝ)|
            * (|(ArithmeticFunction.moebius l : ℝ)| / (selbergWt l * selbergG D P)) := by
          rw [abs_mul, hy]
      _ ≤ 1 * (1 / (selbergWt l * selbergG D P)) := by
          have hden : 0 ≤ selbergWt l * selbergG D P := le_of_lt (mul_pos hlw hGpos)
          have hnum : |(ArithmeticFunction.moebius l : ℝ)| / (selbergWt l * selbergG D P)
              ≤ 1 / (selbergWt l * selbergG D P) :=
            div_le_div_of_nonneg_right (absle_moebius_abs_le_one l) hden
          have hc : 0 ≤ |(ArithmeticFunction.moebius l : ℝ)| / (selbergWt l * selbergG D P) :=
            div_nonneg (abs_nonneg _) hden
          exact mul_le_mul (absle_moebius_abs_le_one (l / d)) hnum hc (by norm_num)
      _ = 1 / (selbergWt l * selbergG D P) := one_mul _
  -- the sum is bounded by `1 / w d`
  have hsum : |∑ l ∈ (selbergT D P).filter (fun l => d ∣ l),
        (ArithmeticFunction.moebius (l / d) : ℝ) * selbergY D P l| ≤ 1 / selbergWt d := by
    refine le_trans (abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
    have hA : ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l), 1 / (selbergWt l * selbergG D P)
        = (∑ l ∈ (selbergT D P).filter (fun l => d ∣ l), 1 / selbergWt l)
            / selbergG D P := by
      have h1 : ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l),
            1 / (selbergWt l * selbergG D P)
          = ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l),
              (1 / selbergWt l) / selbergG D P :=
        Finset.sum_congr rfl (fun l _ => by rw [div_div])
      rw [h1, Finset.sum_div]
    have hinj : Set.InjOn (fun l : ℕ => l / d)
        ↑((selbergT D P).filter (fun l => d ∣ l)) := by
      intro a ha b hb hab
      have ha' : d * (a / d) = a := Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2
      have hb' : d * (b / d) = b := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2
      have hab' : a / d = b / d := hab
      rw [← ha', ← hb', hab']
    have himg : ∑ m ∈ ((selbergT D P).filter (fun l => d ∣ l)).image (fun l : ℕ => l / d),
          1 / selbergWt m
        = ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l), 1 / selbergWt (l / d) :=
      Finset.sum_image (s := (selbergT D P).filter (fun l => d ∣ l))
        (g := fun l : ℕ => l / d) (f := fun m : ℕ => 1 / selbergWt m) hinj
    have hpoint : ∀ l ∈ (selbergT D P).filter (fun l => d ∣ l),
        1 / selbergWt l = (1 / selbergWt d) * (1 / selbergWt (l / d)) := by
      intro l hl
      obtain ⟨hlT, hdl⟩ := Finset.mem_filter.mp hl
      obtain ⟨hl1, hlD, hlP⟩ := absle_mem_selbergT.mp hlT
      have hlsq : Squarefree l := hPsq.squarefree_of_dvd hlP
      have hw : selbergWt l = selbergWt d * selbergWt (l / d) := by
        conv_lhs => rw [← Nat.mul_div_cancel' hdl]
        rw [absle_wt_mul (absle_coprime_div hlsq hdl)]
      rw [hw, one_div, one_div, one_div, mul_inv_rev]
      ring
    have hsub : ((selbergT D P).filter (fun l => d ∣ l)).image (fun l : ℕ => l / d)
        ⊆ selbergT D P := by
      intro m hm
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hlT, hdl⟩ := Finset.mem_filter.mp hl
      obtain ⟨hl1, hlD, hlP⟩ := absle_mem_selbergT.mp hlT
      have hmul : d * (l / d) = l := Nat.mul_div_cancel' hdl
      have hle : l / d ≤ l := by
        calc l / d = 1 * (l / d) := (one_mul _).symm
          _ ≤ d * (l / d) := Nat.mul_le_mul_right _ hd1
          _ = l := hmul
      have h1 : 1 ≤ l / d := by
        rcases Nat.eq_zero_or_pos (l / d) with h | h
        · rw [h, mul_zero] at hmul
          omega
        · exact h
      rw [absle_mem_selbergT]
      exact ⟨h1, le_trans hle hlD, dvd_trans (Nat.div_dvd_of_dvd hdl) hlP⟩
    have hB : ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l), 1 / selbergWt l
        ≤ (1 / selbergWt d) * selbergG D P := by
      have h1 : ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l), 1 / selbergWt l
          = (1 / selbergWt d) * ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l),
              1 / selbergWt (l / d) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hpoint
      have h3 : ∑ m ∈ ((selbergT D P).filter (fun l => d ∣ l)).image (fun l : ℕ => l / d),
            1 / selbergWt m ≤ selbergG D P := by
        have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ =>
          div_nonneg zero_le_one
            (le_of_lt (absle_selbergWt_pos hodd hP0 (absle_mem_selbergT.mp hi).2.2)))
        simpa only [selbergG] using hle
      rw [h1, ← himg]
      exact mul_le_mul_of_nonneg_left h3 (le_of_lt (one_div_pos.mpr hwdpos))
    calc ∑ l ∈ (selbergT D P).filter (fun l => d ∣ l), 1 / (selbergWt l * selbergG D P)
        = (∑ l ∈ (selbergT D P).filter (fun l => d ∣ l), 1 / selbergWt l)
            / selbergG D P := hA
      _ ≤ ((1 / selbergWt d) * selbergG D P) / selbergG D P :=
          div_le_div_of_nonneg_right hB (le_of_lt hGpos)
      _ = 1 / selbergWt d := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hGpos)]
  -- `φ(d)/w(d) = ∏ (p-1)/(p-2)`
  have hphi : (Nat.totient d : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
    rw [totient_eq_prod_sub_one_of_squarefree hdsq, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub hp1, Nat.cast_one]
  have hprod : (Nat.totient d : ℝ) / selbergWt d
      = ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    rw [hphi, selbergWt, ← Finset.prod_div_distrib]
  calc |selbergLam D P d|
      = (Nat.totient d : ℝ) * |∑ l ∈ (selbergT D P).filter (fun l => d ∣ l),
            (ArithmeticFunction.moebius (l / d) : ℝ) * selbergY D P l| := by
          rw [hlam, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (Nat.totient d : ℝ) * (1 / selbergWt d) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
          rw [mul_one_div, hprod]

end

end Work.NumberTheory.Chen.BTermCount
