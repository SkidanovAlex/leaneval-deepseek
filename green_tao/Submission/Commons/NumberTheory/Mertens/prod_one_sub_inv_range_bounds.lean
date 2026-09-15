import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_eventually_bounded
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Harmonic.sum_inv_sq_primes_tail_le

namespace Commons.NumberTheory.Mertens

open Finset Real

/-! ## Helper lemmas toward `prod_one_sub_inv_range_bounds` -/

/-- `primeRecips` is nonnegative. -/
private lemma primeRecips_nonneg' (x : ℝ) : 0 ≤ primeRecips x := by
  unfold primeRecips
  exact Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p))

/-- The two-sided sharp (constant `1` coefficient) second-Mertens bound, valid for
**all** `x ≥ 3` (not merely eventually).  Derived from the eventual version by using
monotonicity of `primeRecips` and of `log ∘ log` on the remaining compact range. -/
private lemma primeRecips_sub_loglog_abs_bounded' :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |primeRecips x - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C, hCpos, X₀, hX₀, hC⟩ := primeRecips_sub_loglog_eventually_bounded
  refine ⟨max C (max (primeRecips X₀) (Real.log (Real.log X₀))), ?_, ?_⟩
  · exact lt_of_lt_of_le hCpos (le_max_left _ _)
  · intro x hx
    rcases le_total X₀ x with hxX | hXx
    · exact le_trans (hC x hxX) (le_max_left _ _)
    · have hxX₀ : x ≤ X₀ := hXx
      have hpl : primeRecips x ≤ primeRecips X₀ := primeRecips_mono hxX₀
      have hp0 : 0 ≤ primeRecips x := primeRecips_nonneg' x
      have hll0 : 0 ≤ Real.log (Real.log x) := log_log_nonneg_of_three_le hx
      have hll_le : Real.log (Real.log x) ≤ Real.log (Real.log X₀) := by
        apply Real.log_le_log (Real.log_pos (by linarith : (1:ℝ) < x))
        exact Real.log_le_log (by linarith : (0:ℝ) < x) hxX₀
      have hmax : max (primeRecips X₀) (Real.log (Real.log X₀))
          ≤ max C (max (primeRecips X₀) (Real.log (Real.log X₀))) := le_max_right _ _
      have hplC : primeRecips X₀
          ≤ max C (max (primeRecips X₀) (Real.log (Real.log X₀))) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have hle : Real.log (Real.log x)
            ≤ max (primeRecips X₀) (Real.log (Real.log X₀)) :=
          le_trans hll_le (le_max_right _ _)
        linarith [hp0, hle, hmax]
      · linarith [hp0, hll0, hpl, hplC]

/-- `primeRecips x ≤ log (log x) + C` for all `x ≥ 3`. -/
private lemma primeRecips_le_loglog_add :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → primeRecips x ≤ Real.log (Real.log x) + C := by
  obtain ⟨C, hCpos, hC⟩ := primeRecips_sub_loglog_abs_bounded'
  exact ⟨C, hCpos, fun x hx => by
    have := (abs_le.mp (hC x hx)).2; linarith⟩

/-- `1 - 1/p ≤ exp (-1/p)`. -/
private lemma one_sub_inv_le_exp_neg (p : ℕ) :
    (1 : ℝ) - 1 / (p : ℝ) ≤ Real.exp (-(1 / (p : ℝ))) := by
  have h := Real.add_one_le_exp (-(1 / (p : ℝ)))
  linarith

/-- `exp (-1/(p-1)) ≤ 1 - 1/p` for `p ≥ 2`. -/
private lemma exp_neg_inv_pred_le_one_sub_inv (p : ℕ) (hp : 2 ≤ p) :
    Real.exp (-(1 / ((p : ℝ) - 1))) ≤ 1 - 1 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1pos : 0 < (p : ℝ) - 1 := by linarith
  have hpos : 0 < (1 : ℝ) - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast (by omega : 1 < p)
    linarith
  have harg : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
    field_simp
  have hlog : Real.log ((1 : ℝ) - 1 / (p : ℝ))
      = Real.log ((p : ℝ) - 1) - Real.log (p : ℝ) := by
    rw [harg, Real.log_div (ne_of_gt hpm1pos) (ne_of_gt hp0)]
  have hge : -(1 / ((p : ℝ) - 1)) ≤ Real.log ((1 : ℝ) - 1 / (p : ℝ)) := by
    rw [hlog]
    have h := Real.log_le_sub_one_of_pos (div_pos hp0 hpm1pos)
    have hdiv : Real.log ((p : ℝ) / ((p : ℝ) - 1))
        = Real.log (p : ℝ) - Real.log ((p : ℝ) - 1) :=
      Real.log_div (ne_of_gt hp0) (ne_of_gt hpm1pos)
    have hval : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by
      field_simp
      ring
    rw [hdiv, hval] at h
    linarith
  calc Real.exp (-(1 / ((p : ℝ) - 1)))
      ≤ Real.exp (Real.log ((1 : ℝ) - 1 / (p : ℝ))) := Real.exp_le_exp.mpr hge
    _ = (1 : ℝ) - 1 / (p : ℝ) := Real.exp_log hpos

/-- Product form of `1 - 1/p ≤ exp (-1/p)`. -/
private lemma prod_one_sub_inv_le_exp_neg_sum (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∏ p ∈ S, (1 - 1 / (p : ℝ))) ≤ Real.exp (-(∑ p ∈ S, 1 / (p : ℝ))) := by
  have h1 : (∏ p ∈ S, (1 - 1 / (p : ℝ))) ≤ ∏ p ∈ S, Real.exp (-(1 / (p : ℝ))) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (by have := hS p hp; omega : 1 ≤ p)
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have : 1 / (p : ℝ) ≤ 1 := by
        rw [div_le_one hp0]; exact hp1
      linarith
    · intro p _; exact one_sub_inv_le_exp_neg p
  have h2 : (∏ p ∈ S, Real.exp (-(1 / (p : ℝ))))
      = Real.exp (-(∑ p ∈ S, 1 / (p : ℝ))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [h2] at h1; exact h1

/-- Product form of `exp (-1/(p-1)) ≤ 1 - 1/p`. -/
private lemma prod_exp_neg_inv_pred_le (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  have h1 : (∏ p ∈ S, Real.exp (-(1 / ((p : ℝ) - 1)))) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p _; exact le_of_lt (Real.exp_pos _)
    · intro p hp; exact exp_neg_inv_pred_le_one_sub_inv p (hS p hp)
  have h2 : (∏ p ∈ S, Real.exp (-(1 / ((p : ℝ) - 1))))
      = Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [h2] at h1; exact h1

/-- `1/(p-1) = 1/p + 1/(p(p-1))`. -/
private lemma sum_inv_pred_eq (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∑ p ∈ S, 1 / ((p : ℝ) - 1))
      = (∑ p ∈ S, 1 / (p : ℝ)) + ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  field_simp
  ring

/-- The correction sum `Σ 1/(p(p-1))` over primes `p ≤ N` is bounded by `4`. -/
private lemma sum_inv_mul_pred_le_four (N : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ Nat.primesLE N) :
    (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 4 := by
  have h2 : (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1)))
      ≤ ∑ p ∈ S, 2 / ((p : ℝ) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hpmem := hS p hp
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hpmem).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hle : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
      rw [div_le_div_iff₀ hpm1 hp0]; nlinarith
    calc 1 / ((p : ℝ) * ((p : ℝ) - 1))
        = (1 / (p : ℝ)) * (1 / ((p : ℝ) - 1)) := by field_simp
      _ ≤ (1 / (p : ℝ)) * (2 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 / ((p : ℝ) ^ 2) := by field_simp
  have hsubset : S ⊆ (Nat.primesLE N).filter (fun q : ℕ => (2 : ℝ) ≤ (q : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter]
    exact ⟨hS p hp, by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.mem_primesLE.mp (hS p hp)).2.two_le
      exact hp2⟩
  have h3 : (∑ p ∈ S, (1 : ℝ) / ((p : ℝ) ^ 2))
      ≤ ∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => (2 : ℝ) ≤ (q : ℝ)),
          1 / ((q : ℝ) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q _ _ => by positivity)
  have h4 : (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => (2 : ℝ) ≤ (q : ℝ)),
        1 / ((q : ℝ) ^ 2)) ≤ 4 / 2 :=
      Commons.NumberTheory.Harmonic.sum_inv_sq_primes_tail_le 2 N (le_refl 2)
  calc (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1)))
      ≤ ∑ p ∈ S, 2 / ((p : ℝ) ^ 2) := h2
    _ = 2 * ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ 2 * (4 / 2) := by
        exact mul_le_mul_of_nonneg_left (le_trans h3 h4) (by norm_num)
    _ = 4 := by norm_num


/-- `primeRecips Q - primeRecips P` is bounded above by the sum of `1/p` over the primes
`p` with `P ≤ p ≤ ⌊Q⌋` (the surviving difference set is a subset of that range). -/
private lemma primeRecips_diff_le_primeRange_sum (P Q : ℝ) (hPQ : P ≤ Q) :
    primeRecips Q - primeRecips P
      ≤ ∑ p ∈ (Nat.primesLE ⌊Q⌋₊).filter (fun p : ℕ => P ≤ (p : ℝ)), 1 / (p : ℝ) := by
  set N : ℕ := ⌊Q⌋₊ with hN
  set M : ℕ := ⌊P⌋₊ with hM
  have hMN : M ≤ N := Nat.floor_le_floor hPQ
  have hTB : Nat.primesLE M ⊆ Nat.primesLE N := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hMN, hp.2⟩
  have hsum : (∑ p ∈ Nat.primesLE N \ Nat.primesLE M, 1 / (p : ℝ))
      = primeRecips Q - primeRecips P := by
    have hs := Finset.sum_sdiff hTB (f := fun p : ℕ => (1 : ℝ) / p)
    unfold primeRecips
    simp only [hN, hM] at hs ⊢
    linarith
  rw [← hsum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  intro p hp
  rw [Finset.mem_filter]
  rw [Finset.mem_sdiff] at hp
  refine ⟨hp.1, ?_⟩
  have hpnotT : p ∉ Nat.primesLE M := hp.2
  have hgt : M < p := by
    by_contra hle
    push_neg at hle
    exact hpnotT (Nat.mem_primesLE.mpr ⟨hle, (Nat.mem_primesLE.mp hp.1).2⟩)
  have hcast : ((M : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast (by omega : M + 1 ≤ p)
  have hPlt : P < (M : ℝ) + 1 := Nat.lt_floor_add_one P
  linarith

/-- The sum of `1/p` over primes `p` with `P ≤ p ≤ ⌊Q⌋` is at most
`primeRecips Q - primeRecips P + 1/3`. -/
private lemma primeRange_sum_le_primeRecips_diff_add (P Q : ℝ) (hP : 3 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ (Nat.primesLE ⌊Q⌋₊).filter (fun p : ℕ => P ≤ (p : ℝ)), 1 / (p : ℝ))
      ≤ primeRecips Q - primeRecips P + 1 / 3 := by
  set N : ℕ := ⌊Q⌋₊ with hN
  set M : ℕ := ⌊P⌋₊ with hM
  have hMN : M ≤ N := Nat.floor_le_floor hPQ
  have hTB : Nat.primesLE M ⊆ Nat.primesLE N := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hMN, hp.2⟩
  have hsum : (∑ p ∈ Nat.primesLE N \ Nat.primesLE M, 1 / (p : ℝ))
      = primeRecips Q - primeRecips P := by
    have hs := Finset.sum_sdiff hTB (f := fun p : ℕ => (1 : ℝ) / p)
    unfold primeRecips
    simp only [hN, hM] at hs ⊢
    linarith
  have hSU : (Nat.primesLE N).filter (fun p : ℕ => P ≤ (p : ℝ))
      ⊆ (Nat.primesLE N \ Nat.primesLE M) ∪ {M} := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hpB, hpP⟩
    rw [Finset.mem_union]
    by_cases hpT : p ∈ Nat.primesLE M
    · right
      rw [Finset.mem_singleton]
      have hpMle : (p : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hpT).1
      have hMleP : (M : ℝ) ≤ P := Nat.floor_le (by linarith)
      have : (p : ℝ) = (M : ℝ) := le_antisymm hpMle (le_trans hMleP hpP)
      exact_mod_cast this
    · left
      exact Finset.mem_sdiff.mpr ⟨hpB, hpT⟩
  have hle : (∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => P ≤ (p : ℝ)), 1 / (p : ℝ))
      ≤ ∑ p ∈ (Nat.primesLE N \ Nat.primesLE M) ∪ {M}, 1 / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSU
      (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  have hMnotU : M ∉ Nat.primesLE N \ Nat.primesLE M := by
    rw [Finset.mem_sdiff]
    rintro ⟨hMB, hMT⟩
    exact hMT (Nat.mem_primesLE.mpr ⟨le_refl M, (Nat.mem_primesLE.mp hMB).2⟩)
  have hdisj : Disjoint (Nat.primesLE N \ Nat.primesLE M) {M} := by
    rw [Finset.disjoint_left]
    intro a ha haM
    rw [Finset.mem_singleton] at haM
    exact hMnotU (haM ▸ ha)
  have hsumU : (∑ p ∈ (Nat.primesLE N \ Nat.primesLE M) ∪ {M}, 1 / (p : ℝ))
      = (primeRecips Q - primeRecips P) + 1 / (M : ℝ) := by
    rw [Finset.sum_union hdisj, Finset.sum_singleton, hsum]
  have hM3 : (3 : ℝ) ≤ (M : ℝ) := by
    have : 3 ≤ M := Nat.le_floor hP
    exact_mod_cast this
  have hMinv : 1 / (M : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hM3
  simp only [hN] at hle
  linarith [hle, hsumU, hMinv]

/-- **Range bound for `∏_{P ≤ p ≤ Q} (1 - 1/p)`.** There are positive constants `c, C`
with
`c · (log P / log Q) ≤ ∏_{P ≤ p ≤ Q} (1 - 1/p) ≤ C · (log P / log Q)`
for all `3 ≤ P ≤ Q`.  This is the effective form of Mertens' third theorem over a range of
primes; both sides follow from the sharp second-Mertens bound together with
`1 - 1/p ≤ exp(-1/p)` and `exp(-1/(p-1)) ≤ 1 - 1/p`. -/
theorem prod_one_sub_inv_range_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ P Q : ℝ, 3 ≤ P → P ≤ Q →
      c * (Real.log P / Real.log Q)
          ≤ ∏ p ∈ (Nat.primesLE ⌊Q⌋₊).filter (fun p : ℕ => P ≤ (p : ℝ)),
              (1 - 1 / ((p : ℕ) : ℝ))
        ∧ (∏ p ∈ (Nat.primesLE ⌊Q⌋₊).filter (fun p : ℕ => P ≤ (p : ℝ)),
              (1 - 1 / ((p : ℕ) : ℝ))) ≤ C * (Real.log P / Real.log Q) := by
  obtain ⟨Cb, hCbpos, hCb⟩ := primeRecips_sub_loglog_abs_bounded'
  refine ⟨Real.exp (-(2 * Cb + 13 / 3)), Real.exp (2 * Cb),
    Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro P Q hP hPQ
  have hP1 : (1 : ℝ) < P := by linarith
  have hQ1 : (1 : ℝ) < Q := by linarith
  have hlogPpos : 0 < Real.log P := Real.log_pos hP1
  have hlogQpos : 0 < Real.log Q := Real.log_pos hQ1
  have hQ3 : 3 ≤ Q := le_trans hP hPQ
  set S := (Nat.primesLE ⌊Q⌋₊).filter (fun p : ℕ => P ≤ (p : ℝ)) with hSdef
  have hS2 : ∀ p ∈ S, 2 ≤ p := by
    intro p hp
    rw [hSdef] at hp
    exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.two_le
  have hdivlog : Real.log (Real.log Q / Real.log P)
      = Real.log (Real.log Q) - Real.log (Real.log P) :=
    Real.log_div (ne_of_gt hlogQpos) (ne_of_gt hlogPpos)
  have hrec_le : primeRecips Q - primeRecips P
      ≤ Real.log (Real.log Q / Real.log P) + 2 * Cb := by
    have hQ := (abs_le.mp (hCb Q hQ3)).2
    have hP' := (abs_le.mp (hCb P hP)).1
    rw [hdivlog]; linarith
  have hrec_ge : Real.log (Real.log Q / Real.log P) - 2 * Cb
      ≤ primeRecips Q - primeRecips P := by
    have hQ := (abs_le.mp (hCb Q hQ3)).1
    have hP' := (abs_le.mp (hCb P hP)).2
    rw [hdivlog]; linarith
  have hsum_ge : Real.log (Real.log Q / Real.log P) - 2 * Cb
      ≤ ∑ p ∈ S, 1 / (p : ℝ) := by
    refine le_trans hrec_ge ?_
    rw [hSdef]
    exact primeRecips_diff_le_primeRange_sum P Q hPQ
  have hsum_le : (∑ p ∈ S, 1 / (p : ℝ))
      ≤ Real.log (Real.log Q / Real.log P) + 2 * Cb + 1 / 3 := by
    have h := primeRange_sum_le_primeRecips_diff_add P Q hP hPQ
    rw [hSdef]
    linarith
  have hcorr : (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 4 := by
    refine sum_inv_mul_pred_le_four ⌊Q⌋₊ S ?_
    intro p hp
    rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).1
  have hratio : 0 < Real.log Q / Real.log P := div_pos hlogQpos hlogPpos
  have hexp_ratio : Real.exp (-Real.log (Real.log Q / Real.log P))
      = Real.log P / Real.log Q := by
    rw [Real.exp_neg, Real.exp_log hratio, inv_div]
  have hUp : (∏ p ∈ S, (1 - 1 / (p : ℝ)))
      ≤ Real.exp (2 * Cb) * (Real.log P / Real.log Q) := by
    have h1 := prod_one_sub_inv_le_exp_neg_sum S hS2
    have h2 : Real.exp (-(∑ p ∈ S, 1 / (p : ℝ)))
        ≤ Real.exp (2 * Cb) * (Real.log P / Real.log Q) := by
      have h3 : Real.exp (-(∑ p ∈ S, 1 / (p : ℝ)))
          ≤ Real.exp (-(Real.log (Real.log Q / Real.log P) - 2 * Cb)) :=
        Real.exp_le_exp.mpr (by linarith)
      have h4 : Real.exp (-(Real.log (Real.log Q / Real.log P) - 2 * Cb))
          = Real.exp (2 * Cb) * (Real.log P / Real.log Q) := by
        rw [show -(Real.log (Real.log Q / Real.log P) - 2 * Cb)
              = 2 * Cb + (-Real.log (Real.log Q / Real.log P)) by ring,
            Real.exp_add, hexp_ratio]
      rwa [h4] at h3
    exact le_trans h1 h2
  have hLo : Real.exp (-(2 * Cb + 13 / 3)) * (Real.log P / Real.log Q)
      ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    have h1 := prod_exp_neg_inv_pred_le S hS2
    have hsum_pred : (∑ p ∈ S, 1 / ((p : ℝ) - 1))
        = (∑ p ∈ S, 1 / (p : ℝ)) + ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
      sum_inv_pred_eq S hS2
    have h2 : Real.exp (-(2 * Cb + 13 / 3)) * (Real.log P / Real.log Q)
        ≤ Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) := by
      have hsum_le2 : (∑ p ∈ S, 1 / ((p : ℝ) - 1))
          ≤ Real.log (Real.log Q / Real.log P) + 2 * Cb + 13 / 3 := by
        rw [hsum_pred]; linarith
      have h3 : Real.exp (-(Real.log (Real.log Q / Real.log P) + 2 * Cb + 13 / 3))
          ≤ Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) :=
        Real.exp_le_exp.mpr (by linarith)
      have h4 : Real.exp (-(Real.log (Real.log Q / Real.log P) + 2 * Cb + 13 / 3))
          = Real.exp (-(2 * Cb + 13 / 3)) * (Real.log P / Real.log Q) := by
        rw [show -(Real.log (Real.log Q / Real.log P) + 2 * Cb + 13 / 3)
              = -(2 * Cb + 13 / 3) + (-Real.log (Real.log Q / Real.log P)) by ring,
            Real.exp_add, hexp_ratio]
      rwa [h4] at h3
    exact le_trans h2 h1
  exact ⟨hLo, hUp⟩


end Commons.NumberTheory.Mertens
