import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs
import Submission.Work.LadderP.lemma51P_succ_of_p3Heart

/-!
# (ADP) The `c = 1` heart at level `t ≥ 1` implies the frozen level-`(t+1)` statement

`Work.Peluse.LadderP.p3Heart t` is the level-`(t+1)` statement of `lemma51P` with the polynomial
coefficient `c = 1` and an arbitrary normalisation window `S` (of the same order as `symIcc N`).

The module `Submission/Work/LadderP/lemma51P_succ_of_p3Heart.lean` proves the frozen induction step
`lemma51P (t+1)` from `p3Heart t` for `t ≥ 2`, together with the level-`t` hypothesis `lemma51P t`
— but that hypothesis is never used in its body: the assembly (class splitting of `symIcc N` mod
`c`, power mean over the classes, the heart applied to each class, and the reassembly of the
uniformity norm by `p2UNormSplit`) is *level generic*: at level `t + 1` it only ever uses `1 ≤ t+1`
for the power-mean ingredient `p3AvgLe`, never `2 ≤ t`.  Indeed `lemma51P 2` (the `t = 1` case)
needs exactly the same class machinery as every other level.

This module records the resulting **adapter**: `p3Heart t ⟹ lemma51P (t+1)` for every `t ≥ 1`.
The proof body is the one of `Work.LadderP.lemma51P_succ_of_p3Heart` with its unused `lemma51P t`
hypothesis dropped and the heart's level fixed at `t` (so no `∀ t ≥ 2` family of hearts is needed).
-/

set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section

private lemma p3BoxAvg_nonneg_aux {s M₁ M₂ : ℕ} (b : Fin s → ℤ) (S : Finset ℤ) (g : ℤ → ℂ) :
    0 ≤ Work.Peluse.LadderP.p3BoxAvg s M₁ M₂ b S g := by
  rw [Work.Peluse.LadderP.p3BoxAvg]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) _))

/-- **(ADP) Adapter.**  The `c = 1` heart `p3Heart t` at level `t` implies the frozen level-`(t+1)`
statement `lemma51P (t+1)`, for every `t ≥ 1` — the paper's "split `ℤ` into arithmetic progressions
mod `c`" step.  It is a copy of the proved `Work.LadderP.lemma51P_succ_of_p3Heart` whose body never
uses its `lemma51P t` hypothesis, restated for `t ≥ 1` (the class machinery is identical at `t = 1`). -/
theorem lemma51P_succ_of_heart : ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.p3Heart t →
    Work.Peluse.LadderP.lemma51P (t + 1) := by
  classical
  intro t _ H B₀
  obtain ⟨s', hs'1, e, he1, C_h, hCh0, hCh1, hHeart⟩ := H B₀
  refine ⟨s', hs'1, 2 ^ (t + 1) * e, ?_, C_h * (1 / 2 : ℝ) ^ e,
    mul_pos hCh0 (by positivity), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt (Nat.mul_pos (pow_pos (by norm_num) (t + 1)) (by omega)))
  · exact mul_le_one₀ hCh1 (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  intro c M₁ M₂ N D b γ η ε f hc hM2 hM2M1 hN hNM hD hb hsup hbd hγ0 hγ1 hη0 hη hε0 hε hDs hDn
    hbad hbox
  have hM₁ : 1 ≤ M₁ := by omega
  have hM₂1 : 1 ≤ M₂ := by omega
  have hfs : Work.Peluse.FinSuppZ f := Work.Peluse.FinSuppZ.of_supportIn hsup
  -- (0) the fit `c ≤ 2N+1`
  have hcN : c ≤ 2 * (N : ℤ) + 1 := by
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    have hM₁R : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast le_trans hM2 hM2M1
    have hM₂R : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM2
    have h4 : (4 : ℝ) ≤ (N : ℝ) / (c : ℝ) := by nlinarith [hNM, hM₁R, hM₂R]
    have h4c : (4 : ℝ) * (c : ℝ) ≤ (N : ℝ) := (le_div_iff₀ hcpos).mp h4
    have hcN' : (c : ℝ) ≤ (N : ℝ) := by nlinarith [h4c, hcpos.le]
    have hcN'' : c ≤ (N : ℤ) := by exact_mod_cast hcN'
    linarith
  -- (1) the per-class box norms are at most `1`
  have hu1 : ∀ a ∈ Finset.Icc 1 M₁, ∀ r ∈ Finset.range c.natAbs,
      Work.Peluse.boxNorm (t + 1) (fun i : Fin (t + 1) => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂)
        (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f) ≤ 1 := by
    intro a _ r hr
    have hr' : r < c.natAbs := Finset.mem_range.mp hr
    have hbdd : ∀ x : ℤ, ‖Work.Peluse.LadderP.p2ClsFn c r f x‖ ≤ 1 := fun x => hbd _
    have hsupp : ∀ x : ℤ, x ∉ Work.Peluse.LadderP.p2Sup c N r →
        Work.Peluse.LadderP.p2ClsFn c r f x = 0 :=
      Work.Peluse.LadderP.p2Sup_support hc hr' hsup
    have hcard : (Work.Peluse.LadderP.p2Sup c N r).card ≤
        (Work.Peluse.LadderP.p2Cls c N r).card :=
      (Work.Peluse.LadderP.p2Sup_card hc).le
    have hpow : Work.Peluse.boxNormPow (t + 1)
        (fun i : Fin (t + 1) => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂)
        (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f) ≤ 1 :=
      Work.Peluse.BoxNorm.boxNormPow_le_one_of_card_le hbdd hsupp hcard
    rw [Work.Peluse.boxNorm]
    exact Real.rpow_le_one (norm_nonneg _) hpow (by positivity)
  -- (2) the weighted power mean of the class averages
  have hγ4 : γ ^ (2 ^ (t + 1)) ≤ ∑ r ∈ Finset.range c.natAbs, Work.Peluse.LadderP.p2Wt c N r *
      Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N r)
        (Work.Peluse.LadderP.p2ClsFn c r f) :=
    Work.LadderP.p3AvgLe (n := t + 1) (by omega) hc hM₁ hM₂1 b γ hcN hfs hγ0.le hγ1 hu1 hbox
  -- (3) the class averages are at most `1`
  have hUle : ∀ r ∈ Finset.range c.natAbs,
      Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N r)
        (Work.Peluse.LadderP.p2ClsFn c r f) ≤ 1 := by
    intro r hr
    have hM₁R : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast hM₁
    have hsum : ∑ a ∈ Finset.Icc 1 M₁,
        Work.Peluse.boxNorm (t + 1)
          (fun i : Fin (t + 1) => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂)
          (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f) ≤ (M₁ : ℝ) := by
      calc ∑ a ∈ Finset.Icc 1 M₁,
            Work.Peluse.boxNorm (t + 1)
              (fun i : Fin (t + 1) => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂)
              (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f)
          ≤ ∑ _a ∈ Finset.Icc 1 M₁, (1 : ℝ) := Finset.sum_le_sum (fun a ha => hu1 a ha r hr)
        _ = (((Finset.Icc 1 M₁).card : ℕ) : ℝ) := by simp
        _ = (M₁ : ℝ) := by rw [Nat.card_Icc]; push_cast; ring
    rw [Work.Peluse.LadderP.p3BoxAvg]
    calc ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
          Work.Peluse.boxNorm (t + 1)
            (fun i : Fin (t + 1) => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂)
            (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f)
        ≤ ((M₁ : ℝ))⁻¹ * (M₁ : ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt hM₁R)]
  -- (4) the heart at each class with `γ_r ≥ γ^{2^{t+1}} / 2`
  have hheart : ∀ r ∈ Finset.range c.natAbs,
      γ ^ (2 ^ (t + 1)) / 2 ≤ Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
          (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f) →
      C_h * (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N r)
          (Work.Peluse.LadderP.p2ClsFn c r f)) ^ e
        ≤ Work.Peluse.uNorm s' (Work.Peluse.arithIcc 1 D) (Work.Peluse.LadderP.p2Cls c N r)
            (Work.Peluse.LadderP.p2ClsFn c r f) := by
    intro r hr hgr
    obtain ⟨_, _, _⟩ := Work.Peluse.LadderP.p2ClassFit hc hN hNM hr
    obtain ⟨hNdat, hNdat2, hNdat1⟩ :=
      Work.Peluse.LadderP.p2ClassData hc hN hNM (by nlinarith [hM2, hM2M1]) hsup hr
    obtain ⟨hg0, hgη, hgD, hgN⟩ := Work.LadderP.pTransfer (P := 2 ^ (t + 1)) Nat.one_le_two_pow hM₁ hM₂1 hD hγ0
      hγ1 hη0 (mul_pos hCh0 (pow_pos (by norm_num) e)) hCh0 hCh1 he1 le_rfl hη hDs hDn hgr
      (hUle r hr)
    have hε' : ε ≤ C_h * (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
        (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f)) ^ e := by
      have hstep : (1 / 2 : ℝ) ^ e * γ ^ (2 ^ (t + 1) * e) =
          (γ ^ (2 ^ (t + 1)) / 2) ^ e := by
        rw [div_pow, one_pow, div_pow, pow_mul]
        ring
      have hge : (γ ^ (2 ^ (t + 1)) / 2) ^ e ≤ (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
          (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f)) ^ e :=
        pow_le_pow_left₀ (by positivity) hgr e
      calc ε ≤ C_h * (1 / 2 : ℝ) ^ e * γ ^ (2 ^ (t + 1) * e) := hε
        _ = C_h * ((1 / 2 : ℝ) ^ e * γ ^ (2 ^ (t + 1) * e)) := by ring
        _ ≤ C_h * (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N r)
              (Work.Peluse.LadderP.p2ClsFn c r f)) ^ e := by
            rw [hstep]
            exact mul_le_mul_of_nonneg_left hge hCh0.le
    have hMN : ((M₁ : ℝ) * (M₂ : ℝ) ≤ ((N / c.natAbs + 2 : ℕ) : ℝ)) := by
      have h1 : ((M₁ * M₂ : ℕ) : ℝ) ≤ (N : ℝ) / (c : ℝ) := by
        rw [Nat.cast_mul]; exact hNM
      have hcn : ((c.natAbs : ℕ) : ℝ) = (c : ℝ) := by
        have h0 : ((c.natAbs : ℕ) : ℤ) = c := Int.natAbs_of_nonneg hc.le
        calc ((c.natAbs : ℕ) : ℝ) = (((c.natAbs : ℕ) : ℤ) : ℝ) := by simp
          _ = (c : ℝ) := by rw [h0]
      have h3 : ((M₁ * M₂ : ℕ) : ℝ) ≤ (N : ℝ) / (c.natAbs : ℝ) := by rw [hcn]; exact h1
      have hcnpos : (0 : ℝ) < (c.natAbs : ℝ) := by
        have : (0 : ℕ) < c.natAbs := by rw [Int.natAbs_pos]; omega
        exact_mod_cast this
      have hmul : ((M₁ * M₂ : ℕ) : ℝ) * (c.natAbs : ℝ) ≤ (N : ℝ) := by
        rw [le_div_iff₀ hcnpos] at h3
        linarith [h3]
      have h2 : M₁ * M₂ ≤ N / c.natAbs := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < c.natAbs)]
        exact_mod_cast hmul
      have h4 : N / c.natAbs ≤ N / c.natAbs + 2 := by omega
      exact_mod_cast (le_trans h2 h4)
    have hbad' : (((Finset.Icc 1 M₁).filter
          (fun a : ℕ => ¬ Work.Peluse.LadderP.p3good (t + 1) M₁ b η a)).card : ℝ)
        ≤ ε * (M₁ : ℝ) := by
      have hiff : ∀ a ∈ Finset.Icc 1 M₁,
          (¬ Work.Peluse.LadderP.p3good (t + 1) M₁ b η a) ↔
          (¬ ((∀ i k : Fin (t + 1), i ≠ k →
                ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b k) : ℕ) : ℝ) ≤ 1 / η)
              ∧ ∀ i : Fin (t + 1), η * (M₁ : ℝ) ≤ ((|((a : ℤ) + b i)| : ℤ) : ℝ))) := by
        intro a _
        rw [Work.Peluse.LadderP.p3good]
      rw [Finset.filter_congr hiff]
      exact hbad
    exact hHeart M₁ M₂ D (N / c.natAbs + 2) (Work.Peluse.LadderP.p2Cls c N r) b
      (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N r)
        (Work.Peluse.LadderP.p2ClsFn c r f)) η ε (Work.Peluse.LadderP.p2ClsFn c r f)
      hM2 hM2M1 hD hNdat1 hNdat hNdat2 hMN hb
      (fun x => hbd _) hg0 (hUle r hr) hη0 hgη hε0 hε' hgD hgN hbad' (le_refl _)
  -- (5) the class splitting of the uniformity norm
  have hUnorm : Work.Peluse.uNormPow s' (Work.Peluse.arithIcc c D) (Work.Peluse.symIcc N) f
      = ∑ i : Fin c.natAbs, Work.Peluse.LadderP.p2Wt c N i.val *
          Work.Peluse.uNormPow s' (Work.Peluse.arithIcc 1 D) (Work.Peluse.LadderP.p2Cls c N i.val)
            (Work.Peluse.LadderP.p2ClsFn c i.val f) := by
    rw [Work.Peluse.LadderP.p2UNormSplit hc hs'1 hD hcN hfs]
    exact Finset.sum_range (fun r => Work.Peluse.LadderP.p2Wt c N r *
      Work.Peluse.uNormPow s' (Work.Peluse.arithIcc 1 D) (Work.Peluse.LadderP.p2Cls c N r)
        (Work.Peluse.LadderP.p2ClsFn c r f))
  -- (6) Jensen over the classes
  have hΘ1 : 1 ≤ e * 2 ^ s' := Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (Nat.mul_pos (by omega) (pow_pos (by norm_num) s')))
  have hws : ∑ i : Fin c.natAbs, Work.Peluse.LadderP.p2Wt c N i.val = 1 := by
    rw [← Finset.sum_range (fun r => Work.Peluse.LadderP.p2Wt c N r)]
    exact Work.Peluse.LadderP.p2Wt_sum hc N
  have hγ4' : γ ^ (2 ^ (t + 1)) ≤ ∑ i : Fin c.natAbs, Work.Peluse.LadderP.p2Wt c N i.val *
      Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N i.val)
        (Work.Peluse.LadderP.p2ClsFn c i.val f) := by
    simpa only [Finset.sum_range] using hγ4
  have hj := Work.Peluse.LadderP.p2jensen
    (fun i : Fin c.natAbs => Work.Peluse.LadderP.p2Wt c N i.val)
    (fun i : Fin c.natAbs => Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
      (Work.Peluse.LadderP.p2Cls c N i.val) (Work.Peluse.LadderP.p2ClsFn c i.val f))
    (γ ^ (2 ^ (t + 1))) (e * 2 ^ s') hΘ1
    (fun i => Work.Peluse.LadderP.p2Wt_nonneg c N i.val) hws
    (fun i => p3BoxAvg_nonneg_aux b _ _)
    (fun i => hUle i.val (Finset.mem_range.mpr i.isLt)) (by positivity) hγ4'
  -- (7) the weighted class sum, lower bound
  have hA : C_h ^ (2 ^ s') * (∑ i ∈ Finset.univ.filter (fun i : Fin c.natAbs =>
        γ ^ (2 ^ (t + 1)) / 2 ≤ Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
          (Work.Peluse.LadderP.p2Cls c N i.val) (Work.Peluse.LadderP.p2ClsFn c i.val f)),
        Work.Peluse.LadderP.p2Wt c N i.val *
          (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N i.val)
            (Work.Peluse.LadderP.p2ClsFn c i.val f)) ^ (e * 2 ^ s'))
      = ∑ i ∈ Finset.univ.filter (fun i : Fin c.natAbs =>
        γ ^ (2 ^ (t + 1)) / 2 ≤ Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
          (Work.Peluse.LadderP.p2Cls c N i.val) (Work.Peluse.LadderP.p2ClsFn c i.val f)),
        Work.Peluse.LadderP.p2Wt c N i.val *
          (C_h * (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
            (Work.Peluse.LadderP.p2Cls c N i.val)
            (Work.Peluse.LadderP.p2ClsFn c i.val f)) ^ e) ^ (2 ^ s') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_pow, ← pow_mul]
    ring
  have hA' : C_h ^ (2 ^ s') * (γ ^ (2 ^ (t + 1)) / 2) ^ (e * 2 ^ s')
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin c.natAbs =>
        γ ^ (2 ^ (t + 1)) / 2 ≤ Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
          (Work.Peluse.LadderP.p2Cls c N i.val) (Work.Peluse.LadderP.p2ClsFn c i.val f)),
        Work.Peluse.LadderP.p2Wt c N i.val *
          (C_h * (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
            (Work.Peluse.LadderP.p2Cls c N i.val)
            (Work.Peluse.LadderP.p2ClsFn c i.val f)) ^ e) ^ (2 ^ s') := by
    rw [← hA]
    exact mul_le_mul_of_nonneg_left hj (pow_nonneg hCh0.le _)
  -- (8) the class sum, upper bound
  have hB : (∑ i ∈ Finset.univ.filter (fun i : Fin c.natAbs =>
        γ ^ (2 ^ (t + 1)) / 2 ≤ Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
          (Work.Peluse.LadderP.p2Cls c N i.val) (Work.Peluse.LadderP.p2ClsFn c i.val f)),
        Work.Peluse.LadderP.p2Wt c N i.val *
          (C_h * (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
            (Work.Peluse.LadderP.p2Cls c N i.val)
            (Work.Peluse.LadderP.p2ClsFn c i.val f)) ^ e) ^ (2 ^ s'))
      ≤ Work.Peluse.uNormPow s' (Work.Peluse.arithIcc c D) (Work.Peluse.symIcc N) f := by
    rw [hUnorm]
    refine le_trans (Finset.sum_le_sum (fun i hi => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => mul_nonneg (Work.Peluse.LadderP.p2Wt_nonneg c N i.val) (norm_nonneg _)))
    have hhi := hheart i.val (Finset.mem_range.mpr i.isLt) (Finset.mem_filter.mp hi).2
    have hpowu : (C_h * (Work.Peluse.LadderP.p3BoxAvg (t + 1) M₁ M₂ b
          (Work.Peluse.LadderP.p2Cls c N i.val)
          (Work.Peluse.LadderP.p2ClsFn c i.val f)) ^ e) ^ (2 ^ s')
        ≤ Work.Peluse.uNormPow s' (Work.Peluse.arithIcc 1 D) (Work.Peluse.LadderP.p2Cls c N i.val)
            (Work.Peluse.LadderP.p2ClsFn c i.val f) := by
      rw [Work.Peluse.LadderP.p2uNormPow_eq_pow]
      exact pow_le_pow_left₀
        (mul_nonneg hCh0.le (pow_nonneg (p3BoxAvg_nonneg_aux b _ _) e)) hhi _
    exact mul_le_mul_of_nonneg_left hpowu (Work.Peluse.LadderP.p2Wt_nonneg c N i.val)
  -- (9) conclude
  have hfin : C_h ^ (2 ^ s') * (γ ^ (2 ^ (t + 1)) / 2) ^ (e * 2 ^ s')
      ≤ Work.Peluse.uNormPow s' (Work.Peluse.arithIcc c D) (Work.Peluse.symIcc N) f :=
    le_trans hA' hB
  have hYpow : (C_h * (γ ^ (2 ^ (t + 1)) / 2) ^ e) ^ (2 ^ s')
      = C_h ^ (2 ^ s') * (γ ^ (2 ^ (t + 1)) / 2) ^ (e * 2 ^ s') := by
    rw [mul_pow, ← pow_mul]
  rw [← hYpow] at hfin
  have hY0 : (0 : ℝ) ≤ C_h * (γ ^ (2 ^ (t + 1)) / 2) ^ e := by positivity
  have hcast : ((((2 : ℕ) ^ s' : ℕ)) : ℝ) = (2 : ℝ) ^ s' := by push_cast; ring
  rw [← Real.rpow_natCast (C_h * (γ ^ (2 ^ (t + 1)) / 2) ^ e) (2 ^ s')] at hfin
  have hlt := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (C_h * (γ ^ (2 ^ (t + 1)) / 2) ^ e) ^ (((2 : ℕ) ^ s' : ℕ) : ℝ))
    hfin (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ s')
  rw [← Real.rpow_mul hY0 _ _] at hlt
  rw [hcast, mul_one_div, div_self (by positivity), Real.rpow_one] at hlt
  have hstep : (1 / 2 : ℝ) ^ e * γ ^ (2 ^ (t + 1) * e) = (γ ^ (2 ^ (t + 1)) / 2) ^ e := by
    rw [div_pow, one_pow, div_pow, pow_mul]
    ring
  simp only [Work.Peluse.uNorm] at hlt ⊢
  refine le_trans ?_ hlt
  rw [mul_assoc, hstep]

end

end Work.Peluse.SwapA
