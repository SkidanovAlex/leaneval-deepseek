import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Lemma 3.1, linear forms part.**  If `ν` satisfies the linear forms condition with
error `ε` then so does `ν' = (ν+1)/2`.  This is the device which allows one to replace the
hypothesis `|F| ≤ ν + 1` by `|F| ≤ ν` (Green–Tao §6). -/
lemma lfc_half {p : ℕ} [Fact p.Prime] {ν : ZMod p → ℝ} {m₀ t₀ L₀ : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (h : Commons.NumberTheory.Sieve.LinFormsCond p ν m₀ t₀ L₀ ε) :
    Commons.NumberTheory.Sieve.LinFormsCond p (fun x => (ν x + 1) / 2) m₀ t₀ L₀ ε := by
  classical
  intro ι _ _ hι1 hι2 t ht1 ht2 L hLs hne hnp b
  set N : ℝ := (Fintype.card (Fin t → ZMod p) : ℝ) with hN
  set w : (Fin t → ZMod p) → ι → ℝ :=
    fun x i => ν (Commons.NumberTheory.Sieve.linForm p (L i) (b i) x) with hw
  set g : Finset ι → ℝ :=
    fun S => N⁻¹ * ∑ x : Fin t → ZMod p, ∏ i ∈ S, w x i with hg
  have hcard_fun : Fintype.card (Fin t → ZMod p) = p ^ t := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hNpos : 0 < N := by
    rw [hN, hcard_fun]
    exact_mod_cast (pow_pos (Fact.out : p.Prime).pos t)
  have hNne : N ≠ 0 := ne_of_gt hNpos
  show |N⁻¹ * (∑ x : Fin t → ZMod p, ∏ i : ι, (w x i + 1) / 2) - 1| ≤ ε
  -- (1) sub-condition: every nonempty sub-collection of the linear forms satisfies the LFC.
  have hsub : ∀ S : Finset ι, S.Nonempty → |g S - 1| ≤ ε := by
    intro S hS
    have hS1 : 1 ≤ Fintype.card {i // i ∈ S} := by
      rw [Fintype.card_coe]
      exact Finset.card_pos.mpr hS
    have hS2 : Fintype.card {i // i ∈ S} ≤ m₀ := by
      rw [Fintype.card_coe]
      exact le_trans (Finset.card_le_univ S) hι2
    have hLs' : ∀ i j, Commons.NumberTheory.Sieve.IsSmallRat L₀
        ((fun i : {i // i ∈ S} => L i.1) i j) := fun i j => hLs i.1 j
    have hne' : ∀ i, Commons.NumberTheory.Sieve.NonzeroTuple
        ((fun i : {i // i ∈ S} => L i.1) i) := fun i => hne i.1
    have hnp' : ∀ i i', i ≠ i' → Commons.NumberTheory.Sieve.NotProp
        ((fun i : {i // i ∈ S} => L i.1) i) ((fun i : {i // i ∈ S} => L i.1) i') :=
      fun i i' hii' => hnp i.1 i'.1 (fun he => hii' (Subtype.ext he))
    have hmain := h {i // i ∈ S} hS1 hS2 t ht1 ht2 (fun i : {i // i ∈ S} => L i.1)
      hLs' hne' hnp' (fun i => b i.1)
    have hsum_eq : (∑ x : Fin t → ZMod p,
          ∏ i : {i // i ∈ S}, ν (Commons.NumberTheory.Sieve.linForm p (L i.1) (b i.1) x))
        = ∑ x : Fin t → ZMod p, ∏ i ∈ S, w x i := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.prod_coe_sort S (fun i => ν (Commons.NumberTheory.Sieve.linForm p (L i) (b i) x))]
    rw [hsum_eq] at hmain
    rw [hg]
    exact hmain
  -- (2) the empty sub-collection contributes `1`.
  have hg_empty : g ∅ = 1 := by
    rw [hg]
    simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
    rw [inv_mul_cancel₀ hNne]
  have hg_bound : ∀ S ∈ (Finset.univ : Finset ι).powerset, |g S - 1| ≤ ε := by
    intro S _
    by_cases hSne : S.Nonempty
    · exact hsub S hSne
    · rw [Finset.not_nonempty_iff_eq_empty] at hSne
      rw [hSne, hg_empty]
      simpa using hε
  -- (3) expand `∏ ((ν+1)/2)` as a signed powerset average.
  have hfac : ∀ x : Fin t → ZMod p,
      (∏ i : ι, (w x i + 1) / 2)
        = ((2 : ℝ) ^ (Fintype.card ι))⁻¹ * ∏ i : ι, (w x i + 1) := by
    intro x
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, div_eq_inv_mul, mul_comm]
  have hexp : ∀ x : Fin t → ZMod p,
      (∏ i : ι, (w x i + 1))
        = ∑ S ∈ (Finset.univ : Finset ι).powerset, ∏ i ∈ S, w x i := by
    intro x
    have hswap : (∏ i : ι, (w x i + 1)) = ∏ i : ι, (1 + w x i) := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    rw [hswap, Finset.prod_one_add]
  have hmain : N⁻¹ * (∑ x : Fin t → ZMod p, ∏ i : ι, (w x i + 1) / 2)
      = ((2 : ℝ) ^ (Fintype.card ι))⁻¹ * ∑ S ∈ (Finset.univ : Finset ι).powerset, g S := by
    have e1 : ∀ x : Fin t → ZMod p,
        (∏ i : ι, (w x i + 1) / 2)
          = ((2 : ℝ) ^ (Fintype.card ι))⁻¹ *
              (∑ S ∈ (Finset.univ : Finset ι).powerset, ∏ i ∈ S, w x i) := by
      intro x; rw [hfac x, hexp x]
    have e2 : ∑ S ∈ (Finset.univ : Finset ι).powerset, g S
        = N⁻¹ * ∑ S ∈ (Finset.univ : Finset ι).powerset,
            ∑ x : Fin t → ZMod p, ∏ i ∈ S, w x i := by
      simp only [hg, Finset.mul_sum]
    rw [e2]
    simp only [e1]
    rw [← Finset.mul_sum, Finset.sum_comm]
    ring
  -- (4) numerical bound.
  have hcard2 : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card ι) := by positivity
  have hsum1 : ∑ S ∈ (Finset.univ : Finset ι).powerset, (1 : ℝ)
      = (2 : ℝ) ^ (Fintype.card ι) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, Finset.card_univ]
    push_cast
    ring
  have hstep : N⁻¹ * (∑ x : Fin t → ZMod p, ∏ i : ι, (w x i + 1) / 2) - 1
      = ((2 : ℝ) ^ (Fintype.card ι))⁻¹ *
          ∑ S ∈ (Finset.univ : Finset ι).powerset, (g S - 1) := by
    have hc : ((2 : ℝ) ^ (Fintype.card ι)) ≠ 0 := ne_of_gt hcard2
    rw [hmain, Finset.sum_sub_distrib, hsum1, mul_sub, inv_mul_cancel₀ hc]
  rw [hstep, abs_mul, abs_of_pos (inv_pos.mpr hcard2)]
  calc ((2 : ℝ) ^ (Fintype.card ι))⁻¹ *
        |∑ S ∈ (Finset.univ : Finset ι).powerset, (g S - 1)|
      ≤ ((2 : ℝ) ^ (Fintype.card ι))⁻¹ *
          ∑ S ∈ (Finset.univ : Finset ι).powerset, |g S - 1| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ ((2 : ℝ) ^ (Fintype.card ι))⁻¹ *
          ∑ S ∈ (Finset.univ : Finset ι).powerset, ε :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hg_bound) (by positivity)
    _ = ((2 : ℝ) ^ (Fintype.card ι))⁻¹ * ((2 : ℝ) ^ (Fintype.card ι) * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, Finset.card_univ]
        push_cast
        ring
    _ = ε := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard2), one_mul]

end Commons.Combinatorics.Transference
