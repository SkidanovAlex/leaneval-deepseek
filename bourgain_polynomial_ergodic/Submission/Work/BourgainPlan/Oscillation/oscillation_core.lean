import Mathlib
import Submission.PolynomialKernel

/-!
# Elementary core of the ℓ² oscillation inequality

`Submission.BourgainPlan.OscillationStatement` is Bourgain's ℓ² oscillation inequality for the
polynomial averages `discAvg P N` along the lacunary sequence `N_i = ⌊ρ^i⌋`: for every `ε > 0`
there is `J₀` such that for every `J ≥ J₀`, every strictly increasing `k : ℕ → ℕ` and every
finitely supported `g`,

  `Σ_{j<J} ‖ sup_{k_j ≤ i < k_{j+1}} |discAvg P N_i g − discAvg P N_{k_j} g| ‖²_{ℓ²} ≤ ε J ‖g‖²`.

This file proves the *soft* half:

* `sup_block_le_sum_increments` — the oscillation over a block is at most the total variation
  inside the block (telescoping, pointwise);
* `block_oscillation_le_sum_increments` — consequently the square-summable block oscillation is
  controlled by the *ℓ¹-sum of the increment `ℓ²`-norms* over the block (Cauchy--Schwarz);
* `oscillation_of_sublinear` — a bound of the form `C J^s` with `s < 1` (in particular the
  uniform `O(1)` bound `s = 0`, or Bourgain's `J^{1/2}`) implies the `o(J)` conclusion.

The analytic content (the sublinear bound for the polynomial Weyl sums / their major-arc model)
is isolated in `SublinearOscillation` and supplied by the other modules of this area.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

/-- **Telescoping a block.**  For `a ≤ i` the difference `u i - u a` is the sum of the increments
`u (j+1) - u j` over `j ∈ [a, i)`, hence is bounded by the sum of the absolute increments over any
larger block `[a, b)`. -/
lemma abs_sub_le_sum_increments (u : ℕ → ℝ) {a b i : ℕ} (hai : a ≤ i) (hib : i ≤ b) :
    |u i - u a| ≤ ∑ j ∈ Finset.Ico a b, |u (j + 1) - u j| := by
  have htel : ∑ j ∈ Finset.Ico a i, (u (j + 1) - u j) = u i - u a :=
    Finset.sum_Ico_sub u hai
  calc |u i - u a| = |∑ j ∈ Finset.Ico a i, (u (j + 1) - u j)| := by rw [htel]
    _ ≤ ∑ j ∈ Finset.Ico a i, |u (j + 1) - u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Ico a b, |u (j + 1) - u j| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hib)
          (fun j _ _ => abs_nonneg _)

/-- **The supremum over a block is dominated by the total variation inside the block.**  This is
the pointwise (in the position `n`) inequality behind every "oscillation" bound. -/
lemma sup_block_le_sum_increments (u : ℕ → ℕ → ℝ) (k : ℕ → ℕ) (j n : ℕ) :
    Finset.sup (Finset.Ico (k j) (k (j + 1)))
        (fun i => ENNReal.ofReal |u i n - u (k j) n|)
      ≤ ∑ i ∈ Finset.Ico (k j) (k (j + 1)), ENNReal.ofReal |u (i + 1) n - u i n| := by
  refine Finset.sup_le (fun i hi => ?_)
  have hai : k j ≤ i := (Finset.mem_Ico.mp hi).1
  have hib : i ≤ k (j + 1) := le_of_lt (Finset.mem_Ico.mp hi).2
  calc ENNReal.ofReal |u i n - u (k j) n|
      ≤ ENNReal.ofReal (∑ m ∈ Finset.Ico (k j) (k (j + 1)), |u (m + 1) n - u m n|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le_sum_increments (fun m => u m n) hai hib)
    _ = ∑ m ∈ Finset.Ico (k j) (k (j + 1)), ENNReal.ofReal |u (m + 1) n - u m n| :=
        ENNReal.ofReal_sum_of_nonneg (fun m _ => abs_nonneg _)

/-- **The block oscillation is controlled by the ℓ¹-sum of the increment norms.**  If the
increments of a sequence of functions `u i : ℕ → ℝ` are bounded in `ℓ²` by `a i`, then the squared
oscillations of the blocks `[k j, k (j+1))` sum to at most the square of the total increment
budget `Σ_i a i` — *no* dependence on the block lengths. -/
lemma block_oscillation_le_sum_increments
    (u : ℕ → ℕ → ℝ) (s : Finset ℕ) (k : ℕ → ℕ) (hk : StrictMono k) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hδ : ∀ i, ∑ n ∈ s, (u (i + 1) n - u i n) ^ 2 ≤ (a i) ^ 2) (J : ℕ) :
    ∑ j ∈ Finset.range J,
        ∑ n ∈ s, (Finset.sup (Finset.Ico (k j) (k (j + 1)))
          (fun i => ENNReal.ofReal |u i n - u (k j) n|)).toReal ^ 2
      ≤ (∑ i ∈ Finset.range (k J), a i) ^ 2 := by
  classical
  have hblock : ∀ j : ℕ,
      ∑ n ∈ s, (Finset.sup (Finset.Ico (k j) (k (j + 1)))
          (fun i => ENNReal.ofReal |u i n - u (k j) n|)).toReal ^ 2
        ≤ (∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i) ^ 2 := by
    intro j
    -- pointwise control of the supremum
    have hpt : ∀ n : ℕ,
        (Finset.sup (Finset.Ico (k j) (k (j + 1)))
          (fun i => ENNReal.ofReal |u i n - u (k j) n|)).toReal
          ≤ ∑ i ∈ Finset.Ico (k j) (k (j + 1)), |u (i + 1) n - u i n| := by
      intro n
      have h := sup_block_le_sum_increments u k j n
      have hfin : (∑ i ∈ Finset.Ico (k j) (k (j + 1)),
          ENNReal.ofReal |u (i + 1) n - u i n|) ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.ofReal_ne_top)
      calc (Finset.sup (Finset.Ico (k j) (k (j + 1)))
              (fun i => ENNReal.ofReal |u i n - u (k j) n|)).toReal
          ≤ (∑ i ∈ Finset.Ico (k j) (k (j + 1)),
              ENNReal.ofReal |u (i + 1) n - u i n|).toReal := ENNReal.toReal_mono hfin h
        _ = ∑ i ∈ Finset.Ico (k j) (k (j + 1)), |u (i + 1) n - u i n| := by
            rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
            exact Finset.sum_congr rfl (fun i _ => ENNReal.toReal_ofReal (abs_nonneg _))
    -- expand the square into a double sum over the block and apply Cauchy--Schwarz
    have hexp : ∑ n ∈ s, (∑ i ∈ Finset.Ico (k j) (k (j + 1)), |u (i + 1) n - u i n|) ^ 2
        = ∑ p ∈ Finset.Ico (k j) (k (j + 1)) ×ˢ Finset.Ico (k j) (k (j + 1)),
            ∑ n ∈ s, |u (p.1 + 1) n - u p.1 n| * |u (p.2 + 1) n - u p.2 n| := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [sq, Finset.sum_mul_sum, Finset.sum_product]
    have hcs : ∑ p ∈ Finset.Ico (k j) (k (j + 1)) ×ˢ Finset.Ico (k j) (k (j + 1)),
          ∑ n ∈ s, |u (p.1 + 1) n - u p.1 n| * |u (p.2 + 1) n - u p.2 n|
        ≤ ∑ p ∈ Finset.Ico (k j) (k (j + 1)) ×ˢ Finset.Ico (k j) (k (j + 1)),
            a p.1 * a p.2 := by
      refine Finset.sum_le_sum (fun p _ => ?_)
      have hnn : 0 ≤ ∑ n ∈ s,
          |u (p.1 + 1) n - u p.1 n| * |u (p.2 + 1) n - u p.2 n| :=
        Finset.sum_nonneg (fun n _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hsq : (∑ n ∈ s,
            |u (p.1 + 1) n - u p.1 n| * |u (p.2 + 1) n - u p.2 n|) ^ 2
          ≤ (a p.1 * a p.2) ^ 2 := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq s
          (fun n => |u (p.1 + 1) n - u p.1 n|)
          (fun n => |u (p.2 + 1) n - u p.2 n|)
        have h1 : ∑ n ∈ s, |u (p.1 + 1) n - u p.1 n| ^ 2 ≤ (a p.1) ^ 2 := by
          simpa only [sq_abs] using hδ p.1
        have h2 : ∑ n ∈ s, |u (p.2 + 1) n - u p.2 n| ^ 2 ≤ (a p.2) ^ 2 := by
          simpa only [sq_abs] using hδ p.2
        calc (∑ n ∈ s, |u (p.1 + 1) n - u p.1 n| * |u (p.2 + 1) n - u p.2 n|) ^ 2
            ≤ (∑ n ∈ s, |u (p.1 + 1) n - u p.1 n| ^ 2)
                * (∑ n ∈ s, |u (p.2 + 1) n - u p.2 n| ^ 2) := h
          _ ≤ (a p.1) ^ 2 * (a p.2) ^ 2 :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (a p.1 * a p.2) ^ 2 := by ring
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hnn, Real.sqrt_sq (mul_nonneg (ha p.1) (ha p.2))] at this
    have hprod : (∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i) ^ 2
        = ∑ p ∈ Finset.Ico (k j) (k (j + 1)) ×ˢ Finset.Ico (k j) (k (j + 1)),
            a p.1 * a p.2 := by
      rw [sq, Finset.sum_mul_sum, Finset.sum_product]
    calc ∑ n ∈ s, (Finset.sup (Finset.Ico (k j) (k (j + 1)))
            (fun i => ENNReal.ofReal |u i n - u (k j) n|)).toReal ^ 2
        ≤ ∑ n ∈ s, (∑ i ∈ Finset.Ico (k j) (k (j + 1)), |u (i + 1) n - u i n|) ^ 2 :=
          Finset.sum_le_sum
            (fun n _ => pow_le_pow_left₀ ENNReal.toReal_nonneg (hpt n) 2)
      _ = ∑ p ∈ Finset.Ico (k j) (k (j + 1)) ×ˢ Finset.Ico (k j) (k (j + 1)),
            ∑ n ∈ s, |u (p.1 + 1) n - u p.1 n| * |u (p.2 + 1) n - u p.2 n| := hexp
      _ ≤ ∑ p ∈ Finset.Ico (k j) (k (j + 1)) ×ˢ Finset.Ico (k j) (k (j + 1)),
            a p.1 * a p.2 := hcs
      _ = (∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i) ^ 2 := hprod.symm
  -- sum the per-block bounds
  have hstep : ∑ j ∈ Finset.range J,
      ∑ n ∈ s, (Finset.sup (Finset.Ico (k j) (k (j + 1)))
          (fun i => ENNReal.ofReal |u i n - u (k j) n|)).toReal ^ 2
      ≤ ∑ j ∈ Finset.range J, (∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i) ^ 2 :=
    Finset.sum_le_sum (fun j _ => hblock j)
  have hsq : ∑ j ∈ Finset.range J, (∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i) ^ 2
      ≤ (∑ j ∈ Finset.range J, ∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => ha i))
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range J) : Set ℕ)
      (fun j => Finset.Ico (k j) (k (j + 1))) := by
    intro j _ j' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_Ico] at hi hi'
    rcases lt_or_gt_of_ne hne with h | h
    · have hmono : k (j + 1) ≤ k j' := hk.monotone (by omega)
      omega
    · have hmono : k (j' + 1) ≤ k j := hk.monotone (by omega)
      omega
  have hbU : ∑ j ∈ Finset.range J, ∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i
      ≤ ∑ i ∈ Finset.range (k J), a i := by
    rw [← Finset.sum_biUnion hdisj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ha i)
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨j, hj, hij⟩ := hi
    rw [Finset.mem_range] at hj ⊢
    exact lt_of_lt_of_le (Finset.mem_Ico.mp hij).2
      (hk.monotone (Nat.succ_le_iff.mpr hj))
  have hfinal : (∑ j ∈ Finset.range J, ∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i) ^ 2
      ≤ (∑ i ∈ Finset.range (k J), a i) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => ha i)))
      hbU 2
  exact le_trans hstep (le_trans hsq hfinal)

end Work.BourgainPlan.Oscillation
