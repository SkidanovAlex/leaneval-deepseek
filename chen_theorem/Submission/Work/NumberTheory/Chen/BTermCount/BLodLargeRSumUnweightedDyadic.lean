import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodUnweightedDefs

open Finset Filter
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The large-conductor unweighted bilinear level of distribution: the dyadic assembly

This module proves `BLodLargeRSumUnweightedDyadic`, the second step of the unweighted
bilinear level of distribution (see `notes/UNWEIGHTED_LOD_PLAN.md`, Step 2).

The large-conductor range `R₀ < r ≤ D` is covered by the dyadic conductor blocks
`2^k < r ≤ 2^{k+1}` (`k₀ = Nat.log 2 R₀ ≤ k ≤ Nat.log 2 D`); on each block the dyadic maximal
bilinear character large sieve in the *dominated* form `BLodCutLS` applies with the coefficient
bounds `sum_sq_aCut_le`, `sum_sq_bCut_le`, which are uniform in `t`; the resulting geometric
series in `k` is summed by `BLodGeomSum`.  The outcome is *exactly* the quantity
`blodLSBlockSum` of `BLodUnweightedDefs`, and since it no longer depends on `t`, the outer
`1/φ t`-weighted sum produces the factor `blodW1 D`.

The three ingredients are isolated as the private lemmas `blod_rSum_le_blockSum` (dyadic
cover), `blod_LS_block_bound` (large sieve on one conductor block, for one `t`) and
`blodLS_geom_sum_le` (the geometric summation, exhibiting `blodLSBlockSum`).
-/

/-- `(Nat.totient r : ℝ)⁻¹ ≥ 0`. -/
private lemma blod_totient_inv_nonneg (r : ℕ) : 0 ≤ (Nat.totient r : ℝ)⁻¹ :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

/-- The hyperbola-cut condition `y ≤ U·V` for the block `j`: with `U = blodU M j`
and `V = blodV x M j` the product `U·V` dominates `x + 2`. -/
private lemma blod_x2_le_blodU_mul_blodV (x M j : ℕ) (hM : 1 ≤ M) :
    x + 2 ≤ blodU M j * blodV x M j := by
  have hQ : 1 ≤ blockStart M j := by
    unfold blockStart
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmod : (x + 2) % blockStart M j < blockStart M j := Nat.mod_lt _ (by omega)
  have hdecomp : blockStart M j * ((x + 2) / blockStart M j) + (x + 2) % blockStart M j = x + 2 :=
    Nat.div_add_mod (x + 2) (blockStart M j)
  have hsplit : blockStart M j * ((x + 2) / blockStart M j + 1)
      = blockStart M j * ((x + 2) / blockStart M j) + blockStart M j := by
    rw [Nat.mul_add, Nat.mul_one]
  have hlt : x + 2 < blockStart M j * ((x + 2) / blockStart M j + 1) := by
    have h1 : blockStart M j * ((x + 2) / blockStart M j) + (x + 2) % blockStart M j
        < blockStart M j * ((x + 2) / blockStart M j + 1) := by
      rw [hsplit]; omega
    rwa [hdecomp] at h1
  have hle : x + 2 ≤ blockStart M j * ((x + 2) / blockStart M j + 1) := le_of_lt hlt
  have hgoal : blodU M j * blodV x M j
      = 2 * (blockStart M j * ((x + 2) / blockStart M j + 1)) := by
    unfold blodU blodV
    ring
  rw [hgoal]
  calc x + 2 ≤ blockStart M j * ((x + 2) / blockStart M j + 1) := hle
    _ ≤ 2 * (blockStart M j * ((x + 2) / blockStart M j + 1)) :=
        Nat.le_mul_of_pos_left _ (by norm_num)

/-- **The dyadic cover of the large-conductor range.**  For `R₀ < r ≤ D` (and `2 ≤ R₀`),
the exponent `k = Nat.log 2 (r - 1)` satisfies `k₀ ≤ k ≤ Nat.log 2 D` and
`2^k < r ≤ 2^{k+1}`. -/
private lemma blod_dyadic_cover {r R₀ D : ℕ} (hR₀ : 2 ≤ R₀) (hr : R₀ < r) (hrD : r ≤ D) :
    Nat.log 2 R₀ ≤ Nat.log 2 (r - 1) ∧ Nat.log 2 (r - 1) ≤ Nat.log 2 D ∧
      2 ^ Nat.log 2 (r - 1) < r ∧ r ≤ 2 * 2 ^ Nat.log 2 (r - 1) := by
  have hne : r - 1 ≠ 0 := by omega
  have hp1 : 2 ^ Nat.log 2 (r - 1) ≤ r - 1 := Nat.pow_log_le_self 2 hne
  have hp2 : r - 1 < 2 ^ (Nat.log 2 (r - 1)).succ :=
    Nat.lt_pow_succ_log_self (by norm_num) (r - 1)
  have hsucc : 2 ^ (Nat.log 2 (r - 1)).succ = 2 * 2 ^ Nat.log 2 (r - 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  refine ⟨?_, ?_, by omega, ?_⟩
  · exact Nat.log_mono_right (b := 2) (by omega)
  · exact Nat.log_mono_right (b := 2) (by omega)
  · rw [hsucc] at hp2
    omega

/-- Cast bookkeeping: `↑(2^k) = (2:ℝ)^k`. -/
private lemma blod_cast_two_pow (k : ℕ) : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by
  push_cast
  ring

/-- Cast bookkeeping: `(↑(2·2^k))² = 4·(2:ℝ)^{2k}`, matching `BLodGeomSum`. -/
private lemma blod_cast_two_pow_sq (k : ℕ) :
    (((2 * 2 ^ k : ℕ)) : ℝ) ^ 2 = 4 * (2 : ℝ) ^ (2 * k) := by
  have h : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by
    rw [show 2 * k = k * 2 by ring, pow_mul]
  push_cast
  rw [h]
  ring

/-- Factoring a constant out of a four-fold product under a sum. -/
private lemma blod_sum_factor (s : Finset ℕ) (c lg : ℝ) (p q r : ℕ → ℝ) :
    (∑ k ∈ s, c * p k * q k * r k * lg) = c * (∑ k ∈ s, p k * q k * r k) * lg := by
  rw [← Finset.sum_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- **The geometric summation in `k`**, in the shape in which the dyadic assembly produces it:
for each block `j` the `k`-sum of the large-sieve block bounds is at most the corresponding
term of `blodLSBlockSum`. -/
private lemma blod_geom_block_le (U V B₂ lg c : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hB : 0 ≤ B₂)
    (hlg : 0 ≤ lg) (hc : 0 ≤ c) (k₀ K : ℕ) :
    (∑ k ∈ Finset.Ico k₀ K, c * ((2 : ℝ) ^ k)⁻¹
        * Real.sqrt ((U + 4 * (2 : ℝ) ^ (2 * k)) * U)
        * Real.sqrt ((V + 4 * (2 : ℝ) ^ (2 * k)) * B₂) * lg)
      ≤ c * (Real.sqrt (U * B₂) * (2 * Real.sqrt (U * V) / (2 : ℝ) ^ k₀
          + 2 * Real.sqrt U * K + 2 * Real.sqrt V * K + 4 * (2 : ℝ) ^ K) * lg) := by
  have hgeom := BLodGeomSum U V B₂ K k₀ hU hV hB
  have h1 : (∑ k ∈ Finset.Ico k₀ K, c * ((2 : ℝ) ^ k)⁻¹
        * Real.sqrt ((U + 4 * (2 : ℝ) ^ (2 * k)) * U)
        * Real.sqrt ((V + 4 * (2 : ℝ) ^ (2 * k)) * B₂) * lg)
      = c * (∑ k ∈ Finset.Ico k₀ K, ((2 : ℝ) ^ k)⁻¹
          * Real.sqrt ((U + 4 * (2 : ℝ) ^ (2 * k)) * U)
          * Real.sqrt ((V + 4 * (2 : ℝ) ^ (2 * k)) * B₂)) * lg :=
    blod_sum_factor _ _ _ _ _ _
  rw [h1]
  calc c * (∑ k ∈ Finset.Ico k₀ K, ((2 : ℝ) ^ k)⁻¹
          * Real.sqrt ((U + 4 * (2 : ℝ) ^ (2 * k)) * U)
          * Real.sqrt ((V + 4 * (2 : ℝ) ^ (2 * k)) * B₂)) * lg
      ≤ c * (Real.sqrt (U * B₂) * (2 * Real.sqrt (U * V) / (2 : ℝ) ^ k₀
          + 2 * Real.sqrt U * K + 2 * Real.sqrt V * K + 4 * (2 : ℝ) ^ K)) * lg := by
        refine mul_le_mul_of_nonneg_right ?_ hlg
        exact mul_le_mul_of_nonneg_left hgeom hc
    _ = c * (Real.sqrt (U * B₂) * (2 * Real.sqrt (U * V) / (2 : ℝ) ^ k₀
          + 2 * Real.sqrt U * K + 2 * Real.sqrt V * K + 4 * (2 : ℝ) ^ K) * lg) := by
        rw [mul_assoc]

/-- **The dyadic cover of the conductor range `(R₀, D]`.**  The `r`-sum over the
large-conductor range is dominated by the sum of the conductor blocks
`2^k < r ≤ 2^{k+1}`, `k₀ = Nat.log 2 R₀ ≤ k ≤ Nat.log 2 D`. -/
private lemma blod_rSum_le_blockSum (x M Y D R₀ t : ℕ) (hR₀ : 2 ≤ R₀) :
    (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r),
        (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
      ≤ ∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
          ∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k),
            (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r := by
  have hnn : ∀ r : ℕ, 0 ≤ (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r :=
    fun r => mul_nonneg (blod_totient_inv_nonneg r) (bProdCharSumDivSum_nonneg x M Y t r)
  have hpt : ∀ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r),
      (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r
        ≤ ∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
            (if 2 ^ k < r ∧ r ≤ 2 * 2 ^ k
              then (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r else 0) := by
    intro r hr
    obtain ⟨hrmem, h2r, hRr⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1, hrD⟩ := Finset.mem_Icc.mp hrmem
    obtain ⟨hlog1, hlog2, hlow, hup⟩ := blod_dyadic_cover hR₀ hRr hrD
    have hkmem : Nat.log 2 (r - 1) ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1) := by
      rw [Finset.mem_Ico]
      exact ⟨hlog1, Nat.lt_succ_of_le hlog2⟩
    have hnn' : ∀ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
        0 ≤ (if 2 ^ k < r ∧ r ≤ 2 * 2 ^ k
              then (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r else 0) := by
      intro k _
      split_ifs with h
      · exact hnn r
      · exact le_refl 0
    have hsingle := Finset.single_le_sum hnn' hkmem
    rwa [if_pos ⟨hlow, hup⟩] at hsingle
  calc (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r),
          (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
      ≤ ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r),
          ∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
            (if 2 ^ k < r ∧ r ≤ 2 * 2 ^ k
              then (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
          ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r),
            (if 2 ^ k < r ∧ r ≤ 2 * 2 ^ k
              then (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r else 0) :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
          ∑ r ∈ ((Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r)).filter
              (fun r => 2 ^ k < r ∧ r ≤ 2 * 2 ^ k),
            (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact (Finset.sum_filter (s := (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r))
          (p := fun r => 2 ^ k < r ∧ r ≤ 2 * 2 ^ k)
          (f := fun r => (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)).symm
    _ ≤ ∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
          ∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k),
            (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro r hr
          obtain ⟨_, hP⟩ := Finset.mem_filter.mp hr
          rw [Finset.mem_Icc]
          exact ⟨Nat.lt_iff_add_one_le.mp hP.1, hP.2⟩
        · intro r _ _
          exact hnn r

/-- **The large sieve on one conductor block, for one `t`.**  Applying the dominated dyadic
maximal bilinear character large sieve `BLodCutLS` to the cut coefficient sequences of the
block `j` (`sum_sq_aCut_le`, `sum_sq_bCut_le`) bounds the conductor-block sum by the
`j`-summand of `blodLSBlockSum`, uniformly in `t`. -/
private lemma blod_LS_block_bound (c : ℝ)
    (hc : ∀ (U V y R : ℕ), 1 ≤ U → 1 ≤ V → 1 ≤ R → 1 ≤ y → y ≤ U * V →
      ∀ (a b : ℕ → ℂ) (A₂ B₂ : ℝ),
        (∑ u ∈ Finset.Icc 1 U, ‖a u‖ ^ 2 ≤ A₂) →
        (∑ v ∈ Finset.Icc 1 V, ‖b v‖ ^ 2 ≤ B₂) →
        (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ *
            ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
              ‖bilinForm U V y a b r ψ‖)
          ≤ c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂) *
              Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂) *
              Real.log (2 * (U : ℝ) * (V : ℝ) + 2))
    (x M Y t k : ℕ) (hM : 1 ≤ M) (ht : t ≠ 0) :
    (∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k),
        (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
      ≤ ∑ j ∈ Finset.range (blockCount M Y),
          c * ((2 : ℝ) ^ k)⁻¹
            * Real.sqrt (((blodU M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k)) * (blodU M j : ℝ))
            * Real.sqrt (((blodV x M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k))
                * (bPairCount Y (blodV x M j) : ℝ))
            * Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2) := by
  have hstep : (∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k),
        (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
      ≤ ∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k), (Nat.totient r : ℝ)⁻¹ *
          ∑ j ∈ Finset.range (blockCount M Y),
            ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
              ‖bilinForm (blodU M j) (blodV x M j) (x + 2)
                (aCut M Y j (tSmall Y t)) (bCut Y (tLarge Y t)) r ψ‖ := by
    refine Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left ?_ (blod_totient_inv_nonneg r))
    simpa only [blodU, blodV] using bProdCharSumDivSum_le_block x M Y t r ht hM
  calc (∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k),
        (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
      ≤ ∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k), (Nat.totient r : ℝ)⁻¹ *
          ∑ j ∈ Finset.range (blockCount M Y),
            ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
              ‖bilinForm (blodU M j) (blodV x M j) (x + 2)
                (aCut M Y j (tSmall Y t)) (bCut Y (tLarge Y t)) r ψ‖ := hstep
    _ = ∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k), ∑ j ∈ Finset.range (blockCount M Y),
          (Nat.totient r : ℝ)⁻¹ *
            ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
              ‖bilinForm (blodU M j) (blodV x M j) (x + 2)
                (aCut M Y j (tSmall Y t)) (bCut Y (tLarge Y t)) r ψ‖ := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range (blockCount M Y), ∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k),
          (Nat.totient r : ℝ)⁻¹ *
            ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
              ‖bilinForm (blodU M j) (blodV x M j) (x + 2)
                (aCut M Y j (tSmall Y t)) (bCut Y (tLarge Y t)) r ψ‖ := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (blockCount M Y),
          c * ((2 : ℝ) ^ k)⁻¹
            * Real.sqrt (((blodU M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k)) * (blodU M j : ℝ))
            * Real.sqrt (((blodV x M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k))
                * (bPairCount Y (blodV x M j) : ℝ))
            * Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hU : 1 ≤ blodU M j := by
          unfold blodU blockStart
          have : 0 < M * 2 ^ j := Nat.mul_pos (by omega) (pow_pos (by norm_num) j)
          omega
        have hV : 1 ≤ blodV x M j := by
          unfold blodV
          exact Nat.le_add_left 1 _
        have hR : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have hy1 : 1 ≤ x + 2 := by omega
        have hy : x + 2 ≤ blodU M j * blodV x M j := blod_x2_le_blodU_mul_blodV x M j hM
        have hLS := hc (blodU M j) (blodV x M j) (x + 2) (2 ^ k) hU hV hR hy1 hy
          (aCut M Y j (tSmall Y t)) (bCut Y (tLarge Y t))
          ((blodU M j : ℝ)) ((bPairCount Y (blodV x M j) : ℝ))
          (sum_sq_aCut_le M Y j (tSmall Y t) (blodU M j))
          (sum_sq_bCut_le Y (tLarge Y t) (blodV x M j))
        rw [blod_cast_two_pow, blod_cast_two_pow_sq] at hLS
        exact hLS

/-- **The geometric summation producing `blodLSBlockSum`.**  Summing the large-sieve block
bounds over the dyadic exponents `k₀ ≤ k ≤ Nat.log 2 D` and applying `BLodGeomSum` blockwise
gives exactly `c` times `blodLSBlockSum`. -/
private lemma blodLS_geom_sum_le (x M Y D R₀ : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
        ∑ j ∈ Finset.range (blockCount M Y),
          c * ((2 : ℝ) ^ k)⁻¹
            * Real.sqrt (((blodU M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k)) * (blodU M j : ℝ))
            * Real.sqrt (((blodV x M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k))
                * (bPairCount Y (blodV x M j) : ℝ))
            * Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2))
      ≤ c * blodLSBlockSum x M Y D R₀ := by
  have hswap : (∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
        ∑ j ∈ Finset.range (blockCount M Y),
          c * ((2 : ℝ) ^ k)⁻¹
            * Real.sqrt (((blodU M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k)) * (blodU M j : ℝ))
            * Real.sqrt (((blodV x M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k))
                * (bPairCount Y (blodV x M j) : ℝ))
            * Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2))
      = ∑ j ∈ Finset.range (blockCount M Y),
          ∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
            c * ((2 : ℝ) ^ k)⁻¹
              * Real.sqrt (((blodU M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k)) * (blodU M j : ℝ))
              * Real.sqrt (((blodV x M j : ℝ) + 4 * (2 : ℝ) ^ (2 * k))
                  * (bPairCount Y (blodV x M j) : ℝ))
              * Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2) :=
    Finset.sum_comm
  rw [hswap, blodLSBlockSum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hU : (0 : ℝ) ≤ (blodU M j : ℝ) := Nat.cast_nonneg _
  have hV : (0 : ℝ) ≤ (blodV x M j : ℝ) := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ (bPairCount Y (blodV x M j) : ℝ) := Nat.cast_nonneg _
  have hlg : (0 : ℝ) ≤ Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2) := by
    refine Real.log_nonneg ?_
    nlinarith [hU, hV]
  exact blod_geom_block_le (blodU M j : ℝ) (blodV x M j : ℝ)
    (bPairCount Y (blodV x M j) : ℝ)
    (Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2)) c hU hV hB hlg hc
    (Nat.log 2 R₀) (Nat.log 2 D + 1)

/-- **Lemma.** The large-conductor part of the unweighted bilinear level of distribution is
bounded by the `1/φ`-weighted modulus sum times the large-sieve block sum. -/
theorem BLodLargeRSumUnweightedDyadic :
    ∃ c : ℝ, 0 < c ∧ ∀ (x M Y D R₀ : ℕ), 1 ≤ M → 2 ≤ D → 2 ≤ R₀ →
      Work.NumberTheory.Chen.BTermCount.blodLargeUnw x M Y D R₀ ≤
        c * Work.NumberTheory.Chen.BTermCount.blodW1 D *
          Work.NumberTheory.Chen.BTermCount.blodLSBlockSum x M Y D R₀ := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := BLodCutLS
  refine ⟨c₀, hc₀pos, ?_⟩
  intro x M Y D R₀ hM hD hR₀
  rw [blodLargeUnw]
  calc (∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ *
        ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r),
          (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
      ≤ ∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ *
          (∑ k ∈ Finset.Ico (Nat.log 2 R₀) (Nat.log 2 D + 1),
            ∑ r ∈ Finset.Icc (2 ^ k + 1) (2 * 2 ^ k),
              (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r) := by
        refine Finset.sum_le_sum (fun t _ =>
          mul_le_mul_of_nonneg_left (blod_rSum_le_blockSum x M Y D R₀ t hR₀)
            (blod_totient_inv_nonneg t))
    _ ≤ ∑ t ∈ Finset.Icc 1 D, (Nat.totient t : ℝ)⁻¹ * (c₀ * blodLSBlockSum x M Y D R₀) := by
        refine Finset.sum_le_sum (fun t ht =>
          mul_le_mul_of_nonneg_left ?_ (blod_totient_inv_nonneg t))
        have htne : t ≠ 0 := by
          have h1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
          omega
        exact le_trans
          (Finset.sum_le_sum (fun k _ => blod_LS_block_bound c₀ hc₀ x M Y t k hM htne))
          (blodLS_geom_sum_le x M Y D R₀ c₀ hc₀pos.le)
    _ = c₀ * blodW1 D * blodLSBlockSum x M Y D R₀ := by
        rw [blodW1, ← Finset.sum_mul]
        ring

end Work.NumberTheory.Chen.BTermCount
