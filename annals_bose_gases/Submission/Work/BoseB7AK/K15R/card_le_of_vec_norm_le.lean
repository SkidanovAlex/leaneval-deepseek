import Mathlib.Computability.Reduce
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7AK.K15R.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.card_le_of_vec_norm_le` — the lattice count in the momentum sum

`Work.BoseB4.vec n = 2π n` is the lattice momentum attached to `n : Fin 3 → ℤ`
(`BoseK15/Defs.lean` §2: the box momenta are `ℓ⁻¹ • vec n`, dual-lattice points
of `ℤ³`).  Every lattice sum of the chapter (`sum_inv_one_add_norm_le`, the K2/K5
lattice counts, `tail_hatChiSq`, …) is truncated, and truncation is controlled by
the elementary count proved here: a set of lattice indices whose momenta all lie
in the ball of radius `ρ` has at most `(ρ/π+1)³` elements.

The proof is the crudest possible: since `‖2π n‖ ≥ 2π|nᵢ|`, each coordinate of
`n` lies in `[-⌊ρ/(2π)⌋, ⌊ρ/(2π)⌋]`, so `S` is contained in the box
`∏ᵢ {m : ℤ | |m| ≤ ⌊ρ/(2π)⌋}`, of cardinality `(2⌊ρ/(2π)⌋+1)³ ≤ (ρ/π+1)³`
because `⌊ρ/(2π)⌋ ≤ ρ/(2π)`.  (The volume bound `(4/3)πR³` is much better but
this is all that is needed and needs no analysis.)
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7AK.K15R

/-- Coordinatewise control of the lattice momentum: the `i`-th component of
`vec n = 2π n` is bounded by the norm. -/
lemma two_pi_mul_abs_coord_le_norm_vec (n : Fin 3 → ℤ) (i : Fin 3) :
    2 * Real.pi * |(n i : ℝ)| ≤ ‖Work.BoseB4.vec n‖ := by
  have h2 : |(Work.BoseB4.vec n) i| ≤ ‖Work.BoseB4.vec n‖ := by
    simpa using PiLp.norm_apply_le (Work.BoseB4.vec n) i
  rw [show (Work.BoseB4.vec n) i = 2 * Real.pi * (n i : ℝ) from rfl] at h2
  rwa [abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)] at h2

/-- **The lattice count.**  A finite set of lattice indices whose momenta
`vec n = 2πn` all lie in the ball of radius `ρ` has at most `(ρ/π + 1)³`
elements — the box `∏ᵢ {m : ℤ | |m| ≤ ⌊ρ/(2π)⌋}` of side `2⌊ρ/(2π)⌋+1 ≤ ρ/π+1`
around the origin. -/
theorem card_le_of_vec_norm_le (S : Finset (Fin 3 → ℤ)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hS : ∀ n ∈ S, ‖Work.BoseB4.vec n‖ ≤ ρ) :
    (S.card : ℝ) ≤ (ρ / Real.pi + 1) ^ 3 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set K : ℤ := ⌊ρ / (2 * Real.pi)⌋ with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact Int.floor_nonneg.mpr (by positivity)
  -- every coordinate of every `n ∈ S` is bounded by `ρ/(2π)`
  have hcoord : ∀ n ∈ S, ∀ i : Fin 3, |(n i : ℝ)| ≤ ρ / (2 * Real.pi) := by
    intro n hn i
    have h1 := two_pi_mul_abs_coord_le_norm_vec n i
    have h3 : 2 * Real.pi * |(n i : ℝ)| ≤ ρ := le_trans h1 (hS n hn)
    rw [le_div_iff₀ (show (0 : ℝ) < 2 * Real.pi by positivity)]
    linarith
  -- hence `S` sits in the box of integer vectors with coordinates in `[-K, K]`
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-K) K) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h := abs_le.mp (hcoord n hn i)
    constructor
    · have hle : -(n i) ≤ K := by
        rw [hK]
        refine Int.le_floor.mpr ?_
        have hcast : ((-(n i) : ℤ) : ℝ) = -((n i : ℤ) : ℝ) := by push_cast; ring
        rw [hcast]
        linarith [h.1]
      simpa using neg_le_neg hle
    · rw [hK]
      exact Int.le_floor.mpr h.2
  -- the box has `(2K+1)³` points
  have hcard : (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-K) K)).card
      = (2 * K + 1).toNat ^ 3 := by
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc]
    have h : K + 1 - -K = 2 * K + 1 := by ring
    rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcast : (((2 * K + 1).toNat : ℕ) : ℝ) = 2 * (K : ℝ) + 1 := by
    have h1 : ((2 * K + 1).toNat : ℤ) = 2 * K + 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast h1
  have hbase : 2 * (K : ℝ) + 1 ≤ ρ / Real.pi + 1 := by
    have hKl : (K : ℝ) ≤ ρ / (2 * Real.pi) := by rw [hK]; exact Int.floor_le _
    have h2 : 2 * (ρ / (2 * Real.pi)) = ρ / Real.pi := by field_simp
    linarith
  calc (S.card : ℝ)
      ≤ ((Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-K) K)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (2 * (K : ℝ) + 1) ^ 3 := by rw [hcard]; push_cast; rw [hcast]
    _ ≤ (ρ / Real.pi + 1) ^ 3 := by
        refine pow_le_pow_left₀ ?_ hbase 3
        positivity

end Work.BoseB7AK.K15R
