import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseBox.LatticeModel.Defs
import Submission.Work.BoseBox.LatticeModel.arith_card512
import Submission.Work.BoseBox.LatticeModel.card_le_eight_of_mem_Ioo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Counting lattice cells inside a ball (`latticeCells_card_mul_le`)

For a mesh `h > 0` and the FS lattice `k ↦ latticeCenter h N k = h·(k − N/2)`,
any finset `s` of cells whose centre lies in the ball of radius `2h√3` about the
origin satisfies

    card s · h³  ≤  4π(4h√3)³/3 .

The proof is a **discrete** counting argument (no measure theory is needed):

* the norm bound `eucNorm3 (latticeCenter h N k) < 2h√3` dominates every
  coordinate `|latticeCenter h N k j|`, hence forces
  `|k j − N/2| < 2√3` for each `j` (dividing by `h > 0`);
* so each coordinate of `k` lies in the open interval
  `(N/2 − 2√3, N/2 + 2√3)` of length `4√3 < 7`, which contains at most `7`
  integers (`card_le_eight_of_mem_Ioo`, a colleague's lemma);
* a finset of `Fin 3 → Fin N` all of whose coordinates lie in a set of at most
  `8` values is contained in the product of the three coordinate finsets
  (`Fintype.piFinset`), so `card s ≤ 8³ = 512`;
* finally `512 ≤ 4π(4√3)³/3 = 256π√3` (`arith_card512`, a colleague's lemma),
  which multiplies through by `h³ ≥ 0`.

The constant is deliberately loose: the true bound here is `7³ = 343` cells,
still far below `256π√3 ≈ 1393`.
-/

namespace Work.BoseBox.LatticeModel

/-- Each coordinate of a vector is dominated by `eucNorm3`. -/
private lemma abs_apply_le_eucNorm3 (u : Fin 3 → ℝ) (j : Fin 3) :
    |u j| ≤ Submission.BoseGases.eucNorm3 u := by
  rw [Submission.BoseGases.eucNorm3, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j))

/-- **The coordinate bound.**  If the centre `latticeCenter h N k` lies in the
ball of radius `2h√3` about the origin, then every coordinate of the index `k`
differs from `N/2` by less than `2√3`. -/
private lemma coord_abs_lt {h : ℝ} (hh : 0 < h) {N : ℕ} {k : Fin 3 → Fin N}
    (hk : Submission.BoseGases.eucNorm3 (latticeCenter h N k) < 2 * h * Real.sqrt 3)
    (j : Fin 3) : |((k j : ℕ) : ℝ) - (N : ℝ) / 2| < 2 * Real.sqrt 3 := by
  have h1 : |latticeCenter h N k j| < 2 * h * Real.sqrt 3 :=
    lt_of_le_of_lt (abs_apply_le_eucNorm3 _ j) hk
  rw [latticeCenter, abs_mul, abs_of_pos hh] at h1
  nlinarith [Real.sqrt_nonneg 3]

theorem latticeCells_card_mul_le {h : ℝ} (hh : 0 < h) {N : ℕ} {s : Finset (Fin 3 → Fin N)}
    (hs : ∀ k ∈ s, Submission.BoseGases.eucNorm3 (latticeCenter h N k) < 2 * h * Real.sqrt 3) :
    (s.card : ℝ) * h ^ 3 ≤ 4 * Real.pi * (4 * h * Real.sqrt 3) ^ 3 / 3 := by
  -- the finset of admissible values of a single coordinate of `k`
  set A : Fin 3 → Finset (Fin N) :=
    fun j => Finset.univ.filter (fun i => |((i : ℕ) : ℝ) - (N : ℝ) / 2| < 2 * Real.sqrt 3)
    with hAdef
  -- its cardinality is at most `8`: the elements lie in an open interval of length `4√3 ≤ 7`
  have hAcard : ∀ j, (A j).card ≤ 8 := by
    intro j
    refine card_le_eight_of_mem_Ioo (a := (N : ℝ) / 2 - 2 * Real.sqrt 3)
      (L := 4 * Real.sqrt 3)
      (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]) ?_
    intro i hi
    simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨h1, h2⟩ := abs_lt.mp hi
    exact ⟨by linarith, by linarith⟩
  -- `s` is contained in the product of the three coordinate finsets
  have hsub : s ⊆ Fintype.piFinset A := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro j
    simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact coord_abs_lt hh (hs k hk) j
  have hcard : s.card ≤ 512 := by
    calc s.card ≤ (Fintype.piFinset A).card := Finset.card_le_card hsub
      _ = ∏ j : Fin 3, (A j).card := Fintype.card_piFinset A
      _ ≤ ∏ _j : Fin 3, (8 : ℕ) :=
          Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => hAcard i)
      _ = 512 := by norm_num
  -- arithmetic: `512 ≤ 4π(4√3)³/3`, multiplied by `h³ ≥ 0`
  exact arith_card512 hh (by exact_mod_cast hcard)

end Work.BoseBox.LatticeModel
