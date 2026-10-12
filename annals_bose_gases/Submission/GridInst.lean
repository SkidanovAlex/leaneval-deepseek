import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Corollaries
import Submission.GridSubadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — the concrete `m³` grid instance of the multi-cell subadditivity.

Cells are indexed by `(Fin m)³`; the cell `(a,b,c)` sits at the offset
`(a·(ℓ+R), b·(ℓ+R), c·(ℓ+R))`.  Any two distinct cells differ by `≥ 1` in some
grid coordinate, hence their offsets differ by `≥ ℓ + R` there, so
points of distinct cells are at distance `≥ R` and cross interactions
vanish.  We derive two consequences of `boxEnergy_cells_subadd`:

* `boxEnergy_grid_subadd` : `E(Σ n j , L) ≤ Σ E(n j , ℓ)`;
* `boxEnergy_grid_balanced` : if `N ≤ m³·nbar` then `E(N, L) ≤ m³·E(nbar, ℓ)`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The offset of the grid cell `(a,b,c)`: the vector `(a·s, b·s, c·s)`.
Coordinate access: `(gridOff m s j).ofLp k`. -/
noncomputable def gridOff (m : ℕ) (s : ℝ) (j : Fin m × Fin m × Fin m) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun k : Fin 3 =>
    if h : k.1 = 0 then (j.1 : ℝ) * s
    else if h : k.1 = 1 then (j.2.1 : ℝ) * s
    else (j.2.2 : ℝ) * s)

/-- The `k`-th coordinate of a grid offset is the `(grid axis)`-component. -/
lemma gridOff_apply0 (m : ℕ) (s : ℝ) (j : Fin m × Fin m × Fin m) :
    (gridOff m s j).ofLp 0 = (j.1 : ℝ) * s := by
  simp [gridOff]

lemma gridOff_apply1 (m : ℕ) (s : ℝ) (j : Fin m × Fin m × Fin m) :
    (gridOff m s j).ofLp 1 = (j.2.1 : ℝ) * s := by
  simp [gridOff]

lemma gridOff_apply2 (m : ℕ) (s : ℝ) (j : Fin m × Fin m × Fin m) :
    (gridOff m s j).ofLp 2 = (j.2.2 : ℝ) * s := by
  simp [gridOff]

/-- One grid coordinate: two distinct cell coordinates give offsets (multiples of `s`)
that differ by at least `s` in absolute value (one of the two orders). -/
lemma coord_off_sep {m : ℕ} {s : ℝ} (a b : Fin m) (hab : a ≠ b) :
    s ≤ (a : ℝ) * s - (b : ℝ) * s ∨ s ≤ (b : ℝ) * s - (a : ℝ) * s := by
  have hne : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  by_cases hs : 0 ≤ s
  · rcases lt_or_gt_of_ne hne with hab' | hba'
    · right
      have h1 : (1 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
        have hreal : (a : ℝ) + 1 ≤ (b : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hab')
        linarith
      have hmul : s ≤ ((b : ℝ) - (a : ℝ)) * s := by
        simpa using (mul_le_mul_of_nonneg_right h1 hs)
      simpa [sub_mul] using hmul
    · left
      have h1 : (1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by
        have hreal : (b : ℝ) + 1 ≤ (a : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hba')
        linarith
      have hmul : s ≤ ((a : ℝ) - (b : ℝ)) * s := by
        simpa using (mul_le_mul_of_nonneg_right h1 hs)
      simpa [sub_mul] using hmul
  · have hsneg : s < 0 := lt_of_not_ge hs
    rcases lt_or_gt_of_ne hne with hab' | hba'
    · left
      have h1 : (1 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
        have hreal : (a : ℝ) + 1 ≤ (b : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hab')
        linarith
      have hmul : ((b : ℝ) - (a : ℝ)) * s ≤ s := by
        simpa using (mul_le_mul_of_nonpos_right h1 (le_of_lt hsneg))
      have hgoal : -(((b : ℝ) - (a : ℝ)) * s) ≥ s := by nlinarith [hmul]
      have hR : (a : ℝ) * s - (b : ℝ) * s = -(((b : ℝ) - (a : ℝ)) * s) := by ring
      rwa [hR]
    · right
      have h1 : (1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by
        have hreal : (b : ℝ) + 1 ≤ (a : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hba')
        linarith
      have hmul : ((a : ℝ) - (b : ℝ)) * s ≤ s := by
        simpa using (mul_le_mul_of_nonpos_right h1 (le_of_lt hsneg))
      have hgoal : -(((a : ℝ) - (b : ℝ)) * s) ≥ s := by nlinarith [hmul]
      have hR : (b : ℝ) * s - (a : ℝ) * s = -(((a : ℝ) - (b : ℝ)) * s) := by ring
      rwa [hR]

/-- A single grid coordinate `a < m` stays in `[0, L]` with room for a cell of side `ℓ`
when `L ≥ mℓ + (m−1)R` (the offset is `a·(ℓ+R)` and `a ≤ m−1`). -/
lemma gridOff_fit_coord {m : ℕ} {L ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hLbox : (m : ℝ) * ℓ + ((m : ℝ) - 1) * R ≤ L) (a : Fin m) :
    0 ≤ (a : ℝ) * (ℓ + R) ∧ (a : ℝ) * (ℓ + R) + ℓ ≤ L := by
  have hs : 0 ≤ ℓ + R := by linarith
  have hnonneg : 0 ≤ (a : ℝ) * (ℓ + R) := by
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le a.val)) hs
  have hle : (a : ℝ) ≤ (m : ℝ) - 1 := by
    have hreal : (a : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt a.isLt)
    linarith
  have hmul : (a : ℝ) * (ℓ + R) ≤ ((m : ℝ) - 1) * (ℓ + R) := by
    exact mul_le_mul_of_nonneg_right hle hs
  constructor
  · exact hnonneg
  · calc
      (a : ℝ) * (ℓ + R) + ℓ ≤ ((m : ℝ) - 1) * (ℓ + R) + ℓ := by linarith
      _ = (m : ℝ) * ℓ + ((m : ℝ) - 1) * R := by ring
      _ ≤ L := hLbox

/-- A grid coordinate of any cell is nonnegative and the cell fits in `[0,L]³`
when `L ≥ mℓ + (m−1)R`. -/
lemma gridOff_fit {m : ℕ} {L ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hLbox : (m : ℝ) * ℓ + ((m : ℝ) - 1) * R ≤ L) (j : Fin m × Fin m × Fin m) (k : Fin 3) :
    0 ≤ (gridOff m (ℓ + R) j).ofLp k ∧ (gridOff m (ℓ + R) j).ofLp k + ℓ ≤ L := by
  fin_cases k
  · simpa [gridOff] using (gridOff_fit_coord (m := m) hℓ hR hLbox j.1)
  · simpa [gridOff] using (gridOff_fit_coord (m := m) hℓ hR hLbox j.2.1)
  · simpa [gridOff] using (gridOff_fit_coord (m := m) hℓ hR hLbox j.2.2)

/-- Distinct cells are separated by at least `ℓ + R` in some coordinate. -/
lemma gridOff_sep {m : ℕ} {ℓ R : ℝ} (hR : 0 ≤ R) {j j' : Fin m × Fin m × Fin m}
    (hjj : j ≠ j') :
    ∃ k : Fin 3, ℓ + R ≤ (gridOff m (ℓ + R) j).ofLp k - (gridOff m (ℓ + R) j').ofLp k ∨
      ℓ + R ≤ (gridOff m (ℓ + R) j').ofLp k - (gridOff m (ℓ + R) j).ofLp k := by
  rcases j with ⟨a, ⟨b, c⟩⟩
  rcases j' with ⟨a', ⟨b', c'⟩⟩
  by_cases ha : a = a'
  · by_cases hb : b = b'
    · have hc : c ≠ c' := by
        intro hcc'
        apply hjj
        simp [ha, hb, hcc']
      rcases coord_off_sep (s := ℓ + R) (a := c) (b := c') hc with hlt | hgt
      · refine ⟨2, ?_⟩
        left
        simpa [gridOff] using hlt
      · refine ⟨2, ?_⟩
        right
        simpa [gridOff] using hgt
    · rcases coord_off_sep (s := ℓ + R) (a := b) (b := b') hb with hlt | hgt
      · refine ⟨1, ?_⟩
        left
        simpa [gridOff] using hlt
      · refine ⟨1, ?_⟩
        right
        simpa [gridOff] using hgt
  · rcases coord_off_sep (s := ℓ + R) (a := a) (b := a') ha with hlt | hgt
    · refine ⟨0, ?_⟩
      left
      simpa [gridOff] using hlt
    · refine ⟨0, ?_⟩
      right
      simpa [gridOff] using hgt

/-- Grid-cell subadditivity with cells of side `ℓ` on an `m`-per-axis grid of
spacing `ℓ + R`, inside a cube of side `L ≥ mℓ + (m−1)R`. -/
lemma boxEnergy_grid_subadd {m : ℕ} (n : Fin m × Fin m × Fin m → ℕ) {L ℓ R : ℝ}
    (hm : 1 ≤ m) (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : 0 < L)
    (hLbox : (m : ℝ) * ℓ + ((m : ℝ) - 1) * R ≤ L)
    {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    boxEnergy (∑ j : Fin m × Fin m × Fin m, n j) L v ≤
      ∑ j : Fin m × Fin m × Fin m, boxEnergy (n j) ℓ v := by
  have hpos : 0 < m := by omega
  haveI : Nonempty (Fin m × Fin m × Fin m) :=
    ⟨(⟨0, hpos⟩, (⟨0, hpos⟩, ⟨0, hpos⟩))⟩
  exact boxEnergy_cells_subadd (ι := Fin m × Fin m × Fin m) n hℓ hR hL
    (off := fun j => gridOff m (ℓ + R) j)
    (fun j k => gridOff_fit (m := m) hℓ hR hLbox j k)
    (fun ⦃j j'⦄ hjj => gridOff_sep (m := m) (ℓ := ℓ) (R := R) hR hjj) hv hv1 hsupp

/-- The number of grid cells: `m³`. -/
lemma card_grid (m : ℕ) : Fintype.card (Fin m × Fin m × Fin m) = m ^ 3 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The balanced form: if `N ≤ m³ · nbar` then `N` particles in the big box cost
no more than `m³` copies of the `nbar`-particle cell energy. -/
lemma boxEnergy_grid_balanced {m nbar N : ℕ} {L ℓ R : ℝ}
    (hm : 1 ≤ m) (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : 0 < L)
    (hLbox : (m : ℝ) * ℓ + ((m : ℝ) - 1) * R ≤ L)
    {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hN : N ≤ m ^ 3 * nbar) :
    boxEnergy N L v ≤ (m ^ 3) * boxEnergy nbar ℓ v := by
  let n : Fin m × Fin m × Fin m → ℕ := fun _ => nbar
  have htot : (∑ j : Fin m × Fin m × Fin m, n j) = m ^ 3 * nbar := by
    dsimp [n]
    rw [Finset.sum_const, Finset.card_univ]
    rw [Nat.nsmul_eq_mul]
    congr 1
    exact card_grid m
  have hmono : boxEnergy N L v ≤ boxEnergy (∑ j : Fin m × Fin m × Fin m, n j) L v := by
    apply boxEnergy_mono_N (v := v) hL hv hv1
    rw [htot]
    exact hN
  have hsub := boxEnergy_grid_subadd (m := m) n hm hℓ hR hL hLbox (v := v) hv hv1 hsupp
  have hsumE : (∑ j : Fin m × Fin m × Fin m, boxEnergy (n j) ℓ v) =
      (m ^ 3) * boxEnergy nbar ℓ v := by
    dsimp [n]
    rw [Finset.sum_const, Finset.card_univ]
    rw [nsmul_eq_mul]
    congr 1
    exact_mod_cast card_grid m
  calc
    boxEnergy N L v ≤ boxEnergy (∑ j : Fin m × Fin m × Fin m, n j) L v := hmono
    _ ≤ ∑ j : Fin m × Fin m × Fin m, boxEnergy (n j) ℓ v := hsub
    _ = (m ^ 3) * boxEnergy nbar ℓ v := hsumE

end BoseGases

end Submission
