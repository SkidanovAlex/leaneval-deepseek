import Mathlib
import Submission.Work.Holonomy3.siegelDefs
import Submission.Work.Holonomy3.lowdiscCells
import Submission.Work.Holonomy3.disc_shift_two
import Submission.Work.Holonomy3.cell_biUnion_measure

namespace Work.Holonomy3

open Submission.CDT.Discrepancy
open MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-!
# Counting the low-discrepancy lattice points

The proof of `Work.Holonomy3.lattice_lowdisc_card`.  The bad exponent vectors `k` with all
coordinates `< D` and `disc (k/D) ≥ ε` are injected (via their half-open grid cell
`cell d D k = ∏_j [k_j/D, (k_j+1)/D)`) into the tail event `{u | ε/2 ≤ disc u}`: every point of the
cell is a shift of `k/D` by at most `D⁻¹`, and `Work.Holonomy3.disc_shift_two` says that shifts the
box discrepancy by at most twice the shift, whence `disc u ≥ ε - 2/D ≥ ε/2` because
`4(1/D + 1/d) ≤ ε`.  The cells are disjoint of equal measure `D^{-d}`, so the concentration
estimate `Submission.CDT.Discrepancy.disc_concentration_four` bounds the number of bad interior
points by `D^d · 100 exp (-d (ε/2)^4 / 100)`.  Finally the exponent vectors with a coordinate
exactly `D` number `(D+1)^d - D^d` and are simply thrown away.
-/

/-- The full box `[0,D]^d ∩ ℕ^d` of exponent vectors. -/
noncomputable def boxAll (d D : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.range (D + 1))

/-- The interior box `[0,D-1]^d ∩ ℕ^d` of exponent vectors. -/
noncomputable def boxIn (d D : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.range D)

lemma boxAll_card (d D : ℕ) : (boxAll d D).card = (D + 1) ^ d := by
  rw [boxAll, Fintype.card_piFinset]
  simp

lemma boxIn_card (d D : ℕ) : (boxIn d D).card = D ^ d := by
  rw [boxIn, Fintype.card_piFinset]
  simp

lemma mem_boxAll {d D : ℕ} {k : Fin d → ℕ} : k ∈ boxAll d D ↔ ∀ j, k j ≤ D := by
  rw [boxAll, Fintype.mem_piFinset]
  simp only [Finset.mem_range]
  constructor
  · intro h j; exact Nat.lt_succ_iff.mp (h j)
  · intro h j; exact Nat.lt_succ_iff.mpr (h j)

lemma mem_boxIn {d D : ℕ} {k : Fin d → ℕ} : k ∈ boxIn d D ↔ ∀ j, k j < D := by
  rw [boxIn, Fintype.mem_piFinset]
  simp only [Finset.mem_range]

lemma boxIn_subset_boxAll (d D : ℕ) : boxIn d D ⊆ boxAll d D := by
  intro k hk
  rw [mem_boxIn] at hk
  rw [mem_boxAll]
  intro j; have := hk j; omega

lemma lowSet_eq_boxAll (d D : ℕ) (ε : ℝ) :
    lowSet d D ε = (boxAll d D).filter
      (fun k : Fin d → ℕ => disc (fun j => (k j : ℝ) / (D : ℝ)) < ε) := rfl

/-- **A bad grid cell lies in the tail event.**  If every point `k j / D` of the grid
configuration has box discrepancy at least `ε`, then the whole cell of `k` is contained in
`{u | ε/2 ≤ disc u}`. -/
lemma cell_subset_tail {d D : ℕ} (hD : 0 < D) {ε : ℝ}
    (hbig : 4 * ((D : ℝ)⁻¹ + (d : ℝ)⁻¹) ≤ ε)
    {k : Fin d → ℕ} (hk : ∀ j, k j < D)
    (hbad : ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))) :
    cell d D k ⊆ {u : Fin d → ℝ | ε / 2 ≤ disc u} := by
  intro u hu
  show ε / 2 ≤ disc u
  rw [mem_cell] at hu
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  set t : Fin d → ℝ := fun j => (k j : ℝ) / (D : ℝ)
  have htj : ∀ j, t j = (k j : ℝ) / (D : ℝ) := fun j => rfl
  have htI : ∀ j, t j ∈ Set.Ico 0 1 := by
    intro j
    have hkD : (k j : ℝ) < (D : ℝ) := by exact_mod_cast hk j
    refine ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hDpos), ?_⟩
    rw [htj j]
    exact (div_lt_one hDpos).mpr hkD
  have huI : ∀ j, u j ∈ Set.Ico 0 1 := by
    intro j
    have hkD : (k j : ℝ) + 1 ≤ (D : ℝ) := by
      have : k j + 1 ≤ D := by have := hk j; omega
      exact_mod_cast this
    refine ⟨le_trans ?_ (hu j).1, ?_⟩
    · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hDpos)
    · have h3 : ((k j : ℝ) + 1) / (D : ℝ) ≤ 1 := by
        rw [div_le_one hDpos]; exact hkD
      linarith [(hu j).2, h3]
  have hdist : ∀ j, |u j - t j| ≤ (D : ℝ)⁻¹ := by
    intro j
    have h1 : (k j : ℝ) / (D : ℝ) ≤ u j := (hu j).1
    have h2 : u j < ((k j : ℝ) + 1) / (D : ℝ) := (hu j).2
    have h3 : (0 : ℝ) ≤ u j - t j := by rw [htj j]; linarith
    rw [abs_of_nonneg h3, htj j]
    have heq : ((k j : ℝ) + 1) / (D : ℝ) - (k j : ℝ) / (D : ℝ) = (D : ℝ)⁻¹ := by
      field_simp
      ring
    linarith
  have hη : (0 : ℝ) ≤ (D : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hDpos)
  have hlip := disc_shift_two t u htI huI hη hdist
  have htwo : 2 * (D : ℝ)⁻¹ ≤ ε / 2 := by
    have h1 : 4 * (D : ℝ)⁻¹ ≤ 4 * ((D : ℝ)⁻¹ + (d : ℝ)⁻¹) := by
      have : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
      linarith
    linarith
  have hle := (abs_le.mp hlip).1
  have hbadt : ε ≤ disc t := hbad
  have hhalf : ε - ε / 2 = ε / 2 := by ring
  have hA : ε - ε / 2 ≤ disc t - 2 * (D : ℝ)⁻¹ := by linarith
  have hB : ε - ε / 2 ≤ disc u := by linarith
  linarith

/-- The number of bad interior exponent vectors is bounded by the tail measure. -/
lemma badK_tail_bound {d D : ℕ} (hd : 0 < d) (hD : 1 ≤ D) {ε : ℝ} (hε : 0 < ε)
    (hbig : 4 * ((D : ℝ)⁻¹ + (d : ℝ)⁻¹) ≤ ε) :
    (((boxIn d D).filter (fun k : Fin d → ℕ =>
        ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ)))).card : ℝ) * ((D : ℝ) ^ d)⁻¹ ≤
      100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100) := by
  classical
  have hD0 : 0 < D := by omega
  have hmemS : ∀ k ∈ (boxIn d D).filter
      (fun k : Fin d → ℕ => ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))), ∀ j, k j < D :=
    fun k hk j => mem_boxIn.mp (Finset.mem_filter.mp hk).1 j
  have hbadS : ∀ k ∈ (boxIn d D).filter
      (fun k : Fin d → ℕ => ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))),
      ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ)) :=
    fun k hk => (Finset.mem_filter.mp hk).2
  have hsub : (⋃ k ∈ (boxIn d D).filter
      (fun k : Fin d → ℕ => ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))), cell d D k)
      ⊆ {u : Fin d → ℝ | ε / 2 ≤ disc u} := by
    intro u hu
    simp only [Set.mem_iUnion] at hu
    obtain ⟨k, hk, hku⟩ := hu
    exact cell_subset_tail hD0 hbig (hmemS k hk) (hbadS k hk) hku
  have h1 : (muP d).real (⋃ k ∈ (boxIn d D).filter
        (fun k : Fin d → ℕ => ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))), cell d D k)
      ≤ (muP d).real {u : Fin d → ℝ | ε / 2 ≤ disc u} := measureReal_mono hsub
  have h2 : (muP d).real (⋃ k ∈ (boxIn d D).filter
        (fun k : Fin d → ℕ => ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))), cell d D k)
      = (((boxIn d D).filter (fun k : Fin d → ℕ =>
            ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ)))).card : ℝ) * ((D : ℝ) ^ d)⁻¹ :=
    cell_biUnion_measure hd D hD0 _ hmemS
  have h3 : (muP d).real {u : Fin d → ℝ | ε / 2 ≤ disc u}
      ≤ 100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100) :=
    disc_concentration_four (by omega) (by positivity)
  rw [h2] at h1
  exact le_trans h1 h3

/-- **The low-discrepancy lattice points are almost all lattice points.** For `d ≥ 1`, `D ≥ 1`,
`ε > 0` with `4 (1/D + 1/d) ≤ ε`, the number of `k : Fin d → ℕ` with all `k j ≤ D` and box
discrepancy `disc (k/D) < ε` (`Work.Holonomy3.lowSet d D ε`) is at least
`D^d (1 - 100 exp (-d (ε/2)^4 / 100))`.

Route (cells + concentration of measure, as in the paper's §"Concentration of measure"): the bad
`k` with all coordinates `≤ D-1` correspond to the half-open cells `C_k = ∏_j [k_j/D, (k_j+1)/D)`;
if `disc (k/D) ≥ ε` then the whole cell `C_k` is contained in `{u : ε/2 ≤ disc u}`, because moving
the points of a configuration by at most `1/D` changes `disc` by at most `2/D + 1/d` (see
`Work.Holonomy3.disc_shift_lipschitz`; a sharper bound `2/d` also works since a grid interval of
length `1/D` contains at most one grid point) and `4(1/D + 1/d) ≤ ε` gives `2/D + 1/d ≤ ε/2`. The
cells are disjoint of `(muP d)`-measure `D^{-d}`, so `#{bad k} ≤ D^d · (muP d).real {u | ε/2 ≤ disc u}`,
which `Submission.CDT.Discrepancy.disc_concentration_four` bounds by `100 exp (-d (ε/2)^4/100)`;
the `k` with some coordinate equal to `D` number `(D+1)^d - D^d`, cancelling against
`#(all k) = (D+1)^d`. -/
theorem lattice_lowdisc_card {d : ℕ} (hd : 0 < d) (D : ℕ) (hD : 1 ≤ D) {ε : ℝ} (hε : 0 < ε)
    (hbig : 4 * ((D : ℝ)⁻¹ + (d : ℝ)⁻¹) ≤ ε) :
    (D : ℝ) ^ d * (1 - 100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100)) ≤
      ((Work.Holonomy3.lowSet d D ε).card : ℝ) := by
  classical
  set A : Finset (Fin d → ℕ) := boxAll d D
  set B : Finset (Fin d → ℕ) := boxIn d D
  set p : (Fin d → ℕ) → Prop := fun k => disc (fun j => (k j : ℝ) / (D : ℝ)) < ε
  set q : (Fin d → ℕ) → Prop := fun k => ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))
  have hD0 : 0 < D := by omega
  have hDpow : (0 : ℝ) < (D : ℝ) ^ d := pow_pos (by positivity) d
  -- cardinalities of the two boxes
  have hAcard : ((A.card : ℕ) : ℝ) = ((D : ℝ) + 1) ^ d := by
    rw [show A.card = (D + 1) ^ d from boxAll_card d D]
    push_cast
    ring
  have hBcard : ((B.card : ℕ) : ℝ) = (D : ℝ) ^ d := by
    rw [show B.card = D ^ d from boxIn_card d D]
    push_cast
    ring
  have hsubBA : B ⊆ A := by
    intro k hk
    change k ∈ boxAll d D
    exact boxIn_subset_boxAll d D hk
  -- the tail bound, multiplied through by D^d
  have hSb_le : ((B.filter q).card : ℝ)
      ≤ (D : ℝ) ^ d * (100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100)) := by
    have h := badK_tail_bound (d := d) (D := D) hd hD hε hbig
    have hkey : ((B.filter q).card : ℝ)
        = (((B.filter q).card : ℝ) * ((D : ℝ) ^ d)⁻¹) * ((D : ℝ) ^ d) := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpow), mul_one]
    rw [hkey]
    calc (((B.filter q).card : ℝ) * ((D : ℝ) ^ d)⁻¹) * ((D : ℝ) ^ d)
        ≤ (100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100)) * ((D : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_right h (le_of_lt hDpow)
      _ = (D : ℝ) ^ d * (100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100)) := by ring
  -- the partition of the box `A` into good and bad exponent vectors
  have hpart : (((A.filter p).card : ℝ) + ((A.filter (fun k => ¬ p k)).card : ℝ)) =
      ((A.card : ℕ) : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not (s := A) p
    exact_mod_cast h
  have hcastbad : ((A.filter (fun k => ¬ p k)).card : ℝ) = ((A.filter q).card : ℝ) := by
    have h : A.filter (fun k => ¬ p k) = A.filter q := by
      refine Finset.filter_congr ?_
      intro k _
      change ¬ (disc (fun j => (k j : ℝ) / (D : ℝ)) < ε) ↔ ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))
      exact not_lt
    rw [h]
  -- the algebraic bound on the number of bad vectors in `A`
  have hbadAle : ((A.filter q).card : ℝ)
      ≤ ((B.filter q).card : ℝ) + (((D : ℝ) + 1) ^ d - (D : ℝ) ^ d) := by
    have hsubset : A.filter (fun k => ¬ p k) ⊆ (B.filter q) ∪ (A \ B) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hkA, hkg⟩ := hk
      have hkb : q k := by
        change ε ≤ disc (fun j => (k j : ℝ) / (D : ℝ))
        exact not_lt.mp hkg
      by_cases hkB : k ∈ B
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hkB, hkb⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hkA, hkB⟩)
    have h1 : (A.filter (fun k => ¬ p k)).card ≤ ((B.filter q) ∪ (A \ B)).card :=
      Finset.card_le_card hsubset
    have h2 : ((B.filter q) ∪ (A \ B)).card ≤ (B.filter q).card + (A \ B).card :=
      Finset.card_union_le _ _
    have h3 : ((A.filter (fun k => ¬ p k)).card : ℝ)
        ≤ ((B.filter q).card : ℝ) + ((A \ B).card : ℝ) := by
      exact_mod_cast le_trans h1 h2
    have hAB : (A \ B).card = A.card - B.card := Finset.card_sdiff_of_subset hsubBA
    rw [hAB] at h3
    have hcast : ((A.card - B.card : ℕ) : ℝ) = ((A.card : ℕ) : ℝ) - ((B.card : ℕ) : ℝ) :=
      Nat.cast_sub (Finset.card_le_card hsubBA)
    rw [hcast, hAcard, hBcard] at h3
    rw [← hcastbad]
    exact h3
  -- conclusion
  have hgood : ((A.filter p).card : ℝ)
      = ((A.card : ℕ) : ℝ) - ((A.filter q).card : ℝ) := by
    have h : ((A.filter (fun k => ¬ p k)).card : ℝ) = ((A.filter q).card : ℝ) := hcastbad
    linarith
  have hθ : (D : ℝ) ^ d * (1 - 100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100))
      = (D : ℝ) ^ d - (D : ℝ) ^ d * (100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100)) := by
    ring
  have hfin : (D : ℝ) ^ d * (1 - 100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100))
      ≤ ((A.filter p).card : ℝ) := by
    linarith [hgood, hbadAle, hSb_le, hθ]
  rw [lowSet_eq_boxAll]
  exact hfin

end Work.Holonomy3
