import ChallengeDeps
import Submission.BracketCount
import Submission.Corridor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Assignment pieces: confinement to the strict interior of the extended cell

The bracket lower bound proceeds by decomposing a state into assignment pieces
`χ_a·Ψ`.  Each piece confines particle `i` to the extended cell of the cell
`a_i` it is assigned to.  Because the concrete profile `rhoProfile` vanishes
outside `(1/4, 7/4)` (strictly inside `(0,2)` — `Profile.rhoProfile_eq_zero_of_le_quarter`
/ `_of_ge_seven_quarters`), the confinement is *strict*: particle `i` of the
piece `χ_a·Ψ` lives in the open cube

    axisSupp ℓ (axis of a_i):  ((j − 3/4)·ℓ, (j + 3/4)·ℓ) per axis,

which lies strictly inside the extended cell `axisExt` of side `2ℓ`.  Hence the
restricted slice (other particles' coordinates frozen) is a smooth function
with compact support in the *interior* of the extended cell — a Dirichlet state
of the extended cell, and therefore (via `embNeu`) an admissible Neumann state
of the extended cell, so its quotient is `≥ eNeu(n_j, 2ℓ)`-type (to be used by
the single-cell bracket lemma).

Results:

  * `piece` — the assignment-localized state `χ_a·Ψ`, smooth;
  * `axisSupp3` / `cellSupp3` — the strict confinement cubes (side `3ℓ/2`),
    strictly inside the extended cell;
  * `axisFam_support_strict` — `ξ_j` vanishes outside `axisSupp3`;
  * `cellCut_support_strict` — `χ_c` vanishes outside `cellSupp3 ℓ c`;
  * `piece_support_ext` — particle `i` of a piece lies in the extended cell of
    `a_i` (support statement from `Corridor`);
  * `piece_support_strict` — particle `i` lies in the strict interior cube
    `cellSupp3 ℓ (a_i)` (Dirichlet-type confinement).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The strict axis-support cube of an axis index: the (open) interval
`((j − 3/4)ℓ, (j + 3/4)ℓ)` inside which `ξ_j` can be nonzero. -/
def axisSupp {m : ℕ} (ℓ : ℝ) (j : Fin (m + 2)) : Set ℝ :=
  {t : ℝ | ((j.val : ℝ) - 3 / 4) * ℓ < t ∧ t < ((j.val : ℝ) + 3 / 4) * ℓ}

/-- The strict 3D support cube of a cell. -/
def cellSupp3 {m : ℕ} (ℓ : ℝ) (c : CellIdx m) : Set ℝ³ :=
  {y : ℝ³ | ∀ k : Fin 3, y k ∈ axisSupp ℓ (axisOf c k)}

/-- The axis cutoff `ξ_j` vanishes outside its strict support interval (which
lies strictly inside the extended cell). -/
lemma axisFam_support_strict {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (j : Fin (m + 2)) {t : ℝ}
    (ht : axisFam rhoProfile ℓ m j t ≠ 0) : t ∈ axisSupp ℓ j := by
  have hnz : rhoProfile (t / ℓ + 1 - (j.val : ℝ)) ≠ 0 := by
    simpa [axisFam] using ht
  -- the concrete profile vanishes outside `(1/4, 7/4)`:
  have hgt : 1 / 4 < t / ℓ + 1 - (j.val : ℝ) := by
    by_contra h
    exact hnz (rhoProfile_eq_zero_of_le_quarter (le_of_not_gt h))
  have hlt : t / ℓ + 1 - (j.val : ℝ) < 7 / 4 := by
    by_contra h
    exact hnz (rhoProfile_eq_zero_of_ge_seven_quarters (le_of_not_gt h))
  unfold axisSupp
  constructor
  · have h : (j.val : ℝ) - 3 / 4 < t / ℓ := by linarith
    exact (lt_div_iff₀ hℓ).mp h
  · have h : t / ℓ < (j.val : ℝ) + 3 / 4 := by linarith
    exact (div_lt_iff₀ hℓ).mp h

/-- The strict support cube is inside the extended cell. -/
lemma axisSupp_subset_axisExt {m : ℕ} (ℓ : ℝ) (j : Fin (m + 2)) :
    axisSupp ℓ j ⊆ axisExt ℓ j := by
  intro t ht
  -- membership in the strict cube forces `0 < ℓ` (both bounds must be ordered),
  -- after which the strict bounds (offset 3/4) imply the extended ones (offset 1).
  have hℓ0 : 0 < ℓ := by
    have hlt : ((j.val : ℝ) - 3 / 4) * ℓ < ((j.val : ℝ) + 3 / 4) * ℓ := lt_trans ht.1 ht.2
    nlinarith
  unfold axisExt
  constructor <;> nlinarith [ht.1, ht.2]

/-- The 3D cell cutoff vanishes outside its strict support cube. -/
lemma cellCut_support_strict {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (c : CellIdx m) {y : ℝ³}
    (hy : cellCut ℓ m c y ≠ 0) : y ∈ cellSupp3 ℓ c := by
  intro k
  fin_cases k
  · apply axisFam_support_strict hℓ m c.1
    have hprod : axisFam rhoProfile ℓ m c.1 (y 0) *
        (axisFam rhoProfile ℓ m c.2.1 (y 1) * axisFam rhoProfile ℓ m c.2.2 (y 2)) ≠ 0 := by
      simpa [cellCut, mul_assoc] using hy
    exact (mul_ne_zero_iff.mp hprod).1
  · apply axisFam_support_strict hℓ m c.2.1
    have hprod : axisFam rhoProfile ℓ m c.1 (y 0) *
        (axisFam rhoProfile ℓ m c.2.1 (y 1) * axisFam rhoProfile ℓ m c.2.2 (y 2)) ≠ 0 := by
      simpa [cellCut, mul_assoc] using hy
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).2).1
  · apply axisFam_support_strict hℓ m c.2.2
    have hprod : axisFam rhoProfile ℓ m c.1 (y 0) *
        (axisFam rhoProfile ℓ m c.2.1 (y 1) * axisFam rhoProfile ℓ m c.2.2 (y 2)) ≠ 0 := by
      simpa [cellCut, mul_assoc] using hy
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).2).2

/-- The assignment-localized state (the piece of `Ψ` with assignment `a`). -/
noncomputable def piece {N m : ℕ} (ℓ : ℝ) (a : Assign m N) (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) :
    X N → ℝ :=
  fun x => cellAssignCut ℓ m N a x * (Ψ : X N → ℝ) x

/-- A piece is smooth. -/
lemma piece_contDiff {N m : ℕ} (ℓ : ℝ) (a : Assign m N)
    (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) : ContDiff ℝ ∞ (piece ℓ a Ψ) := by
  unfold piece
  exact (cellAssignCut_contDiff ℓ m N a).mul (psi_contDiff Ψ)

/-- Support confinement: particle `i` of a nonzero piece lies in the extended
cell of the cell `a i` it is assigned to. -/
lemma piece_support_ext {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Assign m N)
    (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) {x : X N} (hx : piece ℓ a Ψ x ≠ 0) :
    ∀ i : Fin N, x i ∈ extCell3 ℓ (a i) := by
  intro i
  -- a nonzero piece has a nonzero assignment factor at particle `i`...
  have hc : cellAssignCut ℓ m N a x ≠ 0 := by
    unfold piece at hx
    exact (mul_ne_zero_iff.mp hx).1
  have hprod : (∏ j : Fin N, cellCut ℓ m (a j) (x j)) ≠ 0 := by
    simpa [cellAssignCut] using hc
  have hci : cellCut ℓ m (a i) (x i) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact cellCut_support_ext hℓ m (a i) hci

/-- Strict confinement: particle `i` of a nonzero piece lies in the strict
support cube of `a i` (compact support in the interior of the extended cell). -/
lemma piece_support_strict {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Assign m N)
    (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) {x : X N} (hx : piece ℓ a Ψ x ≠ 0) :
    ∀ i : Fin N, x i ∈ cellSupp3 ℓ (a i) := by
  intro i
  -- a nonzero piece has a nonzero assignment factor at particle `i`...
  have hc : cellAssignCut ℓ m N a x ≠ 0 := by
    unfold piece at hx
    exact (mul_ne_zero_iff.mp hx).1
  have hprod : (∏ j : Fin N, cellCut ℓ m (a j) (x j)) ≠ 0 := by
    simpa [cellAssignCut] using hc
  have hci : cellCut ℓ m (a i) (x i) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact cellCut_support_strict hℓ m (a i) hci

end BoseGases

end Submission
