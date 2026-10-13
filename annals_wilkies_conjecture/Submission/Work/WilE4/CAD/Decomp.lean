/-
  WilE4 / CAD — the cylindrical decomposition itself.

  For a family `H` of polynomials in `n` variables, `CadCells n H` is the list of cells of a
  cylindrical algebraic decomposition of `ℝ^n` adapted to `H`:

  * at level `0` there is a single cell, all of `ℝ^0`;
  * at level `k+1` we first decompose `ℝ^k` for the family `projDataT k H` (the projection data of
    `H` together with its derivative tower), and then, over each such base cell `C` and for each
    sign vector `v` of `H` that is realised over `C`, we take the cylinder `C × ℝ` cut by the sign
    condition `v`.

  The intended properties (proved in the files listed next to them) are

  * `CadCells_covers`         — the cells cover `ℝ^n`;
  * `CadCells_isUnionOf`      — every set whose atoms belong to `H` is a union of cells;
  * `CadCells_connected`      — every cell is connected;
  * `CadCells_realized_const` — over a cell, the realizability of a sign vector of `H` is
    constant;
  * `CadCells_deg`/`_length`  — degree and length bounds (polynomial in the input data).

  Together these give the ∃-projection and the complement operation with polynomial degree bounds,
  which is what the fibrewise closure theorem `E4_sa_fiber_closure` needs.
-/
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.cell_proj

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

variable {k m n : ℕ}

/-! ## Auxiliary notions -/

/-- The list of *all* sign vectors with `k` coordinates. -/
def allSign (k : ℕ) : List (Fin k → SignType) := (Finset.univ : Finset (Fin k → SignType)).toList

theorem mem_allSign (k : ℕ) (v : Fin k → SignType) : v ∈ allSign k := by
  simp [allSign]

/-- The sign vector of a family at a point. -/
def signVec {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ)) (z : Fin m → ℝ) :
    Fin G.length → SignType :=
  fun i => SignType.sign (MvPolynomial.eval z (G.get i))

theorem signVec_mem_signCond {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ)) (z : Fin m → ℝ) :
    z ∈ signCond G (signVec G z) := fun _ => rfl

/-- The cell covering all of `ℝ^n`: a single basic set with no atoms. -/
def topCell (n : ℕ) : SAd n := ⟨[⟨[], []⟩]⟩

theorem topCell_set (n : ℕ) : (topCell n).set = Set.univ := by
  ext x
  simp [topCell, SAd.set, BasicD.set, BasicD.Holds]

/-- The family whose sign conditions define the cells: it is the derivative tower of the family of
interest, which is what `Ana.jet_separation` needs for the connectivity of the cells. -/
def towerTop : (n : ℕ) → List (MvPolynomial (Fin n) ℝ) → List (MvPolynomial (Fin n) ℝ)
  | 0, H => H
  | (_ + 1), H => tower H

/-- `v` is realised over the cell `C`: some point of the cylinder `C × ℝ` has sign vector `v`. -/
def RealizedOn {m : ℕ} (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (C : SAd m)
    (v : Fin G.length → SignType) : Prop :=
  ∃ x ∈ C.set, ∃ t : ℝ, ∀ i, SignType.sign (MvPolynomial.eval (Fin.snoc x t) (G.get i)) = v i

/-- Membership in a cell, unfolded. -/
theorem mem_cell_iff {m : ℕ} (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (C : SAd m)
    (v : Fin G.length → SignType) (z : Fin (m + 1) → ℝ) :
    z ∈ (cell C G v).set ↔ Fin.init z ∈ C.set ∧
      ∀ i, SignType.sign (MvPolynomial.eval z (G.get i)) = v i := by
  have h1 : z ∈ (C.pad).set ↔ Fin.init z ∈ C.set := by rw [pad_set]; rfl
  have h2 : z ∈ (BasicD.ofSign G v).set ↔
      ∀ i, SignType.sign (MvPolynomial.eval z (G.get i)) = v i := by rw [ofSign_set]; rfl
  rw [cell, SAd.interBasic_set, Set.mem_inter_iff]
  exact and_congr h1 h2

/-- Realisability over `C` is the non-emptiness of the corresponding cell. -/
theorem realizedOn_iff_nonempty {m : ℕ} (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (C : SAd m)
    (v : Fin G.length → SignType) :
    RealizedOn G C v ↔ ((cell C G v).set).Nonempty := by
  constructor
  · rintro ⟨x, hx, t, ht⟩
    refine ⟨Fin.snoc x t, ?_⟩
    rw [mem_cell_iff, Fin.init_snoc]
    exact ⟨hx, ht⟩
  · rintro ⟨z, hz⟩
    rw [mem_cell_iff] at hz
    refine ⟨Fin.init z, hz.1, z (Fin.last m), fun i => ?_⟩
    rw [Fin.snoc_init_self z]
    exact hz.2 i

/-! ## The decomposition -/

/-- The cells of the cylindrical decomposition of `ℝ^n` adapted to the family `H`. -/
def CadCells : (n : ℕ) → List (MvPolynomial (Fin n) ℝ) → List (SAd n)
  | 0, _ => [topCell 0]
  | (k + 1), H =>
      (CadCells k (projDataT k H)).flatMap fun C =>
        (allSign H.length).filterMap fun v =>
          if RealizedOn H C v then some (cell C H v) else none

/-- The cells of the decomposition adapted to `H`, with the derivative tower taken first so that
the connectivity and type-constancy statements apply. -/
def cadCells (n : ℕ) (H : List (MvPolynomial (Fin n) ℝ)) : List (SAd n) :=
  CadCells n (towerTop n H)

theorem cadCells_zero (H : List (MvPolynomial (Fin 0) ℝ)) : cadCells 0 H = [topCell 0] := rfl

theorem cadCells_succ (H : List (MvPolynomial (Fin (k + 1)) ℝ)) :
    cadCells (k + 1) H
      = (CadCells k (projDataT k (tower H))).flatMap fun C =>
          (allSign (tower H).length).filterMap fun v =>
            if RealizedOn (tower H) C v then some (cell C (tower H) v) else none := rfl

/-- A cell depends only on the base cell it sits over and the sign vector. -/
theorem CadCells_succ_eq (H : List (MvPolynomial (Fin (k + 1)) ℝ)) :
    CadCells (k + 1) H
      = (CadCells k (projDataT k H)).flatMap fun C =>
          (allSign H.length).filterMap fun v =>
            if RealizedOn H C v then some (cell C H v) else none := rfl

/-- Membership in the decomposition at level `k+1`. -/
theorem mem_CadCells_succ {H : List (MvPolynomial (Fin (k + 1)) ℝ)} {D : SAd (k + 1)} :
    D ∈ CadCells (k + 1) H ↔
      ∃ C ∈ CadCells k (projDataT k H), ∃ v : Fin H.length → SignType,
        RealizedOn H C v ∧ D = cell C H v := by
  rw [CadCells_succ_eq, List.mem_flatMap]
  constructor
  · rintro ⟨C, hC, hD⟩
    rw [List.mem_filterMap] at hD
    obtain ⟨v, -, hv⟩ := hD
    by_cases h : RealizedOn H C v
    · rw [if_pos h] at hv
      exact ⟨C, hC, v, h, (Option.some.inj hv).symm⟩
    · rw [if_neg h] at hv
      exact absurd hv (by simp)
  · rintro ⟨C, hC, v, hv, rfl⟩
    refine ⟨C, hC, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨v, mem_allSign H.length v, by rw [if_pos hv]⟩

end Work.WilE4.CAD
