import Mathlib
import Submission.Work.WilE4.CAD.Decomp
import Submission.Work.WilE4.CAD.Level
import Submission.Work.WilE4.CAD.Ops
import Submission.Work.WilE4.CAD.Bounds
import Submission.Work.WilE4.CAD.BoundsClosed
import Submission.Work.WilE4.CAD.Size
import Submission.Work.WilE4.CAD.CadCells_covers
import Submission.Work.WilE4.CAD.CadCells_isUnionOf
import Submission.Work.WilE4.CAD.CellsUnion
import Submission.Work.WilE4.CAD.BasePreconnected
import Submission.Work.WilE4.CAD.CadCells_preconnected
import Submission.Work.WilE4.CAD.Proj

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

/-! ## Iterating the projection along the last coordinates -/

/-- The `m`-fold projection of a subset of `ℝ^{n+m}` onto its first `n` coordinates. -/
def projLastSeq (n : ℕ) : (m : ℕ) → Set (Fin (n + m) → ℝ) → Set (Fin n → ℝ)
  | 0, S => S
  | m + 1, S => projLastSeq n m (WilkiesDesign.projLast S)

/-- The `m`-fold projection removes exactly the last `m` coordinates. -/
theorem projLastSeq_eq (n m : ℕ) (S : Set (Fin (n + m) → ℝ)) :
    projLastSeq n m S = {x : Fin n → ℝ | ∃ t : Fin m → ℝ, Fin.append x t ∈ S} := by
  induction m with
  | zero =>
    ext x
    simp only [projLastSeq, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨Fin.elim0, by simpa [Fin.append_elim0] using hx⟩
    · rintro ⟨t, ht⟩
      have ht' : Fin.append x (Fin.elim0 : Fin 0 → ℝ) ∈ S := by
        simpa [show t = (Fin.elim0 : Fin 0 → ℝ) from Subsingleton.elim t _] using ht
      simpa [Fin.append_elim0] using ht'
  | succ m ih =>
    rw [projLastSeq, ih (WilkiesDesign.projLast S)]
    ext x
    simp only [Set.mem_ofPred_eq, WilkiesDesign.projLast]
    constructor
    · rintro ⟨u, t, ht⟩
      refine ⟨Fin.snoc u t, ?_⟩
      rwa [Fin.append_snoc]
    · rintro ⟨t, ht⟩
      refine ⟨Fin.init t, t (Fin.last m), ?_⟩
      have ht' : Fin.append x (Fin.snoc (Fin.init t) (t (Fin.last m))) ∈ S := by
        rwa [Fin.snoc_init_self t]
      rw [Fin.append_snoc] at ht'
      exact ht'

/-! ## The degree bound polynomials -/

/-- The degree bound attached to the `j`-fold projection: the cell-count and cell-degree bounds at
the last level, composed with the growth of the projection data at every earlier level. -/
def projSeqB (k : ℕ) : ℕ → Polynomial ℕ
  | 0 => (bCellLen k).comp projDataTBound * (bCellDeg k).comp projDataTBound
  | (j + 1) => (projSeqB k j).comp projDataTBound

/-- The number of cells of the decomposition of the projection data of `H` is bounded by
`bCellLen k`, evaluated at `famDeg (projDataT k H)`. -/
theorem cadCells_projDataT_length_le (k : ℕ) (H : List (MvPolynomial (Fin (k + 1)) ℝ))
    (hclosed : ∀ i : Fin H.length, ∃ j : Fin H.length,
      H.get j = MvPolynomial.pderiv (Fin.last k) (H.get i)) :
    (CadCells k (projDataT k H)).length ≤ (bCellLen k).eval (famDeg (projDataT k H)) := by
  match k with
  | 0 => simp [CadCells, bCellLen]
  | (k' + 1) =>
      exact CadCells_length_le_closed k' (projDataT (k' + 1) H) (projDataT_deriv_closed H)

/-- The type constancy of the decomposition of the projection data: a sign vector of `H` realised
somewhere over a cell of `CadCells k (projDataT k H)` is realised over every point of the cell. -/
theorem realizedOn_all_projDataT (k : ℕ) (H : List (MvPolynomial (Fin (k + 1)) ℝ))
    (hclosed : ∀ i : Fin H.length, ∃ j : Fin H.length,
      H.get j = MvPolynomial.pderiv (Fin.last k) (H.get i)) :
    ∀ C ∈ CadCells k (projDataT k H), ∀ v : Fin H.length → SignType, RealizedOn H C v →
      ∀ x ∈ C.set,
        ∃ t : ℝ, ∀ i, SignType.sign (MvPolynomial.eval (Fin.snoc x t) (H.get i)) = v i :=
  fun C hC v hv x hx =>
    realizedOn_all_of_mem_CadCells H C hC (projDataT_base_preconnected H C hC) hclosed v hv x hx

/-! ## The induction -/

/-- The inductive statement: the `j`-fold projection of a set that is a union of cells of the
level-`k+j+1` decomposition of `H` is semialgebraic of degree bounded by `projSeqB k j`. -/
theorem exists_projSeq_aux (k : ℕ) (j : ℕ) :
    ∀ (Z : SAd (k + (j + 1))) (H : List (MvPolynomial (Fin (k + (j + 1))) ℝ)),
      (∀ i : Fin H.length, ∃ i' : Fin H.length,
        H.get i' = MvPolynomial.pderiv (Fin.last (k + j)) (H.get i)) →
      (∀ C ∈ CadCells (k + (j + 1)) H, C.set ⊆ Z.set ∨ Disjoint C.set Z.set) →
      ∃ Z' : SAd k,
        Z'.set = {x : Fin k → ℝ | ∃ t : Fin (j + 1) → ℝ, Fin.append x t ∈ Z.set} ∧
        Z'.deg ≤ (projSeqB k j).eval (famDeg H) := by
  induction j with
  | zero =>
    intro Z H hclosed hUn
    refine ⟨projSAd H Z, ?_, ?_⟩
    · have hset := projSAd_set H Z (CadCells_covers (projDataT k H)) hUn
        (realizedOn_all_projDataT k H hclosed)
      rw [hset]
      exact projLastSeq_eq k 1 Z.set
    · have hβ : ∀ C ∈ CadCells k (projDataT k H), C.deg ≤
          (bCellDeg k).eval (famDeg (projDataT k H)) :=
        fun C hC => (CadCells_deg_basics_le k (projDataT k H) C hC).1
      have hlen := cadCells_projDataT_length_le k H hclosed
      have hdeg := projSAd_deg_le (H := H) Z hβ
      have hfam := famDeg_projDataT_le_bound (n := k) H
      have hmonoLen := polynomial_eval_mono (bCellLen k) hfam
      have hmonoDeg := polynomial_eval_mono (bCellDeg k) hfam
      calc (projSAd H Z).deg
          ≤ (CadCells k (projDataT k H)).length
              * (bCellDeg k).eval (famDeg (projDataT k H)) := hdeg
        _ ≤ (bCellLen k).eval (projDataTBound.eval (famDeg H))
              * (bCellDeg k).eval (projDataTBound.eval (famDeg H)) :=
            Nat.mul_le_mul (hlen.trans hmonoLen) hmonoDeg
        _ = ((bCellLen k).comp projDataTBound
              * (bCellDeg k).comp projDataTBound).eval (famDeg H) := by
            rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_comp]
        _ = (projSeqB k 0).eval (famDeg H) := rfl
  | succ j ih =>
    intro Z H hclosed hUn
    have hUn₁ : ∀ C ∈ CadCells (k + (j + 1)) (projDataT (k + j + 1) H),
        C.set ⊆ (projSAd H Z).set ∨ Disjoint C.set (projSAd H Z).set := fun C hC =>
      cell_subset_unionCells_or_disjoint (projDataT (k + j + 1) H) (projCells H Z)
        (fun D hD => (projCells_mem H Z D hD).1) C hC
    obtain ⟨Z', hsetZ', hdegZ'⟩ :=
      ih (projSAd H Z) (projDataT (k + j + 1) H) (projDataT_deriv_closed H) hUn₁
    refine ⟨Z', ?_, ?_⟩
    · have hset := projSAd_set H Z (CadCells_covers (projDataT (k + j + 1) H)) hUn
        (fun C hC v hv x hx => realizedOn_all_of_mem_CadCells H C hC
          (projDataT_base_preconnected H C hC) hclosed v hv x hx)
      rw [hsetZ', hset, ← projLastSeq_eq k (j + 1) (WilkiesDesign.projLast Z.set),
        ← projLastSeq_eq k (j + 1 + 1) Z.set]
      rfl
    · have hfam := famDeg_projDataT_le_bound (n := k + j + 1) H
      calc Z'.deg ≤ (projSeqB k j).eval (famDeg (projDataT (k + j + 1) H)) := hdegZ'
        _ ≤ (projSeqB k j).eval (projDataTBound.eval (famDeg H)) :=
            polynomial_eval_mono (projSeqB k j) hfam
        _ = ((projSeqB k j).comp projDataTBound).eval (famDeg H) :=
            (Polynomial.eval_comp).symm
        _ = (projSeqB k (j + 1)).eval (famDeg H) := rfl

/-- **Iterated projection with a polynomial degree bound.**

Let `Z ⊆ ℝ^{k + (j+1)}` be a semialgebraic set in disjunctive normal form whose atoms all belong to
a family `H` that is closed under differentiation in the last variable.  Then the projection of `Z`
onto the first `k` coordinates (i.e. the set of points `x : Fin k → ℝ` for which the last `j+1`
coordinates can be chosen to land in `Z`) is again semialgebraic in disjunctive normal form, and its
degree is bounded by a fixed polynomial `B` in `famDeg H` that depends only on `k` and `j`.

This is the `j+1`-fold iteration of the one-variable projection `projSAd` (`Ops.lean`), which is the
middle step of the fibrewise closure (`E4`): the projection removes the coordinates of `y'` and of
`ε` one at a time.

Route.  Write `m := k + j + 1` for the top level and let `H₁ := H`, `H_{i+1} := projDataT (m-i) H_i`
be the family at the level one step down (`projDataT … = tower (projData …) ++ [0]`, so `H_{i+1}`
is *strongly* derivative-closed by `Work.WilE4.CAD.projDataT_deriv_closed` as soon as `m - i ≥ 1`).
Define `Z₀ := Z` and `Z_{i+1} := projSAd H_i Z_i`.  Then

* `(Z_{i+1}).set = WilkiesDesign.projLast (Z_i).set`, by `projSAd_set`.  Its two extra hypotheses
  are available: the cover by `CadCells_covers`; and `hUn` — every cell of `CadCells (m-i) H_i` is
  contained in `Z_i` or disjoint from it — which holds for `i = 0` by `CadCells_isUnionOf`
  (`Z`'s atoms lie in `H` by hypothesis) and for `i ≥ 1` because `Z_i = unionCells (projCells …)`
  is a union of cells of the very decomposition `CadCells (m-i) H_i`
  (`Ops.projSAd` unfolds to `unionCells` of a sub-list of `CadCells`), so that
  `Work.WilE4.CAD.cell_subset_unionCells_or_disjoint` (`CellsUnion.lean`) applies.
  The type-constancy input `hconst` of `projSAd_set` is the `∀ x ∈ C.set` form, which is the first
  disjunct of `syl_minor_type_const` used in `baseCell_type_const` (`Level.lean`): the base cell `C`
  is preconnected by `Work.WilE4.CAD.projDataT_base_preconnected` (`BasePreconnected.lean`), and the
  family `H_i` is strongly closed.
* the degree: `projSAd_deg_le` bounds `(Z_{i+1}).deg` by
  `(CadCells (m-i) (projDataT (m-i) H_i)).length * β`, where `β` bounds the degrees of those cells.
  By `CadCells_deg_basics_le` (`Bounds.lean`, unconditional) and
  `Work.WilE4.CAD.CadCells_length_le_closed` (`BoundsClosed.lean`, the cell-count recursion with the
  derivative-closure hypothesis threaded through — `CadCells_length_le` itself takes the type
  constancy for *all* families, which is not available) both factors are bounded by explicit
  polynomials in `famDeg (projDataT (m-i) H_i) ≤ projDataTBound.eval (famDeg H_i)`, and `famDeg H_i`
  grows by `projDataTBound` at each step (`Size.famDeg_projDataT_le` /
  `Bounds.famDeg_projDataT_le_bound`).  Composing these (`Polynomial.comp`, `Polynomial.eval_comp`,
  `polynomial_eval_mono`) gives the single polynomial `B` in `famDeg H`; note that the bound of each
  step depends only on the family at that level, not on the degree of `Z_i`. -/
theorem exists_projSeq (k j : ℕ) :
    ∃ B : Polynomial ℕ,
      ∀ (Z : SAd (k + (j + 1))) (H : List (MvPolynomial (Fin (k + (j + 1))) ℝ)),
        (∀ i : Fin H.length, ∃ i' : Fin H.length,
          H.get i' = MvPolynomial.pderiv (Fin.last (k + j)) (H.get i)) →
        (∀ B₀ ∈ Z.basics, ∀ P ∈ B₀.eqs ++ B₀.pos, P ∈ H) →
        ∃ Z' : SAd k,
          Z'.set = {x : Fin k → ℝ | ∃ t : Fin (j + 1) → ℝ, Fin.append x t ∈ Z.set} ∧
          Z'.deg ≤ B.eval (famDeg H) := by
  refine ⟨projSeqB k j, fun Z H hclosed hatoms => ?_⟩
  exact exists_projSeq_aux k j Z H hclosed (CadCells_isUnionOf H Z hatoms)

end Work.WilE4.CAD
