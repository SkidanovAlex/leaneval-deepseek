import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.BracketPiece
import Submission.OccEnum
import Submission.ShiftInt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The single-cell slice of a localised state

For an assignment `a : Assign m N` and a cell `j`, let `I_j := occSet a j` be
the particles assigned to `j` (`n_j := cellCount a j` of them).  A state
`φ : X N → ℝ` can be read, with the coordinates of the particles *outside*
`I_j` frozen, as a function of the `n_j` occupied coordinates through the
order-preserving bijection `occEquiv`:

  * `occRestrict a j x : X (cellCount a j)` — reads from the full configuration
    `x` the positions of the particles of `I_j` (in the `occEquiv` order);
  * `occInsert a j y x : X N` — writes the partial configuration `y` into the
    slots of `I_j` of `x`, keeping the other particles at their `x` positions;
  * structural identities `occRestrict_insert` / `occInsert_restrict` (the
    restriction–insertion pair is a projection pair);
  * `sliceFn a j x φ` — the slice `y ↦ φ (occInsert a j y x)`, smooth when
    `φ` is smooth (`sliceFn_contDiff`);
  * confinement: for the assignment piece `piece ℓ a Ψ`, every slice is
    supported in the strict cell cube `cellSupp3 ℓ j` of the occupied
    coordinates (`slice_piece_support`);
  * nonvanishing: if `φ` does not vanish at `x₀`, then the slice at the
    background `x₀` is not identically zero (`sliceFn_nonzero_of`), and has
    positive box norm (`slice_sq_pos_of`), so it can be promoted to a `CNeu`
    state via `CNeu.ofFun` (admissibility for the per-cell bracket).

These give the coordinate identification behind the single-cell slice bracket:
the energy comparison against `eNeu (cellCount a j) (2ℓ) v` runs on the slice,
using `kinBox_shift` / `intWs_constShift` (translation to the standard box)
and `eNeu_le_quot_ofFun`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped NNReal ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Restriction to the occupied coordinates of cell `j` (in `occEquiv` order). -/
noncomputable def occRestrict {m N : ℕ} (a : Assign m N) (j : CellIdx m) (x : X N) :
    X (cellCount a j) :=
  fun t : Fin (cellCount a j) => x (((occEquiv a j) t : {i : Fin N // i ∈ occSet a j}) : Fin N)

/-- Insertion of the occupied coordinates of cell `j` into a background
configuration (the other particles keep their background positions). -/
noncomputable def occInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (x : X N) : X N :=
  fun i : Fin N => if h : i ∈ occSet a j then
    y (((occEquiv a j).symm) ⟨i, h⟩)
  else
    x i

/-- Restricting an insertion recovers the inserted partial configuration. -/
lemma occRestrict_insert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (x : X N) :
    occRestrict a j (occInsert a j y x) = y := by
  funext t
  unfold occRestrict occInsert
  rw [dif_pos]
  · congr 1
    simp
  · exact ((occEquiv a j) t).property

/-- Inserting the restriction of a configuration recovers it. -/
lemma occInsert_restrict {m N : ℕ} (a : Assign m N) (j : CellIdx m) (x : X N) :
    occInsert a j (occRestrict a j x) x = x := by
  funext i
  unfold occInsert occRestrict
  by_cases hi : i ∈ occSet a j
  · rw [dif_pos hi]
    congr 1
    simp
  · rw [dif_neg hi]

/-- The slice of `φ` at the background `x`: `φ` read as a function of the
occupied coordinates of cell `j`. -/
noncomputable def sliceFn {m N : ℕ} (a : Assign m N) (j : CellIdx m) (x : X N)
    (φ : X N → ℝ) : X (cellCount a j) → ℝ :=
  fun y : X (cellCount a j) => φ (occInsert a j y x)

/-- The insertion map `y ↦ occInsert a j y x` is smooth (it is affine). -/
lemma occInsert_contDiff {m N : ℕ} (a : Assign m N) (j : CellIdx m) (x : X N) :
    ContDiff ℝ ∞ (fun y : X (cellCount a j) => occInsert a j y x) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i ∈ occSet a j
  · have hproj : ContDiff ℝ ∞ (fun y : X (cellCount a j) =>
        y ((occEquiv a j).symm ⟨i, hi⟩)) := by
      exact (ContinuousLinearMap.proj ((occEquiv a j).symm ⟨i, hi⟩) :
        X (cellCount a j) →L[ℝ] ℝ³).contDiff
    convert hproj using 1
    funext y
    simp [occInsert, hi]
  · have hconst : ContDiff ℝ ∞ (fun _ : X (cellCount a j) => x i) := contDiff_const
    convert hconst using 1
    funext y
    simp [occInsert, hi]


/-- The slice of a smooth function is smooth (the insertion map is affine). -/
lemma sliceFn_contDiff {m N : ℕ} (a : Assign m N) (j : CellIdx m) (x : X N)
    {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (sliceFn a j x φ) := by
  unfold sliceFn
  exact hφ.comp (occInsert_contDiff a j x)

/-- A slice of the assignment piece is supported in the strict cell cube of the
occupied coordinates. -/
lemma slice_piece_support {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Assign m N)
    (j : CellIdx m) (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) {x : X N}
    {y : X (cellCount a j)} (hy : sliceFn a j x (piece ℓ a Ψ) y ≠ 0) :
    ∀ t : Fin (cellCount a j), y t ∈ cellSupp3 ℓ j := by
  intro t
  have hpiece : piece ℓ a Ψ (occInsert a j y x) ≠ 0 := by
    simpa [sliceFn] using hy
  have hsp := piece_support_strict hℓ a Ψ hpiece
  let e : {i : Fin N // i ∈ occSet a j} := occEquiv a j t
  have hins : occInsert a j y x (e : Fin N) = y t := by
    unfold occInsert
    rw [dif_pos (e.property : (e : Fin N) ∈ occSet a j)]
    congr 1
    simp [e]
  have hye : y t ∈ cellSupp3 ℓ (a (e : Fin N)) := by
    simpa [hins] using hsp (e : Fin N)
  have hae : a (e : Fin N) = j := by
    exact occEquiv_mem a j t
  simpa [hae] using hye

/-- If `φ` does not vanish at `x₀`, then the slice at background `x₀` is not
identically zero (it takes the value `φ x₀` at the restricted configuration). -/
lemma sliceFn_nonzero_of {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {φ : X N → ℝ} {x₀ : X N} (hφ : φ x₀ ≠ 0) :
    sliceFn a j x₀ φ (occRestrict a j x₀) ≠ 0 := by
  unfold sliceFn
  rw [occInsert_restrict]
  exact hφ

lemma eucl_norm_le_of_coord_abs_le {C : ℝ} {y : EuclideanSpace ℝ (Fin 3)} (hC : 0 ≤ C)
    (hy : ∀ k : Fin 3, |y k| ≤ C) : ‖y‖ ≤ Real.sqrt 3 * C := by
  have hb : 0 ≤ Real.sqrt 3 * C := by positivity
  apply le_of_sq_le_sq
  · rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ k : Fin 3, (y k) ^ 2 ≤ ∑ k : Fin 3, C ^ 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC] using hy k)
      _ = 3 * C ^ 2 := by norm_num
      _ = (Real.sqrt 3 * C) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  · exact hb

/-- A tuple whose coordinate norms are bounded by `B` has norm at most `B`. -/
lemma norm_le_of_coord_norm_le {n : ℕ} {B : ℝ} (hB : 0 ≤ B) {y : X n}
    (hy : ∀ t : Fin n, ‖y t‖ ≤ B) : ‖y‖ ≤ B := by
  let c : ℝ≥0 := ⟨B, hB⟩
  have hc : (c : ℝ) = B := rfl
  have hsup : (Finset.univ.sup fun b : Fin n => ‖y b‖₊) ≤ c := by
    refine Finset.sup_le_iff.mpr ?_
    intro t ht
    exact_mod_cast hy t
  rw [Pi.norm_def, ← hc]
  exact_mod_cast hsup

/-- The strict support cube of a cell lies inside a symmetric coordinate box of
radius `(m + 2)·ℓ`. -/
lemma cellSupp3_coord_abs_le {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : CellIdx m)
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ cellSupp3 ℓ j) (k : Fin 3) :
    |z k| ≤ ((m : ℝ) + 2) * ℓ := by
  have hzax : z k ∈ axisSupp ℓ (axisOf j k) := hz k
  have hzext := axisSupp_subset_axisExt ℓ (axisOf j k) hzax
  let c : Fin (m + 2) := axisOf j k
  have hc0 : (0 : ℝ) ≤ (c.val : ℝ) := by exact_mod_cast Nat.zero_le c.val
  have hc1 : (c.val : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast (Nat.le_of_lt_succ c.isLt)
  have hup : z k ≤ ((m : ℝ) + 2) * ℓ := by
    have h1 : z k < ((c.val : ℝ) + 1) * ℓ := hzext.2
    calc
      z k ≤ ((c.val : ℝ) + 1) * ℓ := le_of_lt h1
      _ ≤ ((m : ℝ) + 2) * ℓ := mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hℓ)
  have hlo : -(((m : ℝ) + 2) * ℓ) ≤ z k := by
    have h1 : ((c.val : ℝ) - 1) * ℓ < z k := hzext.1
    calc
      -(((m : ℝ) + 2) * ℓ) = (-((m : ℝ) + 2)) * ℓ := by ring
      _ ≤ ((c.val : ℝ) - 1) * ℓ := by
        refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hℓ)
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
        nlinarith
      _ ≤ z k := le_of_lt h1
  exact abs_le.mpr ⟨hlo, hup⟩

lemma slice_sq_pos_of {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hbig : 0 < (m : ℝ) * ℓ)
    (a : Assign m N) (j : CellIdx m) (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) {x₀ : X N}
    (hx₀ : x₀ ∈ interior (box N ((m : ℝ) * ℓ))) (hφ : piece ℓ a Ψ x₀ ≠ 0) :
    0 < ∫ y : X (cellCount a j), (sliceFn a j x₀ (piece ℓ a Ψ) y) ^ 2 := by
  let φ : X N → ℝ := piece ℓ a Ψ
  let f : X (cellCount a j) → ℝ := fun y => (sliceFn a j x₀ φ y) ^ 2
  let C : ℝ := ((m : ℝ) + 2) * ℓ
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  -- continuity
  have hφcd : ContDiff ℝ ∞ φ := by
    dsimp [φ]
    exact piece_contDiff ℓ a Ψ
  have hslice : ContDiff ℝ ∞ (sliceFn a j x₀ φ) := sliceFn_contDiff a j x₀ hφcd
  have hcont : Continuous f := by
    dsimp [f]
    exact hslice.continuous.pow 2
  -- support is bounded: slice nonvanishing confines every coordinate
  let B : Set (X (cellCount a j)) :=
    {y | ∀ t : Fin (cellCount a j), ∀ k : Fin 3, |(y t) k| ≤ C}
  have hsupP : Function.support f ⊆
      {y : X (cellCount a j) | ∀ t : Fin (cellCount a j), y t ∈ cellSupp3 ℓ j} := by
    intro y hy
    have hne : sliceFn a j x₀ φ y ≠ 0 := by
      dsimp [f] at hy
      by_contra hz
      exact hy (by simp [hz])
    exact slice_piece_support hℓ a j Ψ (by simpa [φ] using hne)
  have hPB : {y : X (cellCount a j) | ∀ t : Fin (cellCount a j), y t ∈ cellSupp3 ℓ j}
      ⊆ B := by
    intro y hy t k
    exact cellSupp3_coord_abs_le hℓ j (hy t) k
  have hsupB : Function.support f ⊆ B := hsupP.trans hPB
  have hboundedB : Bornology.IsBounded B := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * (Real.sqrt 3 * C), ?_⟩
    intro y hy z hz
    have hnorm : ∀ y ∈ B, ‖y‖ ≤ Real.sqrt 3 * C := by
      intro y hy
      exact norm_le_of_coord_norm_le (by positivity) (fun t =>
        eucl_norm_le_of_coord_abs_le hC (fun k => hy t k))
    calc
      dist y z = ‖y - z‖ := by rw [dist_eq_norm]
      _ ≤ ‖y‖ + ‖z‖ := norm_sub_le y z
      _ ≤ Real.sqrt 3 * C + Real.sqrt 3 * C := by
        exact add_le_add (hnorm y hy) (hnorm z hz)
      _ = 2 * (Real.sqrt 3 * C) := by ring
  have hboundedSupp : Bornology.IsBounded (Function.support f) := hboundedB.subset hsupB
  have hboundedTs : Bornology.IsBounded (tsupport f) := by
    rw [tsupport]
    exact hboundedSupp.closure
  have hcs : HasCompactSupport f := by
    exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨isClosed_tsupport f, hboundedTs⟩
  have hint : Integrable f (volume : Measure (X (cellCount a j))) :=
    Continuous.integrable_of_hasCompactSupport hcont hcs
  -- nonnegative
  have hnonneg : 0 ≤ᵐ[volume] f := ae_of_all volume (fun y => by dsimp [f]; exact sq_nonneg _)
  -- strictly positive at the restricted background point
  have hf0 : f (occRestrict a j x₀) ≠ 0 := by
    dsimp [f]
    have hφ0 : φ x₀ ≠ 0 := by simpa [φ] using hφ
    exact pow_ne_zero 2 (sliceFn_nonzero_of a j hφ0)
  let S : Set (X (cellCount a j)) := {y | f y ≠ 0}
  have hSopen : IsOpen S := isOpen_ne.preimage hcont
  rcases (Metric.isOpen_iff.mp hSopen (occRestrict a j x₀) hf0) with ⟨ε, hε, hball⟩
  have hμball : 0 < (volume : Measure (X (cellCount a j))) (Metric.ball (occRestrict a j x₀) ε) :=
    Metric.measure_ball_pos volume (occRestrict a j x₀) hε
  have hball_supp : Metric.ball (occRestrict a j x₀) ε ⊆ Function.support f := by
    intro y hy
    exact hball hy
  have hμsupp : 0 < (volume : Measure (X (cellCount a j))) (Function.support f) :=
    lt_of_lt_of_le hμball (measure_mono hball_supp)
  have hres := (integral_pos_iff_support_of_nonneg_ae (μ := volume) hnonneg hint).2 hμsupp
  simpa [f, φ] using hres

end BoseGases

end Submission
