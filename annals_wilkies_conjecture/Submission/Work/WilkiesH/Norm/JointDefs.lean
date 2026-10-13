import Mathlib
import Submission.Work.WilkiesH.Norm.Defs
import Submission.Work.WilG5.Basic

/-!
# Area H (counting) — the joint set behind `normSet_mem`

`normSet σ A = normMap σ '' (A ∩ normPiece σ)` is the image of `A ∩ normPiece σ` under the
coordinatewise map `normMap σ`, each coordinate of which is one of `t ↦ t`, `t ↦ -t`,
`t ↦ t⁻¹`, `t ↦ -t⁻¹`.

To see that `normSet σ A` is `Ω`-definable (with a loss of a constant format/degree amount
depending only on `n` and `σ`) we exhibit it as a *projection* of a joint set in
`ℝⁿ × ℝⁿ` (image block first, source block last): the ambient space is
`Fin (n + n) → ℝ`, its first `n` coordinates are read by `Fin.castAdd n` and its last `n`
coordinates by `lidx n` (the index function used by `Work.WilG5.liftLast`).

* `shapeRelPoly s`  — the polynomial in two variables `(w 0, w 1)` whose zero set is the
  graph of the shape map on the *invertible* part of the shape region: it is the relation
  `w 0 * w 1 = ± 1` for the inverting shapes and the linear relation for the others
  (`shapeRelPoly_eval_iff_of_mem`: on `shapeSet s` the relation is equivalent to
  `w 0 = shapeMap s (w 1)`);
* `shapeCoordMap i` — the pair of ambient coordinates used by the relation of coordinate `i`;
* `shapeRelSet i s` — that relation, imposed on the ambient space (a `coordPre` of the
  two-variable zero set, hence `Ω`-definable by `coordPre_mem`);
* `normJointGraph σ` — the intersection over `i` of `shapeRelSet i (σ i)`;
* `normJoint σ A` — the joint set `liftLast n A ∩ liftLast n (normPiece σ) ∩ normJointGraph σ`.

The results about these definitions live in the sibling files:

* `Work.WilkiesH.Norm.normPiece_mem` — `normPiece σ` is `Ω`-definable (each shape region is a
  one-dimensional `Ω`-set placed on one coordinate and intersected over `i`);
* `Work.WilkiesH.Norm.normJointGraph_mem` — `normJointGraph σ` is `Ω`-definable (each
  `shapeRelSet i (σ i)` is a `coordPre` of the two-variable zero set of `shapeRelPoly (σ i)`,
  whose total degree is at most `2`, so `coordPre_mem` applies uniformly in `i`);
* `projN_normJoint_eq` below — `projN n (normJoint σ A) = normSet σ A`.

The main theorem `Work.WilkiesH.Norm.normSet_mem` then intersects the three pieces
(`liftLast_mem` for `A` and for `normPiece σ`, `normJointGraph_mem` for the graph) and
projects with `projN_mem`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Norm

open WilkiesDesign WilkiesConjecture
open Work.WilG5

/-- The polynomial relating the image coordinate (variable `0`) to the source coordinate
(variable `1`) for a single shape:

* `pos`    (`t ↦ t`)     : `w 0 - w 1`;
* `neg`    (`t ↦ -t`)    : `w 0 + w 1`;
* `big`    (`t ↦ t⁻¹`)   : `w 0 * w 1 - 1`;
* `bigNeg` (`t ↦ -t⁻¹`)  : `w 0 * w 1 + 1`.

On the shape region `shapeSet s` its zero set is exactly the graph of `shapeMap s`. -/
def shapeRelPoly : NormShape → MvPolynomial (Fin 2) ℝ
  | .pos => MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2)
  | .neg => MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)
  | .big => MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - MvPolynomial.C 1
  | .bigNeg => MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) + MvPolynomial.C 1

/-- The two-variable graph set of a shape: the zero set of `shapeRelPoly s`. -/
def shapeGraphSet (s : NormShape) : Set (Fin 2 → ℝ) :=
  {w | (shapeRelPoly s).eval w = 0}

/-- The pair of ambient coordinates `(image coordinate i, source coordinate i)` of
`Fin (n + n) → ℝ`. -/
def shapeCoordMap {n : ℕ} (i : Fin n) : Fin 2 → Fin (n + n) :=
  ![Fin.castAdd n i, lidx n i]

@[simp] theorem shapeCoordMap_zero {n : ℕ} (i : Fin n) : shapeCoordMap i 0 = Fin.castAdd n i :=
  rfl

@[simp] theorem shapeCoordMap_one {n : ℕ} (i : Fin n) : shapeCoordMap i 1 = lidx n i :=
  rfl

/-- The relation of coordinate `i`, imposed on the ambient space `Fin (n + n) → ℝ`:
the pair `(image coordinate, source coordinate)` satisfies the shape relation. -/
def shapeRelSet {n : ℕ} (i : Fin n) (s : NormShape) : Set (Fin (n + n) → ℝ) :=
  coordPre (shapeCoordMap i) (shapeGraphSet s)

/-- The joint graph relation: for every coordinate `i`, the pair consisting of the `i`-th
coordinate of the image block and the `i`-th coordinate of the source block satisfies the
shape relation of `σ i`. -/
def normJointGraph {n : ℕ} (σ : Fin n → NormShape) : Set (Fin (n + n) → ℝ) :=
  ⋂ i, shapeRelSet i (σ i)

/-- The joint set: `A` and `normPiece σ` are imposed on the last (source) `n` coordinates,
and the graph conditions of `normJointGraph σ` tie the first (image) block to the last one.
Its projection `projN n` forgetting the source block is `normSet σ A`
(`Work.WilkiesH.Norm.projN_normJoint_eq`). -/
def normJoint {n : ℕ} (σ : Fin n → NormShape) (A : Set (Fin n → ℝ)) : Set (Fin (n + n) → ℝ) :=
  liftLast n A ∩ liftLast n (normPiece σ) ∩ normJointGraph σ

/-- On the region of a shape, the shape relation is equivalent to the graph condition
`w 0 = shapeMap s (w 1)`; for the inverting shapes one uses `w 1 ≠ 0`, which holds on
`shapeSet s`. -/
theorem shapeRelPoly_eval_iff_of_mem {s : NormShape} {w : Fin 2 → ℝ}
    (hw : w 1 ∈ shapeSet s) :
    w 0 = shapeMap s (w 1) ↔ (shapeRelPoly s).eval w = 0 := by
  cases s with
  | pos =>
    show w 0 = w 1 ↔ (shapeRelPoly NormShape.pos).eval w = 0
    simp only [shapeRelPoly, MvPolynomial.eval_sub, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  | neg =>
    show w 0 = -(w 1) ↔ (shapeRelPoly NormShape.neg).eval w = 0
    simp only [shapeRelPoly, MvPolynomial.eval_add, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  | big =>
    have hx : w 1 ≠ 0 := by
      have h1 : (1 : ℝ) < w 1 := hw
      linarith
    show w 0 = (w 1)⁻¹ ↔ (shapeRelPoly NormShape.big).eval w = 0
    simp only [shapeRelPoly, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, sub_eq_zero]
    constructor
    · intro h; rw [h, inv_mul_cancel₀ hx]
    · intro h; exact eq_inv_of_mul_eq_one_left h
  | bigNeg =>
    have hx : w 1 ≠ 0 := by
      have h1 : w 1 < -1 := hw
      linarith
    show w 0 = -(w 1)⁻¹ ↔ (shapeRelPoly NormShape.bigNeg).eval w = 0
    simp only [shapeRelPoly, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, add_eq_zero_iff_eq_neg]
    constructor
    · intro h; rw [h, neg_mul, inv_mul_cancel₀ hx]
    · intro h
      have h0 : w 0 * w 1 = -1 := h
      calc w 0 = w 0 * w 1 * (w 1)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hx, mul_one]
        _ = -1 * (w 1)⁻¹ := by rw [h0]
        _ = -(w 1)⁻¹ := by ring

/-- Membership in `normJointGraph σ` for a point whose source block lies in `normPiece σ`:
the joint graph relation is the conjunction of the graph conditions of the shape maps. -/
theorem mem_normJointGraph_iff {n : ℕ} (σ : Fin n → NormShape) {z : Fin (n + n) → ℝ}
    (hz : z ∈ liftLast n (normPiece σ)) :
    z ∈ normJointGraph σ ↔ ∀ i, z (Fin.castAdd n i) = shapeMap (σ i) (z (lidx n i)) := by
  have hx : ∀ i, z (lidx n i) ∈ shapeSet (σ i) := hz
  simp only [normJointGraph, Set.mem_iInter, shapeRelSet, coordPre, shapeGraphSet,
    Set.mem_ofPred_eq]
  constructor
  · intro h i
    exact (shapeRelPoly_eval_iff_of_mem (s := σ i) (w := z ∘ shapeCoordMap i) (hx i)).mpr (h i)
  · intro h i
    exact (shapeRelPoly_eval_iff_of_mem (s := σ i) (w := z ∘ shapeCoordMap i) (hx i)).mp (h i)

/-- `lidx n i` is `Fin.natAdd n i`, the index at which `Fin.append` reads off the second
block. -/
theorem lidx_eq_natAdd {n : ℕ} (i : Fin n) : lidx n i = Fin.natAdd n i :=
  Fin.ext rfl

/-- **The joint set projects onto the normalised set.**  Forgetting the last (source) `n`
coordinates of `normJoint σ A` leaves exactly `normSet σ A`: a point `y` of the image block
is admitted by the joint set for precisely those completions `w` with `w ∈ A`,
`w ∈ normPiece σ` and `y i = shapeMap (σ i) (w i)` for all `i`, i.e. `y = normMap σ w`. -/
theorem projN_normJoint_eq {n : ℕ} (σ : Fin n → NormShape) (A : Set (Fin n → ℝ)) :
    projN n (normJoint σ A) = normSet σ A := by
  have hlift : ∀ (B : Set (Fin n → ℝ)) (y w : Fin n → ℝ),
      Fin.append y w ∈ liftLast n B ↔ w ∈ B := by
    intro B y w
    have hfun : (fun i : Fin n => Fin.append y w (lidx n i)) = w := by
      funext i; rw [lidx_eq_natAdd, Fin.append_right]
    constructor
    · intro h; rwa [liftLast, Set.mem_ofPred_eq, hfun] at h
    · intro h; rwa [liftLast, Set.mem_ofPred_eq, hfun]
  have hgraph : ∀ (y w : Fin n → ℝ), w ∈ normPiece σ →
      (Fin.append y w ∈ normJointGraph σ ↔ ∀ i, y i = shapeMap (σ i) (w i)) := by
    intro y w hw
    have hz : Fin.append y w ∈ liftLast n (normPiece σ) := (hlift (normPiece σ) y w).mpr hw
    rw [mem_normJointGraph_iff σ hz]
    constructor
    · intro h i
      have h1 := h i
      rwa [Fin.append_left, lidx_eq_natAdd, Fin.append_right] at h1
    · intro h i
      rw [Fin.append_left, lidx_eq_natAdd, Fin.append_right]
      exact h i
  ext y
  simp only [projN, normJoint, normSet, Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff]
  constructor
  · rintro ⟨w, ⟨hA, hP⟩, hG⟩
    have hwA := (hlift A y w).mp hA
    have hwP := (hlift (normPiece σ) y w).mp hP
    exact ⟨w, ⟨hwA, hwP⟩, funext fun i => ((hgraph y w hwP).mp hG i).symm⟩
  · rintro ⟨w, ⟨hwA, hwP⟩, hwy⟩
    exact ⟨w, ⟨(hlift A y w).mpr hwA, (hlift (normPiece σ) y w).mpr hwP⟩,
      (hgraph y w hwP).mpr fun i => (congrFun hwy i).symm⟩

end Work.WilkiesH.Norm
