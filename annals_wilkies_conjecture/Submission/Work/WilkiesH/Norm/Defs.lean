import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Norm.absMulHeight_neg
import Submission.Work.WilkiesH.Norm.absMulHeight_inv

/-!
# Area H (counting) — the normalisation pieces and maps

BNZ §6 (and `WilkiesH/DESIGN.md` §3.1) start the counting induction by cutting `X ⊆ ℝⁿ`
into finitely many pieces on which each coordinate is normalised to lie in `[0,1]`: up to
negating and inverting coordinates (which does not affect the height), one may assume
`X ⊆ cube01 n` — the hypothesis under which the algebraic lemma (`WilkiesDesign.AlgLemma`)
is available.

The pieces are indexed by `σ : Fin n → NormShape`.  Coordinate `i` is
* `pos`    if `x i ∈ [0,1]`   (map `t ↦ t`),
* `neg`    if `x i ∈ [-1,0]`  (map `t ↦ -t`),
* `big`    if `x i ∈ (1,∞)`   (map `t ↦ t⁻¹`),
* `bigNeg` if `x i ∈ (-∞,-1)` (map `t ↦ -t⁻¹`).

The map sends each coordinate into `[0,1]`, so `normMap σ '' (A ∩ normPiece σ) ⊆ cube01 n`.
The four shapes (rather than the two shapes "`|x| ≤ 1`" and "`|x| > 1`") are used so that
`normMap σ` is *injective* on `normPiece σ`: the sign of each coordinate is recorded in the
piece, hence recoverable from the image.  This injectivity is what makes the `.trans`
bookkeeping go through — with a non-injective map the preimage of a connected semialgebraic
set may be disconnected.  The pieces are not disjoint (they overlap in `0`), but the
covering is only ever used additively, so this is harmless.

The results about these definitions live in the sibling files, stated so that the counting
induction can consume them (all for an arbitrary `σ : Fin n → NormShape`):

* `exists_normPiece` — the pieces cover `ℝⁿ`;
* `normSet_mem` — `normSet σ A ∈ S.Ω _ _ n` for `A ∈ S.Ω F D n`, i.e. the normalised set
  is `Ω`-definable with explicit format/degree bounds;
* `mem_degreeHeightLE_normMap` — normalisation preserves the degree and the height:
  `normMap σ x ∈ degreeHeightLE (normSet σ X) g H` for `x ∈ degreeHeightLE X g H`;
* `normSet_trans` — `normMap σ '' (T ∩ normPiece σ) ⊆ (normSet σ X).trans` for
  `T ⊆ X.trans`;
* `normMap_mem_cube01_and_injOn` — points of a piece go into `cube01 n`, and the map is
  injective on the piece;
* `isSemialgebraic_normSet`, `isSemialgebraic_preimage_normMap` — the map and its inverse
  are semialgebraic.

Convention: `normSet σ A = normMap σ '' (A ∩ normPiece σ)`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Norm

open WilkiesDesign WilkiesConjecture

/-- The four shapes of a coordinate in the normalisation. -/
inductive NormShape
  /-- `x ∈ [0,1]`, kept as is. -/
  | pos
  /-- `x ∈ [-1,0]`, negated. -/
  | neg
  /-- `x ∈ (1,∞)`, inverted. -/
  | big
  /-- `x ∈ (-∞,-1)`, negated and inverted. -/
  | bigNeg
  deriving DecidableEq

instance NormShape.fintype : Fintype NormShape where
  elems := {NormShape.pos, NormShape.neg, NormShape.big, NormShape.bigNeg}
  complete := by intro x; cases x <;> simp

instance : Nonempty NormShape := ⟨NormShape.pos⟩

/-- The region of `ℝ` associated with a shape. -/
def shapeSet : NormShape → Set ℝ
  | .pos => Set.Icc (0 : ℝ) 1
  | .neg => Set.Icc (-1 : ℝ) 0
  | .big => Set.Ioi (1 : ℝ)
  | .bigNeg => Set.Iio (-1 : ℝ)

/-- The normalising map associated with a shape. -/
def shapeMap : NormShape → ℝ → ℝ
  | .pos => id
  | .neg => fun t => -t
  | .big => fun t => t⁻¹
  | .bigNeg => fun t => -t⁻¹

/-- `normPiece σ ⊆ ℝⁿ`: the piece on which every coordinate lies in the region
prescribed by `σ`. -/
def normPiece {n : ℕ} (σ : Fin n → NormShape) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ shapeSet (σ i)}

/-- The coordinatewise normalising map attached to `σ`. -/
def normMap {n : ℕ} (σ : Fin n → NormShape) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => shapeMap (σ i) (x i)

/-- The normalised image of a set: `normMap σ '' (A ∩ normPiece σ)`. -/
def normSet {n : ℕ} (σ : Fin n → NormShape) (A : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  normMap σ '' (A ∩ normPiece σ)

end Work.WilkiesH.Norm
