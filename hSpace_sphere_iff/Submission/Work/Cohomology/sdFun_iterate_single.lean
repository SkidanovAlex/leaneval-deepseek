import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.SubdivisionSpace
import Submission.Work.Cohomology.SubdivisionChain

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

noncomputable section

/-! ## Auxiliary facts about `sdFun` -/

/-- The continuous map underlying the pushforward of a simplex along `f` is the composite of the
underlying map of the simplex with `f`. -/
lemma homOfSimplex_pushSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    homOfSimplex (pushSimplex f n σ) = homOfSimplex σ ≫ f := by
  apply (TopCat.Hom.equivContinuousMap (stdTopSimplex n) Y).injective
  rw [homOfSimplex_apply, pushSimplex_apply]
  rfl

/-- **Naturality of the subdivision operator**: `sdFun` commutes with pushforward along a
continuous map. -/
lemma sdFun_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : SChain (TopCat.toSSet.obj X) ℚ n) :
    sdFun Y n (pushChain f n c) = pushChain f n (sdFun X n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ r =>
      rw [pushChain_single, sdFun_single, sdFun_single, map_smul, ← pushChain_comp,
        homOfSimplex_pushSimplex]

/-- The continuous map of the simplex associated with a piece `q` is the affine map of `q`. -/
lemma homOfSimplex_simplexOfPiece {N m : ℕ} (q : Piece N m) :
    homOfSimplex (simplexOfPiece q) = TopCat.ofHom (affineSimplex q) := by
  apply (TopCat.Hom.equivContinuousMap (stdTopSimplex m) (stdTopSimplex N)).injective
  rw [homOfSimplex_apply, toSSetObjEquivT_simplexOfPiece]
  rfl

/-- One step of the iteration of the subdivision, on chains of pieces of `Δ^N`. -/
def sdStep (N m : ℕ) : (Piece N m →₀ ℚ) →ₗ[ℚ] (Piece N m →₀ ℚ) :=
  Finsupp.linearCombination ℚ fun q : Piece N m => subdividePiece q

lemma toSingChain_subdividePiece {N m : ℕ} (q : Piece N m) :
    toSingChain (subdividePiece q)
      = pushChain (TopCat.ofHom (affineSimplex q)) m (sdUniv m) := by
  rw [subdividePiece]
  exact toSingChain_pushPieces_affine q (SdPieces m)

lemma sdStep_apply {N m : ℕ} (z : Piece N m →₀ ℚ) :
    sdStep N m z = z.sum fun q r => r • subdividePiece q := by
  rw [sdStep, Finsupp.linearCombination_apply]

/-- The iterated subdivision chain of `Δ^n` is obtained by one application of `sdStep`. -/
lemma SdPiecesPow_succ' (K n : ℕ) :
    SdPiecesPow (K+1) n = sdStep n n (SdPiecesPow K n) := by
  rw [SdPiecesPow_succ, sdStep, Finsupp.linearCombination_apply]

/-- **The subdivision operator on the standard simplex**: on a chain of pieces it is the
piecewise subdivision of each of its simplices. -/
lemma sdFun_stdTopSimplex_toSingChain {N m : ℕ} (z : Piece N m →₀ ℚ) :
    sdFun (stdTopSimplex N) m (toSingChain z) = toSingChain (sdStep N m z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [toSingChain_add, map_add, map_add, toSingChain_add, hx, hy]
  | single q r =>
      rw [toSingChain_single, map_smul, sdFun_single, sdStep, Finsupp.linearCombination_single,
        toSingChain_smul, toSingChain_subdividePiece, homOfSimplex_simplexOfPiece, one_smul]

theorem sdFun_iterate_single (X : TopCat.{0}) (n : ℕ) (N : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    Nat.iterate (Submission.Cohomology.sdFun X n) N (Finsupp.single σ 1)
      = Submission.Cohomology.pushChain (Submission.Cohomology.homOfSimplex σ) n
          (Submission.Cohomology.toSingChain (Submission.Cohomology.SdPiecesPow N n)) := by
  induction N with
  | zero =>
      rw [Function.iterate_zero_apply, SdPiecesPow_zero, toSingChain_single, one_smul,
        pushChain_single, pushSimplex_homOfSimplex_idPiece]
  | succ K ih =>
      rw [Function.iterate_succ_apply', ih, sdFun_natural, sdFun_stdTopSimplex_toSingChain,
        ← SdPiecesPow_succ']

end

end Work.Cohomology
