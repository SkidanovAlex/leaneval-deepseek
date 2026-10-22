/-
AREA RESOL — the terms of the degreewise resolution functor are atomic sums.

`Work.RESOL.Zero.Rco F π hπ` is the functor sending a light condensed abelian group `M` to
the chain complex `(Λ.chainComplex M)` of the zero-preserving cover `(F, π)`, re-indexed in
cohomological degrees `≤ 0` by `ComplexShape.embeddingDownNat`.  Every term of
`Λ.chainComplex M` is of the form `F.obj Z` (this is the inductive construction of a left
resolution, Mathlib's `Abelian.LeftResolution.chainComplexXZeroIso`,
`chainComplexXOneIso`, `chainComplexXIso`), hence a small atomic sum by `hF`.  The image of
`embeddingDownNat` is exactly the non-positive integers, so the remaining degrees of the
extension are zero; a zero object is the empty atomic sum.
-/
import Mathlib
import Submission.Work.RESOL.ZeroSetup
import Submission.Work.RESOL.Basic

open CategoryTheory Limits LightCondensed

namespace Work.RESOL

/-- A zero object is a small atomic sum: it is the coproduct of the empty family
`(S j) = PEmpty.elim j`, whose colimit cocone has point the zero object itself. -/
lemma z_isAtomicSum_of_isZero {M : LightCondAb} (hM : IsZero M) : IsAtomicSum M := by
  refine ⟨PEmpty, PEmpty.elim, Cofan.mk M (fun j => PEmpty.elim j), ⟨?_⟩, ⟨Iso.refl M⟩⟩
  refine Cofan.IsColimit.mk _ (fun s => hM.isInitial.to s.pt) (fun s j => PEmpty.elim j) ?_
  intro s m _
  exact hM.isInitial.hom_ext m _

/-- If every term of a chain complex `K` of light condensed abelian groups is a small atomic
sum, then so is every term of its extension `K.extend ComplexShape.embeddingDownNat` along the
embedding `n ↦ -n` of `ComplexShape.down ℕ` into `ComplexShape.up ℤ`: in degree `n ≤ 0` the
term is a term of `K`, and in degree `n > 0` it is zero. -/
lemma z_isAtomicSum_extend {K : ChainComplex LightCondAb ℕ}
    (hK : ∀ k : ℕ, IsAtomicSum (K.X k)) (n : ℤ) :
    IsAtomicSum ((K.extend ComplexShape.embeddingDownNat).X n) := by
  by_cases hn : n ≤ 0
  · -- `n = -k` with `k = (-n).toNat`, so `X n` is the `k`-th term of `K`
    have hk : ComplexShape.embeddingDownNat.f ((-n).toNat) = n := by
      rw [ComplexShape.embeddingDownNat_f, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n)]
      exact neg_neg n
    exact isAtomicSum_of_iso
      (HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat hk).symm (hK _)
  · -- `n > 0` is not in the image of the embedding, so the term is zero
    push Not at hn
    exact z_isAtomicSum_of_isZero
      (HomologicalComplex.isZero_extend_X K ComplexShape.embeddingDownNat n
        (fun i hi => by rw [ComplexShape.embeddingDownNat_f] at hi; omega))

/-- Every term of the degreewise resolution of a light condensed abelian group by a
zero-preserving functorial atom cover is a small atomic sum. -/
theorem zAtomicTermsRco (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M))
    (hF : ∀ M : LightCondAb, Work.RESOL.IsAtomicSum (F.obj M))
    (M : LightCondAb) (n : ℤ) :
    Work.RESOL.IsAtomicSum (((Work.RESOL.Zero.Rco F π hπ).obj M).X n) := by
  refine z_isAtomicSum_extend ?_ n
  intro k
  rcases k with _ | _ | k
  · -- degree `0`: the term is `F.obj M`
    exact isAtomicSum_of_iso
      (Abelian.LeftResolution.chainComplexXZeroIso (Zero.LR F π hπ) M).symm (hF M)
  · -- degree `1`: the term is `F.obj (kernel (π.app M))`
    exact isAtomicSum_of_iso
      (Abelian.LeftResolution.chainComplexXOneIso (Zero.LR F π hπ) M).symm (hF _)
  · -- degree `k + 2`: the term is `F.obj (kernel (d (k+1) k))`
    exact isAtomicSum_of_iso
      (Abelian.LeftResolution.chainComplexXIso (Zero.LR F π hπ) M k).symm (hF _)

end Work.RESOL
