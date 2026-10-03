/-
# The `Gpiece` func-calculus identity in convolution form

The §5 piece `Gpiece (kmtPj ρ) d u l s N g` is a difference of at most two exact-height
Ionescu--Wainger projections `Π_{l,≤k}` of `g` (`Work.Analysis.EndVar.Gpiece`,
`Work.Analysis.EndVar.piece`), hence a linear convolution of `g` with the explicit kernel
`Work.KMTAreas.A7.pieceKer ρ l (fun s => d (-Log N + s)) 0 s`
(`Work.KMTAreas.A7.exactKer ρ l k = kmtKern ρ l k - kmtKern ρ (l-1) k`).

Both sides are unconditional `tsum`s, so the identity is *not* true for an arbitrary
`g : ℤ → ℂ` (see the header of `Submission/Work/KMTAreas/A7/FpieceEqTm.lean`: `tsum` is `0` on a
non-summable family, while the two sides distribute the difference over a different number of
`tsum`s).  It is true as soon as `g` is bounded, which is exactly the case used in the §5 assembly:
then every kernel occurring in the identity is in `ℓ¹(ℤ)` (`A5.summable_kmtKern_norm`, from
`kmtKernel_decay`) and a bounded function times an `ℓ¹` kernel is summable, so that the
differences can be distributed over the `tsum`s (`Summable.tsum_sub`).

Everything below is sorry-free; only `Submission.Work.KMTAreas.A7.ModelApproxKer` is imported.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxKer

namespace Work.A7

open scoped BigOperators

/-- The convolution operator with kernel a difference of two kernels, for a function against which
both kernels are summable. -/
private lemma convOp_sub_of_summable {κ₁ κ₂ u : ℤ → ℂ}
    (h₁ : ∀ x : ℤ, Summable (fun j : ℤ => κ₁ j * u (x - j)))
    (h₂ : ∀ x : ℤ, Summable (fun j : ℤ => κ₂ j * u (x - j))) :
    Work.KMTAreas.A7.convOp (κ₁ - κ₂) u
      = Work.KMTAreas.A7.convOp κ₁ u - Work.KMTAreas.A7.convOp κ₂ u := by
  funext x
  simp only [Work.KMTAreas.A7.convOp, Pi.sub_apply, sub_mul]
  rw [← (h₁ x).tsum_sub (h₂ x)]

/-- The exact-height Ionescu--Wainger kernel is summable against a bounded function. -/
private lemma summable_exactKer_mul (ρ : ℝ) (l : ℕ) (k : ℤ) {u : ℤ → ℂ}
    (hu : Work.KMTAreas.A5.BoundedZ u) (x : ℤ) :
    Summable (fun j : ℤ => Work.KMTAreas.A7.exactKer ρ l k j * u (x - j)) := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    have h : Work.KMTAreas.A7.exactKer ρ 0 k = Work.KMTAreas.A5.kmtKern ρ 0 k := by
      rw [Work.KMTAreas.A7.exactKer, if_pos rfl]
    rw [h]
    exact Work.KMTAreas.A5.summable_kmtKern_mul ρ 0 k hu x
  · have h : Work.KMTAreas.A7.exactKer ρ l k
        = Work.KMTAreas.A5.kmtKern ρ l k - Work.KMTAreas.A5.kmtKern ρ (l - 1) k := by
      rw [Work.KMTAreas.A7.exactKer, if_neg (Nat.pos_iff_ne_zero.mp hl)]
    rw [h]
    refine ((Work.KMTAreas.A5.summable_kmtKern_mul ρ l k hu x).sub
      (Work.KMTAreas.A5.summable_kmtKern_mul ρ (l - 1) k hu x)).congr (fun j => ?_)
    simp only [Pi.sub_apply, sub_mul]

/-- **The exact-height projection is the convolution with `exactKer`** (for bounded input). -/
private lemma piExact_eq_convOp (ρ : ℝ) (l : ℕ) (k : ℤ) {u : ℤ → ℂ}
    (hu : Work.KMTAreas.A5.BoundedZ u) :
    Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k u
      = Work.KMTAreas.A7.convOp (Work.KMTAreas.A7.exactKer ρ l k) u := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    funext x
    rw [Work.Analysis.EndVar.piExact, if_pos rfl, Work.KMTContract.kmtPj_proj,
      Work.KMTAreas.A5.kmtProj_eq_conv, Work.KMTAreas.A7.convOp, Work.KMTAreas.A7.exactKer,
      if_pos rfl]
  · have hne : l ≠ 0 := Nat.pos_iff_ne_zero.mp hl
    funext x
    rw [Work.Analysis.EndVar.piExact, if_neg hne, Pi.sub_apply, Work.KMTContract.kmtPj_proj,
      Work.KMTContract.kmtPj_proj,
      Work.KMTAreas.A5.kmtProj_eq_conv ρ l k u x,
      Work.KMTAreas.A5.kmtProj_eq_conv ρ (l - 1) k u x,
      Work.KMTAreas.A7.convOp, Work.KMTAreas.A7.exactKer, if_neg hne]
    have h1 : Summable (fun j : ℤ => Work.KMTAreas.A5.kmtKern ρ l k j * u (x - j)) :=
      Work.KMTAreas.A5.summable_kmtKern_mul ρ l k hu x
    have h2 : Summable (fun j : ℤ => Work.KMTAreas.A5.kmtKern ρ (l - 1) k j * u (x - j)) :=
      Work.KMTAreas.A5.summable_kmtKern_mul ρ (l - 1) k hu x
    rw [← h1.tsum_sub h2]
    exact tsum_congr (fun j => by simp only [Pi.sub_apply, sub_mul])

/-- **The §5 piece `piece` is the convolution with `pieceKer`** (for bounded input). -/
private lemma piece_eq_convOp (ρ : ℝ) (l : ℕ) (κ : ℤ → ℤ) (a s : ℤ) {u : ℤ → ℂ}
    (hu : Work.KMTAreas.A5.BoundedZ u) :
    Work.Analysis.EndVar.piece (Work.KMTContract.kmtPj ρ) l κ a s u
      = Work.KMTAreas.A7.convOp (Work.KMTAreas.A7.pieceKer ρ l κ a s) u := by
  by_cases h : s = a
  · rw [Work.Analysis.EndVar.piece, Work.KMTAreas.A7.pieceKer, if_pos h, if_pos h]
    exact piExact_eq_convOp ρ l (κ s) hu
  · rw [Work.Analysis.EndVar.piece, Work.KMTAreas.A7.pieceKer, if_neg h, if_neg h,
      convOp_sub_of_summable (fun x => summable_exactKer_mul ρ l (κ s) hu x)
        (fun x => summable_exactKer_mul ρ l (κ (s - 1)) hu x)]
    rw [← piExact_eq_convOp ρ l (κ s) hu, ← piExact_eq_convOp ρ l (κ (s - 1)) hu]

theorem ModelApproxCore_Gpiece_convOp (ρ : ℝ) (d l₂ k₂ N : ℕ) {g : ℤ → ℂ}
    (hg : Work.KMTAreas.A5.BoundedZ g) :
    Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) (d : ℤ) 0 l₂ (k₂ : ℤ) N g
      = Work.KMTAreas.A7.convOp
          (Work.KMTAreas.A7.pieceKer ρ l₂ (fun s : ℤ => (d : ℤ) * (-(Work.Analysis.EndVar.logN N) + s)) 0 (k₂ : ℤ)) g := by
  rw [Work.Analysis.EndVar.Gpiece_eq]
  simp only [Nat.cast_zero, neg_zero]
  exact piece_eq_convOp ρ l₂ _ 0 (k₂ : ℤ) hg

end Work.A7
