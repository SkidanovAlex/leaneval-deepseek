import Mathlib
import Submission.Work.SSSR.serreE1Snd
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.grFMap
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
/-- **The second projection into the Serre filtration is compatible with face inclusions and with
the inclusions of the filtration.**  For a morphism `f : X ⟶ Y` of simplicial sets:

* the restriction of `Work.SSSR.sndToSerre f σ k` to the `i`-th face is `sndToSerre f (δ i ≫ σ) k`
  (this is what identifies the face terms of the boundary of a lifted σ-cycle with the terms for
  the faces of `σ`);
* the maps `sndToSerre f σ k` for increasing `k` are compatible with the structure maps
  `R_k ⟶ R_{k'}` of the Serre filtration (this is what shows that a term attached to a *degenerate*
  face dies in the graded piece, by refining `k`). -/
theorem sndToSerre_compat {X Y : SSet.{0}} (f : X ⟶ Y) :
    (∀ {P k : ℕ}
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ Y) (i : Fin (P+2))
        (h : SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.SSSR.StemsB.serreSubcomplex f k)
        (h' : SSet.Subcomplex.range
            (pullback.snd (SSet.stdSimplex.δ (n := P) i ≫ σ) f)
          ≤ Work.SSSR.StemsB.serreSubcomplex f k),
      Work.SSSR.pullFaceIncl f σ i ≫ Work.SSSR.sndToSerre f σ k h
        = Work.SSSR.sndToSerre f (SSet.stdSimplex.δ (n := P) i ≫ σ) k h')
    ∧
    (∀ {P k k' : ℕ} (hkk : k ≤ k')
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y)
        (h : SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.SSSR.StemsB.serreSubcomplex f k)
        (h' : SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.SSSR.StemsB.serreSubcomplex f k'),
      Work.SSSR.sndToSerre f σ k h
          ≫ Subfunctor.homOfLe (Work.SSSR.StemsB.serreSubcomplex_mono f hkk)
        = Work.SSSR.sndToSerre f σ k' h') := by
  -- `sndToSerre f σ k h` is `SSet.Subcomplex.lift (pullback.snd σ f) h`, so it is determined by its
  -- composite with the mono inclusion `(serreSubcomplex f k).ι`; hence it suffices to compare the
  -- two composites with that inclusion, and both unify with `pullback.snd` by the defining
  -- equations of `sndToSerre`, `pullFaceIncl` and `Subfunctor.homOfLe`.
  refine ⟨?_, ?_⟩
  · intro P k σ i h h'
    apply (cancel_mono (Work.SSSR.StemsB.serreSubcomplex f k).ι).1
    rw [Category.assoc, Work.SSSR.sndToSerre_ι, Work.SSSR.pullFaceIncl_snd,
      Work.SSSR.sndToSerre_ι]
  · intro P k k' hkk σ h h'
    apply (cancel_mono (Work.SSSR.StemsB.serreSubcomplex f k').ι).1
    rw [Category.assoc, Subfunctor.homOfLe_ι, Work.SSSR.sndToSerre_ι, Work.SSSR.sndToSerre_ι]

end Work.SSSR
