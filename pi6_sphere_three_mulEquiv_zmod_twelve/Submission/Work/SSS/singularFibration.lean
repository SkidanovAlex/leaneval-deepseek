import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.serreE1Defs
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.kanComplex_singularSet
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.SSS.HornDefs
import Submission.Work.SSS.relHLP_of_quotient
import Submission.Work.SSS.relHLP_of_hasHLPRel
import Submission.Work.SSS.coneMap_pair
import Submission.Work.SSS.exists_hornGlue
import Submission.Work.SSS.faceCompat_of_hornMorphism

namespace Work.SSS

open scoped SSet.modelCategoryQuillen Simplicial
open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory

noncomputable section

--- the topological statement for the horn ---

theorem relHLP_horn {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (n : ℕ) (i : Fin (n + 2)) :
    RelHLP p (stdSimplex ℝ (Fin (n + 2))) (TopHorn (n + 1) i) :=
  have h1 : RelHLP p ((Fin n → unitInterval) × unitInterval) (Work.StemsB.LSet n) :=
    relHLP_of_hasHLPRel p n (Work.StemsB.exists_lift_rel p hfib n)
  relHLP_of_quotient p (Work.StemsB.LSet n) (TopHorn (n + 1) i) (coneMap n i)
    (coneMap_pair n i).1 (coneMap_pair n i).2.1
    (fun w w' hww' hne => ((coneMap_pair n i).2.2 w w' hww').resolve_left hne) h1

--- naturality of the bridge between horn morphisms and continuous maps ---

theorem simplexEquiv_toSSet_map {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y))
    (x : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n))) :
    simplexEquiv n Y ((TopCat.toSSet.map (TopCat.ofHom q)).app _ x) =
      q.comp (simplexEquiv n X x) := by
  ext t
  rfl

theorem morphSimplex_comp {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y))
    (u : SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ TopCat.toSSet.obj (TopCat.of X)) :
    morphSimplex n Y (u ≫ TopCat.toSSet.map (TopCat.ofHom q)) = q.comp (morphSimplex n X u) := by
  simp only [morphSimplex, Equiv.trans_apply, SSet.yonedaEquiv_comp]
  exact simplexEquiv_toSSet_map q _

theorem morphSimplex_δ {n : ℕ} {X : Type} [TopologicalSpace X]
    (u : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ TopCat.toSSet.obj (TopCat.of X))
    (j : Fin (n + 2)) :
    morphSimplex n X (SSet.stdSimplex.δ j ≫ u) = (morphSimplex (n + 1) X u).comp (coface n j) := by
  ext z
  show ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk n))
    (SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ u))) z = _
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
  exact TopCat.toSSetObjEquivT_δ_apply _ j z

--- a map on the horn is determined by its faces ---

theorem comp_hornIncl_eq_of_faces {X : Type} [TopologicalSpace X] {n : ℕ} {i : Fin (n + 2)}
    (u : C(↥(TopHorn (n + 1) i), X)) (w : C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      u.comp (faceIncl (n + 1) i j hj) = w.comp (coface n j)) :
    u = w.comp (hornIncl (n + 1) i) := by
  ext q
  obtain ⟨j, hj, hq⟩ := q.2
  have hdel : (faceIncl (n + 1) i j hj) (stdSimplexDel (k := n + 1) j q.1 hq) = q :=
    Subtype.ext (by rw [faceIncl_coe, ← coface_apply]; exact coface_stdSimplexDel j q.1 hq)
  have h2 := congrFun (congrArg DFunLike.coe (h j hj))
    (stdSimplexDel (k := n + 1) j q.1 hq)
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, hdel,
    coface_stdSimplexDel] at h2
  simpa only [ContinuousMap.comp_apply, hornIncl_apply] using h2

--- the SSet lifting property for a horn inclusion ---

theorem hornLift {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty (SSet.horn (n + 1) i).ι (sSingP p) := by
  refine HasLiftingProperty.mk fun {f g} sq => ?_
  let v : C(stdSimplex ℝ (Fin (n + 2)), B) := morphSimplex (n + 1) B g
  have hsp : sSingP p = TopCat.toSSet.map (TopCat.ofHom p) := rfl
  have hface : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      p.comp (faceSimplex f j hj) = v.comp (coface n j) := by
    intro j hj
    have h1 : (SSet.horn.ι i j hj ≫ f) ≫ sSingP p = SSet.stdSimplex.δ j ≫ g := by
      rw [Category.assoc, sq.w, ← Category.assoc, SSet.horn.ι_ι]
    rw [hsp] at h1
    have h2 := congrArg (morphSimplex n B) h1
    rw [morphSimplex_comp, morphSimplex_δ] at h2
    exact h2
  obtain ⟨u, hu⟩ := exists_hornGlue (X := E) (i := i)
    (fun j hj => faceSimplex f j hj) (faceCompat_of_hornMorphism f)
  have hpu : p.comp u = v.comp (hornIncl (n + 1) i) := by
    refine comp_hornIncl_eq_of_faces (p.comp u) v fun j hj => ?_
    rw [ContinuousMap.comp_assoc, hu j hj, hface j hj]
  obtain ⟨F, hF, hFu⟩ := relHLP_horn p hfib n i v u hpu
  have hFu' : F.comp (hornIncl (n + 1) i) = u := hFu
  refine CommSq.HasLift.mk ⟨CommSq.LiftStruct.mk ((morphSimplex (n + 1) E).symm F) ?_ ?_⟩
  · refine SSet.horn.hom_ext' fun j hj => ?_
    rw [SSet.horn.ι_ι_assoc]
    apply (morphSimplex n E).injective
    rw [morphSimplex_δ,
      show (morphSimplex (n + 1) E) ((morphSimplex (n + 1) E).symm F) = F from
        Equiv.apply_symm_apply _ F,
      ← hornIncl_comp_faceIncl n i j hj, ← ContinuousMap.comp_assoc, hFu', hu j hj]
    rfl
  · apply (morphSimplex (n + 1) B).injective
    rw [show ((morphSimplex (n + 1) E).symm F) ≫ sSingP p
        = ((morphSimplex (n + 1) E).symm F) ≫ TopCat.toSSet.map (TopCat.ofHom p) from
      congrArg (fun t => ((morphSimplex (n + 1) E).symm F) ≫ t) hsp]
    rw [morphSimplex_comp,
      show (morphSimplex (n + 1) E) ((morphSimplex (n + 1) E).symm F) = F from
        Equiv.apply_symm_apply _ F,
      hF]

/-- **A Serre fibration induces a Kan fibration of singular simplicial sets.**
For `p : E → B` with the homotopy lifting property for all cubes
(`Work.StemsB.IsSerreFibration`), the induced map
`Work.SSS.sSingP p : sSing E ⟶ sSing B` of singular simplicial sets is a Kan fibration
(a `HomotopicalAlgebra.Fibration` for the Quillen (Kan) fibration structure on `SSet`,
whose fibrations are the maps with the right lifting property against horn inclusions
`Λ[n,i] ⟶ Δ[n]`).

Suggested route: it suffices to check the right lifting property against horn inclusions
(`SSet.fibration_iff`, `SSet.horn.IsCompatible.exists_lift`).  Spelling out the horn
lifting problem in the explicit description of singular simplices
(`TopCat.toSSetObjEquivT`), it becomes the topological statement: given a continuous map
`v : |Δⁿ| → B` and a continuous lift `u` of `v` restricted to the topological horn
`{q : stdSimplex ℝ (Fin (n+1)) | ∃ j ≠ i, q j = 0}` (the simplex boundary with the
interior of the `i`-th face removed), extend `u` to a lift of `v` on the whole simplex.
That is the homotopy lifting property of `p` with respect to the pair
`(|Δⁿ|, |Λ[n,i]|)`.  This pair has the "cup" shape: its complement in `|Δⁿ|` is the
interior of a single `(n-1)`-face, so it can be deduced from `Work.StemsB.HasHLPRel`
(the relative cube HLP, proved in-tree from `hfib`) together with the description of the
pair as a cone: taking the face opposite a vertex `i` of `|Δⁿ|`, one has
`|Δⁿ| = C(F)`, `F := |Δⁿ⁻¹|`, and `|Λ[n,i]| = C(∂F)` with the cone points adjoined.  The
file `Submission/Work/StemsB/kanComplex_singularSet.lean` treats the case `B` = a point
and contains useful lemmas about the topological horn (in particular a continuous
retraction of the simplex onto the horn fixing the horn pointwise). -/
theorem singularFibration {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) :
    HomotopicalAlgebra.Fibration (Work.SSS.sSingP p) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro X Y g hg
  rw [SSet.modelCategoryQuillen.J] at hg
  rw [MorphismProperty.iSup_iff] at hg
  obtain ⟨n, hgn⟩ := hg
  rw [MorphismProperty.ofHoms_iff] at hgn
  obtain ⟨i, hi⟩ := hgn
  exact (HasLiftingProperty.iff_of_arrow_iso_left (eqToIso hi.symm) (Work.SSS.sSingP p)).mp
    (hornLift p hfib n i)

end

end Work.SSS
