/-
AREA RESOL — the homotopy category functor `hq` preserves small coproducts.

`hq : Cpx ⥤ KCat` is the localization of cochain complexes of light condensed abelian
groups at the homotopy equivalences.  The main result of this file is

`hq_coproduct_bijective` : for a family `K : J → Cpx` of complexes with a coproduct, the
canonical map

  `Hom_{KCat}(hq (∐ K), Y) ⟶ ∏ j, Hom_{KCat}(hq (K j), Y),  f ↦ (hq (ι j) ≫ f) j`

is a bijection, i.e. `hq (∐ K)` is the coproduct of the `hq (K j)` in the homotopy category.

The proof rests on the following observation.  Since coproducts in `Cpx` are computed
degreewise (`(∐ K).X i` is the coproduct of the `(K j).X i`, see
`HomologicalComplex.isColimitCoconeOfHasColimitEval` and the instances from
`Submission.Work.RESOL.SigmaSetup`), a map `g : ∐ K ⟶ Y` is null-homotopic as soon as all
its components `ι j ≫ g` are: the homotopy is assembled degreewise out of the component
homotopies.  This is `homotopy_of_components`, the technical heart of the file.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.SigmaSetup

open CategoryTheory Limits LightProfinite LightCondensed
open HomologicalComplex

noncomputable section

namespace Work.RESOL

variable {J : Type}

/-- The quotient functor `Cpx ⥤ KCat` (the localization at homotopy equivalences). -/
abbrev qF : Cpx ⥤ KCat := HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)

/-- **The plumbing lemma.**  If every component `ι j ≫ g` of a map `g : ∐ K ⟶ Y` out of a
coproduct of complexes is null-homotopic, then `g` is null-homotopic.

The homotopy is built degreewise: in degree `i` the map `(∐ K).X i ⟶ Y.X k` is the descent
of the family of components `(ι j ≫ g)` along the coproduct `(∐ K).X i = ∐ j, (K j).X i`. -/
def homotopy_of_components (K : J → Cpx) [HasCoproduct K] {Y : Cpx}
    (g : (∐K) ⟶ Y) (h : ∀ j, Homotopy (Limits.Sigma.ι K j ≫ g) 0) : Homotopy g 0 := by
  let F := Discrete.functor K
  let c : ∀ i : ℤ, Cocone (F ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) i) :=
    fun i => (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) i).mapCocone (colimit.cocone F)
  have hc : ∀ i, IsColimit (c i) := fun i => isColimitOfPreserves _ (colimit.isColimit F)
  let Hhom : ∀ i k, (∐K).X i ⟶ Y.X k := fun i k =>
    IsColimit.desc (hc i) (Cocone.mk (Y.X k) (Discrete.natTrans (fun j => (h j.as).hom i k)))
  have Hfac : ∀ i k (j : Discrete J), (c i).ι.app j ≫ Hhom i k = (h j.as).hom i k := fun i k j => by
    show (c i).ι.app j ≫ IsColimit.desc (hc i) (Cocone.mk (Y.X k)
      (Discrete.natTrans (fun j => (h j.as).hom i k))) = (h j.as).hom i k
    rw [IsColimit.fac]
    simp [Discrete.natTrans_app]
  have Hfac' : ∀ i k j, (Limits.Sigma.ι K j).f i ≫ Hhom i k = (h j).hom i k := fun i k j => by
    rw [show (Limits.Sigma.ι K j).f i = (c i).ι.app (Discrete.mk j) from rfl]
    exact Hfac i k (Discrete.mk j)
  have hdN : ∀ i, dNext i Hhom = (∐K).d i ((ComplexShape.up ℤ).next i) ≫ Hhom _ i := fun i => rfl
  have hprev : ∀ i, prevD i Hhom =
      Hhom i ((ComplexShape.up ℤ).prev i) ≫ Y.d ((ComplexShape.up ℤ).prev i) i := fun i => rfl
  have hnext2 : ∀ i (j : Discrete J),
      (c i).ι.app j ≫ dNext i Hhom = dNext i (h j.as).hom := fun i j => by
    rw [hdN i, show dNext i (h j.as).hom =
        (K j.as).d i ((ComplexShape.up ℤ).next i) ≫ (h j.as).hom _ i from rfl]
    rw [show (c i).ι.app j = (Limits.Sigma.ι K j.as).f i from rfl]
    rw [← Category.assoc, Hom.comm (Limits.Sigma.ι K j.as) i ((ComplexShape.up ℤ).next i),
      Category.assoc, Hfac']
  have hprev2 : ∀ i (j : Discrete J),
      (c i).ι.app j ≫ prevD i Hhom = prevD i (h j.as).hom := fun i j => by
    rw [hprev i, show prevD i (h j.as).hom =
        (h j.as).hom i ((ComplexShape.up ℤ).prev i) ≫ Y.d ((ComplexShape.up ℤ).prev i) i from rfl]
    rw [show (c i).ι.app j = (Limits.Sigma.ι K j.as).f i from rfl]
    rw [← Category.assoc, Hfac']
  refine ⟨Hhom, ?_, ?_⟩
  · intro i k hki
    apply IsColimit.hom_ext (hc i)
    intro j
    rw [Hfac i k j, comp_zero]
    exact (h j.as).zero i k hki
  · intro i
    simp only [HomologicalComplex.zero_f, add_zero]
    apply IsColimit.hom_ext (hc i)
    intro j
    rw [Preadditive.comp_add, hnext2, hprev2]
    rw [show (c i).ι.app j ≫ g.f i = ((Limits.Sigma.ι K j.as) ≫ g).f i from rfl]
    simpa using (h j.as).comm i

/-- The map induced by the coprojections of `∐ K` on `Hom` into a fixed object of `KCat`. -/
def hqCoproductMap (K : J → Cpx) [HasCoproduct K] (Y : KCat) :
    (qF.obj (∐K) ⟶ Y) → ((j : J) → qF.obj (K j) ⟶ Y) :=
  fun f j => qF.map (Limits.Sigma.ι K j) ≫ f

set_option backward.isDefEq.respectTransparency false
/-- **`hq` preserves small coproducts.**  For a family `K : J → Cpx` with a coproduct, the
object `hq (∐ K)` of the homotopy category is the coproduct of the objects `hq (K j)`, with
coprojections `hq (ι j)`. -/
theorem hq_coproduct_bijective (K : J → Cpx) [HasCoproduct K] (Y : KCat) :
    Function.Bijective (hqCoproductMap K Y) := by
  constructor
  · intro f f' hff
    -- it suffices to show that a map all of whose components vanish is zero
    have key : ∀ φ : qF.obj (∐K) ⟶ Y,
        (∀ j, qF.map (Limits.Sigma.ι K j) ≫ φ = 0) → φ = 0 := by
      intro φ hφ
      let g : (∐K) ⟶ Y.as := φ.out
      have hg : qF.map g = φ := HomotopyCategory.quotient_map_out φ
      have hzero : ∀ j, qF.map (Limits.Sigma.ι K j ≫ g) = 0 := fun j => by
        rw [Functor.map_comp, hg, hφ j]
      have hcomp : ∀ j, Nonempty (Homotopy (Limits.Sigma.ι K j ≫ g) 0) := fun j =>
        (HomotopyCategory.quotient_map_eq_zero_iff _).mp (hzero j)
      have hg0 : φ = 0 := by
        rw [← hg]
        exact (HomotopyCategory.quotient_map_eq_zero_iff g).mpr
          ⟨homotopy_of_components K g fun j => (hcomp j).some⟩
      exact hg0
    have hsub : ∀ j, qF.map (Limits.Sigma.ι K j) ≫ (f - f') = 0 := fun j => by
      rw [Preadditive.comp_sub, sub_eq_zero]
      exact congrFun hff j
    have : f - f' = 0 := key _ hsub
    exact sub_eq_zero.mp this
  · intro x
    -- build the map out of the coproduct from representatives of the components
    let g : (∐K) ⟶ Y.as := IsColimit.desc (colimit.isColimit (Discrete.functor K))
      (Cocone.mk Y.as (Discrete.natTrans (fun j => (x j.as).out)))
    refine ⟨qF.map g, ?_⟩
    funext j
    have hfac : Limits.Sigma.ι K j ≫ g = (x j).out := by
      show (colimit.cocone (Discrete.functor K)).ι.app (Discrete.mk j) ≫ _ = _
      rw [IsColimit.fac]
      simp [Discrete.natTrans_app]
    show qF.map (Limits.Sigma.ι K j) ≫ qF.map g = x j
    rw [← qF.map_comp, hfac]
    exact HomotopyCategory.quotient_map_out _

end Work.RESOL
