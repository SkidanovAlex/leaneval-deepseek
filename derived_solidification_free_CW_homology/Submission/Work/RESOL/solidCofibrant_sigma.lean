import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.SigmaSetup
import Submission.Work.RESOL.hq_coproduct
import Submission.Work.RESOL.Qh_coproduct_bijective

/-!
AREA RESOL — solid-cofibrant complexes are stable under small coproducts (B4, `sigma`).

The proof is a two-step factorisation of the comparison map
`Φ : Hom_K(hq (∐ K), Y) ⟶ Hom_D(Qh (hq (∐ K)), Qh Y)`, `f ↦ Qh.map f`, where `Y = hq (ιC N)`
for a complex `N` of solid objects:

* `hqCoproductMap`/`hq_coproduct_bijective` decompose `Hom_K(hq (∐ K), Y) = ∏ j, Hom_K(hq (K j), Y)`
  (`hq` preserves the coproduct, proved directly in `RESOL/hq_coproduct.lean`);
* `decB`/`Qh_coproduct_bijective` decompose `Hom_D(Qh (hq (∐ K)), Qh Y) = ∏ j, Hom_D(Qh (hq (K j)), Qh Y)`
  (`Resol/Qh_coproduct_bijective.lean`).

Under these two decompositions, `Φ` becomes the product of the maps
`Φ_j : Hom_K(hq (K j), Y) → Hom_D(Qh (hq (K j)), Qh Y)` given by the hypothesis, so `Φ` is
bijective because the two decompositions and each `Φ_j` are.
-/
open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

namespace Work.RESOL

theorem solidCofibrant_sigma (J : Type) (K : J → Work.RESOL.Cpx)
    [CategoryTheory.Limits.HasCoproduct K]
    (h : ∀ j, Submission.Blueprint.SolidCofibrant (K j)) :
    Submission.Blueprint.SolidCofibrant (∐ K) := by
  intro N
  let Xc : Cpx := Submission.Blueprint.ιC.obj N
  let Y : KCat := qF.obj Xc
  let decA : (qF.obj (∐K) ⟶ Y) → ((j : J) → qF.obj (K j) ⟶ Y) := hqCoproductMap K Y
  let Phi : (qF.obj (∐K) ⟶ Y) →
      (DerivedCategory.Qh.obj (qF.obj (∐K)) ⟶ DerivedCategory.Qh.obj (qF.obj Xc)) :=
    fun f => DerivedCategory.Qh.map f
  let decB : (DerivedCategory.Qh.obj (qF.obj (∐K)) ⟶ DerivedCategory.Qh.obj (qF.obj Xc)) →
      ((j : J) → DerivedCategory.Qh.obj (qF.obj (K j)) ⟶ DerivedCategory.Qh.obj (qF.obj Xc)) :=
    fun g j => DerivedCategory.Qh.map (qF.map (Limits.Sigma.ι K j)) ≫ g
  let prodPhi : ((j : J) → qF.obj (K j) ⟶ Y) →
      ((j : J) → DerivedCategory.Qh.obj (qF.obj (K j)) ⟶ DerivedCategory.Qh.obj (qF.obj Xc)) :=
    fun x j => DerivedCategory.Qh.map (x j)
  have hA : Function.Bijective decA := hq_coproduct_bijective K Y
  have hB : Function.Bijective decB := Qh_coproduct_bijective K Xc
  have hcomp : ∀ f, decB (Phi f) = prodPhi (decA f) := by
    intro f
    funext j
    exact (Functor.map_comp (DerivedCategory.Qh) (qF.map (Limits.Sigma.ι K j)) f).symm
  have hprod_inj : Function.Injective prodPhi := fun x x' H =>
    funext fun j => (h j N).injective (congrFun H j)
  have hprod_surj : Function.Surjective prodPhi := fun y =>
    ⟨fun j => ((h j N).surjective (y j)).choose,
      funext fun j => ((h j N).surjective (y j)).choose_spec⟩
  refine ⟨fun f f' H => ?_, fun g => ?_⟩
  · have H' : prodPhi (decA f) = prodPhi (decA f') := by
      rw [← hcomp f, ← hcomp f']
      exact congrArg decB H
    exact hA.injective (hprod_inj H')
  · obtain ⟨x, hx⟩ : ∃ x, prodPhi x = decB g := hprod_surj (decB g)
    obtain ⟨f, hf⟩ : ∃ f, decA f = x := hA.surjective x
    exact ⟨f, hB.injective (by rw [hcomp f, hf, hx])⟩

end Work.RESOL
