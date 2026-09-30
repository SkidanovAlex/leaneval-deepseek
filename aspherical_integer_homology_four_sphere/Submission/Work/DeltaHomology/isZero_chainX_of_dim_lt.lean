import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.Chain
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology Work.DeltaHomology

noncomputable section

/-- A coproduct over an empty index type is a zero object: the cocone given by the
universal property is a colimit of an empty diagram, hence its point is an initial
object, so any two endomorphisms of it coincide and `𝟙 = 0`. -/
theorem isZero_coproduct_of_isEmpty {C : Type*} [Category* C] [HasZeroMorphisms C]
    {β : Type*} [IsEmpty β] (f : β → C) [HasCoproduct f] : IsZero (∐ f) := by
  let c : Cofan f := Cofan.mk (∐ f) (Sigma.ι f)
  have hcolim : IsColimit c := coproductIsCoproduct f
  have hinit : IsInitial (∐ f) := (isColimitEquivIsInitialOfIsEmpty C c) hcolim
  exact (IsZero.iff_id_eq_zero (∐ f)).mpr (hinit.hom_ext _ _)

/-- The `Δ`-chain complex of a finite `Δ`-complex is concentrated in degrees `≤ K.dim`: above the dimension the chain group `K.chainX k = ∐ (fun _ : Fin (K.card k) => ℤ)` is the coproduct over the empty index type (`K.card_eq_zero k h : K.card k = 0`), hence the zero object of `ModuleCat ℤ`. Note: `K.chainX k` is an `abbrev` for the coproduct and is not defeq to a Pi type; the empty coproduct's being initial (hence zero) has to be transported across `Fin (K.card k) ≃ Fin 0` (e.g. `finCongr`, `Sigma.whiskerEquiv`/`Sigma.mapIso`), and `infer_instance` will not find it directly. -/
theorem isZero_chainX_of_dim_lt (K : DeltaCx) {k : ℕ} (h : K.dim < k) :
    IsZero (K.chainX k) := by
  have hcard : K.card k = 0 := K.card_eq_zero k h
  have hiso : K.chainX k ≅ ∐ (fun _ : Fin 0 => Work.Homology.ZMod) :=
    Sigma.whiskerEquiv (f := fun _ : Fin (K.card k) => Work.Homology.ZMod)
      (g := fun _ : Fin 0 => Work.Homology.ZMod) (finCongr hcard) (fun _ => Iso.refl _)
  exact IsZero.of_iso (isZero_coproduct_of_isEmpty (fun _ : Fin 0 => Work.Homology.ZMod)) hiso

end

end Work.DeltaHomology
