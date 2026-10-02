import Mathlib
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.naturalModelClass
import Submission.Work.Thom.step_natural
import Submission.Work.Thom.ProdMapTools
import Submission.Work.Thom.Mn_natural_map

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Naturality of the punctured model class under an arbitrary base change

`Work.Thom.Mpun n B` is the model class of the *punctured* trivial bundle of rank `n` over `B`,
`(B × ℝⁿ, B × (ℝⁿ ∖ 0))`: it is the unique preimage of the sphere-bundle model class `Mn n B`
under the isomorphism `Work.Thom.bijective_jMap B n n` induced by the inclusion of pairs
`(B × ℝⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × (ℝⁿ∖0))` (`Work.Thom.Mpun_spec`).

The files `Submission/Work/Thom/naturalModelClass_punct.lean` and
`Submission/Work/Thom/step_natural.lean` prove the naturality of `Mpun` (and `Mn`) for the
inclusions `↥W × ℝⁿ → B × ℝⁿ` induced by a subset `W ⊆ B`.  Here we prove it for an **arbitrary**
continuous map `g : C(B', B)`: pulling `Mpun n B` back along the base change
`prodMapA g ℝⁿ : B' × ℝⁿ → B × ℝⁿ`, `(b, v) ↦ (g b, v)`, gives `Mpun n B'`.

The proof is a small diagram chase: the two squares `Work.Thom.jMap_comp_prodMapA_punct` and
`Work.Thom.prodMapA_punct_eq_prodMapA_sph_comp_jMap` (of `Submission/Work/Thom/ProdMapTools.lean`)
compute the fibre of the pair-isomorphism in terms of the base change, and the general naturality
`Work.Thom.Mn_natural_map` of the sphere-bundle model class (proved by the same induction as
`Work.Thom.Mn_natural`, with `prodMapA` in place of the inclusion) identifies the result.  Since
`Work.Thom.bijective_jMap B' n n` is injective, this pins the pullback down to `Mpun n B'`.
-/

namespace Work.Thom

open CategoryTheory

theorem Mpun_natural_map {n : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) :
    (Work.Thom.relCohMap
      (⟨fun p : B' × EuclideanSpace ℝ (Fin n) => (g p.1, p.2),
        g.continuous.comp continuous_fst |>.prodMk continuous_snd⟩ :
        C(B' × EuclideanSpace ℝ (Fin n), B × EuclideanSpace ℝ (Fin n)))
      (Work.Thom.Punct B' n) (Work.Thom.Punct B n) (fun _ hp => hp) ℤ n).hom
        (Work.Thom.Mpun n B)
      = Work.Thom.Mpun n B' := by
  show (relCohMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Punct B' n) (Punct B n)
      (fun _ hp => hp) ℤ n).hom (Mpun n B) = Mpun n B'
  -- the isomorphism of the punctured pair with the sphere-bundle pair over `B'` is injective, so
  -- it suffices to compare after applying it
  apply (bijective_jMap B' n n).1
  -- its composite with the base change over `B'` is the base change into the punctured pair ...
  rw [jMap_comp_prodMapA_punct g n (Mpun n B), Mpun_spec n B']
  -- ... and that is the base change into the sphere-bundle pair applied to the image of `Mpun n B`
  rw [prodMapA_punct_eq_prodMapA_sph_comp_jMap g n (Mpun n B), Mpun_spec n B]
  exact Mn_natural_map n g

end Work.Thom
