import Mathlib
import Submission.Work.Thom.Coh_zero_cover_injective

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

open Work.TangentClasses CategoryTheory CategoryTheory.Limits

namespace Work.Thom

variable {X : Type} [TopologicalSpace X] {ι : Type}

/-- **A class of `H⁰` killed by restriction to the members of a cover is zero**, with the cover
indexed by an arbitrary type `ι` (the same statement as `Work.Thom.Coh_zero_cover_injective`,
which is the case `ι = Fin N`; the proof is identical, `Fin N` playing no role -- copy that proof
body verbatim and keep the file-level `set_option backward.isDefEq.respectTransparency false`,
which the `rw [h j, map_zero] at hnat` step needs). -/
theorem Coh_zero_cover_injective_gen (V : ι → Set X) (hV : ∀ j, IsOpen (V j))
    (hcov : ∀ x : X, ∃ j, x ∈ V j) (x : Work.Thom.Coh ℤ 0 X)
    (h : ∀ j, (Work.Thom.CohMap (Work.Thom.subtypeMap (V j)) ℤ 0).hom x = 0) : x = 0 := by
  refine h0Ev_eq_zero x (fun s => ?_)
  -- the point underlying the `0`-simplex `s`, and a member of the cover containing it
  set p : X := TopCat.toSSetObj₀Equiv s with hp
  obtain ⟨j, hpj⟩ := hcov p
  -- the `0`-simplex of `V j` lying over `p`
  set s' : (TopCat.toSSet.obj (TopCat.of ↥(V j))).obj (Opposite.op (SimplexCategory.mk 0)) :=
    TopCat.toSSetObj₀Equiv.symm (⟨p, hpj⟩ : ↥(V j)) with hs'
  -- it is mapped to `s` by the inclusion `V j ↪ X`
  have himg : (ConcreteCategory.hom ((TopCat.toSSet.map (TopCat.ofHom (subtypeMap (V j)))).app
      (Opposite.op (SimplexCategory.mk 0)))) s' = s := by
    apply TopCat.toSSetObj₀Equiv.injective
    rw [toSSetObj₀Equiv_map]
    rw [hs', Equiv.apply_symm_apply]
    exact hp
  -- naturality of the evaluation, and the hypothesis that `x` restricts to `0` on `V j`
  have hnat := h0Ev_pullback (subtypeMap (V j)) s' x
  rw [h j, map_zero] at hnat
  rw [himg] at hnat
  exact hnat.symm

namespace Work.Thom

/-- The same statement under the doubly-nested name, as a courtesy alias. -/
theorem Coh_zero_cover_injective_gen (V : ι → Set X) (hV : ∀ j, IsOpen (V j))
    (hcov : ∀ x : X, ∃ j, x ∈ V j) (x : Work.Thom.Coh ℤ 0 X)
    (h : ∀ j, (Work.Thom.CohMap (Work.Thom.subtypeMap (V j)) ℤ 0).hom x = 0) : x = 0 :=
  _root_.Work.Thom.Coh_zero_cover_injective_gen V hV hcov x h

end Work.Thom

end Work.Thom
