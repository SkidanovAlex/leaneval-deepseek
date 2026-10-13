import Mathlib
import ChallengeDeps
import Submission.Work.DSF1.Sheaf.exists_cechSheafPresheaf
import Submission.Work.DSF1.Cech.exists_cechZ_lift

/-!
# The coaugmentation of the sheaf-level Čech complex (DSF1)

Let `X` be a scheme, `U : ι → X.Opens` a family of opens and

`K = (cechComplexFunctor U).obj (cechSheafPresheaf X) : CochainComplex X.Modules ℕ`

the sheaf-level Čech complex whose degree-`n` term is the product of the sheaves
`secSheaf (U (x 0) ⊓ ⋯ ⊓ U (x n))` over `x : Fin (n+1) → ι`.  This file defines the
*coaugmentation*

`cechSheafCoaug U : (single₀ X.Modules).obj (secSheaf ⊤) ⟶ K`,

the chain map whose degree-`0` component is the product of the restriction maps
`secSheaf ⊤ ⟶ secSheaf (U i)` (equivalently the unit of the adjunction
`restrictFunctor ⊣ pushforward` at the structure sheaf).  That such a chain map exists is exactly
the statement that the alternating sum of the cofaces kills a constant section, which is
`Work.DSF1.Cech.cechComplex_coaug_isCycle`; the chain map is then produced by the universal
property `CochainComplex.fromSingle₀Equiv` of `single₀`.

The coaugmentation is used in the assembly of area `F1` in two ways:

* `Work.DSF1.Cech.cechSheafCoaug_quasiIso`: for a **covering** family `U`, the coaugmentation is
  a quasi-isomorphism -- the sheaf-level Čech complex is a resolution of the structure sheaf.
  (The vanishing of the positive-degree homology is proved in
  `Submission/Work/DSF1/Sheaf/cechSheafPresheaf_homology_vanishing.lean`; what is needed here is
  the exactness in degree `0`, i.e. the sheaf condition for the cover `U`.)
* `Work.DSF1.Cech.cechSheafCoaug_f_zero`: the component formula, used to identify the degree-`0`
  component of the challenge's Čech coaugmentation `DSMap.coaug0`.
-/

namespace Work.DSF1.Cech

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}

/-- The coaugmentation `𝒪_X ⟶ Č⁰` of the sheaf-level Čech complex of `U`, as a chain map
`(single₀ X.Modules).obj 𝒪_X ⟶ (cechComplexFunctor U).obj (cechSheafPresheaf X)`.

Its degree-`0` component is `Pi.lift (fun x => P.map ((isTerminalTop.from _).op))`, the product of
the restriction maps `𝒪_X ⟶ (U (x 0))_* 𝒪`; the chain map exists because this map is killed by
the Čech differential (`Work.DSF1.Cech.cechComplex_coaug_isCycle`). -/
noncomputable def cechSheafCoaug (U : ι → X.Opens) :
    (CochainComplex.single₀ X.Modules).obj
        ((Work.DSF1.Sheaf.cechSheafPresheaf X).obj (Opposite.op ⊤)) ⟶
      ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Sheaf.cechSheafPresheaf X) : CochainComplex X.Modules ℕ) :=
  (CochainComplex.fromSingle₀Equiv
      ((CategoryTheory.cechComplexFunctor U).obj (Work.DSF1.Sheaf.cechSheafPresheaf X))
      ((Work.DSF1.Sheaf.cechSheafPresheaf X).obj (Opposite.op ⊤))).symm
    ⟨Pi.lift (fun x : Fin 1 → ι =>
      (Work.DSF1.Sheaf.cechSheafPresheaf X).map
        ((isTerminalTop (α := X.Opens)).from (∏ᶜ (U ∘ x))).op),
      Work.DSF1.Cech.cechComplex_coaug_isCycle (Work.DSF1.Sheaf.cechSheafPresheaf X)
        (isTerminalTop (α := X.Opens)) U⟩

/-- The degree-`0` component of the coaugmentation is the product of the restriction maps. -/
lemma cechSheafCoaug_f_zero (U : ι → X.Opens) :
    (cechSheafCoaug U).f 0 =
      Pi.lift (fun x : Fin 1 → ι =>
        (Work.DSF1.Sheaf.cechSheafPresheaf X).map
          ((isTerminalTop (α := X.Opens)).from (∏ᶜ (U ∘ x))).op) := by
  simp only [cechSheafCoaug]
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end Work.DSF1.Cech
