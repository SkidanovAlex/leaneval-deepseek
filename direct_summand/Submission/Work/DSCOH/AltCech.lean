/-
Area DSCOH (curric-46) — the *geometric* alternating Čech complex of a family of opens.

The frozen `DSMap.cech A X f U` of the challenge is Mathlib's `cechComplexFunctor`, i.e. the
product over **all** functions `Fin (q+1) → ι` (tuples *with repetitions*).  The chart Čech complex
`Work.DSCOH.chartCech` of this area, and the geometric complex the bridge needs, are instead
indexed by the **subsets** of `ι`: this file defines that complex, so that the quasi-isomorphism
between the two shapes (the normalized/unnormalized Čech comparison) can be stated.

`altCechDiff` is its alternating differential; the lemma
`Work.DSCOH.altCechDiff_comp` proves that it squares to zero, after which `altCech` is a cochain
complex of `A`-modules.
-/
import Mathlib

open CategoryTheory

namespace Work.DSCOH

variable {X : Type*} [TopologicalSpace X]
variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The `q`-th term of the alternating Čech complex of a family of opens `U` with coefficients in
a presheaf `P` of `A`-modules: the product, over the `(q+1)`-element subsets `S` of the index set,
of the sections of `P` over the intersection `⋂_{i ∈ S} U i`. -/
abbrev AltCechTerm (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (q : ℕ) : Type _ :=
  ∀ S : {S : Finset ι // S.card = q + 1}, P.obj (Opposite.op (S.1.inf U))

/-- The alternating Čech differential: its `T`-component is the alternating sum, over the elements
`i` of `T`, of the restriction from the `(T.erase i)`-component, with sign `(-1)^{#{j ∈ T : j < i}}`
(the standard alternating convention for the alternating Čech complex). -/
noncomputable def altCechDiff (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (q : ℕ) :
    AltCechTerm P U q →ₗ[A] AltCechTerm P U (q + 1) :=
  LinearMap.pi (R := A) fun T =>
    ∑ i ∈ T.1.attach,
      (-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card •
        ((P.map ((homOfLE (Finset.le_inf fun k hk =>
          Finset.inf_le (Finset.mem_of_mem_erase hk))).op)).hom.comp
          (LinearMap.proj (R := A)
            (φ := fun S : {S : Finset ι // S.card = q + 1} =>
              P.obj (Opposite.op (S.1.inf U)))
            ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩))

end Work.DSCOH
