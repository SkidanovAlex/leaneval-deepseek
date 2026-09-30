import Mathlib
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Core.section_prime_sup_fibre_quot
import Submission.Work.SpecLin.Alt.sup_eq_of_le_maximal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Alt

universe u

open scoped TensorProduct

/-- In the affine chart, if the section prime `I_m` and the fibre prime `P` are both contained in
a maximal ideal `N`, then `I_m ⊔ P = N`: the section meets the special fibre in a single reduced
point, so the only maximal ideal above both is the section's specialisation. -/
theorem sectionPrime_sup_fibrePrime_eq_of_le {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (φ : C.left.presheaf.obj (Opposite.op W) →ₐ[K] R)
    (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W ≤ N)
    (hIN : Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ ≤ N) :
    Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ ⊔
      Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N := by
  -- The sum `I_m ⊔ P` is the kernel of the residue evaluation `B → κ`, hence its quotient is
  -- isomorphic to the residue field `κ` of `R`: in particular it is a *maximal* ideal.
  have hfield : IsField (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W ⧸
      (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ ⊔
        Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)) :=
    MulEquiv.isField (Field.toIsField _)
      (Work.SpecLin.Core.section_prime_sup_fibre_quot (K := K) (R := R) φ).toMulEquiv
  have hmax : (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ ⊔
      Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ hfield
  -- A maximal ideal containing both `P` and `I_m` is therefore `I_m ⊔ P`, and it is contained in
  -- `N`, which is maximal and proper.
  exact Work.SpecLin.Alt.sup_eq_of_le_maximal hPN hIN hmax

end Work.SpecLin.Alt
