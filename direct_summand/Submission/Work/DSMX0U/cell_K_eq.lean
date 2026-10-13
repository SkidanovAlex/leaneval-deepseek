import Mathlib
import Submission.Work.DSMX0U.Cell

namespace Work.DSMX0U

universe a

theorem cell_K_eq {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0} {q : ℤ}
    (s : Work.DSMX0U.Cell A C c₀ q) (x : ↥s.gen × ↥s.rel) :
    x ∈ s.K A ↔ s.dHom A x = 0 ∧
      s.φHom A x ∈ LinearMap.range (C.d ((q - 1) - 1) (q - 1)).hom := by
  simp only [Cell.K, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply, bdryQ,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end Work.DSMX0U
