import Mathlib
import Submission.Work.Kunneth.TensorCo
import Submission.Work.Kunneth.Tensor
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.ctensAux
import Submission.Work.Kunneth.TpDualCompat

/-!
# The duality `(tpC C (sumShift M))^* ≅ ctens C^* (M^*)`

For a chain complex `C` of `ℤ`-modules and a family of finite free `ℤ`-modules `M q`, the `ℤ`-dual
of the tensor product chain complex `tpC C (sumShift M)` is isomorphic, as a cochain complex, to
`ctens (dualComplex ℤ C) (homDual M)`: degreewise this is the hom-tensor adjunction together with
the fact that `(A ⊗ N)^* ≅ A^* ⊗ N^*` for `N` finite free
(`Work.Kunneth.dualDistribEquivRight`), and the differentials match because the Koszul sign is
killed by the zero differential of `sumShift M` (`Work.Kunneth.ctensD_tpDualEquiv`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

set_option backward.isDefEq.respectTransparency false

theorem ctens_dual_tpC (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (hM : ∀ q, Module.Free ℤ ↥(M q)) (hMf : ∀ q, Module.Finite ℤ ↥(M q)) :
    Nonempty (CategoryTheory.Iso
      (Work.Cohomology.dualComplex ℤ (Work.Kunneth.tpC C (Work.Kunneth.sumShift M)))
      (Work.Kunneth.ctens (Work.Cohomology.dualComplex ℤ C) (Work.Kunneth.homDual M))) := by
  haveI := hM
  haveI := hMf
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun n => (tpDualEquiv C M n).toModuleIso) ?_⟩
  intro n m hnm
  rw [ComplexShape.up_Rel] at hnm
  have hmn : m = n + 1 := hnm.symm
  subst hmn
  apply ModuleCat.hom_ext
  ext f
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ctens_d_hom, dualComplex_d_hom,
    tpC_d, ModuleCat.hom_ofHom, LinearEquiv.toModuleIso_hom]
  show ctensD (Work.Cohomology.dualComplex ℤ C) (homDual M) n (tpDualEquiv C M n f)
    = tpDualEquiv C M (n + 1) (f.comp (tpD C (sumShift M) n))
  exact ctensD_tpDualEquiv C M n f

end

end Work.Kunneth
