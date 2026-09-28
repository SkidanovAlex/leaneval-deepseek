import Mathlib
import Submission.Work.Kunneth.Basic
import Submission.Work.Kunneth.AWAux
import Submission.Work.Kunneth.awKey
import Submission.Work.Kunneth.awDec

/-!
# The Alexander–Whitney map is a chain map

`Work.Kunneth.awHom X Y n : C_n(X ⊗ Y) ⟶ ⨁_{p+q=n} C_p(X) ⊗_ℤ C_q(Y)` is the Alexander–Whitney
map of `Submission/Work/Kunneth/Basic.lean`.  This file proves that it commutes with the
differentials, i.e. that it is a chain map `C_*(X ⊗ Y) ⟶ C_*(X) ⊗_ℤ C_*(Y)`.

The proof checks the identity on generators of `C_{n+1}(X ⊗ Y)`: for an `(n+1)`-simplex `z`,
* `awDecU` identifies the Koszul differential of the Alexander–Whitney chain of `z` with the sum
  `∑_{a} tpLof ⟨(a, n+1-(a+1))⟩ (awU a)` of its `(a, n-a)`-components;
* `awDecV` identifies the Alexander–Whitney chain of the boundary `∂z` with the same sum, with the
  components `awV` of the boundary;
* `awKey` says that these components agree, `awU = awV`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

theorem awHom_d (X Y : SSet) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Kunneth.awHom X Y (n + 1))
        ((Work.Kunneth.tChain X Y).d (n + 1) n)
      = CategoryTheory.CategoryStruct.comp ((Work.Kunneth.sChain (Work.Kunneth.sProd X Y)).d (n + 1) n)
          (Work.Kunneth.awHom X Y n) := by
  apply SSet.chainComplex_hom_ext
  intro z
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  rw [tpC_d]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_comp]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [ModuleCat.hom_ofHom]
  have hgc : ∀ (m : ℕ) (w : (X ⊗ Y) _⦋m⦌),
      ModuleCat.Hom.hom ((X ⊗ Y).ιChainComplex (R := zz) w) 1 = genCh (X ⊗ Y) w := fun m w => rfl
  rw [hgc (n+1) z]
  have hgen : ∀ (m : ℕ) (w : (X ⊗ Y) _⦋m⦌),
      ModuleCat.Hom.hom (awHom X Y m) (genCh (X ⊗ Y) w) = (awGen X Y m w).hom 1 := by
    intro m w
    have h := congrArg (fun (g : zz ⟶ (tChain X Y).X m) => ModuleCat.Hom.hom g 1) (awHom_gen X Y m w)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  rw [hgen (n+1) z]
  have hd : ModuleCat.Hom.hom ((sChain (sProd X Y)).d (n+1) n) (genCh (X ⊗ Y) z)
      = ∑ k : Fin (n+2), (-1:ℤ)^(k:ℕ) • genCh (X ⊗ Y) ((X ⊗ Y).δ k z) :=
    d_genCh (X ⊗ Y) n z
  rw [hd]
  have hR : ModuleCat.Hom.hom (awHom X Y n)
        (∑ k : Fin (n+2), (-1:ℤ)^(k:ℕ) • genCh (X ⊗ Y) ((X ⊗ Y).δ k z))
      = ∑ k : Fin (n+2), (-1:ℤ)^(k:ℕ) • (awGen X Y n ((X ⊗ Y).δ k z)).hom 1 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact (map_zsmul (ModuleCat.Hom.hom (awHom X Y n)) ((-1:ℤ)^(k:ℕ))
        (genCh (X ⊗ Y) ((X ⊗ Y).δ k z))).trans
      (congrArg (fun u => (-1:ℤ)^(k:ℕ) • u) (hgen n ((X ⊗ Y).δ k z)))
  rw [hR]
  exact (awDecU X Y n z).trans ((Finset.sum_congr rfl (fun (a : Fin (n+1)) _ =>
      congrArg (fun u => tpLof (sChain X) (sChain Y) n ⟨(a.val, n+1-(a.val+1)), by omega⟩ u)
        (awKey X Y n z.1 z.2 a))).trans (awDecV X Y n z).symm)

end

end Work.Kunneth
