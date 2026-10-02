import Mathlib
import Submission.Work.Kunneth.ModelContr
import Submission.Work.Kunneth.stdS_d_zero
import Submission.Work.Kunneth.stdS_d_succ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The contraction of the chains of the standard simplex

This file assembles the data of `Work.Kunneth.ModelContr` for `C_*(Δ[p])`:
the contraction `stdS p` (from the extra degeneracy of the standard simplex),
the deficiency operator `stdPl p` (the rank-one projection onto the base point in degree `0`),
the degree-`0` identity `stdS_d_zero`, the positive-degree identity `stdS_d_succ`
and the compatibility `stdPl_d` of the deficiency with the differential.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The augmentation kills `1`-boundaries. -/
theorem stdAug_d (p : ℕ) (y : ↥((sChain (SdS p)).X 1)) :
    stdAug p (((sChain (SdS p)).d 1 0).hom y) = 0 := by
  have hgen : ∀ σ : (SdS p) _⦋1⦌,
      stdAug p (((sChain (SdS p)).d 1 0).hom (((SdS p).ιChainComplex (R := zz) σ).hom 1))
        = 0 := by
    intro σ
    rw [chainComplex_d_one_gen (SdS p) σ, map_sub, stdAug_gen, stdAug_gen, sub_self]
  have hzero : ModuleCat.ofHom ((stdAug p).comp (((sChain (SdS p)).d 1 0).hom))
      = (0 : (sChain (SdS p)).X 1 ⟶ zz) := by
    apply SSet.chainComplex_hom_ext (X := SdS p) (R := zz) (n := 1) (T := zz)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
      LinearMap.zero_apply] using hgen σ
  have h2 := congrArg (fun (φ : (sChain (SdS p)).X 1 ⟶ zz) => φ.hom y) hzero
  simpa only [ModuleCat.hom_ofHom, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h2

/-- The deficiency operator of the contraction of `C_*(Δ[p])` is compatible with the
differential. -/
theorem stdPl_d (p pp : ℕ) (x : ↥((sChain (SdS p)).X pp)) :
    ((sChain (SdS p)).d pp (pp-1)).hom (stdPl p pp x)
      + (stdPl p (pp-1)) (((sChain (SdS p)).d pp (pp-1)).hom x) = 0 := by
  rcases Nat.eq_zero_or_pos pp with h | h
  · obtain rfl : pp = 0 := h
    have hd : (sChain (SdS p)).d 0 (0 - 1) = 0 :=
      HomologicalComplex.shape _ _ _ (by simp [ComplexShape.down])
    rw [hd]
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, pp = k + 1 := ⟨pp - 1, by omega⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · obtain rfl : k = 0 := hk
      rw [stdPl_succ p 0]
      simp only [LinearMap.zero_apply, map_zero, zero_add]
      show stdPl p 0 (((sChain (SdS p)).d 1 0).hom x) = 0
      rw [stdPl_zero_apply]
      show (LinearMap.toSpanSingleton ℤ ↥((sChain (SdS p)).X 0) (stdBP p))
        (stdAug p (((sChain (SdS p)).d 1 0).hom x)) = 0
      rw [stdAug_d p x]
      exact map_zero _
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h2 : stdPl p (k' + 1 + 1 - 1) = 0 := stdPl_succ p k'
      rw [stdPl_succ p (k' + 1), h2]
      simp only [LinearMap.zero_apply, map_zero, add_zero]

/-- **The contraction of the chains of the standard simplex.** -/
theorem stdModelContr (p : ℕ) : Nonempty (ModelContr (sChain (SdS p))) :=
  ⟨{ s := stdS p
     P := stdPl p
     s_zero := stdS_d_zero p
     s_succ := fun m x => by
       rw [stdS_d_succ p m x, stdPl_succ p m, LinearMap.zero_apply, sub_zero]
     P_succ := stdPl_succ p
     Pd := stdPl_d p }⟩

end

end Work.Kunneth
