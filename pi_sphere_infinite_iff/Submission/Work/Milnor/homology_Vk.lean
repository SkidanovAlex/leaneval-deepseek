import Mathlib
import Submission.Work.Milnor.cohomology_Vk
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.homologyMV
import Submission.Work.Cohomology.mvLeft_zero_injective

/-!
# The homology of the total space `Vk k` of Milnor's bundle `ξ`

`Submission.Milnor.Vk k` is the total space of the rank-`4` real vector bundle `ξ` over `S⁴`
(the disc bundle), realised by gluing two copies of `MSpace8 = ℝ⁴ × ℍ` along `{x ≠ 0}`.
Since `ξ` is a vector bundle over `S⁴`, `Vk k` is homotopy equivalent to `S⁴`, so its singular
homology with `ℤ` coefficients is `ℤ` in degrees `0` and `4` and vanishes in every other degree.

This is the homology counterpart of `Work.Milnor.cohomology_Vk`, and it is proved in exactly the
same way: Mayer–Vietoris for the open cover of `Vk k` by the two chart images
`U = range ιX` and `V = range ιY`.  Both are contractible (they are homeomorphic to
`MSpace8`), they cover `Vk k`, and their intersection `U ∩ V` is the gluing region, homotopy
equivalent to `S³` (`Work.Milnor.homotopyEquiv_inter_sphere`).  Hence

* `H₀(Vk k) = ℤ`, since `Vk k` is path connected (`Work.Milnor.pathConnectedSpace_Vk`);
* `H₁(Vk k) = 0`, because `H₀(U ∩ V) → H₀(U) ⊞ H₀(V)` is injective for a path connected
  intersection (`Work.Cohomology.mvLeft_zero_injective`);
* the connecting map `H_{n+1}(Vk k) → H_n(U ∩ V)` is an isomorphism for `n ≥ 1`
  (`Work.Cohomology.mvδX_isIso`), so `H₄(Vk k) ≅ H₃(S³) ≅ ℤ`
  (`Work.Cohomology.sphereHomologyTop`) and `Hₙ(Vk k) = 0` for `n ≥ 2`, `n ≠ 4`
  (`Work.Cohomology.sphereHomologyZero`).
-/

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Limits

namespace Work.Milnor

noncomputable section

theorem homology_Vk (k : ℤ) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of (Submission.Milnor.Vk k))).homology n ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0)) → ℤ)) := by
  haveI hpc : PathConnectedSpace ↥(TopCat.of (Submission.Milnor.Vk k)) :=
    Work.Milnor.pathConnectedSpace_Vk k
  haveI hpcI : PathConnectedSpace
      ↥((Set.range (Submission.Milnor.vData k).ιX : Set (TopCat.of (Submission.Milnor.Vk k))) ∩
        (Set.range (Submission.Milnor.vData k).ιY : Set (TopCat.of (Submission.Milnor.Vk k)))) :=
    Work.Milnor.pathConnectedSpace_inter_Vk k
  haveI hcX : ContractibleSpace ↥(Set.range (Submission.Milnor.vData k).ιX) :=
    Work.Milnor.contractibleSpace_range_ιX k
  haveI hcY : ContractibleSpace ↥(Set.range (Submission.Milnor.vData k).ιY) :=
    Work.Milnor.contractibleSpace_range_ιY k
  have hU : IsOpen (Set.range (Submission.Milnor.vData k).ιX : Set (TopCat.of (Submission.Milnor.Vk k))) :=
    (Submission.Milnor.vData k).isOpenMap_ιX.isOpen_range
  have hV : IsOpen (Set.range (Submission.Milnor.vData k).ιY : Set (TopCat.of (Submission.Milnor.Vk k))) :=
    (Submission.Milnor.vData k).isOpenMap_ιY.isOpen_range
  have hcov : (Set.range (Submission.Milnor.vData k).ιX : Set (TopCat.of (Submission.Milnor.Vk k))) ∪
      (Set.range (Submission.Milnor.vData k).ιY : Set (TopCat.of (Submission.Milnor.Vk k))) = Set.univ :=
    (Submission.Milnor.vData k).range_ιX_union_range_ιY
  rcases eq_or_ne n 0 with rfl | hn0
  · -- degree `0`: `H₀ = ℤ`, since `Vk k` is path connected
    have hfin : (if (0 : ℕ) = 0 then 1 else 0) + (if (0 : ℕ) = 4 then 1 else 0) = 1 := by
      norm_num
    rw [hfin]
    exact ⟨CategoryTheory.asIso (TopCat.singularHomology₀ε (TopCat.of (Submission.Milnor.Vk k))
        (ModuleCat.of ℤ ℤ)) ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · rcases eq_or_ne n 1 with rfl | hn1
    · -- degree `1`: the connecting map embeds `H₁` into `H₀(U ∩ V)`, and
      -- `H₀(U ∩ V) → H₀(U) ⊞ H₀(V)` is injective because `U ∩ V` is path connected
      have hfin : (if (1 : ℕ) = 0 then 1 else 0) + (if (1 : ℕ) = 4 then 1 else 0) = 0 := by
        norm_num
      rw [hfin]
      have hB : IsZero (Work.Cohomology.HBiprod (X := TopCat.of (Submission.Milnor.Vk k))
          (Set.range (Submission.Milnor.vData k).ιX)
          (Set.range (Submission.Milnor.vData k).ιY) 1) :=
        Work.Cohomology.isZero_HBiprod _ _ 1 le_rfl
      have hl : Mono (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft
          (X := TopCat.of (Submission.Milnor.Vk k))
          (Set.range (Submission.Milnor.vData k).ιX)
          (Set.range (Submission.Milnor.vData k).ιY)) 0) :=
        (ModuleCat.mono_iff_injective _).mpr (Work.Cohomology.mvLeft_zero_injective _ _)
      haveI hz1 : IsZero
          ((Work.Cohomology.singularChains ℤ (TopCat.of (Submission.Milnor.Vk k))).homology 1) :=
        IsZero.of_iso (Work.Cohomology.mvH_one_isZero _ _ hB hl)
          (Work.Cohomology.smallIso _ _ hU hV hcov 1).symm
      exact ⟨IsZero.iso hz1 (ModuleCat.isZero_of_subsingleton _)⟩
    · rcases eq_or_ne n 4 with rfl | hn4
      · -- degree `4`: Mayer–Vietoris and `H₃(S³) ≅ ℤ`
        have hfin : (if (4 : ℕ) = 0 then 1 else 0) + (if (4 : ℕ) = 4 then 1 else 0) = 1 := by
          norm_num
        rw [hfin]
        haveI hiso : IsIso (Work.Cohomology.mvδX (X := TopCat.of (Submission.Milnor.Vk k))
            (Set.range (Submission.Milnor.vData k).ιX)
            (Set.range (Submission.Milnor.vData k).ιY) hU hV hcov 3) :=
          Work.Cohomology.mvδX_isIso _ _ hU hV hcov 3 (by norm_num)
        obtain ⟨e2⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv
          (Work.Milnor.homotopyEquiv_inter_sphere k).some 3
        obtain ⟨e3⟩ := Work.Cohomology.sphereHomologyTop 3 (by norm_num)
        exact ⟨CategoryTheory.asIso (Work.Cohomology.mvδX (X := TopCat.of (Submission.Milnor.Vk k))
            (Set.range (Submission.Milnor.vData k).ιX)
            (Set.range (Submission.Milnor.vData k).ιY) hU hV hcov 3) ≪≫
          e2 ≪≫ e3 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
      · -- all other degrees `n ≥ 2`, `n ≠ 4`: `Hₙ ≅ Hₙ₋₁(S³) = 0`
        have hn2 : 2 ≤ n := by omega
        have hfin : (if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) = 0 := by
          rw [if_neg hn0, if_neg hn4, add_zero]
        rw [hfin]
        haveI hiso : IsIso (Work.Cohomology.mvδX (X := TopCat.of (Submission.Milnor.Vk k))
            (Set.range (Submission.Milnor.vData k).ιX)
            (Set.range (Submission.Milnor.vData k).ιY) hU hV hcov (n - 1)) :=
          Work.Cohomology.mvδX_isIso _ _ hU hV hcov (n - 1) (by omega)
        have e1 : (Work.Cohomology.singularChains ℤ (TopCat.of (Submission.Milnor.Vk k))).homology
              ((n - 1) + 1) ≅
            Work.Cohomology.HInter (X := TopCat.of (Submission.Milnor.Vk k))
              (Set.range (Submission.Milnor.vData k).ιX)
              (Set.range (Submission.Milnor.vData k).ιY) (n - 1) :=
          CategoryTheory.asIso (Work.Cohomology.mvδX (X := TopCat.of (Submission.Milnor.Vk k))
            (Set.range (Submission.Milnor.vData k).ιX)
            (Set.range (Submission.Milnor.vData k).ιY) hU hV hcov (n - 1))
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at e1
        obtain ⟨e2⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv
          (Work.Milnor.homotopyEquiv_inter_sphere k).some (n - 1)
        have hz : IsZero
            ((Work.Cohomology.singularChains ℤ (TopCat.of Work.Milnor.Sph3)).homology (n - 1)) :=
          Work.Cohomology.sphereHomologyZero 3 (n - 1) (by norm_num) (by omega) (by omega)
        exact ⟨e1 ≪≫ e2 ≪≫ IsZero.iso hz (ModuleCat.isZero_of_subsingleton _)⟩

end

end Work.Milnor
