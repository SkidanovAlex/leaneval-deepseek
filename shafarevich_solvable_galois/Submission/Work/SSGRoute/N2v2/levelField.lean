import Mathlib
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.step4_y_escape_v2.Orthogonality
import Submission.Work.SSGRoute.EscapeCoreLib.charSeparation
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
import Submission.Work.SSGRoute.CFTSide.exists_intermediateField_normClassSubgroup_eq_of_index
import Submission.Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level field of the `hsplit` orthogonality

`exists_levelField_of_gesUPow_subfield_N`: with `U' = gesU ↾K ⊔ (p-th powers)` and `N` the
`↥K`-copy of `L₁ ⊔ L₂`, there is a finite abelian `F ≤ N` over `↥K` with
`N_{F/↥K}C_F = U' ⊔ N_{N/↥K}C_N`.

`F` is the level at which the orthogonality is computed: its characters are the characters of
`C_↥K/(U' ⊔ N_N C_N)`, and `F ≤ N` is what makes `hsplit` applicable to their pull-backs.

## Construction (no monotonicity of the norm-group correspondence is needed)

Write `W := N_{N/↥K}C_N` and `V := U' ⊔ W`.

1. `Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le` (norm limitation,
   `NK.CFTLib.fundamentalClassElement`) applied to `N/↥K` with `V := W` gives an abelian
   `A : IntermediateField ↥K ↥N` with `N_{A/↥K}C_A ≤ W`; transitivity
   (`Idele.normClassSubgroup_le_of_tower`, `A ≤ N`) upgrades this to `N_{A/↥K}C_A = W`.
2. `NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index` applied **inside the
   abelian extension `A/↥K`** with `V ⊇ W = N_{A/↥K}C_A` gives
   `E : IntermediateField ↥K ↥A` with `IsGalois ↥K ↥E` and `N_{E/↥K}C_E = V`.
3. `F := E.map ((IntermediateField.val N).comp (IntermediateField.val A))` is an intermediate field
   of `Ω/↥K` with `F ≤ N`; the norm group transports along `IntermediateField.equivMap` and
   `Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv`, the finiteness/Galoisness along the same
   isomorphism (`IsGalois.of_algEquiv`, `FiniteDimensional.of_injective`, and
   `NumberField.of_module_finite`), and the commutativity from `Gal(A/↥K)` (a surjective
   restriction).
-/

namespace Work.SSGRoute.N2v2

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- **A level field inside `N` whose norm class subgroup is `U' ⊔ N_{N/↥K}C_N`.** -/
theorem exists_levelField_of_gesUPow_subfield_N (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (N : IntermediateField ↥K Ω) [FiniteDimensional ↥K N] [IsGalois ↥K N] [NumberField ↥N]
    (hN : (N : Set Ω) = ((L₁ ⊔ L₂ : IntermediateField k Ω) : Set Ω)) :
    ∃ (F : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K F) (_ : IsGalois ↥K F)
      (_ : NumberField ↥F) (_ : IsMulCommutative (↥F ≃ₐ[↥K] ↥F)),
      F ≤ N ∧
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥F =
        (((NK.GlobalCFT.Idele.principalSubgroup ↥K ⊔ Work.SSGRoute.powTIdeles ↥K p T').map
            (NK.GlobalCFT.IdeleClassGroup.mk ↥K))
          ⊔ Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (NK.GlobalCFT.IdeleClassGroup ↥K))
        ⊔ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- the subgroup `V = U' ⊔ W` of `C_↥K`
  set U' : Subgroup (IdeleClassGroup ↥K) :=
    (((Idele.principalSubgroup ↥K ⊔ Work.SSGRoute.powTIdeles ↥K p T').map
        (IdeleClassGroup.mk ↥K))
      ⊔ Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K)) with hU'
  set W : Subgroup (IdeleClassGroup ↥K) := Idele.normClassSubgroup ↥K ↥N with hW
  -- ## (i) the norm-limitation theorem inside `N`
  obtain ⟨A, hAgal, hAcomm, hAle⟩ :=
    Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
      NK.CFTLib.fundamentalClassElement (K := ↥K) (L := ↥N) W le_rfl
  haveI : IsGalois ↥K ↥A := hAgal
  haveI : IsMulCommutative (↥A ≃ₐ[↥K] ↥A) := hAcomm
  -- transitivity upgrades `≤` to `=`: `A ≤ N`, so `N_{N/↥K}C_N ≤ N_{A/↥K}C_A`
  have hAeq : Idele.normClassSubgroup ↥K ↥A = W := by
    refine le_antisymm hAle ?_
    rw [hW]
    exact Idele.normClassSubgroup_le_of_tower (K := ↥K) (L := ↥A) (M := ↥N)
  -- ## (ii) the norm-group correspondence inside the abelian extension `A/↥K`
  obtain ⟨E, hEgal, hEnorm, hEdeg⟩ :=
    NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index
      NK.CFTLib.artinReciprocityIdeal_proved NK.CFTLib.fundamentalClassElement
      (K := ↥K) (L := ↥A) (U' ⊔ W) (by rw [hAeq]; exact le_sup_right)
  haveI : IsGalois ↥K ↥E := hEgal
  -- ## (iii) transport `E ⊆ A ⊆ N` into `Ω`
  -- The composite `↥A →ₐ[↥K] Ω`; `F` is the image of `E ⊆ ↥A` under it, so `F ≤ N`.
  let f : ↥A →ₐ[↥K] Ω := (IntermediateField.val N).comp (IntermediateField.val A)
  let F : IntermediateField ↥K Ω := E.map f
  have hFN : F ≤ N := by
    intro x hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact (IntermediateField.val A y).2
  -- the isomorphism `↥E ≃ₐ[↥K] ↥F`
  haveI hFfd : FiniteDimensional ↥K ↥F :=
    FiniteDimensional.of_injective
      (IntermediateField.equivMap E f).symm.toLinearEquiv.toLinearMap
      (IntermediateField.equivMap E f).symm.injective
  haveI hFgal : IsGalois ↥K ↥F := IsGalois.of_algEquiv (IntermediateField.equivMap E f)
  haveI hFnf : NumberField ↥F := NumberField.of_module_finite ↥K ↥F
  -- `Gal(↥E/↥K)` is commutative, being a quotient of the commutative `Gal(↥A/↥K)`
  haveI hEcomm : IsMulCommutative (↥E ≃ₐ[↥K] ↥E) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥E) (E := ↥A) a
    obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥E) (E := ↥A) b
    rw [← map_mul, ← map_mul, mul_comm']
  haveI hFcomm : IsMulCommutative (↥F ≃ₐ[↥K] ↥F) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    let e := AlgEquiv.autCongr (IntermediateField.equivMap E f)
    have h := mul_comm' (e.symm a) (e.symm b)
    exact e.symm.injective (by rw [map_mul, map_mul, h])
  -- the norm class subgroup of `F` is that of `E`, transported along `↥E ≃ₐ[↥K] ↥F`
  have hFnorm : Idele.normClassSubgroup ↥K ↥F = U' ⊔ W := by
    rw [← hEnorm]
    exact SetLike.ext fun x =>
      (Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv
        (IntermediateField.equivMap E f) x).symm
  exact ⟨F, hFfd, hFgal, hFnf, hFcomm, hFN, hFnorm⟩

end Work.SSGRoute.N2v2
