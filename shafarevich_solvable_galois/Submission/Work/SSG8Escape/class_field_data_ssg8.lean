import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos
import Submission.Work.SSGRoute.ZDataMup.IdealModulusKernel.CycloPrincipalId
import Submission.Work.SSGRoute.ZDataMup.IdealModulusKernel.IndexLeIdId
import Submission.Work.SSGRoute.ZDataMup.MupAux.ThetaKerId
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
import Submission.Work.SSGRoute.ZDataMup.localFactor_unramified_eq_frob_pow
import Submission.Work.SSGRoute.ZDataMup.nonempty_artinReciprocity_of_abelian
import Submission.Work.SSGRoute.ZDataMup.weakApprox_pos_numberField

/-!
# The class-field data for the escape step of the Shafarevich route (`p`-th power version)

This module assembles the class-field-theoretic input used by the escape step
`Work.SSG8Escape.escape_prime_ssg8`: for the open finite-index subgroup

  `U_p = gesU_{T'} ⊔ (p-th powers of C_↥K)   (Work.SSGRoute.SSG8Escape.gesUPow)`

of the idèle class group `C_↥K` of a number field `↥K` there is an intermediate field `M` of the
ambient algebraic closure `Ω`, finite dimensional and abelian Galois over `↥K`, whose idèlic norm
class subgroup is exactly `U_p`, together with the abelian idèlic Artin map
`art : 𝕀_↥K →* Gal(M/↥K)`; the map has kernel `N_{M/↥K}𝕀_M ⊔ ↥Kˣ` and sends the idèle of a prime
`𝔮` unramified in `M/↥K` to the Frobenius `Frob_𝔮`.

The two ingredients are the existence theorem of global class field theory
(`Work.SSGRoute.CFTSide.classField_exists_of_index`, promoted to an *abelian* class field by
`Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le`, and transported into `Ω`
by `IsAlgClosed.lift`) and Artin reciprocity for finite abelian extensions
(`Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors`).
-/

namespace Work.SSG8Escape

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **The abelian class field, inside `Ω`, of an open finite-index subgroup of `C_↥K`.**

Let `K / k` be a finite Galois extension of the number field `k` inside the algebraic closure `Ω`,
and let `U ≤ C_↥K` be open of finite index.  Then there is an intermediate field
`M : IntermediateField ↥K Ω`, finite dimensional and abelian Galois over `↥K`, with
`N_{M/↥K} C_M = U`.

The proof is the existence theorem of global class field theory in abelian form: the class field
`L / ↥K` of `U` (`Work.SSGRoute.CFTSide.classField_exists_of_index`) has norm class subgroup `U`,
its maximal abelian subextension `A / ↥K`
(`Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le`) has norm class subgroup
`U` as well (by the norm limitation theorem, `N_{L/↥K} C_L ≤ N_{A/↥K} C_A ≤ U`), and `A` is then
transported into `Ω` by an `↥K`-algebra embedding `IsAlgClosed.lift`; `Gal` commutativity and the
norm class subgroup travel along the resulting `↥K`-algebra equivalence
(`Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv`, `AlgEquiv.autCongr`). -/
theorem exists_abelian_classField_open {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (U : Subgroup (IdeleClassGroup ↥K)) (hUfin : U.FiniteIndex)
    (hUopen : IsOpen (U : Set (IdeleClassGroup ↥K))) :
    ∃ (M : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K M) (_ : IsGalois ↥K M)
      (_ : NumberField ↥M) (_ : IsMulCommutative (↥M ≃ₐ[↥K] ↥M)),
      Idele.normClassSubgroup ↥K ↥M = U := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hidxpos : 0 < U.index := Nat.pos_of_ne_zero (Subgroup.finiteIndex_iff.mp hUfin)
  -- the abstract class field `L / ↥K` of `U`
  obtain ⟨L, hFL, hNL, hAL, hfdL, hGalL, hNormL, _⟩ :=
    Work.SSGRoute.CFTSide.classField_exists_of_index (K := ↥K) U.index hidxpos U hUfin hUopen rfl
  letI : Algebra ↥K L := hAL
  letI : FiniteDimensional ↥K L := hfdL
  haveI : IsGalois ↥K L := hGalL
  -- its maximal abelian subextension `A / ↥K`, which still has norm class subgroup `U`
  obtain ⟨A, hAgal, hAcomm, hAle⟩ :=
    Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
      NK.CFTLib.fundamentalClassElement (K := ↥K) (L := L) U (le_of_eq hNormL)
  haveI : IsGalois ↥K ↥A := hAgal
  haveI : IsMulCommutative (↥A ≃ₐ[↥K] ↥A) := hAcomm
  haveI : NumberField ↥A := NumberField.of_module_finite ↥K ↥A
  haveI : FiniteDimensional ↥K ↥A := inferInstance
  have hnormA : Idele.normClassSubgroup ↥K ↥A = U := by
    refine le_antisymm hAle ?_
    rw [← hNormL]
    exact Idele.normClassSubgroup_le_of_tower (K := ↥K) (L := ↥A) (M := L)
  -- transport `A` into `Ω` along an `↥K`-algebra embedding
  haveI : Algebra.IsAlgebraic ↥K L := Algebra.IsAlgebraic.of_finite ↥K L
  let ιL : L →ₐ[↥K] Ω := IsAlgClosed.lift
  let j : ↥A →ₐ[↥K] Ω := ιL.comp A.val
  let M : IntermediateField ↥K Ω := j.fieldRange
  let φ : ↥A ≃ₐ[↥K] ↥M := j.equivFieldRange
  haveI hfdM : FiniteDimensional ↥K ↥M :=
    FiniteDimensional.of_injective φ.symm.toLinearEquiv.toLinearMap φ.symm.injective
  haveI hgalM : IsGalois ↥K ↥M := IsGalois.of_algEquiv φ
  haveI hnfM : NumberField ↥M := NumberField.of_module_finite ↥K ↥M
  -- commutativity of `Gal(M/↥K)` is transported along the conjugation by `φ`
  have hcommM : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := by
    rw [isMulCommutative_iff] at hAcomm ⊢
    intro σ τ
    let Φ : (↥A ≃ₐ[↥K] ↥A) ≃* (↥M ≃ₐ[↥K] ↥M) := AlgEquiv.autCongr φ
    have h2 := congrArg Φ (hAcomm (Φ.symm σ) (Φ.symm τ))
    rw [map_mul, map_mul] at h2
    simpa using h2
  refine ⟨M, hfdM, hgalM, hnfM, hcommM, ?_⟩
  -- the norm class subgroup is transported along `φ` as well
  rw [show Idele.normClassSubgroup ↥K ↥M = Idele.normClassSubgroup ↥K ↥A from
    SetLike.ext fun x => Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv φ.symm x,
    hnormA]

/-- **The subgroup `U_p = gesU_{T'} ⊔ (p-th powers)` is open and of finite index in `C_K`.**

The finite index comes from `Work.SSGRoute.finiteIndex_gesU` (a finiteness argument for
`U = im(Kˣ · E)`), and openness from `Work.SSGRoute.isOpen_gesU` together with the fact that a
subgroup containing an open subgroup is open; the `p`-th powers are adjoined on top of `gesU`, so
both properties are inherited. -/
theorem gesUPow_finiteIndex_and_isOpen (K : Type) [Field K] [NumberField K] (p : ℕ)
    [Fact p.Prime] (T' : Finset (NK.Chebotarev.PrimeIdeal K)) :
    (Work.SSGRoute.SSG8Escape.gesUPow K p T').FiniteIndex ∧
      IsOpen ((Work.SSGRoute.SSG8Escape.gesUPow K p T') : Set (IdeleClassGroup K)) := by
  haveI hpk : p.Prime := Fact.out
  haveI hgesfin : (Work.SSGRoute.GrunwaldEscapeCore.gesU K p T').FiniteIndex :=
    Work.SSGRoute.finiteIndex_gesU K p T'
  exact ⟨Subgroup.finiteIndex_of_le le_sup_left,
    Subgroup.isOpen_mono le_sup_left (Work.SSGRoute.isOpen_gesU hpk T')⟩

theorem class_field_data_ssg8 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K)) :
    ∃ (M : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K M) (_ : IsGalois ↥K M)
      (_ : NumberField ↥M) (_ : IsMulCommutative (↥M ≃ₐ[↥K] ↥M))
      (art : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M)),
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M = Work.SSGRoute.SSG8Escape.gesUPow ↥K p T' ∧
      art.ker = NK.GlobalCFT.Idele.normImage ↥K ↥M ⊔ NK.GlobalCFT.Idele.principalSubgroup ↥K ∧
      (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
        NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
        art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮) := by
  classical
  -- `U_p` is open of finite index, so it has an abelian class field `M` inside `Ω`
  obtain ⟨hUfin, hUopen⟩ := gesUPow_finiteIndex_and_isOpen ↥K p T'
  obtain ⟨M, hfdM, hgalM, hnfM, hcommM, hnormM⟩ :=
    exists_abelian_classField_open (K := K) (U := Work.SSGRoute.SSG8Escape.gesUPow ↥K p T')
      hUfin hUopen
  haveI : FiniteDimensional ↥K M := hfdM
  haveI : IsGalois ↥K M := hgalM
  haveI : NumberField ↥M := hnfM
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hcommM
  -- Artin reciprocity supplies the idèlic Artin map with its kernel and Frobenius normalisation
  obtain ⟨art : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M), hartker, -, -, -, hartfrob, -⟩ :=
    Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K) (L := ↥M)
      (fun a b => mul_comm' a b)
  exact ⟨M, hfdM, hgalM, hnfM, hcommM, art, hnormM, hartker, hartfrob⟩

end Work.SSG8Escape
