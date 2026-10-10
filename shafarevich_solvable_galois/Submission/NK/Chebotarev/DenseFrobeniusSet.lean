import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.Chebotarev.ExistsFrobeniusOfRestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Density of the Frobenius elements of an infinite Galois extension

Let `K` be a number field and `K'/K` a Galois extension (possibly infinite), and assume Čebotarev's
theorem in the form `hC`: for every *finite normal* intermediate field `L` and every
`τ : Gal(L/K)` there is a prime `p` of `K` and a prime `P` of `𝓞 L` above `p`, unramified over `p`,
at which `τ` is a Frobenius element.

Then the set of elements of `Gal(K'/K)` which are Frobenius elements at a *single* prime `p` of `K`
in *every* finite normal intermediate field is **dense** in `Gal(K'/K)` for the Krull topology.

This is the form in which the density of the Frobenius elements is consumed by the
Neukirch–Uchida reconstruction: for each finite quotient `Gal(L/K)` every element is realised by a
Frobenius, and a common `σ ∈ Gal(K'/K)` realises compatible choices simultaneously
(`NK.Chebotarev.ExistsFrobeniusOfRestriction`).  Density then follows because the basic open sets
of the Krull topology are the fibres of the restriction maps to finite quotients, and the normal
closure of a finite-dimensional intermediate field is again finite-dimensional.

The proof is short but uses only the fact that the *normal closure* of a finite-dimensional
subextension is finite-dimensional: given an open set `U` and `x ∈ U`, the Krull topology provides a
finite-dimensional `E` with `x · Gal(K'/E) ⊆ U`; taking `L₀` the normal closure of `E`, the element
`σ` produced by `ExistsFrobeniusOfRestriction` with `σ|_{L₀} = x|_{L₀}` lies in `x · Gal(K'/L₀) ⊆ U`
and in the Frobenius set.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Topology

namespace NK.Chebotarev

/-- **The Frobenius elements of `Gal(K'/K)` are dense.**  Under Čebotarev's theorem `hC` for the
finite normal subextensions of `K'/K`, the set of `σ ∈ Gal(K'/K)` for which there is a prime `p` of
`K` such that `σ|_L` is a Frobenius element at a prime above `p` for *every* finite normal
intermediate field `L` is dense in the Krull topology. -/
theorem DenseFrobeniusSet {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsGalois K K']
    (hC : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
      (τ : Gal(↥L/K)), ∃ p : NK.Chebotarev.PrimeIdeal K, ∃ P : NK.Chebotarev.PrimeIdeal ↥L,
        P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        NK.Chebotarev.IsFrobAt P τ) :
    Dense {σ : Gal(K'/K) | ∃ p : NK.Chebotarev.PrimeIdeal K,
      ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
        ∃ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal ∧
          NK.Chebotarev.IsFrobAt P (AlgEquiv.restrictNormalHom L σ)} := by
  classical
  -- It suffices to meet every nonempty open set.
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  -- The Krull topology has a basis of translates of `Gal(K'/E)`, `E/K` finite dimensional.
  have hxUnhds : U ∈ 𝓝 x := hU.mem_nhds hxU
  obtain ⟨V, hV, hVU⟩ :=
    (GroupFilterBasis.nhds_hasBasis (galGroupBasis K K') x).mem_iff.mp hxUnhds
  obtain ⟨H, ⟨E, hEfin, hEH⟩, hHV⟩ := hV
  -- Replace `E` by its normal closure `L₀`, which is still finite dimensional over `K`.
  let L₀ : IntermediateField K K' := IntermediateField.normalClosure K E K'
  haveI hEfd : FiniteDimensional K E := hEfin
  haveI : FiniteDimensional K L₀ := inferInstance
  haveI : Normal K L₀ := inferInstance
  haveI : NumberField ↥L₀ :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L₀
  -- Realise the restriction of `x` to `L₀` by a Frobenius element at a single prime.
  obtain ⟨σ, hσL₀, p, hσS⟩ :=
    NK.Chebotarev.ExistsFrobeniusOfRestriction (K := K) (K' := K') hC L₀
      (AlgEquiv.restrictNormalHom L₀ x)
  refine ⟨σ, ?_, ?_⟩
  · -- `σ = x * (x⁻¹ * σ)` with `x⁻¹ * σ ∈ Gal(K'/L₀) ⊆ Gal(K'/E)`, so `σ ∈ x · V ⊆ U`.
    have hfix : x⁻¹ * σ ∈ L₀.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h1 : σ (y : K') = x (y : K') := by
        have h0 : (AlgEquiv.restrictNormalHom L₀ σ) ⟨y, hy⟩ =
            (AlgEquiv.restrictNormalHom L₀ x) ⟨y, hy⟩ := by rw [hσL₀]
        have h0' := congrArg Subtype.val h0
        rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply] at h0'
        exact h0'
      show (x⁻¹ * σ) y = y
      rw [AlgEquiv.mul_apply, h1]
      simp
    have hmemV : x⁻¹ * σ ∈ V := by
      rw [← hHV, ← hEH]
      exact E.fixingSubgroup_le (IntermediateField.le_normalClosure E) hfix
    have hxU' : x * (x⁻¹ * σ) ∈ U := hVU (Set.mem_image_of_mem (fun y => x * y) hmemV)
    simpa using hxU'
  · exact ⟨p, hσS⟩

end NK.Chebotarev
