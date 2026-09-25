/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `p`-torsion of the profinite completion of `κˣ` is `μ_p(κ)`

For `κ = K_𝔭` the `𝔭`-adic completion of a number field (`𝔭` a finite prime, `p` the residue
characteristic), the profinite completion `NK.LocalReciprocity.completionUnits κ = κˣ^{∧}` of
the unit group has

  `κˣ^{∧}[p] = μ_p(κ)`,

i.e. it has a non-trivial element of order dividing `p` exactly when `κ` contains a primitive
`p`-th root of unity.  This is the corrected form of the `p_torsion_iff` field of the local input
bundles of `NK.LocalAnabelian`/`NK.LocalInputs`, and it is *proved* here from

* `NK.PTorsionTop.completion_pow_eq_one_of` (no new `p`-torsion) and
* `NK.PTorsionTop.hasPTorsion_completion_of_exponent` (`p`-torsion survives), the exponent
  bound being the finiteness of the `p`-power roots of unity of `κ`
  (`NK.LocalInputs.PowerQuotient.exists_powTorsion_exponent`),

together with the arithmetic input `|κˣ/(κˣ)^p| = p^{d+1+δ}`
(`NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow`, discharged unconditionally by
`NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime`), which supplies the finiteness of the
`p`-power class group.

## Main results

* `NK.PTorsionTop.hasPTorsion_completionUnits_iff_zeta`
* `NK.PTorsionTop.hasPTorsionAbelianizationTop_completionUnits_iff_zeta`
-/
import Mathlib
import Submission.NK.PTorsionTop.CompletionTorsion
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.LocalInputs.PowerQuotient.exists_powTorsion_exponent
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.PTorsionTop

universe u

noncomputable section

/-- **The `p`-power class group of `κˣ` is finite**, from the power-class count
`|κˣ/(κˣ)^p| = p^{[κ:ℚ_p] + 1 + δ}`. -/
theorem finite_units_quot_pow_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Finite ((𝔭.adicCompletion K)ˣ ⧸ (powMonoidHom p :
      ((𝔭.adicCompletion K)ˣ) →* ((𝔭.adicCompletion K)ˣ)).range) := by
  have hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p :=
    NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hchar
  have hcard := NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow 𝔭 hF
  rw [NK.LocalAnabelian.KummerGroup, NK.LocalAnabelian.powSubgroup] at hcard
  refine Nat.finite_of_card_ne_zero ?_
  rw [hcard]
  exact pow_ne_zero _ hp.ne_zero

/-! ## The torsion subgroup `μ_κ` of `κˣ`, and the indicator `δ` -/

/-- **`μ_κ`, the group of roots of unity of `κ`**: the torsion subgroup of `κˣ`.  For a `p`-adic
field it is finite and cyclic (with `μ_κ = μ_{q-1}` for odd `p` and the `1 + 2𝔪` refinement for
`p = 2`), but only its `p`-torsion — `μ_κ[p] = μ_p(κ)` — is used here. -/
def rootsOfUnityUnits (κ : Type*) [Field κ] : Subgroup κˣ := CommGroup.torsion κˣ

/-- **`δ = 1` exactly when `μ_κ` has an element of order `p`**: the group-theoretic form of
`NK.LocalInputs.zetaIndicator_eq_one_iff`. -/
theorem zetaIndicator_eq_one_iff_exists_rootsOfUnityUnits {κ : Type*} [Field κ] {p : ℕ}
    (hp : p.Prime) :
    NK.LocalInputs.zetaIndicator p κ = 1 ↔
      ∃ x : rootsOfUnityUnits κ, x ≠ 1 ∧ x ^ p = 1 := by
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := (NK.LocalInputs.zetaIndicator_eq_one_iff p κ).mp h
    have hζne : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
    refine ⟨⟨Units.mk0 ζ hζne, ?_⟩, ?_, ?_⟩
    · change Units.mk0 ζ hζne ∈ CommGroup.torsion κˣ
      rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨p, hp.pos, Units.ext hζ.pow_eq_one⟩
    · intro hc
      exact hζ.ne_one hp.one_lt
        (congrArg (fun u : κˣ => (u : κ)) (Subtype.ext_iff.mp hc))
    · exact Subtype.ext (Units.ext hζ.pow_eq_one)
  · rintro ⟨x, hx1, hxp⟩
    have hx' : ((x : κˣ) : κ) ^ p = 1 := by
      have h := congrArg (fun u : κˣ => (u : κ)) (Subtype.ext_iff.mp hxp)
      simpa using h
    have hne : ((x : κˣ) : κ) ≠ 1 := fun h =>
      hx1 (Subtype.ext (Units.ext h))
    have hdvd : orderOf (((x : κˣ) : κ)) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx'
    have hord : orderOf (((x : κˣ) : κ)) = p := by
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    exact (NK.LocalInputs.zetaIndicator_eq_one_iff p κ).mpr
      ⟨_, (by rw [← hord]; exact IsPrimitiveRoot.orderOf _)⟩

/-- **A unit of the completion of order dividing `p` is trivial when `ζ_p ∉ κ`.** -/
theorem eq_one_of_pow_eq_one_units_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hzeta : NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 0) :
    ∀ ζ : (𝔭.adicCompletion K)ˣ, ζ ^ p = 1 → ζ = 1 := by
  intro ζ hζ
  by_contra hne
  have hζ' : ((ζ : 𝔭.adicCompletion K)) ^ p = 1 := by
    have h := congrArg (fun u : (𝔭.adicCompletion K)ˣ => (u : 𝔭.adicCompletion K)) hζ
    simpa using h
  have hdvd : orderOf (ζ : 𝔭.adicCompletion K) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hζ'
  have hne1 : orderOf (ζ : 𝔭.adicCompletion K) ≠ 1 := fun h =>
    hne (Units.ext (orderOf_eq_one_iff.mp h))
  have hord : orderOf (ζ : 𝔭.adicCompletion K) = p := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hprim : IsPrimitiveRoot (ζ : 𝔭.adicCompletion K) p := by
    rw [← hord]
    exact IsPrimitiveRoot.orderOf _
  exact ((NK.LocalInputs.zetaIndicator_eq_zero_iff p (𝔭.adicCompletion K)).mp hzeta)
    ⟨_, hprim⟩

/-- **The `p`-torsion of `κˣ^{∧}` is `μ_p(κ)`.**

This is the corrected `p_torsion_iff`: the `p`-torsion of the *profinite* completion of the unit
group of `κ = K_𝔭` is non-trivial exactly when `κ` contains a primitive `p`-th root of unity. -/
theorem hasPTorsion_completionUnits_iff_zeta {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    HasPTorsion p (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)) ↔
      NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1 := by
  haveI hfin : Finite ((𝔭.adicCompletion K)ˣ ⧸ (powMonoidHom p :
      ((𝔭.adicCompletion K)ˣ) →* ((𝔭.adicCompletion K)ˣ)).range) :=
    finite_units_quot_pow_adicCompletion 𝔭 hp hchar
  constructor
  · -- `ζ_p ∈ κ` from a non-trivial element of order `p` in `κˣ^{∧}`
    intro h
    by_contra hzeta
    have hzeta0 : NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 0 := by
      have hle := NK.LocalInputs.zetaIndicator_le_one p (𝔭.adicCompletion K)
      omega
    obtain ⟨x, hx1, hxp⟩ := h
    exact hx1 (completion_pow_eq_one_of hp hfin
      (eq_one_of_pow_eq_one_units_adicCompletion 𝔭 hp hzeta0) x hxp)
  · -- a primitive `p`-th root of unity gives `p`-torsion in `κˣ^{∧}`
    intro hzeta
    obtain ⟨ζ, hζ⟩ := (NK.LocalInputs.zetaIndicator_eq_one_iff p (𝔭.adicCompletion K)).mp hzeta
    obtain ⟨N, hN⟩ :=
      NK.LocalInputs.PowerQuotient.exists_powTorsion_exponent 𝔭 hp hchar
    have hζne : ζ ≠ 0 := hζ.ne_zero (hp.ne_zero)
    have hζne1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
    refine hasPTorsion_completion_of_exponent (A := (𝔭.adicCompletion K)ˣ) N hN
      (Units.mk0 ζ hζne) ?_ ?_
    · intro hc
      exact hζne1 (congrArg (fun u : (𝔭.adicCompletion K)ˣ => (u : 𝔭.adicCompletion K)) hc)
    · exact Units.ext (by simpa using hζ.pow_eq_one)

/-- **The corrected predicate on `κˣ^{∧}`**: since the completion of the units is commutative,
`HasPTorsionAbelianizationTop` is plain `p`-torsion there. -/
theorem hasPTorsionAbelianizationTop_completionUnits_iff_zeta {K : Type*} [Field K]
    [NumberField K] (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    HasPTorsionAbelianizationTop p (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)) ↔
      NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1 := by
  haveI : IsMulCommutative (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)) :=
    NK.LocalInputs.CommGroupRank.isMulCommutative_cpl ((𝔭.adicCompletion K)ˣ)
  refine (hasPTorsionAbelianizationTop_iff_hasPTorsion_of_isMulCommutative p _ ?_).trans
    (hasPTorsion_completionUnits_iff_zeta 𝔭 hp hchar)
  exact fun x y => IsMulCommutative.is_comm.comm x y

end

end NK.PTorsionTop
