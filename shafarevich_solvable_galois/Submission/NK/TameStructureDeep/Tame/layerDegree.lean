import Mathlib
import Submission.NK.TameStructureDeep.Tame.UnramifiedNoPow
import Submission.NK.TameStructureDeep.Tame.kummerLayer_finrank_dvd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree of a prime-to-`p` Kummer layer over the maximal unramified extension

For a prime-to-`p` `n` and an `n`-th root `β` of a uniformiser `π` of `κ = K_𝔭`, the layer
`κ^{ur}(β)` has degree exactly `n` over `κ^{ur}` (and, by the Kummer pairing, Galois group `μ_n`).

This is the arithmetic heart of the tamely ramified structure theorem: it is what makes the
Kummer pairing `Gal(κ^{ur}(β)/κ^{ur}) → μ_n` surjective, and hence the tame inertia
`Gal(κ^{tr}/κ^{ur}) = lim_n μ_n` pro-cyclic.
-/

open Polynomial IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

noncomputable section

/-! ## 3. The degree of a prime-to-`p` Kummer layer over `κ^{ur}`

The arithmetic input that makes the tame inertia pro-cyclic at every place: for a prime-to-`p`
`n` and an `n`-th root `β` of the uniformiser `π`, the layer `κ^{ur}(β)` has degree exactly `n`
over `κ^{ur}`.

Indeed `m = [κ^{ur}(β) : κ^{ur}]` divides `n` and `β ^ m ∈ κ^{ur}` (the general Kummer layer
statement `kummerLayer_finrank_dvd`), so `π = (β ^ m) ^ (n / m)` would exhibit an `(n / m)`-th
root of the uniformiser in `κ^{ur}`; by `UnramifiedNoPow` this forces `n / m = 1`. -/

section LayerDegree

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
  [IsSepClosure (𝔭.adicCompletion K) K']

local notation "κur" =>
  NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)

/-- **The degree of a prime-to-`p` Kummer layer over `κ^{ur}`.** -/
theorem finrank_adjoin_urCl {n : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n (resCharAt 𝔭))
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) {β : K'}
    (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) :
    Module.finrank ↥κur ↥(IntermediateField.adjoin ↥κur {β}) = n := by
  have hp : (resCharAt 𝔭).Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hpn : (resCharAt 𝔭).Coprime n := Nat.coprime_comm.mp hcop
  have hpnd : ¬ resCharAt 𝔭 ∣ n := (Nat.Prime.coprime_iff_not_dvd hp).mp hpn
  -- a primitive `n`-th root of unity inside `κ^{ur}`
  haveI hchark : CharZero (𝔭.adicCompletion K) :=
    Algebra.charZero_of_charZero K (𝔭.adicCompletion K)
  haveI hchar : CharZero K' := Algebra.charZero_of_charZero (𝔭.adicCompletion K) K'
  haveI : NeZero (n : K') := ⟨(Nat.cast_ne_zero).mpr hn.ne'⟩
  haveI : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := K') (n := n)
  have hζF : ζ ∈ κur :=
    NK.TameStructureDeep.mem_unramifiedClosure_of_isPrimitiveRoot hpnd hζ
  have hζsub : (primitiveRoots n ↥κur).Nonempty :=
    ⟨⟨ζ, hζF⟩, (mem_primitiveRoots hn).mpr
      ((IsPrimitiveRoot.coe_submonoidClass_iff (N := κur) (ζ := (⟨ζ, hζF⟩ : ↥κur))).mp hζ)⟩
  -- the general Kummer layer statement over `κ^{ur}`
  have hβF : β ^ n = algebraMap ↥κur K'
      (⟨algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K),
        (κur).algebraMap_mem π⟩ : ↥κur) := by
    simpa using hβ
  obtain ⟨hmdvd, c, hc⟩ := kummerLayer_finrank_dvd (F := ↥κur) (E := K') hn hβF hζsub
  set m := Module.finrank ↥κur ↥(IntermediateField.adjoin ↥κur {β}) with hm
  -- `(c : K') ^ (n / m) = π`
  have hmn : m * (n / m) = n := Nat.mul_div_cancel' hmdvd
  have hpow : (c : K') ^ (n / m) =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := by
    calc (c : K') ^ (n / m) = (algebraMap ↥κur K' c) ^ (n / m) := rfl
      _ = (β ^ m) ^ (n / m) := by rw [hc]
      _ = β ^ (m * (n / m)) := by rw [pow_mul]
      _ = β ^ n := by rw [hmn]
      _ = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := hβ
  haveI : FiniteDimensional ↥κur ↥(IntermediateField.adjoin ↥κur {β}) :=
    IntermediateField.adjoin.finiteDimensional (IsIntegral.of_pow hn (by rw [hβF]; exact isIntegral_algebraMap))
  have hmpos : 0 < m := by
    rw [hm]
    exact Module.finrank_pos
  have hmle : m ≤ n := Nat.le_of_dvd hn hmdvd
  have hnm1 : n / m = 1 := by
    by_contra hne
    have h2 : 2 ≤ n / m := by
      have h1 : 1 ≤ n / m := (Nat.one_le_div_iff hmpos).mpr hmle
      omega
    have hcop' : Nat.Coprime (n / m) (resCharAt 𝔭) :=
      hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hmdvd)
    exact (noPowRootAt_of_isUniformizerAt 𝔭 hπ).2 (n / m) h2 hcop' (c : K') c.2 hpow
  rw [← hmn, hnm1, mul_one]

end LayerDegree

end

end NK.TameStructureDeep.Tame
