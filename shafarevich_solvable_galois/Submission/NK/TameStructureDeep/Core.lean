/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The normalised Frobenius, unconditionally, at a `𝔭`-adic completion

`NK.TameStructureDeep.exists_frobenius_adicCompletion`: for every number field `K`, every finite
prime `𝔭` (with `κ = K_𝔭`, residue characteristic `p`, residue cardinality `q`) and every
separable closure `K'` of `κ`, there is an element of `G_κ = Gal(K'/κ)` which

* lies outside the inertia subgroup `I_κ` (`NK.LocalAnabelian.inertiaSubgroup p`), and
* acts on the prime-to-`p` roots of unity by `ζ ↦ ζ^q`

— the classical normalised (arithmetic) Frobenius, NSW (7.5.6).  This is the field
`exists_frobenius` of the residual `NK.TameStructureDeep.TameRamificationCore`, *proved*.

The proof takes the Frobenius `F` of the maximal unramified extension
(`NK.TameStructureDeep.Degree.exists_frobenius_unramifiedClosure`), lifts it to `K'` along the
surjection `Gal(K'/κ) → Gal(κ^ur/κ)` (`AlgEquiv.liftNormal`), and shows that the lift is outside
`I_κ`: it acts on a primitive `ℓ`-th root of unity (ℓ a prime larger than `q`) by `ζ ↦ ζ^q ≠ ζ`,
since `q < ℓ` forces `q ≠ 1`.
-/
import Submission.NK.TameStructureDeep.Residual
import Submission.NK.TameStructureDeep.Support.mem_unramifiedClosure_of_isPrimitiveRoot
import Submission.NK.TameStructureDeep.Degree.exists_frobenius_unramifiedClosure
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep

universe u

noncomputable section

/-- **The normalised Frobenius exists.**  There is an element of `G_κ = Gal(K'/κ)` outside the
inertia subgroup acting on the prime-to-`p` roots of unity by `ζ ↦ ζ^q`.  This is the field
`exists_frobenius` of the residual, proved. -/
theorem exists_frobenius_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] :
    ∃ x : Gal(K'/𝔭.adicCompletion K),
      NK.LocalAnabelian.IsFrobeniusFor (κ := 𝔭.adicCompletion K) (K' := K')
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))
        (NK.LocalStructure.residueCard K 𝔭) x := by
  classical
  let κ := 𝔭.adicCompletion K
  let p := ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
  let q := NK.LocalStructure.residueCard K 𝔭
  obtain ⟨F, hF⟩ := Degree.exists_frobenius_unramifiedClosure (K := K) 𝔭 (K' := K')
  let L : IntermediateField κ K' := NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p
  haveI hnormL : Normal κ ↥L :=
    (NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure (κ := κ) (K' := K')
      p).to_normal
  let σ : Gal(K'/κ) := F.liftNormal K'
  have hσ : σ.restrictNormal ↥L = F := F.restrict_liftNormal K'
  have hpprime : p.Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p :=
    NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  obtain ⟨f, hfpos, hqf⟩ :=
    NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hpprime hchar
  have hqge : 2 ≤ q := by
    rw [show q = p ^ f from hqf]
    calc (2 : ℕ) ≤ p := hpprime.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hpprime.pos hfpos
  -- `K'` has characteristic zero, hence roots of unity of every order
  have hcast : ∀ n : ℕ, n ≠ 0 → (n : K') ≠ 0 := by
    intro n hn h
    have h2 : ((n : ℕ) : κ) = 0 := by
      apply RingHom.injective (algebraMap κ K')
      rw [map_natCast, h, map_zero]
    have h4 : ((n : ℕ) : K) = 0 := by
      apply RingHom.injective (algebraMap K κ)
      rw [map_natCast, h2, map_zero]
    have h4' : ((n : ℕ) : K) = ((0 : ℕ) : K) := by simpa using h4
    exact hn (Nat.cast_injective h4')
  refine ⟨σ, ?_, ?_⟩
  · -- `σ` is outside the inertia subgroup: it acts on a suitable root of unity by `ζ ↦ ζ^q ≠ ζ`
    intro hmem
    obtain ⟨ℓ, hℓge, hℓprime⟩ := Nat.exists_infinite_primes (max p q + 1)
    have hℓp : ¬ p ∣ ℓ := by
      intro hd
      have hpe : p = ℓ := (Nat.prime_dvd_prime_iff_eq hpprime hℓprime).mp hd
      omega
    haveI : NeZero (ℓ : K') := ⟨hcast ℓ hℓprime.ne_zero⟩
    haveI hscK' : IsSepClosed K' := IsSepClosure.sep_closed κ
    obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := K') (n := ℓ)
    have hζL : ζ ∈ L := mem_unramifiedClosure_of_isPrimitiveRoot hℓp hζ
    have hFζ := hF ℓ hℓp (⟨ζ, hζL⟩ : ↥L)
      (by rw [← IsPrimitiveRoot.coe_submonoidClass_iff]; exact hζ)
    have h5 : ((σ.restrictNormal ↥L) ⟨ζ, hζL⟩ : K') = σ ((⟨ζ, hζL⟩ : ↥L) : K') :=
      AlgEquiv.restrictNormal_apply (F := κ) (K₁ := K') L σ ⟨ζ, hζL⟩
    have key : ((σ.restrictNormal ↥L) ⟨ζ, hζL⟩ : K') = ζ ^ q := by
      rw [hσ, hFζ, SubmonoidClass.coe_pow]
    have hσζ : σ ζ = ζ ^ q := by
      rw [← h5]
      exact key
    have hσid : σ ζ = ζ :=
      ((NK.LocalAnabelian.mem_inertiaSubgroup_iff p σ).mp hmem) ℓ hℓp ζ hζ
    have hqlt : q < ℓ := by omega
    have hone : 1 < ℓ := by omega
    have hq1 : q = 1 := by
      refine hζ.pow_inj (k := ℓ) hqlt hone ?_
      rw [pow_one]
      exact hσζ ▸ hσid
    omega
  · -- `σ` acts by `ζ ↦ ζ^q` on every prime-to-`p` root of unity
    intro n hn ζ hζ
    have hζL : ζ ∈ L := mem_unramifiedClosure_of_isPrimitiveRoot hn hζ
    have hFζ := hF n hn (⟨ζ, hζL⟩ : ↥L)
      (by rw [← IsPrimitiveRoot.coe_submonoidClass_iff]; exact hζ)
    have h5 : ((σ.restrictNormal ↥L) ⟨ζ, hζL⟩ : K') = σ ((⟨ζ, hζL⟩ : ↥L) : K') :=
      AlgEquiv.restrictNormal_apply (F := κ) (K₁ := K') L σ ⟨ζ, hζL⟩
    have key : ((σ.restrictNormal ↥L) ⟨ζ, hζL⟩ : K') = ζ ^ q := by
      rw [hσ, hFζ, SubmonoidClass.coe_pow]
    rw [← h5]
    exact key

end

end NK.TameStructureDeep
