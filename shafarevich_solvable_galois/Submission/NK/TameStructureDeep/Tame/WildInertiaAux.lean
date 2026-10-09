import Mathlib
import Submission.NK.TameStructureDeep.Tame.TameInertiaCorrected
import Submission.NK.TameStructureDeep.Tame.isMaximal_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.CorrectedResidual
import Submission.NK.TameStructureDeep.UnramifiedLevels.isProP_le_fixingSubgroup_levelField
import Submission.NK.LocalTame.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliaries for `wildInertiaSubgroup = correctedWildInertia`

For a number field `K`, a finite place `𝔭`, `κ = K_𝔭` and a separable closure `K'`, this file
collects the *proved* ingredients of the comparison between the join `W_κ` of the normal pro-`p`
subgroups of `G_κ = Gal(K'/κ)` and the corrected wild inertia `V_κ = Gal(K'/κ^{tr})`:

* `le_of_isProP_of_coprime_index`: a pro-`p` subgroup `Q` of a group `T` lies in every finite
  index normal subgroup `M ◁ T` of prime-to-`p` index (apply the pro-`p` condition to `Q ∩ M` and
  compare with the injection `Q/(Q∩M) ↪ T/M`);
* `exists_conj_notMem_correctedWildInertia`: **the cyclotomic character is faithful**.  An `x`
  outside the inertia which conjugates `I_κ` into `V_κ` (i.e. acts trivially on `I_κ/V_κ`) is a
  tame Frobenius lift with exponent `q = 1`, so that the converse direction of the Frobenius
  normalisation (`actsAsFrobenius_of_isTameFrobeniusLift`, valid for arbitrary `q`) forces `x` to
  fix all prime-to-`p` roots of unity, i.e. `x ∈ I_κ` — a contradiction.  Hence some `y ∈ I_κ`
  fails to satisfy `[x,y] ∈ V_κ`.
* `isProP_of_le_inertia_fixes_pow_root`: a pro-`p` subgroup contained in the inertia fixes every
  prime-to-`p` root of the uniformiser: the Kummer pairing is a homomorphism there, with image a
  quotient of a pro-`p` group inside `μ_n` of prime-to-`p` order `n`.
-/

open scoped Classical
open IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

/-! ## A pro-`p` subgroup of a group with prime-to-`p` indices -/

/-- **A pro-`p` subgroup of a group lies in every normal subgroup of finite index prime to `p`.**

For `Q ≤ T` with `Q` pro-`p` and `M ◁ T` of finite index: `Q ∩ M` is normal of finite index in
`Q`, so `[Q : Q ∩ M] = p ^ k`; on the other hand `Q/(Q ∩ M)` injects into `T ⧸ M`, whose order is
prime to `p`.  Hence `[Q : Q ∩ M] = 1`, i.e. `Q ≤ M`. -/
theorem le_of_isProP_of_coprime_index {T : Type*} [Group T] {Q M : Subgroup T} [M.Normal]
    [M.FiniteIndex] {p : ℕ} (hQ : NK.LocalTame.IsProP p ↥Q)
    (hcop : Nat.Coprime p M.index) : Q ≤ M := by
  haveI : (M.subgroupOf Q).Normal := inferInstance
  have hdvd : (M.subgroupOf Q).index ∣ M.index := by
    have h := Subgroup.relIndex_dvd_index_of_normal (G := T) M Q
    rwa [Subgroup.relIndex] at h
  have hne : (M.subgroupOf Q).index ≠ 0 := fun h0 =>
    Subgroup.FiniteIndex.index_ne_zero (H := M) (zero_dvd_iff.mp (h0 ▸ hdvd))
  have hfin : (M.subgroupOf Q).FiniteIndex := Subgroup.finiteIndex_iff.mpr hne
  obtain ⟨k, hk⟩ := hQ (M.subgroupOf Q) hfin
  have hpow : p ^ k ∣ M.index := hk ▸ hdvd
  have hone : p ^ k = 1 := (hcop.pow_left k).eq_one_of_dvd hpow
  have hidx : (M.subgroupOf Q).index = 1 := by rw [hk, hone]
  exact Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hidx)

/-! ## The cyclotomic character is faithful -/

/-- **Faithfulness of the action of `G_κ/I_κ` on `I_κ/V_κ`.**

There is no `x ∈ Gal(K'/κ)` outside the inertia `I_κ` with `[x, I_κ] ≤ V_κ`: such an `x` would be a
tame Frobenius lift for the exponent `q = 1`, whose Frobenius normalisation
(`Tame.actsAsFrobenius_of_isTameFrobeniusLift`, valid for arbitrary `q`) says that `x` acts on
every prime-to-`p` root of unity by `ζ ↦ ζ^1 = ζ`, i.e. that `x ∈ I_κ`. -/
theorem exists_conj_notMem_correctedWildInertia {π : 𝔭.adicCompletionIntegers K}
    (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    {x : Gal(K'/𝔭.adicCompletion K)}
    (hx : x ∉ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭)) :
    ∃ y ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭),
      x * y * x⁻¹ * y⁻¹ ∉ NK.TameStructureDeep.Tame.correctedWildInertia
        (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)
        (π : 𝔭.adicCompletion K) := by
  by_contra hcon
  push_neg at hcon
  have hlift : NK.LocalTame.IsTameFrobeniusLift 1
      (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K))
      (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)) x :=
    ⟨hx, fun y hy => by simpa using hcon y hy⟩
  have hF := NK.TameStructureDeep.Tame.actsAsFrobenius_of_isTameFrobeniusLift 𝔭 hπ hlift
  exact hx ((NK.LocalAnabelian.mem_inertiaSubgroup_iff (κ := 𝔭.adicCompletion K) (K' := K')
    (NK.TameStructureDeep.Tame.resCharAt 𝔭) x).mpr fun n hn ζ hζ => by simpa using hF n hn ζ hζ)

/-- The uniformiser is nonzero in the completion. -/
theorem uniformizer_ne_zero {π : 𝔭.adicCompletionIntegers K}
    (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π) :
    (π : 𝔭.adicCompletion K) ≠ 0 := by
  have hirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  exact fun h => hirr.ne_zero (Subtype.ext (by simpa using h))

/-! ## A pro-`p` subgroup of the inertia fixes the Kummer layers -/

/-- **A pro-`p` subgroup of the inertia fixes every prime-to-`p` root of the uniformiser.**

The Kummer pairing `w ↦ wβ/β` is a homomorphism `N → μ_n` because `N ≤ I_κ` fixes `μ_n`; its
image is a quotient of the pro-`p` group `N` and a subgroup of `μ_n`, of order `n` prime to `p`;
so it is trivial. -/
theorem isProP_of_le_inertia_fixes_pow_root {N : Subgroup (Gal(K'/𝔭.adicCompletion K))}
    (hNI : N ≤ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭))
    (hNpro : NK.LocalTame.IsProP (NK.TameStructureDeep.Tame.resCharAt 𝔭) ↥N)
    {n : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n (NK.TameStructureDeep.Tame.resCharAt 𝔭))
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    {β : K'} (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    {z : Gal(K'/𝔭.adicCompletion K)} (hz : z ∈ N) : z β = β := by
  classical
  set p := NK.TameStructureDeep.Tame.resCharAt 𝔭 with hpdef
  haveI : NeZero n := ⟨hn.ne'⟩
  have hp : p.Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hnp : ¬ p ∣ n := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop.symm
  haveI : CharZero (𝔭.adicCompletion K) := Algebra.charZero_of_charZero K _
  haveI : CharZero K' := Algebra.charZero_of_charZero (𝔭.adicCompletion K) K'
  have hπ0 : (π : 𝔭.adicCompletion K) ≠ 0 := uniformizer_ne_zero 𝔭 hπ
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hβ
    exact hπ0 (FaithfulSMul.algebraMap_injective _ K' (by simpa using hβ.symm))
  have hroot : ∀ w : ↥N, (((w : Gal(K'/𝔭.adicCompletion K)) β) / β) ^ n = 1 := by
    intro w
    have hwπ : (w : Gal(K'/𝔭.adicCompletion K)) (algebraMap (𝔭.adicCompletion K) K'
        (π : 𝔭.adicCompletion K)) = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) :=
      (w : Gal(K'/𝔭.adicCompletion K)).commutes _
    have hwβn : (w : Gal(K'/𝔭.adicCompletion K)) (β ^ n) = β ^ n := by rw [hβ, hwπ]
    have h1 : ((w : Gal(K'/𝔭.adicCompletion K)) β) ^ n = β ^ n := by
      rw [← map_pow]; exact hwβn
    rw [div_pow, h1, div_self (pow_ne_zero n hβ0)]
  let f : ↥N →* rootsOfUnity n K' :=
    { toFun := fun w => rootsOfUnity.mkOfPowEq (((w : Gal(K'/𝔭.adicCompletion K)) β) / β) (hroot w)
      map_one' := by
        apply Subtype.ext; apply Units.ext
        simp only [rootsOfUnity.coe_mkOfPowEq, OneMemClass.coe_one, Units.val_one]
        rw [AlgEquiv.one_apply, div_self hβ0]
      map_mul' := by
        intro u w
        apply Subtype.ext; apply Units.ext
        simp only [Subgroup.coe_mul, rootsOfUnity.coe_mkOfPowEq, Units.val_mul]
        have hmem : ((w : Gal(K'/𝔭.adicCompletion K)) β / β) ∈
            NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') p :=
          NK.TameStructureDeep.Tame.mem_unramifiedClosure_of_pow_eq_one (κ := 𝔭.adicCompletion K)
            (K' := K') hnp (hroot w)
        have hufix : (u : Gal(K'/𝔭.adicCompletion K))
            (((w : Gal(K'/𝔭.adicCompletion K)) β) / β) =
            ((w : Gal(K'/𝔭.adicCompletion K)) β) / β := by
          have huI : (u : Gal(K'/𝔭.adicCompletion K)) ∈
              (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
                p).fixingSubgroup := by
            rw [← NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
              (κ := 𝔭.adicCompletion K) (K' := K') p]
            exact hNI u.2
          exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp huI _ hmem
        have huβ : (u : Gal(K'/𝔭.adicCompletion K)) β ≠ 0 := fun h =>
          hβ0 ((u : Gal(K'/𝔭.adicCompletion K)).injective (by rw [h, map_zero]))
        rw [AlgEquiv.mul_apply]
        calc (u : Gal(K'/𝔭.adicCompletion K)) ((w : Gal(K'/𝔭.adicCompletion K)) β) / β
            = (u : Gal(K'/𝔭.adicCompletion K)) (((w : Gal(K'/𝔭.adicCompletion K)) β) / β) *
                (((u : Gal(K'/𝔭.adicCompletion K)) β) / β) := by
              rw [map_div₀]; field_simp
          _ = (((w : Gal(K'/𝔭.adicCompletion K)) β) / β) *
                (((u : Gal(K'/𝔭.adicCompletion K)) β) / β) := by rw [hufix]
          _ = (((u : Gal(K'/𝔭.adicCompletion K)) β) / β) *
                (((w : Gal(K'/𝔭.adicCompletion K)) β) / β) := by ring }
  have hcard : Nat.card (rootsOfUnity n K') = n := by
    haveI : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
    haveI : NeZero ((n : ℕ) : K') := ⟨by rw [Nat.cast_ne_zero]; exact hn.ne'⟩
    obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := K') (n := n)
    exact hζ.card_rootsOfUnity
  haveI : Finite ↥(rootsOfUnity n K') :=
    (Nat.card_ne_zero.mp (by rw [hcard]; exact hn.ne')).2
  have hf : f = 1 :=
    NK.TameStructureDeep.UnramifiedLevels.eq_one_of_isProP_of_coprime_card hNpro f
      (by rw [hcard]; exact hcop.symm)
  have hz1 : ((z : Gal(K'/𝔭.adicCompletion K)) β) / β = 1 := by
    have h2 : f ⟨z, hz⟩ = 1 := by rw [hf]; rfl
    have h3 := congrArg (fun w : rootsOfUnity n K' => ((w : K'ˣ) : K')) h2
    simpa [f, rootsOfUnity.coe_mkOfPowEq] using h3
  exact (div_eq_one_iff_eq hβ0).mp hz1


/-! ## Roots of unity of order prime to `p` are `ℓ`-th powers in `κ^{ur}` -/

/-- **A root of unity of order prime to `p` is an `ℓ`-th power of a root of unity of order prime to
`p`**, for `ℓ ≠ p` a prime.

For a primitive `(nℓ)`-th root of unity `η`, the power `η ^ ℓ` is a primitive `n`-th root of unity,
so a primitive `n`-th root `ζ` is a power of it, `ζ = (η ^ ℓ) ^ i = (η ^ i) ^ ℓ`; and `η ^ i` has
order dividing `nℓ`, which is prime to `p`, so it lies in `κ^{ur}`. -/
theorem exists_pow_eq_of_isPrimitiveRoot_unramifiedClosure {n ℓ : ℕ} (hn : 0 < n)
    (hnp : ¬ NK.TameStructureDeep.Tame.resCharAt 𝔭 ∣ n) (hℓ : ℓ.Prime)
    (hℓp : ℓ ≠ NK.TameStructureDeep.Tame.resCharAt 𝔭) {ζ : K'}
    (hζ : IsPrimitiveRoot ζ n) :
    ∃ w ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭), w ^ ℓ = ζ := by
  set p := NK.TameStructureDeep.Tame.resCharAt 𝔭 with hpdef
  have hp : p.Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  haveI : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  haveI : CharZero (𝔭.adicCompletion K) := Algebra.charZero_of_charZero K _
  haveI : CharZero K' := Algebra.charZero_of_charZero (𝔭.adicCompletion K) K'
  haveI : NeZero ((n * ℓ : ℕ) : K') :=
    ⟨by rw [Nat.cast_ne_zero]; exact Nat.mul_ne_zero hn.ne' hℓ.ne_zero⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨η, hη⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := K') (n := n * ℓ)
  -- `η ^ ℓ` is a primitive `n`-th root of unity
  have hηℓ : IsPrimitiveRoot (η ^ ℓ) n :=
    hη.pow (Nat.mul_pos hn hℓ.pos) (by ring)
  -- and `ζ` is a power of it
  obtain ⟨i, -, hi⟩ := hηℓ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine ⟨η ^ i, ?_, ?_⟩
  · have hpow1 : (η ^ i) ^ (n * ℓ) = 1 := by
      rw [← pow_mul, mul_comm i (n * ℓ), pow_mul, hη.pow_eq_one, one_pow]
    have hnp' : ¬ p ∣ n * ℓ := fun h => (hp.dvd_mul.mp h).elim hnp (fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp hd).symm)
    exact NK.TameStructureDeep.Tame.mem_unramifiedClosure_of_pow_eq_one (κ := 𝔭.adicCompletion K)
      (K' := K') hnp' hpow1
  · rw [← pow_mul, mul_comm i ℓ, pow_mul, hi]

end

end NK.TameStructureDeep.Tame
