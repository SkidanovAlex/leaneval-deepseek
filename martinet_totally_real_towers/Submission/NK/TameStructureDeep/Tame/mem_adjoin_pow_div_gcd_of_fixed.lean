import Mathlib
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.Kummer
import Submission.NK.TameStructureDeep.Support.mem_unramifiedClosure_of_isPrimitiveRoot
import Submission.NK.TameStructureDeep.Tame.layerDegree
import Submission.NK.TameStructureDeep.Tame.kummerLayer_fixedField_pow

namespace NK.TameStructureDeep.Tame

open Polynomial IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-! ## Two lattice lemmas relating `adjoin` over an intermediate field to `⊔` -/

/-- `adjoin` of `L ∪ S` is the join of `L` with the `adjoin` of `S`. -/
theorem adjoin_union_eq_sup {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (S : Set E) :
    IntermediateField.adjoin F (↑L ∪ S) = L ⊔ IntermediateField.adjoin F S := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · exact (SetLike.coe_subset_coe.mpr le_sup_left) hx
    · exact (SetLike.coe_subset_coe.mpr le_sup_right) (IntermediateField.subset_adjoin F S hx)
  · refine sup_le (fun x hx => IntermediateField.subset_adjoin F _ (Set.subset_union_left hx)) ?_
    exact IntermediateField.adjoin_le_iff.mpr
      (fun x hx => IntermediateField.subset_adjoin F _ (Set.subset_union_right hx))

/-- Membership in `adjoin L {y}` over the base `↥L` is membership in `L ⊔ adjoin F {y}`. -/
theorem mem_adjoin_singleton_iff_mem_sup {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (y x : E) :
    x ∈ IntermediateField.adjoin ↥L ({y} : Set E) ↔
      x ∈ L ⊔ IntermediateField.adjoin F ({y} : Set E) := by
  have h : IntermediateField.restrictScalars F (IntermediateField.adjoin ↥L ({y} : Set E))
      = L ⊔ IntermediateField.adjoin F ({y} : Set E) := by
    rw [IntermediateField.restrictScalars_adjoin, adjoin_union_eq_sup]
  rw [← h, IntermediateField.mem_restrictScalars]

/-! ## Lifting a power-fixing hypothesis across the Galois correspondence -/

/-- **Lifting a power-fixing hypothesis from `Gal(E/F)` to `Gal(↥M/↥L)`.**

Let `L` be an intermediate field of `E/F` with `E/F` normal and `M` an intermediate field of
`E/↥L`.  If `x ∈ M` is fixed by the `m`-th powers of all the `F`-automorphisms of `E` that fix
`L` pointwise, then the image of `x` in `M` is fixed by the `m`-th powers of all the
`↥L`-automorphisms of `M`. -/
theorem pow_fixed_of_mem_fixingSubgroup {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Normal F E] (L : IntermediateField F E) (M : IntermediateField ↥L E) {m : ℕ} {x : E}
    (hxM : x ∈ M) (hfix : ∀ σ : Gal(E/F), σ ∈ L.fixingSubgroup → (σ ^ m) x = x) :
    ∀ τ : Gal(↥M / ↥L), (τ ^ m) ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
  haveI : Normal ↥L E := inferInstance
  intro τ
  have hlift_apply : ∀ y : ↥M, (τ.liftNormal E) (y : E) = (τ y : E) := by
    intro y
    have h := AlgEquiv.liftNormal_commutes τ E y
    simpa using h
  have hlift : ∀ k : ℕ, ∀ y : ↥M, ((τ.liftNormal E) ^ k) (y : E) = ((τ ^ k) y : E) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hlift_apply, ih]
  set χ : Gal(E/↥L) := τ.liftNormal E with hχ
  set σ : ↥L.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv L).symm χ with hσ
  have hχσ : ∀ y : E, χ y = ((σ : Gal(E/F))) y := fun y => rfl
  have hpow : ∀ k : ℕ, ∀ y : E, (χ ^ k) y = (((σ : Gal(E/F))) ^ k) y := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, hχσ]
  have h4 : ((τ ^ m) ⟨x, hxM⟩ : E) = x := by
    rw [(hlift m ⟨x, hxM⟩).symm, hpow m x]
    exact hfix _ σ.2
  exact Subtype.ext h4

end

/-! ## The main statement -/

/-- **The layer computation in the ambient separable closure.**  Let `κ = K_𝔭`, `F = κ^{ur}` its
maximal unramified extension inside a separable closure `K'`, `π` a uniformiser, `p` the residue
characteristic, and `β` an `n`-th root of `π` with `p ∤ n` (so that `[F⟮β⟯ : F] = n`).  If
`x ∈ F ⊔ κ⟮β⟯` is fixed by the `m`-th power of every element of the inertia subgroup `I =
Gal(K'/F)`, then `x` already lies in the smaller layer `F ⊔ κ⟮β ^ (n / gcd n m)⟯`. -/
theorem mem_adjoin_pow_div_gcd_of_fixed {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π)
    {n m : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n (resCharAt 𝔭)) {β x : K'}
    (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    (hx : x ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) ⊔
      IntermediateField.adjoin (𝔭.adicCompletion K) ({β} : Set K'))
    (hfix : ∀ σ : Gal(K'/(𝔭.adicCompletion K)),
      σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)).fixingSubgroup →
      (σ ^ m) x = x) :
    x ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) ⊔
      IntermediateField.adjoin (𝔭.adicCompletion K) ({β ^ (n / Nat.gcd n m)} : Set K') := by
  classical
  haveI hczk : CharZero (𝔭.adicCompletion K) := Algebra.charZero_of_charZero K (𝔭.adicCompletion K)
  haveI hcz : CharZero K' := Algebra.charZero_of_charZero (𝔭.adicCompletion K) K'
  -- the maximal unramified extension `F = κ^{ur}`
  set F : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) with hF
  haveI hczF : CharZero ↥F := inferInstance
  -- the uniformiser as an element of `F`
  set a : ↥F := uniformizerInClosure 𝔭 (K' := K') π with ha
  have hβa : β ^ n = algebraMap ↥F K' a := by
    rw [hβ]
    simp [ha, uniformizerInClosure]
  -- `F⟮β⟯` has degree `n` over `F`, so `X ^ n - C a` is the minimal polynomial of `β`
  have hβint : IsIntegral ↥F β :=
    ⟨X ^ n - C a, monic_X_pow_sub_C a hn.ne', by simp [hβa]⟩
  have hfin : Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({β} : Set K')) = n :=
    finrank_adjoin_urCl 𝔭 hn hcop hπ hβ
  have hminp : (minpoly ↥F β).natDegree = n := by
    rw [← adjoin.finrank hβint]
    exact hfin
  have hdvd : minpoly ↥F β ∣ X ^ n - C a :=
    minpoly.dvd ↥F β (by simp [hβa])
  have hminpeq : X ^ n - C a = minpoly ↥F β :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβint) (monic_X_pow_sub_C a hn.ne')
      hdvd (by rw [natDegree_X_pow_sub_C, hminp])
  have hirr : Irreducible (X ^ n - C a) := by
    rw [hminpeq]
    exact minpoly.irreducible hβint
  -- a primitive `n`-th root of unity inside `F`
  have hp : (resCharAt 𝔭).Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hpnd : ¬ resCharAt 𝔭 ∣ n :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hcop)
  haveI : NeZero (n : K') := ⟨(Nat.cast_ne_zero).mpr hn.ne'⟩
  haveI : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := K') (n := n)
  have hζF : ζ ∈ F := NK.TameStructureDeep.mem_unramifiedClosure_of_isPrimitiveRoot hpnd hζ
  have hζsub : (primitiveRoots n ↥F).Nonempty :=
    ⟨⟨ζ, hζF⟩, (mem_primitiveRoots hn).mpr
      ((IsPrimitiveRoot.coe_submonoidClass_iff (N := F) (ζ := (⟨ζ, hζF⟩ : ↥F))).mp hζ)⟩
  -- membership of `x` in `F⟮β⟯`
  have hxM : x ∈ IntermediateField.adjoin ↥F ({β} : Set K') :=
    (mem_adjoin_singleton_iff_mem_sup F β x).mpr hx
  -- the power-fixing hypothesis for `Gal(F⟮β⟯/F)`
  have hfix' := pow_fixed_of_mem_fixingSubgroup F (IntermediateField.adjoin ↥F ({β} : Set K')) hxM hfix
  -- Kummer theory over `F`
  have hres := kummerLayer_fixedField_pow (F := ↥F) (E := K') (n := n) (m := m) hn (a := a)
    hβa hζsub hirr hxM hfix'
  exact (mem_adjoin_singleton_iff_mem_sup F (β ^ (n / Nat.gcd n m)) x).mp hres

end NK.TameStructureDeep.Tame
