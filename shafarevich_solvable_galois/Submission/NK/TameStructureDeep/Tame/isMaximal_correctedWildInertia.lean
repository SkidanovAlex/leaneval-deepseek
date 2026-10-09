import Mathlib
import Submission.NK.TameStructureDeep.Tame.CorrectedResidual
import Submission.NK.TameStructureDeep.Tame.isProCyclic_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.isProPrimeToP_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.exists_kummerLayer_of_mem_tameClosure
import Submission.NK.TameStructureDeep.Tame.exists_level_of_notMem_inertia
import Submission.NK.TameStructureDeep.Tame.exists_smul_root_unramifiedClosure
import Submission.NK.TameStructureDeep.Support.quotientImage_normal_iff
import Submission.NK.TameStructureDeep.Support.isProCyclic_quotientImage_iff
import Submission.NK.LocalTame.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The maximality of the corrected tame inertia `I_κ/V_κ`

This file proves the maximality clause of the local structure theorem in its *corrected* form:
for `V_κ = Gal(K'/κ^{tr})` the fixing subgroup of the maximal tamely ramified extension
(`NK.TameStructureDeep.Tame.correctedWildInertia`) and `I_κ = Gal(K'/κ^{ur})` the inertia subgroup,
every subgroup `J ≥ V_κ` of `G_κ = Gal(K'/κ)` whose image `J/V_κ` in `G_κ^{tr} = G_κ/V_κ` is normal
and pro-cyclic (in the finite-quotient formulation of `NK.LocalTame.IsProCyclic`) is contained in
`I_κ`.  Equivalently, `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ^{tr}`.

## The argument

Let `σ ∈ J` and suppose `σ ∉ I_κ`.  The extraction of a *level* (a prime-to-`p` integer `n`, a
primitive `n`-th root of unity `ζ` with `σ ζ ≠ ζ`, and an exponent `a` with `σ ζ = ζ ^ a` for which
in addition `n ∤ (a - 1)²`) is `exists_level_of_notMem_inertia`, an `ℓ`-adic level argument.

Choose `β` with `β ^ n = π` and, using the surjectivity of the Kummer pairing over `κ^{ur}`
(`exists_smul_root_unramifiedClosure`, proved from the *proved* layer degree `[κ^{ur}(β):κ^{ur}] = n`),
an element `τ ∈ Gal(K'/κ^{ur})` with `τ β = ζ β`.  Then

* `x := [σ, τ] ∈ J` (as `J ◁ G_κ`) and `x β = ζ ^ (a-1) β ≠ β` (`commutator_apply_root`);
* `y := [σ, x] ∈ J` and `y β = ζ ^ ((a-1)²) β ≠ β`, again by `commutator_apply_root` (applied with the
  Kummer character `ζ ^ (a-1)`).

On the other hand the image of `J` in the *finite* Galois group `Gal(E/κ)` of the layer
`E = κ(rootSet(X^n - C π))` — which is the splitting field of `X ^ n - C π` over `κ` inside `K'`,
hence finite Galois over `κ` — is a finite quotient of the pro-cyclic group `J/V_κ`, hence cyclic,
hence abelian.  As `σ, x ∈ J`, the element `y = [σ, x]` therefore acts trivially on `E`, and
in particular `y β = β`, a contradiction.  Hence `J ≤ I_κ`.
-/

open scoped Classical
open IntermediateField

namespace NK.TameStructureDeep.Tame

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

/-! ## Generic group-theoretic auxiliaries -/

/-- A cyclic group is commutative. -/
lemma commute_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (a b : G) : a * b = b * a := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  have ha : a ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top a
  have hb : b ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top b
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]

/-- An element of a cyclic subgroup commutes with every element of it. -/
lemma commute_of_isCyclic_sub {G : Type*} [Group G] {H : Subgroup G} (h : IsCyclic ↥H)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  have hc := commute_of_isCyclic (⟨a, ha⟩ : ↥H) (⟨b, hb⟩ : ↥H)
  exact congrArg Subtype.val hc

/-- In a group, commuting elements have trivial commutator. -/
lemma mul_inv_mul_inv_eq_one_of_mul_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [h, mul_assoc b a a⁻¹, mul_inv_cancel, mul_one, mul_inv_cancel]

/-- A quotient of a pro-cyclic group (in the sense of `NK.LocalTame.IsProCyclic`) is pro-cyclic. -/
lemma isProCyclic_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (h : NK.LocalTame.IsProCyclic G) :
    NK.LocalTame.IsProCyclic H := by
  intro N hN hfi
  haveI := hN
  let F : G →* H ⧸ N := (QuotientGroup.mk' N).comp f
  have hFs : Function.Surjective F := (QuotientGroup.mk'_surjective N).comp hf
  have hker : F.ker = Subgroup.comap f N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff (f x), Subgroup.mem_comap]
  have hfin : F.ker.FiniteIndex := by
    rw [hker, Subgroup.finiteIndex_iff, Subgroup.index_comap_of_surjective N hf]
    exact (Subgroup.finiteIndex_iff (H := N)).mp hfi
  have hcyc : IsCyclic (G ⧸ F.ker) := h _ hfin
  exact (QuotientGroup.quotientKerEquivOfSurjective F hFs).isCyclic.mp hcyc

/-- A homomorphic image of a pro-cyclic group is pro-cyclic. -/
lemma isProCyclic_range {G H : Type*} [Group G] [Group H] (f : G →* H)
    (h : NK.LocalTame.IsProCyclic G) : NK.LocalTame.IsProCyclic ↥(f.range) :=
  isProCyclic_of_surjective (f.codRestrict f.range (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)) (by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, rfl⟩) h

/-- A *finite* pro-cyclic group is cyclic. -/
lemma isCyclic_of_isProCyclic_of_finite {G : Type*} [Group G] [Finite G]
    (h : NK.LocalTame.IsProCyclic G) : IsCyclic G := by
  have hfi : (⊥ : Subgroup G).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    exact Subgroup.index_ne_zero_of_finite
  have hc := h ⊥ hfi
  exact (QuotientGroup.quotientBot (G := G)).isCyclic.mp hc

/-- **The Kummer commutator computation.**  Let `β ≠ 0` and let `ζ` be a primitive `n`-th root of
unity.  Suppose `σ, τ ∈ Gal(K'/κ)`, `a, a' : ℤ`, `c ∈ K'` with

* `a` and `a'` are inverse exponents (`σ ζ = ζ ^ a`, `σ (ζ ^ a') = ζ`);
* `τ` fixes `ζ` and acts on the Kummer line by the character `c`: `τ β = c * β`, `c ^ n = 1`;
* `σ` fixes `β ^ n`.

Then the commutator `[σ, τ]` acts on `β` by the character `c ^ (a - 1)`:
`(σ * τ * σ⁻¹ * τ⁻¹) β = c ^ (a - 1) * β`. -/
lemma commutator_apply_root_kummer {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    {n : ℕ} (hn : 0 < n) {β ζ c : K'} (hζ : IsPrimitiveRoot ζ n) (hβ : β ≠ 0) (hc : c ^ n = 1)
    {σ τ : Gal(K'/κ)} {a a' : ℤ}
    (hσ : σ ζ = ζ ^ a) (hσ' : σ (ζ ^ a') = ζ) (hτζ : τ ζ = ζ) (hτβ : τ β = c * β)
    (hσβ : σ (β ^ n) = β ^ n) :
    (σ * τ * σ⁻¹ * τ⁻¹) β = c ^ (a - 1) * β := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow hn.ne'] at hc; exact zero_ne_one hc
  have hcZ : c ^ (n : ℤ) = 1 := by rw [zpow_natCast, hc]
  -- (0) `ζ ^ (a * a') = ζ`, and its consequence for every `n`-th root of unity
  have hpow1 : ζ ^ (a * a') = ζ := by
    have h2 : (σ ζ) ^ a' = ζ := by rw [← map_zpow₀, hσ']
    rw [hσ, ← zpow_mul] at h2
    exact h2
  have hpowμ : ∀ w : K', w ^ n = 1 → w ^ (a * a') = w := by
    intro w hw
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hw
    rw [← hi, ← zpow_natCast ζ i, ← zpow_mul, mul_comm (i : ℤ) (a * a'), zpow_mul, hpow1]
  -- (1) the action of `σ` and `τ` on `μ_n`
  have hσμ : ∀ w : K', w ^ n = 1 → σ w = w ^ a := by
    intro w hw
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hw
    rw [← hi, map_pow, hσ, ← zpow_natCast (ζ ^ a) i, ← zpow_natCast ζ i, ← zpow_mul,
      ← zpow_mul, mul_comm]
  have hτμ : ∀ w : K', w ^ n = 1 → τ w = w := by
    intro w hw
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hw
    rw [← hi, map_pow, hτζ]
  have hτc : τ c = c := hτμ c hc
  have hσc : σ c = c ^ a := hσμ c hc
  have hcn : (c ^ a') ^ n = 1 := by
    rw [← zpow_natCast (c ^ a') n, ← zpow_mul, mul_comm a' (n : ℤ), zpow_mul, hcZ, one_zpow]
  have hσc' : σ (c ^ a') = c := by
    rw [hσμ (c ^ a') hcn, ← zpow_mul, mul_comm a' a, hpowμ c hc]
  have hσinv_c : σ⁻¹ c = c ^ a' := (AlgEquiv.symm_apply_eq σ).mpr hσc'.symm
  have hσc_inv : σ (c ^ (-a')) = c⁻¹ := by
    rw [zpow_neg, map_inv₀, hσc']
  have hβ'app : σ (σ⁻¹ β) = β := AlgEquiv.apply_symm_apply σ β
  -- (2) the Kummer character `e` of `σ⁻¹`
  set e : K' := σ⁻¹ β / β with hedef
  have heβ : σ⁻¹ β = e * β := by rw [hedef]; exact (div_mul_cancel₀ _ hβ).symm
  have hepow : e ^ n = 1 := by
    rw [hedef, div_pow]
    have h : (σ⁻¹ β) ^ n = β ^ n := by
      rw [← map_pow]
      exact (AlgEquiv.symm_apply_eq σ).mpr hσβ.symm
    rw [h, div_self (pow_ne_zero n hβ)]
  -- (3) the computation
  have hτσinv : τ (σ⁻¹ β) = c * (σ⁻¹ β) := by
    rw [heβ, map_mul, hτμ e hepow, hτβ]
    ring
  have hτcinv : τ (c ^ (-a')) = c ^ (-a') := by rw [map_zpow₀, hτc]
  have e1 : τ⁻¹ β = c⁻¹ * β :=
    (AlgEquiv.symm_apply_eq τ).mpr (by rw [map_mul, map_inv₀, hτc, hτβ, ← mul_assoc,
      inv_mul_cancel₀ hc0, one_mul])
  have e2 : σ⁻¹ (c⁻¹ * β) = c ^ (-a') * (σ⁻¹ β) := by
    rw [map_mul, map_inv₀, hσinv_c, ← zpow_neg]
  have e3 : τ (c ^ (-a') * (σ⁻¹ β)) = c ^ (-a') * (c * (σ⁻¹ β)) := by
    rw [map_mul, hτcinv, hτσinv]
  have e4 : σ (c ^ (-a') * (c * (σ⁻¹ β))) = (c⁻¹ * c ^ a) * β := by
    rw [map_mul, map_mul, hσc_inv, hσc, hβ'app, mul_assoc]
  have e5 : (c⁻¹ * c ^ a) * β = c ^ (a - 1) * β := by
    rw [← zpow_neg_one c, ← zpow_add₀ hc0, show (-1 : ℤ) + a = a - 1 by ring]
  calc (σ * τ * σ⁻¹ * τ⁻¹) β
      = σ (τ (σ⁻¹ (τ⁻¹ β))) := by simp only [AlgEquiv.mul_apply]
    _ = σ (τ (σ⁻¹ (c⁻¹ * β))) := by rw [e1]
    _ = σ (τ (c ^ (-a') * (σ⁻¹ β))) := by rw [e2]
    _ = σ (c ^ (-a') * (c * (σ⁻¹ β))) := by rw [e3]
    _ = (c⁻¹ * c ^ a) * β := by rw [e4]
    _ = c ^ (a - 1) * β := e5


/-! ## The finite Galois layer `κ(rootSet(X ^ n - C π))` -/

/-- **The finite layer of the Kummer data**: the splitting field of `X ^ n - C π` over `κ` inside
`K'`, i.e. the field generated by the `n`-th roots of the uniformiser.  For `β ^ n = π` and `ζ` a
primitive `n`-th root of unity it is `κ(β, ζ)`. -/
noncomputable def kummerLayer (n : ℕ) (π : 𝔭.adicCompletionIntegers K) :
    IntermediateField (𝔭.adicCompletion K) K' :=
  IntermediateField.adjoin (𝔭.adicCompletion K)
    ((Polynomial.X ^ n - Polynomial.C (π : 𝔭.adicCompletion K)).rootSet K')

/-- An `n`-th root of the uniformiser lies in the layer. -/
lemma kummerLayer_mem_of_pow_eq {n : ℕ} (hn : n ≠ 0) {π : 𝔭.adicCompletionIntegers K} {β : K'}
    (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) :
    β ∈ kummerLayer 𝔭 n π := by
  refine IntermediateField.subset_adjoin _ _ ?_
  rw [Polynomial.mem_rootSet]
  refine ⟨Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) _, ?_⟩
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [sub_eq_zero]
  exact hβ

/-- A primitive `n`-th root of unity lies in the layer. -/
lemma kummerLayer_mem_of_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) {π : 𝔭.adicCompletionIntegers K}
    {β ζ : K'} (hβ0 : β ≠ 0)
    (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    (hζ : IsPrimitiveRoot ζ n) : ζ ∈ kummerLayer 𝔭 n π := by
  have hβζ : β * ζ ∈ kummerLayer 𝔭 n π :=
    kummerLayer_mem_of_pow_eq 𝔭 hn (by rw [mul_pow, hβ, hζ.pow_eq_one, mul_one])
  have hβm : β ∈ kummerLayer 𝔭 n π := kummerLayer_mem_of_pow_eq 𝔭 hn hβ
  have hζeq : ζ = (β * ζ) * β⁻¹ := by field_simp
  rw [hζeq]
  exact IntermediateField.mul_mem _ hβζ (IntermediateField.inv_mem _ hβm)

/-- Every element of the layer lies in the maximal tamely ramified extension, for `n` prime to `p`. -/
lemma kummerLayer_le_tameClosure {n : ℕ} (hn : n ≠ 0) (hnp : ¬ resCharAt 𝔭 ∣ n)
    {π : 𝔭.adicCompletionIntegers K} {β : K'} (hβ0 : β ≠ 0)
    (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) :
    kummerLayer 𝔭 n π ≤ tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  intro y hy
  rw [Polynomial.mem_rootSet] at hy
  obtain ⟨-, hyroot⟩ := hy
  have hyn : y ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := by
    have h := hyroot
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
    rw [sub_eq_zero] at h
    exact h
  have hπne : algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) ≠ 0 := by
    rw [← hβ]
    exact pow_ne_zero n hβ0
  have hratio : (y / β) ^ n = 1 := by
    rw [div_pow, hyn, hβ, div_self hπne]
  have hβtr : β ∈ tameClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
      (π : 𝔭.adicCompletion K) :=
    adjoin_root_mem_tameClosure hnp hβ (IntermediateField.mem_adjoin_simple_self _ β)
  have hunr : y / β ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K)
      (K' := K') (resCharAt 𝔭) := by
    refine mem_unramifiedClosure_of_isPrimitiveRoot ?_ (IsPrimitiveRoot.iff_orderOf.mpr rfl)
    intro hdvd
    exact hnp (hdvd.trans (orderOf_dvd_iff_pow_eq_one.mpr hratio))
  rw [show y = (y / β) * β from (div_mul_cancel₀ y hβ0).symm]
  exact IntermediateField.mul_mem _ (le_trans (unramifiedClosure_le_tameClosure _ _) le_rfl hunr) hβtr

/-! ## The maximality theorem -/

theorem isMaximal_correctedWildInertia {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    [hV : (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).Normal] :
    ∀ J : Subgroup (Gal(K'/𝔭.adicCompletion K)),
      NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) ≤ J →
      (NK.LocalTame.quotientImage
        (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)) J).Normal →
      NK.LocalTame.IsProCyclic
        ↥(NK.LocalTame.quotientImage
          (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
            (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)) J) →
      J ≤ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) := by
  classical
  -- the wild inertia, abbreviated
  set V : Subgroup (Gal(K'/𝔭.adicCompletion K)) :=
    correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
      (π : 𝔭.adicCompletion K) with hVdef
  haveI hVnorm : V.Normal := hV
  intro J hVJ hJnorm hJcyc σ hσJ
  by_contra hσI
  -- ### 0. The residue characteristic and the Kummer formalism
  have hp : (resCharAt 𝔭).Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  haveI hcharK : CharZero (𝔭.adicCompletion K) := Algebra.charZero_of_charZero K (𝔭.adicCompletion K)
  haveI hcharK' : CharZero K' := Algebra.charZero_of_charZero (𝔭.adicCompletion K) K'
  haveI hsepclosed : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  have hπ0 : (π : 𝔭.adicCompletion K) ≠ 0 := by
    intro h
    have hz : π = 0 := Subtype.ext h
    exact IsDiscreteValuationRing.not_a_field (𝔭.adicCompletionIntegers K)
      (by rw [hπ, hz, Ideal.span_singleton_eq_bot])
  -- ### 1. `J` is normal in `G_κ` and `J/V` is pro-cyclic
  have hJnormal : J.Normal :=
    (NK.TameStructureDeep.Support.quotientImage_normal_iff hVJ).mp hJnorm
  have hcyc : NK.LocalTame.IsProCyclic (↥J ⧸ V.subgroupOf J) :=
    (NK.TameStructureDeep.Support.isProCyclic_quotientImage_iff (V := V) (I := J)).mp hJcyc
  haveI hsubnorm : (V.subgroupOf J).Normal := hVnorm.subgroupOf J
  -- ### 2. The prime-to-`p` level at which `σ` is non-trivial
  obtain ⟨n, hnp, hn1, ζ, hζ, hσζ, a, hσa, hdiv1, hdiv2⟩ :=
    exists_level_of_notMem_inertia (κ := 𝔭.adicCompletion K) (K' := K') hp hσI
  have hn0 : 0 < n := lt_trans zero_lt_one hn1
  have hnne : n ≠ 0 := hn0.ne'
  have hcast0 : (n : 𝔭.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr hnne
  haveI : NeZero n := ⟨hnne⟩
  haveI : NeZero (n : K') := ⟨Nat.cast_ne_zero.mpr hnne⟩
  have hcop : Nat.Coprime n (resCharAt 𝔭) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnp |>.symm
  -- ### 3. The Kummer layer, a root `β` of `π`, and the inertial element `τ`
  obtain ⟨β, hβ⟩ : ∃ β : K',
      β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) :=
    IsSepClosed.exists_pow_nat_eq
      (algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) n
  have hβ0 : β ≠ 0 := by
    intro h
    have h1 : algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) = 0 := by
      rw [← hβ, h, zero_pow hnne]
    exact hπ0 (FaithfulSMul.algebraMap_injective (𝔭.adicCompletion K) K' (by simpa using h1))
  obtain ⟨τ, hτmem, hτβ, hτζ⟩ := exists_smul_root_unramifiedClosure 𝔭 hn0 hcop hπ hβ hζ
  -- the inverse exponent of `σ` on `μ_n`
  obtain ⟨a', ha'⟩ : ∃ a' : ℤ, σ (ζ ^ a') = ζ := by
    have h1 : (σ.symm ζ) ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨(i : ℤ), ?_⟩
    rw [zpow_natCast, hi]
    exact AlgEquiv.apply_symm_apply σ ζ
  have hσπ : σ (algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) =
      algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := σ.commutes _
  have hσβn : σ (β ^ n) = β ^ n := by rw [hβ, hσπ]
  -- ### 4. The two commutators
  set x : Gal(K'/𝔭.adicCompletion K) := σ * τ * σ⁻¹ * τ⁻¹ with hxdef
  have hxJ : x ∈ J := by
    have h1 : τ * σ⁻¹ * τ⁻¹ ∈ J := by
      have hc := hJnormal.conj_mem σ⁻¹ (Subgroup.inv_mem _ hσJ) τ
      simpa only [mul_assoc] using hc
    have h2 : σ * (τ * σ⁻¹ * τ⁻¹) ∈ J := Subgroup.mul_mem _ hσJ h1
    simpa only [hxdef, mul_assoc] using h2
  have hxβ : x β = ζ ^ (a - 1) * β := by
    have h := commutator_apply_root_kummer (κ := 𝔭.adicCompletion K) hn0 hζ hβ0 hζ.pow_eq_one
      hσa ha' hτζ hτβ hσβn
    simpa only [hxdef] using h
  have hxζ : x ζ = ζ := by
    have hτinv : τ⁻¹ ζ = ζ := (AlgEquiv.symm_apply_eq τ).mpr hτζ.symm
    have hσinv : σ⁻¹ ζ = ζ ^ a' := (AlgEquiv.symm_apply_eq σ).mpr ha'.symm
    rw [hxdef]
    simp only [AlgEquiv.mul_apply]
    rw [hτinv, hσinv, map_zpow₀, hτζ, ha']
  set y : Gal(K'/𝔭.adicCompletion K) := σ * x * σ⁻¹ * x⁻¹ with hydef
  have hyJ : y ∈ J := by
    have h1 : x * σ⁻¹ * x⁻¹ ∈ J := by
      have hc := hJnormal.conj_mem σ⁻¹ (Subgroup.inv_mem _ hσJ) x
      simpa only [mul_assoc] using hc
    have h2 : σ * (x * σ⁻¹ * x⁻¹) ∈ J := Subgroup.mul_mem _ hσJ h1
    simpa only [hydef, mul_assoc] using h2
  have hyβ : y β = ζ ^ ((a - 1) * (a - 1)) * β := by
    -- the second commutator, with the Kummer character `ζ ^ (a - 1)`
    have hζZ : ζ ^ (n : ℤ) = 1 := by rw [zpow_natCast, hζ.pow_eq_one]
    have hc2 : (ζ ^ (a - 1)) ^ n = 1 := by
      rw [← zpow_natCast (ζ ^ (a - 1)) n, ← zpow_mul, mul_comm (a - 1) (n : ℤ), zpow_mul,
        hζZ, one_zpow]
    have h := commutator_apply_root_kummer (κ := 𝔭.adicCompletion K) hn0 hζ hβ0 hc2
      hσa ha' hxζ hxβ hσβn
    rw [← zpow_mul] at h
    simpa only [hydef] using h
  -- ### 5. The finite Galois layer `E` and cyclicity of the image of `J`
  let E : IntermediateField (𝔭.adicCompletion K) K' := kummerLayer 𝔭 n π
  have hEβ : β ∈ E := kummerLayer_mem_of_pow_eq 𝔭 hnne hβ
  have hEle : E ≤ tameClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
      (π : 𝔭.adicCompletion K) := kummerLayer_le_tameClosure 𝔭 hnne hnp hβ0 hβ
  have hVE : V ≤ E.fixingSubgroup := IntermediateField.fixingSubgroup_le hEle
  haveI hsplit : Polynomial.IsSplittingField (𝔭.adicCompletion K) ↥E
      (Polynomial.X ^ n - Polynomial.C (π : 𝔭.adicCompletion K)) := by
    refine IntermediateField.adjoin_rootSet_isSplittingField (K := 𝔭.adicCompletion K)
      (L := K') (p := Polynomial.X ^ n - Polynomial.C (π : 𝔭.adicCompletion K)) ?_
    exact IsSepClosed.splits_codomain (Polynomial.X ^ n - Polynomial.C (π : 𝔭.adicCompletion K))
      (Polynomial.separable_X_pow_sub_C (π : 𝔭.adicCompletion K) hcast0 hπ0)
  haveI hfindim : FiniteDimensional (𝔭.adicCompletion K) ↥E :=
    Polynomial.IsSplittingField.finiteDimensional ↥E
      (Polynomial.X ^ n - Polynomial.C (π : 𝔭.adicCompletion K))
  haveI hgal : IsGalois (𝔭.adicCompletion K) ↥E :=
    IsGalois.of_separable_splitting_field
      (Polynomial.separable_X_pow_sub_C (π : 𝔭.adicCompletion K) hcast0 hπ0)
  haveI hEnorm : E.fixingSubgroup.Normal := IsGalois.fixingSubgroup_normal_of_isGalois E
  have hEfin : E.fixingSubgroup.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, ← IntermediateField.finrank_eq_fixingSubgroup_index K' E]
    exact ne_of_gt Module.finrank_pos
  -- the restriction map `J → G_κ ⧸ Gal(K'/E)`, factoring through `J/V`
  let ψ : ↥J →* Gal(K'/𝔭.adicCompletion K) ⧸ E.fixingSubgroup :=
    (QuotientGroup.mk' E.fixingSubgroup).comp J.subtype
  have hfac : V.subgroupOf J ≤ ψ.ker := by
    intro v hv
    rw [MonoidHom.mem_ker]
    have hvV : (v : Gal(K'/𝔭.adicCompletion K)) ∈ V := (Subgroup.mem_subgroupOf).mp hv
    show (QuotientGroup.mk' E.fixingSubgroup) (v : Gal(K'/𝔭.adicCompletion K)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hVE hvV
  let ψ' : (↥J ⧸ V.subgroupOf J) →* Gal(K'/𝔭.adicCompletion K) ⧸ E.fixingSubgroup :=
    QuotientGroup.lift _ ψ hfac
  haveI : Fintype (Gal(K'/𝔭.adicCompletion K) ⧸ E.fixingSubgroup) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  haveI : Finite ↥ψ'.range := inferInstance
  have hprocyc : NK.LocalTame.IsProCyclic ↥ψ'.range := isProCyclic_range ψ' hcyc
  have hcycr : IsCyclic ↥ψ'.range := isCyclic_of_isProCyclic_of_finite hprocyc
  have hcomp : ψ'.comp (QuotientGroup.mk' (V.subgroupOf J)) = ψ :=
    QuotientGroup.lift_comp_mk' _ _ hfac
  -- ### 6. `y` acts trivially on `E`
  have hyE : y ∈ E.fixingSubgroup := by
    rw [← QuotientGroup.eq_one_iff y]
    show ψ ⟨y, hyJ⟩ = 1
    have heq : (⟨y, hyJ⟩ : ↥J) =
        (⟨σ, hσJ⟩ : ↥J) * (⟨x, hxJ⟩ : ↥J) * (⟨σ, hσJ⟩ : ↥J)⁻¹ * (⟨x, hxJ⟩ : ↥J)⁻¹ := by
      ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hydef]
    rw [← hcomp, heq]
    simp only [MonoidHom.comp_apply, map_mul, map_inv]
    refine mul_inv_mul_inv_eq_one_of_mul_comm ?_
    exact commute_of_isCyclic_sub hcycr (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hyβfix : y β = β := (IntermediateField.mem_fixingSubgroup_iff E y).mp hyE β hEβ
  -- ### 7. Contradiction
  have hζsq : ζ ^ ((a - 1) * (a - 1)) = 1 := by
    have h1 : ζ ^ ((a - 1) * (a - 1)) * β = β := by rw [← hyβ, hyβfix]
    exact mul_right_cancel₀ hβ0 (by simpa [mul_assoc] using h1)
  refine hdiv2 ?_
  have h := (hζ.zpow_eq_one_iff_dvd ((a - 1) * (a - 1))).mp hζsq
  rwa [← show ((a - 1) ^ 2 : ℤ) = (a - 1) * (a - 1) by ring] at h

end

end NK.TameStructureDeep.Tame
