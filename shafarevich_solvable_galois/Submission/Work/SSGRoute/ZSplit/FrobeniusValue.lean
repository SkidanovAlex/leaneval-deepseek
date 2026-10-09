import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime
import Submission.Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.shafarevich_z_data_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The value of a locally constant class at a Frobenius, and the level-`K` Kummer cochain

This file contains the local layer which Schmidt--Wingberg's §4 construction of the auxiliary class
`z` (Theorem 13, `A = μ_p`, `Submission/Work/SSGRoute/z_data_mup_arith.lean`'s
`Work.SSGRoute.sw_z_exists_odd_sketch`) uses to talk about "the value of a class at the Frobenius":
the verification of the sharpened condition (b) of that construction compares the *values at a
Frobenius element* of two classes which are unramified at the place in question, and the bookkeeping
of condition (1) ("`(z_i)_{P_i} ≡ Frob_{P_i}` modulo `H¹_nr`") needs the fact that such a value is
well defined.

Everything here is in the *trivial coefficient* setting actually used by §4: the cocycle
`z : G_k → ZMod p` is additive on `K.fixingSubgroup` (`K` a finite Galois level of `k`).  In that
case `z` restricted to `K.fixingSubgroup` is a group homomorphism into `(ZMod p, +)`, so

`z (g ^ m) = m • z g`   for every `m : ℤ`,

and if `τ * (σ ^ m)⁻¹` lies in the kernel of the restriction to a level `L` and `z` kills that
kernel, then `z τ = m • z σ`.

## Main results

* `z_zpow_eq_zsmul`, `localValue_eq_zsmul_of_res_eq_zpow` — the two computations above;
* `localValue_eq_zero_of_frob_eq_zero`, `localValue_eq_of_agree_on_frob` — an unramified class is
  determined on the whole local group by its value at a Frobenius element (the two statements used
  in the §4 verification);
* `localValue_eq_zsmul_of_isFrobAtPrime`, `localValue_eq_zero_of_isFrobAtPrime` — the same with the
  "`res k L τ` is a power of the Frobenius" input produced from
  `Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime`;
* `hker_of_kills_inertia` — the level-kernel hypothesis of the above is implied by "kills the
  inertia" as soon as the level `L` captures the unramified part at the place;
* `nodeKummerCocharZMod` — the level-`K` Kummer cochain of `β ∈ Kˣ` for a general prime `p`
  (`ζ_p ∈ K`), the general-`p` companion of `Work.SSGRoute.nodeKummerCochar` (`p = 2`), with its
  additivity; this is the entry point of Shafarevich's Kummer-theoretic construction of §4.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZSplit

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime]
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-! ## The local value at a Frobenius element -/

/-- **Integer powers of an additive map**: if `z` is additive on a subgroup `H` (in the trivial
coefficient setting), then `z (g ^ m) = m • z g` for every `m : ℤ`. -/
theorem z_zpow_eq_zsmul {H : Subgroup (Ω ≃ₐ[k] Ω)} {z : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hz : ∀ g ∈ H, ∀ h ∈ H, z (g * h) = z g + z h) (g : Ω ≃ₐ[k] Ω) (hg : g ∈ H) (m : ℤ) :
    z (g ^ m) = m • z g := by
  have hz1 : z 1 = 0 := by
    have h := hz 1 H.one_mem 1 H.one_mem
    rw [one_mul] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  let f : H →* Multiplicative (ZMod p) :=
    { toFun := fun x => Multiplicative.ofAdd (z x)
      map_one' := by
        show Multiplicative.ofAdd (z 1) = 1
        rw [hz1]; rfl
      map_mul' := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        show Multiplicative.ofAdd (z (a * b)) =
          Multiplicative.ofAdd (z a) * Multiplicative.ofAdd (z b)
        rw [hz a ha b hb, ofAdd_add] }
  have h := map_zpow f (⟨g, hg⟩ : H) m
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_zpow] at h
  exact Multiplicative.ofAdd.injective h

/-- **The local value of a class at a Frobenius power.**

Let `z` be additive on `K.fixingSubgroup`, `A` a place, `L` a finite Galois level, and
`σ, τ ∈ decomp k A ⊓ K.fixingSubgroup` with `res k L τ = (res k L σ) ^ m`.  If `z` kills the
*level kernel* inside the local group
(`∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → z u = 0`) then `z τ = m • z σ`.

This is the computation behind "an unramified class is determined by its value at the Frobenius":
the caller supplies the power relation from
`Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime`, and the level-kernel hypothesis
holds for any class killing the inertia as soon as `L` captures the maximal unramified subextension
(see `hker_of_kills_inertia`). -/
theorem localValue_eq_zsmul_of_res_eq_zpow
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ decomp k A ⊓ K.fixingSubgroup)
    (τ : Ω ≃ₐ[k] Ω) (hτ : τ ∈ decomp k A ⊓ K.fixingSubgroup)
    (m : ℤ) (hm : res k L τ = (res k L σ) ^ m)
    (hker : ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → z u = 0) :
    z τ = m • z σ := by
  have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
  have hσD : σ ∈ decomp k A := (Subgroup.mem_inf.mp hσ).1
  have hτK : τ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hτ).2
  have hτD : τ ∈ decomp k A := (Subgroup.mem_inf.mp hτ).1
  have hσmK : σ ^ m ∈ K.fixingSubgroup := K.fixingSubgroup.zpow_mem hσK m
  have hσmD : σ ^ m ∈ decomp k A := (decomp k A).zpow_mem hσD m
  have huK : τ * (σ ^ m)⁻¹ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem hτK (K.fixingSubgroup.inv_mem hσmK)
  have huD : τ * (σ ^ m)⁻¹ ∈ decomp k A :=
    (decomp k A).mul_mem hτD ((decomp k A).inv_mem hσmD)
  have hres1 : res k L (τ * (σ ^ m)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hm, mul_inv_cancel]
  have hu0 : z (τ * (σ ^ m)⁻¹) = 0 :=
    hker _ (Subgroup.mem_inf.mpr ⟨huD, huK⟩) hres1
  have hmul : z τ = z (τ * (σ ^ m)⁻¹) + z (σ ^ m) := by
    have h := hz (τ * (σ ^ m)⁻¹) huK (σ ^ m) hσmK
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h
  rw [hmul, hu0, zero_add, z_zpow_eq_zsmul hz σ hσK m]

/-- **An unramified class whose value at a Frobenius element vanishes is trivial on the local
group.**  (`m = 0` in the exponent, i.e. `z σ = 0`.) -/
theorem localValue_eq_zero_of_frob_eq_zero
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ decomp k A ⊓ K.fixingSubgroup)
    (hpow : ∀ τ ∈ decomp k A ⊓ K.fixingSubgroup,
      ∃ m : ℤ, res k L τ = (res k L σ) ^ m)
    (hker : ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → z u = 0)
    (hval : z σ = 0) :
    ∀ τ ∈ decomp k A ⊓ K.fixingSubgroup, z τ = 0 := by
  intro τ hτ
  obtain ⟨m, hm⟩ := hpow τ hτ
  rw [localValue_eq_zsmul_of_res_eq_zpow K L A z hz σ hσ τ hτ m hm hker, hval, smul_zero]

/-- **Two classes unramified at `A` which agree at a Frobenius element agree on the whole local
group.**  This is the step Schmidt--Wingberg use in the verification of condition (b): "since `z_i`
and `z_N` are unramified at `σP_N`, it suffices to show that their values on `Frob_{σP_N}` are
mutually inverse". -/
theorem localValue_eq_of_agree_on_frob
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (z z' : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hz' : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z' (g * h) = z' g + z' h)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ decomp k A ⊓ K.fixingSubgroup)
    (hpow : ∀ τ ∈ decomp k A ⊓ K.fixingSubgroup,
      ∃ m : ℤ, res k L τ = (res k L σ) ^ m)
    (hker : ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → z u = 0)
    (hker' : ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → z' u = 0)
    (hval : z σ = z' σ) :
    ∀ τ ∈ decomp k A ⊓ K.fixingSubgroup, z τ = z' τ := by
  intro τ hτ
  obtain ⟨m, hm⟩ := hpow τ hτ
  rw [localValue_eq_zsmul_of_res_eq_zpow K L A z hz σ hσ τ hτ m hm hker,
    localValue_eq_zsmul_of_res_eq_zpow K L A z' hz' σ hσ τ hτ m hm hker', hval]

/-- **The level-kernel hypothesis from "kills the inertia".**  If every element of the local group
which restricts trivially to the level `L` is an inertia element at `A` (true as soon as `L`
contains the maximal unramified subextension of the local field, e.g. whenever `L` is large enough
compared with the residue field extension), then a class killing the inertia kills the level kernel
of the local group. -/
theorem hker_of_kills_inertia
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hLI : ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → IsInertia k A u)
    (hzI : ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, IsInertia k A u → z u = 0) :
    ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → z u = 0 :=
  fun u hu hu1 => hzI u hu (hLI u hu hu1)

/-! ## The same statements with the Frobenius input produced from `IsFrobAtPrime` -/

/-- **The local value of a class at a Frobenius element, in the form used by §4.**  If `L/k` is
unramified at `A` and `res k L σ` is a Frobenius at `A`, then every `τ` in the local group has
`res k L τ` a power of `res k L σ` (this is
`Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime`), hence `z τ = m • z σ` for the
corresponding `m : ℤ`. -/
theorem localValue_eq_zsmul_of_isFrobAtPrime
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    (hunrL : ¬ IsRamifiedIn k L A)
    (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ decomp k A ⊓ K.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (res k L σ))
    (hker : ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → z u = 0)
    (τ : Ω ≃ₐ[k] Ω) (hτ : τ ∈ decomp k A ⊓ K.fixingSubgroup) :
    ∃ m : ℤ, z τ = m • z σ := by
  have hpram : (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers k) = 1 :=
    Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn k Ω L A hA hunrL
  have hmap : (decomp k A).map (res k L) = Subgroup.zpowers (res k L σ) :=
    Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime k Ω L A hA 𝔭 h𝔭 hpram σ
      (Subgroup.mem_inf.mp hσ).1 hfrob
  have hmem : res k L τ ∈ (decomp k A).map (res k L) :=
    Subgroup.mem_map.mpr ⟨τ, (Subgroup.mem_inf.mp hτ).1, rfl⟩
  rw [hmap] at hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact ⟨m, localValue_eq_zsmul_of_res_eq_zpow K L A z hz σ hσ τ hτ m hm.symm hker⟩

/-- **The powers of a Frobenius generate the restrictions of the local group** — the `hpow`
hypothesis of `localValue_eq_zero_of_frob_eq_zero` / `localValue_eq_of_agree_on_frob`, produced from
`IsFrobAtPrime`. -/
theorem localGroup_pow_of_isFrobAtPrime
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    (hunrL : ¬ IsRamifiedIn k L A)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ decomp k A)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (res k L σ)) :
    ∀ τ ∈ decomp k A ⊓ K.fixingSubgroup,
      ∃ m : ℤ, res k L τ = (res k L σ) ^ m := by
  have hpram : (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers k) = 1 :=
    Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn k Ω L A hA hunrL
  have hmap : (decomp k A).map (res k L) = Subgroup.zpowers (res k L σ) :=
    Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime k Ω L A hA 𝔭 h𝔭 hpram σ
      hσ hfrob
  intro τ hτ
  have hmem : res k L τ ∈ (decomp k A).map (res k L) :=
    Subgroup.mem_map.mpr ⟨τ, (Subgroup.mem_inf.mp hτ).1, rfl⟩
  rw [hmap] at hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact ⟨m, hm.symm⟩

/-- **Unramified classes are determined by their value at a Frobenius** (the §4 verification step):
if `z` kills the level kernel of the local group and vanishes at a Frobenius element `σ` of a level
`L` unramified at `A`, then `z` vanishes on the whole local group. -/
theorem localValue_eq_zero_of_isFrobAtPrime
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    (hunrL : ¬ IsRamifiedIn k L A)
    (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ decomp k A ⊓ K.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (res k L σ))
    (hker : ∀ u ∈ decomp k A ⊓ K.fixingSubgroup, res k L u = 1 → z u = 0)
    (hval : z σ = 0) :
    ∀ τ ∈ decomp k A ⊓ K.fixingSubgroup, z τ = 0 :=
  localValue_eq_zero_of_frob_eq_zero K L A z hz σ hσ
    (localGroup_pow_of_isFrobAtPrime K L A hA 𝔭 h𝔭 hunrL σ (Subgroup.mem_inf.mp hσ).1 hfrob)
    hker hval

/-! ## The level-`K` Kummer cochain for a general prime `p`

`H¹(k_S|K, μ_p) ≅ Kˣ/(Kˣ)^p` whenever `ζ_p ∈ K`; the cocycle attached to `β ∈ Kˣ` is the Kummer
character of `β`.  The `p = 2` instance is `Work.SSGRoute.nodeKummerCochar`; the general-`p`
version below is what the Kummer-theoretic form of Schmidt--Wingberg's §4 construction
(Shafarevich's existence theorem [12]) consumes. -/

section KummerCocharZMod

variable [IsAlgClosed Ω]

/-- A primitive `p`-th root of unity in `Ω` lying in `K` is primitive in `K`. -/
lemma isPrimitiveRoot_subtype_of_mem_zmod {K : IntermediateField k Ω} {ζ : Ω} (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ p) : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
  IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
    (algebraMap ↥K Ω).injective

/-- **The global Kummer cochain of `β ∈ Kˣ` at the level `K`**, `p` arbitrary: the Kummer character
of `β` on `G_K = K.fixingSubgroup`, extended by `0` off it. -/
noncomputable def nodeKummerCocharZMod (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) : (Ω ≃ₐ[k] Ω) → ZMod p := by
  classical
  exact fun σ => if h : σ ∈ K.fixingSubgroup then
    kummerCharZMod (Ω := Ω) p (ζ := (⟨ζ, hζK⟩ : ↥K))
      (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) β
      ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩) else 0

lemma nodeKummerCocharZMod_apply {K : IntermediateField k Ω} {ζ : Ω} {hζK : ζ ∈ K}
    {hζ : IsPrimitiveRoot ζ p} {β : (↥K)ˣ} {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    nodeKummerCocharZMod K ζ hζK hζ β σ =
      kummerCharZMod (Ω := Ω) p (ζ := (⟨ζ, hζK⟩ : ↥K))
        (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) := by
  simp only [nodeKummerCocharZMod, dif_pos hσ]

lemma nodeKummerCocharZMod_of_notMem {K : IntermediateField k Ω} {ζ : Ω} {hζK : ζ ∈ K}
    {hζ : IsPrimitiveRoot ζ p} {β : (↥K)ˣ} {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∉ K.fixingSubgroup) :
    nodeKummerCocharZMod K ζ hζK hζ β σ = 0 := by
  simp only [nodeKummerCocharZMod, dif_neg hσ]

/-- **The Kummer cochain of `β` is additive on `G_K`.** -/
lemma nodeKummerCocharZMod_add (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
      nodeKummerCocharZMod K ζ hζK hζ β (g * h) =
        nodeKummerCocharZMod K ζ hζK hζ β g + nodeKummerCocharZMod K ζ hζK hζ β h := by
  intro g hg h hh
  have hgh : g * h ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg hh
  rw [nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β) hgh,
    nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β) hg,
    nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β) hh]
  have hkey : (⟨g * h, hgh⟩ : ↥(K.fixingSubgroup)) = ⟨g, hg⟩ * ⟨h, hh⟩ := Subtype.ext rfl
  rw [hkey, map_mul (IntermediateField.fixingSubgroupEquiv K)]
  show kummerCharZMod (Ω := Ω) p (ζ := (⟨ζ, hζK⟩ : ↥K))
      (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) β
      ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩ *
        (IntermediateField.fixingSubgroupEquiv K) ⟨h, hh⟩) = _
  rw [kummerCharZMod_apply, kummerCharZMod_apply, kummerCharZMod_apply]
  exact kummerIdx_mul_apply p (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) β
    (kummerSqrtUnitZMod (Ω := Ω) p β) (kummerSqrtUnitZMod_pow (Ω := Ω) p β) _ _

end KummerCocharZMod

end Work.SSGRoute.ZSplit
