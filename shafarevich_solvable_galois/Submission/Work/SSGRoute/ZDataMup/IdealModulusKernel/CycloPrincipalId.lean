/-
# The principal ray of an ideal modulus is killed in a cyclotomic extension

`CycloPrincipalId`: for a cyclotomic extension `Ω = k(ζ_n)` of a number field `k`, an ideal modulus
`𝔪` whose support contains the prime divisors of `(n)` (`hsupp`) and whose levels dominate those of
`(n)` at those primes (`hlev`), the ideal-theoretic Artin symbol of `Ω/k` kills the whole principal
ray `P(𝔪) = principalRayId 𝔪`.

This is the cyclotomic case of Lang's Theorem 2 (the "cyclotomic base case" of Artin reciprocity),
in the ideal-modulus form.  The proof is the transfer of the natural-number-modulus statement
`NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_congr_pos` at modulus `n`, whose inputs are
supplied from `𝔪`:

* *The cyclotomic reciprocity law* at `n`: `NK.CFTLib.ARL.artinReciprocity_cyclotomic`.
* *Unramifiedness off `n`*: `NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension` (relative form) —
  a prime `𝔭 ∤ (n)` is unramified in `Ω/k`, whence `ramificationIdxIn 𝔭 (𝓞 Ω) = 1`; this is the
  `hram` hypothesis of the natural-number statement at `m = n`.
* *The congruence at `(n)`*: if `(n) ∈ 𝔭` then `𝔪 ≤ 𝔭` (`hsupp`), and the `𝔭`-adic level of `(n)`
  is at most that of `𝔪` (`hlev`, converted through
  `val_natCast_adicCompletion_eq_exp_neg_count_span`), so `CongrOneId 𝔪 b` at `b` implies the
  natural-number congruence `b ≡ 1 mod (n)`.
-/
import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.dictionary_ramifiedPart
import Submission.Work.SSGRoute.ZDataMup.MupAux.Base
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_mem_congruence
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.kernelLe_of_auxField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.IdealModulusKernel

open NK.CFTLib.ArtinReciprocityIdeal

/-- **The principal ray of an ideal modulus is killed in a cyclotomic extension.**

For `Ω = k(ζ_n)` a cyclotomic extension of a number field `k` and an ideal modulus `𝔪` of `k`
whose support contains the primes dividing `(n)` and whose levels dominate those of `(n)`, the
Artin symbol of `Ω/k` kills the principal ray `P(𝔪)`. -/
theorem CycloPrincipalId (k Ω : Type) [Field k] [NumberField k] [Field Ω] [NumberField Ω]
    [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]
    [IsMulCommutative (Ω ≃ₐ[k] Ω)]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} k Ω]
    (𝔪 : Ideal (NumberField.RingOfIntegers k)) (h𝔪 : 𝔪 ≠ ⊥)
    (hsupp : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal →
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭)
    (hlev : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal →
      WithZero.exp
          (-(FractionalIdeal.count k 𝔭 (𝔪 : FractionalIdeal (nonZeroDivisors
            (NumberField.RingOfIntegers k)) k) : ℤ))
        ≤ Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
            (((n : ℕ) : 𝔭.adicCompletion k))) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac k,
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 →
      NK.CFTLib.Arl.artinSym (K := k) (L := Ω)
        (fun a b : Ω ≃ₐ[k] Ω => IsMulCommutative.is_comm.comm a b) A = 1 := by
  classical
  let hcomm : ∀ a b : Gal(Ω/k), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  let f : NK.CFTLib.ArtinReciprocityIdeal.Frac k →* Gal(Ω/k) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := k) (L := Ω) hcomm
  -- it suffices to prove the containment `P(𝔪) ≤ ker`
  have hle : NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ≤ f.ker := by
    rw [NK.CFTLib.ArtinReciprocityIdeal.principalRayId, Subgroup.closure_le]
    rintro A ⟨b, hb, rfl⟩
    change NK.CFTLib.Arl.artinSym (K := k) (L := Ω) hcomm
      (((NK.CFTLib.ArtinReciprocityIdeal.spanUnit b : NK.CFTLib.ArtinReciprocityIdeal.Frac k) :
        FractionalIdeal (𝓞 k)⁰ k)) = 1
    -- ### the congruence at `(n)` inherited from `CongrOneId 𝔪 b`
    have hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 k),
        (n : 𝓞 k) ∈ 𝔭.asIdeal →
        Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap k (𝔭.adicCompletion k) ((b : kˣ) : k) - 1)
          ≤ Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
              (((n : ℕ) : 𝔭.adicCompletion k)) := by
      intro 𝔭 h𝔭
      have hdvd : NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 := hsupp 𝔭 h𝔭
      have h1 : WithZero.exp
            (-(FractionalIdeal.count k 𝔭 (𝔪 : FractionalIdeal (𝓞 k)⁰ k) : ℤ))
          ≤ Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
              (((n : ℕ) : 𝔭.adicCompletion k)) := hlev 𝔭 h𝔭
      rw [Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.val_natCast_adicCompletion_eq_exp_neg_count_span
            (K := k) n (NeZero.ne n) 𝔭] at h1 ⊢
      exact le_trans (hb.1 𝔭 hdvd) h1
    -- ### unramifiedness off `(n)`
    have hramn : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 k),
        (n : 𝓞 k) ∉ 𝔭.asIdeal →
        Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 Ω) = 1 := by
      intro 𝔭 h𝔭
      exact (NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one_Id
        (K := k) (L := Ω) 𝔭).mp
        (NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := k) (Ω := Ω) n 𝔭 h𝔭)
    -- ### the cyclotomic reciprocity law at `n`
    have hprincn : ∀ (a : 𝓞 k), a - 1 ∈ Ideal.span {(n : 𝓞 k)} →
        (∀ φ : k →+* ℝ, 0 < φ (a : k)) →
        ∀ (s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 k)))
          (e : IsDedekindDomain.HeightOneSpectrum (𝓞 k) → ℕ)
          (σ : IsDedekindDomain.HeightOneSpectrum (𝓞 k) → Gal(Ω/k)),
          (∀ p ∈ s, (n : 𝓞 k) ∉ p.asIdeal) →
          Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
          (∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (K := k) (L := Ω) p (σ p)) →
          (s.toList.map (fun p => σ p ^ e p)).prod = 1 :=
      fun a ha hpos s e σ hs hfac hfrob =>
        NK.CFTLib.ARL.artinReciprocity_cyclotomic k Ω n a ha hpos s e σ hs hfac hfrob
    -- ### the natural-number-modulus statement at `m = n`
    have h := NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_congr_pos (K := k) (L := Ω)
      hcomm n (NeZero.pos n) hramn hprincn b hcong hb.2
    simpa only [NK.CFTLib.ArtinReciprocityIdeal.coe_spanUnit] using h
  intro A hA
  have hker : f A = 1 := hle hA
  change NK.CFTLib.Arl.artinSym (K := k) (L := Ω)
    (fun a b : Ω ≃ₐ[k] Ω => IsMulCommutative.is_comm.comm a b) A = 1
  exact hker


/-- **The intermediate-field form: `k ⊆ M ⊆ Ω = k(ζ_n)`.**

Same statement as `CycloPrincipalId`, but for a finite Galois subextension `M/k` of a cyclotomic
extension `Ω = k(ζ_n)`.  The natural-number-modulus input is
`NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe_artinKillsPrincipal` at `m = n` (which is the
ambient cyclotomic reciprocity law `artinReciprocity_cyclotomic`, transferred to `M/k` by
restricting the chosen Frobenius elements along `AlgEquiv.restrictNormalHom`), and unramifiedness
off `(n)` for `M/k` follows from the corresponding statement for `Ω/k` by going down to the
subextension (`NK.CFTLib.ArtinReciprocityIdeal.isUnramified_intermediateField`). -/
theorem CycloPrincipalIdSub (k Ω : Type) [Field k] [NumberField k] [Field Ω] [NumberField Ω]
    [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k M] [NumberField ↥M] [IsGalois k ↥M]
    [IsMulCommutative ((↥M) ≃ₐ[k] (↥M))]
    (𝔪 : Ideal (NumberField.RingOfIntegers k)) (h𝔪 : 𝔪 ≠ ⊥)
    (hsupp : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal →
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭)
    (hlev : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal →
      WithZero.exp
          (-(FractionalIdeal.count k 𝔭 (𝔪 : FractionalIdeal (nonZeroDivisors
            (NumberField.RingOfIntegers k)) k) : ℤ))
        ≤ Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
            (((n : ℕ) : 𝔭.adicCompletion k))) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac k,
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 →
      NK.CFTLib.Arl.artinSym (K := k) (L := ↥M)
        (fun a b : ↥M ≃ₐ[k] ↥M => IsMulCommutative.is_comm.comm a b) A = 1 := by
  classical
  let hcomm : ∀ a b : Gal(↥M/k), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  let f : NK.CFTLib.ArtinReciprocityIdeal.Frac k →* Gal(↥M/k) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := k) (L := ↥M) hcomm
  have hle : NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ≤ f.ker := by
    rw [NK.CFTLib.ArtinReciprocityIdeal.principalRayId, Subgroup.closure_le]
    rintro A ⟨b, hb, rfl⟩
    change NK.CFTLib.Arl.artinSym (K := k) (L := ↥M) hcomm
      (((NK.CFTLib.ArtinReciprocityIdeal.spanUnit b : NK.CFTLib.ArtinReciprocityIdeal.Frac k) :
        FractionalIdeal (𝓞 k)⁰ k)) = 1
    -- ### the congruence at `(n)` inherited from `CongrOneId 𝔪 b`
    have hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 k),
        (n : 𝓞 k) ∈ 𝔭.asIdeal →
        Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap k (𝔭.adicCompletion k) ((b : kˣ) : k) - 1)
          ≤ Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
              (((n : ℕ) : 𝔭.adicCompletion k)) := by
      intro 𝔭 h𝔭
      have hdvd : NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 := hsupp 𝔭 h𝔭
      have h1 : WithZero.exp
            (-(FractionalIdeal.count k 𝔭 (𝔪 : FractionalIdeal (𝓞 k)⁰ k) : ℤ))
          ≤ Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
              (((n : ℕ) : 𝔭.adicCompletion k)) := hlev 𝔭 h𝔭
      rw [Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.val_natCast_adicCompletion_eq_exp_neg_count_span
            (K := k) n (NeZero.ne n) 𝔭] at h1 ⊢
      exact le_trans (hb.1 𝔭 hdvd) h1
    -- ### unramifiedness off `(n)` for `M/k`, descended from `Ω/k`
    have hramM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 k),
        (n : 𝓞 k) ∉ 𝔭.asIdeal →
        Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 ↥M) = 1 := by
      intro 𝔭 h𝔭
      have hunrΩ : Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 Ω) = 1 :=
        (NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one_Id
          (K := k) (L := Ω) 𝔭).mp
          (NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := k) (Ω := Ω) n 𝔭 h𝔭)
      exact (NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one_Id
        (K := k) (L := ↥M) 𝔭).mp
        (NK.CFTLib.ArtinReciprocityIdeal.isUnramified_intermediateField (K := k) (Ω := Ω) M hunrΩ)
    -- ### the cyclotomic product condition for `M/k`, at the modulus `n`
    have hprinc : NK.CFTLib.artinKillsPrincipal k ↥M n :=
      NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe_artinKillsPrincipal
        (k' := k) (E' := Ω) M n n dvd_rfl
        (fun p hp => by
          by_contra hmem
          exact hp ((NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one_Id
            (K := k) (L := ↥M) p).mpr (hramM p hmem)))
    -- ### the natural-number-modulus statement at `m = n`, over `M`
    have h := NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_congr_pos (K := k) (L := ↥M)
      hcomm n (NeZero.pos n) hramM hprinc b hcong hb.2
    simpa only [NK.CFTLib.ArtinReciprocityIdeal.coe_spanUnit] using h
  intro A hA
  have hker : f A = 1 := hle hA
  change NK.CFTLib.Arl.artinSym (K := k) (L := ↥M)
    (fun a b : ↥M ≃ₐ[k] ↥M => IsMulCommutative.is_comm.comm a b) A = 1
  exact hker

/-!
## Status note (for the lane)

`CycloPrincipalId` above is proved with no `sorry` and is axiom-clean
(`#print axioms` = `propext, Classical.choice, Quot.sound`); it is the cyclotomic case of Lang's
Theorem 2 in ideal-modulus form, and it is the missing leaf of the ideal-modulus cyclotomic cell
(`ArtinReciprocity/IdealModulus/cellId.lean`, whose other leaves `normKerId`, `surjId`, `indexLeId`
are all sorry-free).

**A structural obstruction, found while assembling the cell.**  The natural-number-modulus
machinery that this file uses brings the *natural-number* `adjId`
(`NK.CFTLib.ArtinReciprocityIdeal.adjId`, defined in
`NK/CFTLib/ArtinReciprocityIdeal/indexIdealCoprimeLeNormClassIndex.lean`) into the environment.
This happens through `NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`,
`NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_mem_congruence` and `MupAux/Base` — each of them
transitively imports the natural-number `adjId` (verified by `#check`).  The *ideal*-modulus
`AdjustId.lean` defines the same name in the same namespace, so no file may import both
`ArtinReciprocity/IdealModulus/AdjustId` and any of those three.  Consequently the ideal cyclotomic
cell cannot be assembled from `cellId.lean`'s ingredients directly: it needs `P(𝔪) ⊆ ker`
(this file: cyclotomic machinery, natural-number `adjId` in scope) *and* the ideal index inequality
`indexLeId` (ideal `AdjustId` in scope).

The fix is the one already used by the IdPort lane: route the ideal `θ`-chain through the renamed
copy `Work.SSGRoute.ZDataMup.IdPort` (`IdPort/Adjust.lean`, whose `adjId` lives in its own
namespace), so that the ideal index inequality
`Nat.card (I(𝔪) ⧸ P(𝔪)·𝔑(𝔪)) ≤ (normClassSubgroup K L).index` can be proved in a
clash-free file and combined with this one.
-/


end Work.SSGRoute.ZDataMup.IdealModulusKernel
