import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
-- (Cycle repair: this file imported `localFactor_productFormula_abelian`, which — through
-- `ideleArtin_ideleOfPrime_of_unramified` → `ZDataMupClean.*` → `ArtinReciprocity.productFormula_cyclotomic`
-- → `localGlobalMap_productFormula` → `CycleFromReciprocityModulus` → … → `IdealModulus.surjId` —
-- imported this file back, producing a `build cycle detected` failure that took the whole
-- `ZDataMup` cone (hence every module importing `mup_localArtin_productFormula`) out of the build.
-- The import was unused here: no declaration of `localFactor_productFormula_abelian.lean`
-- (`exists_ideleArtin_abelian_frob_unramified`, `localFactor_productFormula_abelian`) occurs in this
-- file.  Removed.)
import Submission.NK.CFTLib.HR.Basic
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup

/-!
# Auxiliaries for the conductor drop at an admissible modulus

Shared, reusable lemmas for the proof of
`Work.SSGRoute.ZDataMup.artinSym_eq_one_of_isAdmissible_cyclic` and for the auxiliary statement
that the idèlic Artin map is Frobenius-normalised at an *unramified* prime dividing the modulus.

Everything here is `sorry`-free and depends only on clean modules.
-/

namespace Work.SSGRoute.ZDataMup

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain
open NK.GlobalCFT

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- `Ideal.ramificationIdxIn p (𝓞 L) = 1` is `NK.HeckeL.IsUnramifiedIn p`. -/
theorem isUnramifiedIn_of_ramificationIdxIn_eq_one (p : HeightOneSpectrum (𝓞 K))
    (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
  letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  intro q hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver p.asIdeal := hq
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal q.asIdeal
    (Gal(L/K))]
  exact h

/-- The converse reading: a prime which is not unramified has ramification index `≠ 1`. -/
theorem ramificationIdxIn_ne_one_of_not_isUnramifiedIn (p : HeightOneSpectrum (𝓞 K))
    (h : ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p) :
    Ideal.ramificationIdxIn p.asIdeal (𝓞 L) ≠ 1 :=
  fun h1 => h (isUnramifiedIn_of_ramificationIdxIn_eq_one (K := K) (L := L) p h1)

/-- The `q`-adic exponent of the principal idèle of `b` is the multiplicity of `q` in `(b)`. -/
theorem exps_spanSingleton_eq_exp (b : Kˣ) (Q : HeightOneSpectrum (𝓞 K)) :
    NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q
      = Idele.exp Q (Idele.principalIdele K b) := by
  rw [NK.CFTLib.Arl.exps_apply, ← Idele.idealOf_principalIdele, Idele.count_idealOf]

/-- **The valuation of an element at a finite place is the negative exponential of its
multiplicity.**  The bridge between the local (`Valued.v` in the completion) and the global
(`FractionalIdeal.count` of the principal ideal) description of the order of vanishing. -/
theorem val_eq_exp_neg_exps_spanSingleton (b : Kˣ) (Q : HeightOneSpectrum (𝓞 K)) :
    Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap K (Q.adicCompletion K) ((b : Kˣ) : K))
      = WithZero.exp (-(NK.CFTLib.Arl.exps
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q)) := by
  have hne : ((b : Kˣ) : K) ≠ 0 := Units.ne_zero b
  have h1 : FractionalIdeal.count K Q
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K))
      = -WithZero.log ((Q.valuation K) ((b : Kˣ) : K)) :=
    NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq Q hne
  have hval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap K (Q.adicCompletion K) ((b : Kˣ) : K))
      = (Q.valuation K) ((b : Kˣ) : K) :=
    Commons.NumberTheory.NumberField.Completion.valued_alg_eq Q ((b : Kˣ) : K)
  have hvne : (Q.valuation K) ((b : Kˣ) : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact hne
  rw [hval, NK.CFTLib.Arl.exps_apply, h1, neg_neg]
  exact (WithZero.exp_log hvne).symm

/-- The image of `b` in the completion at a finite place, as the coercion of `localImageAt`. -/
theorem localImageAt_ofFinite_coe (Q : HeightOneSpectrum (𝓞 K)) (b : Kˣ) :
    ((NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K)
      = algebraMap K (Q.adicCompletion K) ((b : Kˣ) : K) := rfl

/-! ## Products of local factors -/

/-- The `cprod` of a function over the image of a finite set of primes. -/
theorem cprod_image {G : Type} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    {ι κ : Type} [DecidableEq ι] {s : Finset κ} {g : κ → ι} (hg : Set.InjOn g ↑s) (f : ι → G) :
    NK.CFTLib.IdeleHasse.cprod hcomm (s.image g) f
      = NK.CFTLib.IdeleHasse.cprod hcomm s (fun x => f (g x)) := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold NK.CFTLib.IdeleHasse.cprod
  rw [Finset.prod_image hg]

/-- The `cprod` over the support of the exponent vector of a fractional ideal is the Artin
symbol of that ideal. -/
theorem cprod_support_eq_artinSym (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (A : FractionalIdeal (𝓞 K)⁰ K) :
    NK.CFTLib.IdeleHasse.cprod hcomm (NK.CFTLib.Arl.exps A).support
        (fun Q => (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ (NK.CFTLib.Arl.exps A Q))
      = NK.CFTLib.Arl.artinSym hcomm A := by
  letI : CommMonoid Gal(L/K) := NK.CFTLib.Arl.galCommMonoid hcomm
  unfold NK.CFTLib.IdeleHasse.cprod NK.CFTLib.Arl.artinSym
  rw [Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps A) (subset_refl _)
    (fun Q e => (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ e)
    (fun i _ => zpow_zero _)]
  exact Finset.prod_congr rfl (fun i _ => rfl)

/-- `(frobAtPrime Q) ^ (exps A Q) = 1` when `Q` is outside the support of `exps A`. -/
theorem frob_zpow_exps_eq_one_of_notMem_support (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (A : FractionalIdeal (𝓞 K)⁰ K) {Q : HeightOneSpectrum (𝓞 K)}
    (hQ : Q ∉ (NK.CFTLib.Arl.exps A).support) :
    (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ (NK.CFTLib.Arl.exps A Q) = 1 := by
  rw [(Finsupp.notMem_support_iff).mp hQ, zpow_zero]

end

end Work.SSGRoute.ZDataMup
