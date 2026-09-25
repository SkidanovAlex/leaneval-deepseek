import Mathlib
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.IdeleHasse.Descent.cyclotomicOnePlace_of_unramified
import Submission.NK.CFTLib.IdeleHasse.Descent.localConditionOdd
import Submission.NK.CFTLib.IdeleHasse.Descent.transferOnePlace

/-!
# The crux `HilbertReciprocityOnePlace` from the one-place transfer and the local condition

Assembly of the workspace's crux `NK.CFTLib.HilbertReciprocityOnePlace` from its two halves, in
the **one-place** form recorded in `Work/CFTLib/HR/NOTES_localCondition_and_transfer.md` §3 and §6:

* `NK.CFTLib.HR.transferAt` (the Brauer transfer with the one-place hypothesis `hM` at `v₀`), and
* the local condition at `v₀` (`LocalConditionOdd` below, = `localConditionOdd`), which supplies an
  auxiliary cyclic cyclotomic level `M = K(ζ_m)` (`m` an odd prime), unramified at a finite `v₀`,
  together with the `E/M`-local-norm property of every `x ∈ Kˣ` at the places `w | v₀`.

The one-place hypothesis `hM` of the transfer is then supplied *without* any ramified cyclotomic
input by `NK.CFTLib.IdeleHasse.Descent.cyclotomicOnePlace_of_unramified` (the finite case is
`HR.localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified_neZero`, the real case
`HR.isCyclotomic_onePlace_real`, the complex case is trivial).

Compare `NK.CFTLib.HR.hilbertReciprocityOnePlace_primePower`, which feeds the transfer the `∀ v`
form of `hM` and therefore additionally needs the *ramified* cyclotomic crux
(`IdeleHasse.hilbertReciprocity_cyclotomic`, whose module is at present missing from the workspace).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse.Descent

open NK.GlobalCFT

/-- **The local condition at `v₀`** (Milne, *CFT*, VII.7.3 + III.3.5/6), in the strengthened form
the one-place transfer consumes: the auxiliary level `M = K(ζ_m)` has an **odd** modulus `m` (so
`M` is totally complex) and is unramified at a finite `v₀`. -/
def LocalConditionOdd : Prop :=
  ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L)) (v₀ : Place K),
    ∃ (M E : Type) (_ : Field M) (_ : NumberField M) (_ : Field E) (_ : NumberField E)
      (_ : Algebra K M) (_ : Algebra K E) (_ : Algebra L E) (_ : Algebra M E)
      (_ : IsScalarTower K L E) (_ : IsScalarTower K M E)
      (_ : FiniteDimensional K M) (_ : FiniteDimensional K E)
      (_ : IsGalois K M) (_ : IsGalois K E) (_ : IsCyclic (M ≃ₐ[K] M))
      (m : ℕ) (_ : 2 < m) (_ : IsCyclotomicExtension {m} K M),
      (Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), v₀ = Place.ofFinite Q → (m : 𝓞 K) ∉ Q.asIdeal) ∧
      (∀ (x : Kˣ) (w : Place M), Place.LiesOver w v₀ →
        Units.map (algebraMap M (Place.localField M w)).toMonoidHom
          (Units.map (algebraMap K M).toMonoidHom x) ∈
          localNormSubgroup (K := M) (L := E) w)

/-- **The one-place Brauer transfer** (Milne, *CFT*, VII §8: Lemma 8.5 + Prop. 7.2 + Lemma 8.6
for one pair of cyclic levels), in the form in which the descent consumes it: the hypothesis `hM`
is needed only at the single place `v₀`. -/
def TransferOnePlace : Prop :=
  ∀ {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
    [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M] [Algebra K E]
    [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L)) (hcycM : IsCyclic (M ≃ₐ[K] M))
    (v₀ : Place K)
    (hM : ∀ y : Kˣ,
      (∀ v : Place K, v ≠ v₀ →
        localImageAt v y ∈ localNormSubgroup (K := K) (L := M) v) →
      localImageAt v₀ y ∈ localNormSubgroup (K := K) (L := M) v₀)
    (x : Kˣ)
    (hx : ∀ v : Place K, v ≠ v₀ →
      localImageAt v x ∈ localNormSubgroup (K := K) (L := L) v)
    (hv₀ : ∀ w : Place M, Place.LiesOver w v₀ →
      Units.map (algebraMap M (Place.localField M w)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) ∈
        localNormSubgroup (K := M) (L := E) w) ,
    localImageAt v₀ x ∈ localNormSubgroup (K := K) (L := L) v₀

/-- **The crux from the one-place transfer and the local condition.** -/
theorem hilbertReciprocityOnePlace_of_localCondition (hT : TransferOnePlace)
    (hC : LocalConditionOdd) :
    NK.CFTLib.HilbertReciprocityOnePlace := by
  intro K L _ _ _ _ _ _ _ hcyc x v₀ h
  obtain ⟨M, E, hMf, hMnf, hEf, hEnf, hKM, hKE, hLE, hME, hst1, hst2, hfdKM, hfdKE,
    hgalM, hgalE, hcycM, m, hm, hcycExt, hadj, hunr, hv₀⟩ := hC (K := K) (L := L) hcyc v₀
  letI : Field M := hMf
  letI : NumberField M := hMnf
  letI : Field E := hEf
  letI : NumberField E := hEnf
  letI : Algebra K M := hKM
  letI : Algebra K E := hKE
  letI : Algebra L E := hLE
  letI : Algebra M E := hME
  letI : IsScalarTower K L E := hst1
  letI : IsScalarTower K M E := hst2
  letI : FiniteDimensional K M := hfdKM
  letI : FiniteDimensional K E := hfdKE
  letI : IsGalois K M := hgalM
  letI : IsGalois K E := hgalE
  letI : IsCyclotomicExtension {m} K M := hcycExt
  have hM : ∀ y : Kˣ,
      (∀ v : Place K, v ≠ v₀ →
        localImageAt v y ∈ localNormSubgroup (K := K) (L := M) v) →
      localImageAt v₀ y ∈ localNormSubgroup (K := K) (L := M) v₀ :=
    fun y hy => cyclotomicOnePlace_of_unramified (K := K) (M := M) m hm v₀ hunr y
      (fun v hv => hy v hv)
  exact hT (K := K) (L := L) (M := M) (E := E) hadj hcyc hcycM v₀ hM x
    (fun v hv => h v hv) (fun w hw => hv₀ x w hw)

 /-- **The crux from the one-place transfer alone**: the local condition `LocalConditionOdd` is
provided by `NK.CFTLib.IdeleHasse.Descent.localConditionOdd`. -/
theorem hilbertReciprocityOnePlace_of_transferOnePlace (hT : TransferOnePlace) :
    NK.CFTLib.HilbertReciprocityOnePlace :=
  hilbertReciprocityOnePlace_of_localCondition hT
    (fun (hcyc : IsCyclic (_ ≃ₐ[_] _)) (v₀ : Place _) => localConditionOdd hcyc v₀)

 /-- The one-place transfer `TransferOnePlace` is `NK.CFTLib.IdeleHasse.Descent.transferOnePlace`. -/
theorem transferOnePlace_eq : TransferOnePlace :=
  fun hgen hcycL hcycM v₀ hM x hx hv₀ => transferOnePlace hgen hcycL hcycM v₀ hM x hx hv₀

/-- **The crux `NK.CFTLib.HilbertReciprocityOnePlace`, unconditionally.** -/
theorem hilbertReciprocityOnePlace : NK.CFTLib.HilbertReciprocityOnePlace :=
  hilbertReciprocityOnePlace_of_transferOnePlace transferOnePlace_eq

end NK.CFTLib.IdeleHasse.Descent
