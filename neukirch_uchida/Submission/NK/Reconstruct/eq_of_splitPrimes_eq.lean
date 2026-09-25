import Mathlib
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup_under_mul_card_ker
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.NK.Reconstruct.eq_one_of_fixes_sup
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime

/-!
# The completely split primes determine a finite normal subextension

Let `K` be a number field, `K'/K` a Galois extension and `L, M ⊆ K'` finite normal intermediate
fields which are number fields.  If a prime `p` of `K` splits completely in `L` (that is, has a
prime of `𝓞 L` above it with ramification index and inertia degree both `1`) exactly when it
splits completely in `M`, then `L = M`.

The proof is the classical Čebotarev-density argument:

* the set of completely split primes has Dirichlet density `1 / [E : K]`
  (`hasDirichletDensity_primes_splitsCompletely`), so equal split-prime sets force equal degrees;
* a prime splitting completely in `L` and in `M` splits completely in the compositum `L ⊔ M`
  (the crux: the decomposition group of a prime of `L ⊔ M` over `p` restricts trivially to `L`
  and to `M`, hence is trivial, because an automorphism of the compositum fixing both factors is
  the identity);
* applying the density statement to `L ⊔ M` and to `L` gives `[L ⊔ M : K] = [L : K]`, whence
  `M ≤ L`, and symmetrically `L ≤ M`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.Reconstruct

open IsDedekindDomain

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- The set of finite primes of `K` that split completely in the number field `E` over `K`: those
`p` having exactly `[E : K]` primes of `𝓞 E` above them. -/
def splitPrimesSet (K : Type*) [Field K] [NumberField K] (E : Type*) [Field E] [NumberField E]
    [Algebra K E] : Set (NK.Chebotarev.PrimeIdeal K) :=
  {p | (p.asIdeal.primesOver (NumberField.RingOfIntegers E)).ncard = Module.finrank K E}

/-- **Splitting completely, in the witness form, is the counting form.**  For a finite Galois
extension `E/K` of number fields, a prime `p` of `K` has a prime of `𝓞 E` above it with
ramification index and inertia degree one if and only if `p` has `[E : K]` primes above it. -/
theorem splitsCompletely_iff_ncard (K : Type*) [Field K] [NumberField K] (E : Type*) [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (p : NK.Chebotarev.PrimeIdeal K) :
    (∃ P : NK.Chebotarev.PrimeIdeal E, P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ↔
      p ∈ splitPrimesSet K E := by
  show _ ↔ (p.asIdeal.primesOver (NumberField.RingOfIntegers E)).ncard = Module.finrank K E
  rw [Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
    (K := K) (L := E) p]
  constructor
  · rintro ⟨P, hP, he, hf⟩
    constructor
    · rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers E) p.asIdeal P.asIdeal (Gal(E/K)) (hp := hP)]
      exact he
    · rw [Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers E) p.asIdeal P.asIdeal (Gal(E/K)) (hp := hP)]
      exact hf
  · rintro ⟨he, hf⟩
    have hne : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers E)) :=
      Ideal.nonempty_primesOver p.asIdeal
    obtain ⟨P⟩ := hne
    have hP : (P : Ideal (NumberField.RingOfIntegers E)).LiesOver p.asIdeal := P.2.2
    refine ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot P.2⟩, hP, ?_, ?_⟩
    · rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers E) p.asIdeal P.1 (Gal(E/K)) (hPp := P.2.1) (hp := hP)]
      exact he
    · rw [← Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers E) p.asIdeal P.1 (Gal(E/K)) (hPp := P.2.1) (hp := hP)]
      exact hf

/-- The completely split primes have Dirichlet density the reciprocal of the degree. -/
theorem hasDirichletDensity_splitPrimesSet (K : Type*) [Field K] [NumberField K] (E : Type*)
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E] :
    NumberField.Set.HasDirichletDensity (splitPrimesSet K E)
      (1 / (Module.finrank K E : ℝ)) :=
  Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
    (K := K) (L := E)

/-- **A prime splitting completely in an extension splits completely in a subextension**: for a
tower `K ⊆ L ⊆ L ⊔ M` of number fields with `L ⊔ M` Galois over `K`, every prime of `K` splitting
completely in `L ⊔ M` splits completely in `L`.  This is the multiplicativity of ramification
index and inertia degree in towers. -/
theorem splitPrimesSet_sup_le {L M : IntermediateField K K'} [FiniteDimensional K L] [Normal K L]
    [NumberField ↥L] [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    [NumberField ↥(L ⊔ M)] :
    splitPrimesSet K ↥(L ⊔ M) ⊆ splitPrimesSet K ↥L := by
  letI : Algebra ↥L ↥(L ⊔ M) := (Subsemiring.inclusion (le_sup_left : L ≤ L ⊔ M)).toAlgebra
  haveI : IsScalarTower K ↥L ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun x => rfl
  intro p hp
  haveI hGalN : IsGalois K ↥(L ⊔ M) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  obtain ⟨heN, hfN⟩ :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥(L ⊔ M)) p).mp hp
  have hne : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥(L ⊔ M))) :=
    Ideal.nonempty_primesOver p.asIdeal
  obtain ⟨R⟩ := hne
  set q : NK.Chebotarev.PrimeIdeal ↥(L ⊔ M) :=
    ⟨R.1, R.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot R.2⟩ with hq
  have hqLies : q.asIdeal.LiesOver p.asIdeal := R.2.2
  haveI hliesL : q.asIdeal.LiesOver (q.under (NumberField.RingOfIntegers ↥L)).asIdeal := ⟨rfl⟩
  -- the ramification index and inertia degree of `q` over `p` are one
  have heR : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥(L ⊔ M)) p.asIdeal q.asIdeal (Gal(↥(L ⊔ M)/K))
      (hp := hqLies)]
    exact heN
  have hfR : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥(L ⊔ M)) p.asIdeal q.asIdeal (Gal(↥(L ⊔ M)/K))
      (hp := hqLies)]
    exact hfN
  -- and hence so are those of the prime below on `L`
  have heLR : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers K) = 1 := by
    have htw := Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers ↥L) (T := NumberField.RingOfIntegers ↥(L ⊔ M))
      (q.under (NumberField.RingOfIntegers ↥L)).asIdeal q.asIdeal
    have h1 : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers K) *
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L) = 1 := by
      rw [← htw]
      exact heR
    exact (mul_eq_one.mp h1).1
  have hfLR : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers K) = 1 := by
    have htw := Ideal.inertiaDeg_tower (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers ↥L) (T := NumberField.RingOfIntegers ↥(L ⊔ M))
      (q.under (NumberField.RingOfIntegers ↥L)).asIdeal q.asIdeal
    have h1 : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥L) = 1 := by
      rw [← htw]
      exact hfR
    exact (mul_eq_one.mp h1).1
  have hLies : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact hqLies.over
  show (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard = Module.finrank K ↥L
  rw [Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
    (K := K) (L := ↥L) p]
  constructor
  · rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥L) p.asIdeal
      (q.under (NumberField.RingOfIntegers ↥L)).asIdeal (Gal(↥L/K)) (hp := hLies)]
    exact heLR
  · rw [Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥L) p.asIdeal
      (q.under (NumberField.RingOfIntegers ↥L)).asIdeal (Gal(↥L/K)) (hp := hLies)]
    exact hfLR

/-- **A prime splitting completely in two subextensions splits completely in their compositum.**
This is the crux of the reconstruction: for `p` splitting completely in `L` and in `M`, the
decomposition group of any prime of `𝓞 (L ⊔ M)` above `p` restricts trivially to `L` and to `M`,
hence is trivial, so `p` splits completely in `L ⊔ M`. -/
theorem splitPrimesSet_subset_sup {L M : IntermediateField K K'} [FiniteDimensional K L]
    [Normal K L] [NumberField ↥L] [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    [NumberField ↥(L ⊔ M)] {p : NK.Chebotarev.PrimeIdeal K}
    (hpL : p ∈ splitPrimesSet K ↥L) (hpM : p ∈ splitPrimesSet K ↥M) :
    p ∈ splitPrimesSet K ↥(L ⊔ M) := by
  letI : Algebra ↥L ↥(L ⊔ M) := (Subsemiring.inclusion (le_sup_left : L ≤ L ⊔ M)).toAlgebra
  haveI : IsScalarTower K ↥L ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun x => rfl
  letI : Algebra ↥M ↥(L ⊔ M) := (Subsemiring.inclusion (le_sup_right : M ≤ L ⊔ M)).toAlgebra
  haveI : IsScalarTower K ↥M ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalM : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalN : IsGalois K ↥(L ⊔ M) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  obtain ⟨heL, hfL⟩ :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥L) p).mp hpL
  obtain ⟨heM, hfM⟩ :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥M) p).mp hpM
  have hne : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥(L ⊔ M))) :=
    Ideal.nonempty_primesOver p.asIdeal
  obtain ⟨R₀⟩ := hne
  set q : NK.Chebotarev.PrimeIdeal ↥(L ⊔ M) :=
    ⟨R₀.1, R₀.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot R₀.2⟩ with hq
  have hqLies : q.asIdeal.LiesOver p.asIdeal := R₀.2.2
  -- the decomposition group of `q` is trivial
  have hbot : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    have hσ' : σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(L ⊔ M) q =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(L ⊔ M) q :=
      (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
        q σ).mpr hσ
    -- restriction to `L` is trivial
    have hL1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥L σ = 1 := by
      have hkey := restrictNormalHom_smul_valuationSubringAtPrime (K := K) (E := ↥L)
        (N := ↥(L ⊔ M)) (q := q) (q' := q.under (NumberField.RingOfIntegers ↥L)) rfl hσ'
      have hmem : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥L σ ∈
          Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
            (q.under (NumberField.RingOfIntegers ↥L)) :=
        (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
          (q.under (NumberField.RingOfIntegers ↥L)) _).mp hkey
      have hLiesP : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.LiesOver p.asIdeal := by
        refine ⟨?_⟩
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
        exact hqLies.over
      have hbotP : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
          (q.under (NumberField.RingOfIntegers ↥L)) = ⊥ :=
        (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
          p _ hLiesP).mpr ⟨heL, hfL⟩
      rw [hbotP] at hmem
      exact Subgroup.mem_bot.mp hmem
    -- restriction to `M` is trivial
    have hM1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥M σ = 1 := by
      have hkey := restrictNormalHom_smul_valuationSubringAtPrime (K := K) (E := ↥M)
        (N := ↥(L ⊔ M)) (q := q) (q' := q.under (NumberField.RingOfIntegers ↥M)) rfl hσ'
      have hmem : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥M σ ∈
          Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
            (q.under (NumberField.RingOfIntegers ↥M)) :=
        (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
          (q.under (NumberField.RingOfIntegers ↥M)) _).mp hkey
      have hLiesQ : (q.under (NumberField.RingOfIntegers ↥M)).asIdeal.LiesOver p.asIdeal := by
        refine ⟨?_⟩
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
        exact hqLies.over
      have hbotQ : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
          (q.under (NumberField.RingOfIntegers ↥M)) = ⊥ :=
        (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
          p _ hLiesQ).mpr ⟨heM, hfM⟩
      rw [hbotQ] at hmem
      exact Subgroup.mem_bot.mp hmem
    -- an automorphism of the compositum fixing both factors is the identity
    refine eq_one_of_fixes_sup L M σ ?_ ?_
    · intro x
      have h3 : (σ.restrictNormal ↥L) x = x := by
        rw [show (σ.restrictNormal ↥L) = 1 from hL1]
        rfl
      have h2 := AlgEquiv.restrictNormal_commutes (F := K) σ ↥L x
      rw [h3] at h2
      have h4 : algebraMap ↥L ↥(L ⊔ M) x =
          ⟨x.1, (le_sup_left : L ≤ L ⊔ M) x.2⟩ := Subtype.ext rfl
      rw [h4] at h2
      exact h2.symm
    · intro x
      have h3 : (σ.restrictNormal ↥M) x = x := by
        rw [show (σ.restrictNormal ↥M) = 1 from hM1]
        rfl
      have h2 := AlgEquiv.restrictNormal_commutes (F := K) σ ↥M x
      rw [h3] at h2
      have h4 : algebraMap ↥M ↥(L ⊔ M) x =
          ⟨x.1, (le_sup_right : M ≤ L ⊔ M) x.2⟩ := Subtype.ext rfl
      rw [h4] at h2
      exact h2.symm
  -- hence the local degree of `q` is one, and `p` splits completely in `L ⊔ M`
  have hcard : Nat.card (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
      (K := K) q) = 1 := (Subgroup.eq_bot_iff_card _).mp hbot
  have hcard' := Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup
    (K := K) (L := ↥(L ⊔ M)) p q hqLies
  rw [hcard] at hcard'
  obtain ⟨heN, hfN⟩ := mul_eq_one.mp hcard'.symm
  exact (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
    (K := K) (L := ↥(L ⊔ M)) p).mpr ⟨heN, hfN⟩

/-- **Two finite normal number-field subextensions with the same completely split primes are
equal.**  This is the classical statement that the completely split primes determine a finite
normal subextension, used to identify the level correspondence attached to an isomorphism of
absolute Galois groups. -/
theorem eq_of_splitPrimes_eq {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsGalois K K'] {L M : IntermediateField K K'} [FiniteDimensional K L] [Normal K L]
    [NumberField ↥L] [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    (h : ∀ p : NK.Chebotarev.PrimeIdeal K,
      (∃ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal ∧
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
          P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ↔
        (∃ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver p.asIdeal ∧
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
          Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1)) :
    L = M := by
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalM : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI : NumberField ↥(L ⊔ M) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (L ⊔ M)
  haveI hGalN : IsGalois K ↥(L ⊔ M) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- the split prime sets of `L` and `M` agree
  have hset : splitPrimesSet K ↥L = splitPrimesSet K ↥M := by
    ext p
    rw [← splitsCompletely_iff_ncard K ↥L p, ← splitsCompletely_iff_ncard K ↥M p]
    exact h p
  -- and both agree with the split prime set of the compositum
  have hsupL : splitPrimesSet K ↥(L ⊔ M) = splitPrimesSet K ↥L := by
    refine Set.Subset.antisymm (splitPrimesSet_sup_le (L := L) (M := M)) ?_
    intro p hp
    exact splitPrimesSet_subset_sup (L := L) (M := M) hp (hset ▸ hp)
  have hsupM : splitPrimesSet K ↥(L ⊔ M) = splitPrimesSet K ↥M := by
    rw [hsupL, hset]
  -- densities
  have hdL : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥L)
      (1 / (Module.finrank K ↥L : ℝ)) := hasDirichletDensity_splitPrimesSet K ↥L
  have hdM : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥M)
      (1 / (Module.finrank K ↥M : ℝ)) := hasDirichletDensity_splitPrimesSet K ↥M
  have hdN : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥(L ⊔ M))
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) := hasDirichletDensity_splitPrimesSet K ↥(L ⊔ M)
  have hdNL : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥L)
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) := hsupL ▸ hdN
  have hdNM : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥M)
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) := hsupM ▸ hdN
  have hdegL : Module.finrank K ↥L = Module.finrank K ↥(L ⊔ M) := by
    have heq := tendsto_nhds_unique hdL hdNL
    rw [one_div, one_div] at heq
    have h2 : (Module.finrank K ↥L : ℝ) = (Module.finrank K ↥(L ⊔ M) : ℝ) := inv_inj.mp heq
    exact_mod_cast h2
  have hdegM : Module.finrank K ↥M = Module.finrank K ↥(L ⊔ M) := by
    have heq := tendsto_nhds_unique hdM hdNM
    rw [one_div, one_div] at heq
    have h2 : (Module.finrank K ↥M : ℝ) = (Module.finrank K ↥(L ⊔ M) : ℝ) := inv_inj.mp heq
    exact_mod_cast h2
  have hLtop : L = L ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_left hdegL
  have hMtop : M = L ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_right hdegM
  have hMleL : M ≤ L := by rw [hLtop]; exact le_sup_right
  have hLleM : L ≤ M := by rw [hMtop]; exact le_sup_left
  exact le_antisymm hLleM hMleL

end NK.Reconstruct
