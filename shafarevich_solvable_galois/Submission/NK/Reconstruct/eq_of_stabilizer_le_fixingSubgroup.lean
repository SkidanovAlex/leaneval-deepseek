import Mathlib
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.NK.Reconstruct.eq_one_of_fixes_sup
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup_under_mul_card_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place system determines a finite normal subextension

If two finite normal number-field subextensions `N`, `N'` of the separable closure `K'` of a
number field `K` have the same decomposition groups — more precisely, if the places `B` of `K'`
over finite primes whose stabiliser is contained in the fixing subgroup of `N` are exactly those
whose stabiliser is contained in the fixing subgroup of `N'` — then `N = N'`.

The proof has three steps:

* the stabiliser condition at a place `B` above a prime `p` is equivalent to `p` splitting
  completely in the corresponding field (`stabilizer_le_fixingSubgroup_iff_splitCompletely`);
* every finite prime of `K` has an extension to `K'` (`exists_valuationSubring_at_prime`), so the
  hypothesis says exactly that the completely split primes of `N` and of `N'` agree;
* the completely split primes determine the field: this is the Čebotarev-density statement
  (`eq_of_splitPrimesOf_eq`).
-/

namespace NK.Reconstruct

open IsDedekindDomain
open scoped Pointwise

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- The set of finite primes of `K` which split completely in the number field `E` over `K`, i.e.
which have exactly `[E : K]` primes of `𝓞 E` above them. -/
def splitPrimesOf (K : Type*) [Field K] [NumberField K] (E : Type*) [Field E] [NumberField E]
    [Algebra K E] : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {p | (p.asIdeal.primesOver (NumberField.RingOfIntegers E)).ncard = Module.finrank K E}

/-- **Splitting completely is triviality of the decomposition group.**  For a finite Galois
extension `E/K` of number fields, a prime `p` of `K` splits completely (in the counting sense)
exactly when the decomposition group of any place `w` of `E` above `p` is trivial. -/
theorem split_iff_decompSubgroup_eq_bot {K E : Type*} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hw : w.asIdeal.LiesOver p.asIdeal) :
    (p.asIdeal.primesOver (NumberField.RingOfIntegers E)).ncard = Module.finrank K E ↔
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) w = ⊥ :=
  (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := E) p).trans
    (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      p w hw).symm

/-- **The completely split primes determine a finite normal subextension.**

Let `L`, `M` be finite normal number-field subextensions of `K'/K` which have the same completely
split primes.  Then `L = M`.

The proof is the classical Čebotarev-density argument: the completely split primes have Dirichlet
density the reciprocal of the degree, so `L` and `M` have the same degree over `K`; and a prime
splitting completely in `L` and in `M` splits completely in the compositum `L ⊔ M` (the
decomposition group of a prime of `L ⊔ M` above `p` restricts trivially to `L` and to `M`, hence
is trivial), so the compositum has the same degree as `L` and as `M`; hence `L ⊔ M = L = M`. -/
theorem eq_of_splitPrimesOf_eq {L M : IntermediateField K K'} [FiniteDimensional K L]
    [Normal K L] [NumberField ↥L] [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    (h : splitPrimesOf K ↥L = splitPrimesOf K ↥M) : L = M := by
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalM : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  letI : Algebra ↥L ↥(L ⊔ M) := (Subsemiring.inclusion (le_sup_left : L ≤ L ⊔ M)).toAlgebra
  haveI : IsScalarTower K ↥L ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower ↥L ↥(L ⊔ M) K' := IsScalarTower.of_algebraMap_eq fun x => rfl
  letI : Algebra ↥M ↥(L ⊔ M) := (Subsemiring.inclusion (le_sup_right : M ≤ L ⊔ M)).toAlgebra
  haveI : IsScalarTower K ↥M ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower ↥M ↥(L ⊔ M) K' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : NumberField ↥(L ⊔ M) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (L ⊔ M)
  haveI hGalN : IsGalois K ↥(L ⊔ M) := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- ## (1) every prime splitting in the compositum splits in `L`
  have hle1 : splitPrimesOf K ↥(L ⊔ M) ⊆ splitPrimesOf K ↥L := by
    intro p hp
    simp only [splitPrimesOf, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨heN, hfN⟩ :=
      (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
        (K := K) (L := ↥(L ⊔ M)) p).mp hp
    obtain ⟨R0⟩ :=
      (inferInstance : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥(L ⊔ M))))
    let R : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(L ⊔ M)) :=
      ⟨R0.1, R0.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot R0.2⟩
    have hRlies : R.asIdeal.LiesOver p.asIdeal := R0.2.2
    haveI hRL : R.asIdeal.LiesOver (R.under (NumberField.RingOfIntegers ↥L)).asIdeal :=
      ⟨IsDedekindDomain.HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers ↥L) R⟩
    have heR : R.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥(L ⊔ M)) p.asIdeal R.asIdeal (Gal(↥(L ⊔ M)/K))
        (hp := hRlies)).symm.trans heN
    have hfR : R.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 :=
      (Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥(L ⊔ M)) p.asIdeal R.asIdeal (Gal(↥(L ⊔ M)/K))
        (hp := hRlies)).symm.trans hfN
    have hunderLies : (R.under (NumberField.RingOfIntegers ↥L)).asIdeal.LiesOver p.asIdeal := by
      refine ⟨?_⟩
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
      exact hRlies.over
    haveI : (R.under (NumberField.RingOfIntegers ↥L)).asIdeal.LiesOver p.asIdeal := hunderLies
    have he : p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L) = 1 := by
      have htw := Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers K)
        (S := NumberField.RingOfIntegers ↥L) (T := NumberField.RingOfIntegers ↥(L ⊔ M))
        (R.under (NumberField.RingOfIntegers ↥L)).asIdeal R.asIdeal
      rw [heR] at htw
      have h1 : (R.under (NumberField.RingOfIntegers ↥L)).asIdeal.ramificationIdx
          (NumberField.RingOfIntegers K) = 1 := Nat.eq_one_of_mul_eq_one_right htw.symm
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥L) p.asIdeal
        (R.under (NumberField.RingOfIntegers ↥L)).asIdeal (Gal(↥L/K)) (hp := hunderLies)]
      exact h1
    have hf : p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) = 1 := by
      have htw := Ideal.inertiaDeg_tower (R := NumberField.RingOfIntegers K)
        (S := NumberField.RingOfIntegers ↥L) (T := NumberField.RingOfIntegers ↥(L ⊔ M))
        (R.under (NumberField.RingOfIntegers ↥L)).asIdeal R.asIdeal
      rw [hfR] at htw
      have h1 : (R.under (NumberField.RingOfIntegers ↥L)).asIdeal.inertiaDeg
          (NumberField.RingOfIntegers K) = 1 := Nat.eq_one_of_mul_eq_one_right htw.symm
      rw [Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥L) p.asIdeal
        (R.under (NumberField.RingOfIntegers ↥L)).asIdeal (Gal(↥L/K)) (hp := hunderLies)]
      exact h1
    exact (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥L) p).mpr ⟨he, hf⟩
  -- ## (2) every prime splitting in `L` (hence, by hypothesis, in `M`) splits in the compositum
  have hle2 : splitPrimesOf K ↥L ⊆ splitPrimesOf K ↥(L ⊔ M) := by
    intro p hp
    have hpM : p ∈ splitPrimesOf K ↥M := by rw [← h]; exact hp
    simp only [splitPrimesOf, Set.mem_ofPred_eq] at hp hpM ⊢
    obtain ⟨heL, hfL⟩ :=
      (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
        (K := K) (L := ↥L) p).mp hp
    obtain ⟨heM, hfM⟩ :=
      (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
        (K := K) (L := ↥M) p).mp hpM
    obtain ⟨R0⟩ :=
      (inferInstance : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥(L ⊔ M))))
    let R : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(L ⊔ M)) :=
      ⟨R0.1, R0.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot R0.2⟩
    have hRlies : R.asIdeal.LiesOver p.asIdeal := R0.2.2
    have hunderLlies : (R.under (NumberField.RingOfIntegers ↥L)).asIdeal.LiesOver p.asIdeal := by
      refine ⟨?_⟩
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
      exact hRlies.over
    have hunderMlies : (R.under (NumberField.RingOfIntegers ↥M)).asIdeal.LiesOver p.asIdeal := by
      refine ⟨?_⟩
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
      exact hRlies.over
    -- the decomposition group of `R` is trivial
    have hbot : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) R = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      have hσ' : σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(L ⊔ M) R =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(L ⊔ M) R :=
        (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
          (F := K) (E := ↥(L ⊔ M)) R σ).mpr hσ
      have hL1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥L σ = 1 := by
        have hkey := restrictNormalHom_smul_valuationSubringAtPrime
          (K := K) (E := ↥L) (N := ↥(L ⊔ M)) R (R.under (NumberField.RingOfIntegers ↥L)) rfl hσ'
        have hmem : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥L σ ∈
            Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
              (R.under (NumberField.RingOfIntegers ↥L)) :=
          (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
            (F := K) (E := ↥L) (R.under (NumberField.RingOfIntegers ↥L)) _).mp hkey
        have hbotP : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
            (R.under (NumberField.RingOfIntegers ↥L)) = ⊥ :=
          (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
            p _ hunderLlies).mpr ⟨heL, hfL⟩
        rw [hbotP] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hM1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥M σ = 1 := by
        have hkey := restrictNormalHom_smul_valuationSubringAtPrime
          (K := K) (E := ↥M) (N := ↥(L ⊔ M)) R (R.under (NumberField.RingOfIntegers ↥M)) rfl hσ'
        have hmem : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥M σ ∈
            Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
              (R.under (NumberField.RingOfIntegers ↥M)) :=
          (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
            (F := K) (E := ↥M) (R.under (NumberField.RingOfIntegers ↥M)) _).mp hkey
        have hbotQ : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
            (R.under (NumberField.RingOfIntegers ↥M)) = ⊥ :=
          (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
            p _ hunderMlies).mpr ⟨heM, hfM⟩
        rw [hbotQ] at hmem
        exact Subgroup.mem_bot.mp hmem
      refine eq_one_of_fixes_sup L M σ ?_ ?_
      · intro x
        have h3 : (σ.restrictNormal ↥L) x = x := by
          rw [show σ.restrictNormal ↥L = 1 from hL1]; rfl
        have h2 := AlgEquiv.restrictNormal_commutes (F := K) σ ↥L x
        rw [h3] at h2
        have h4 : algebraMap ↥L ↥(L ⊔ M) x = ⟨x.1, (le_sup_left : L ≤ L ⊔ M) x.2⟩ := rfl
        rw [h4] at h2
        exact h2.symm
      · intro x
        have h3 : (σ.restrictNormal ↥M) x = x := by
          rw [show σ.restrictNormal ↥M = 1 from hM1]; rfl
        have h2 := AlgEquiv.restrictNormal_commutes (F := K) σ ↥M x
        rw [h3] at h2
        have h4 : algebraMap ↥M ↥(L ⊔ M) x = ⟨x.1, (le_sup_right : M ≤ L ⊔ M) x.2⟩ := rfl
        rw [h4] at h2
        exact h2.symm
    have hcard1 : Nat.card (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
        (K := K) R) = 1 := (Subgroup.eq_bot_iff_card _).mp hbot
    have hcard := Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup
      (K := K) (L := ↥(L ⊔ M)) p R hRlies
    rw [hcard1] at hcard
    refine (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥(L ⊔ M)) p).mpr ⟨?_, ?_⟩
    · exact Nat.eq_one_of_mul_eq_one_right hcard.symm
    · exact Nat.eq_one_of_mul_eq_one_left hcard.symm
  -- ## (3) the density argument
  have hsupL : splitPrimesOf K ↥(L ⊔ M) = splitPrimesOf K ↥L :=
    Set.Subset.antisymm hle1 hle2
  have hdL : NumberField.Set.HasDirichletDensity (splitPrimesOf K ↥L)
      (1 / (Module.finrank K ↥L : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
  have hdN : NumberField.Set.HasDirichletDensity (splitPrimesOf K ↥(L ⊔ M))
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
  have hdNL : NumberField.Set.HasDirichletDensity (splitPrimesOf K ↥L)
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) := hsupL ▸ hdN
  have hdegL : Module.finrank K ↥L = Module.finrank K ↥(L ⊔ M) := by
    have heq := tendsto_nhds_unique hdL hdNL
    rw [one_div, one_div] at heq
    have h2 : (Module.finrank K ↥L : ℝ) = (Module.finrank K ↥(L ⊔ M) : ℝ) := inv_inj.mp heq
    exact_mod_cast h2
  have hLtop : L = L ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_left hdegL
  have hsupM : splitPrimesOf K ↥(L ⊔ M) = splitPrimesOf K ↥M := by rw [hsupL, h]
  have hdM : NumberField.Set.HasDirichletDensity (splitPrimesOf K ↥M)
      (1 / (Module.finrank K ↥M : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
  have hdNM : NumberField.Set.HasDirichletDensity (splitPrimesOf K ↥M)
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) := hsupM ▸ hdN
  have hdegM : Module.finrank K ↥M = Module.finrank K ↥(L ⊔ M) := by
    have heq := tendsto_nhds_unique hdM hdNM
    rw [one_div, one_div] at heq
    have h2 : (Module.finrank K ↥M : ℝ) = (Module.finrank K ↥(L ⊔ M) : ℝ) := inv_inj.mp heq
    exact_mod_cast h2
  have hMtop : M = L ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_right hdegM
  have hMleL : M ≤ L := by rw [hLtop]; exact le_sup_right
  have hLleM : L ≤ M := by rw [hMtop]; exact le_sup_left
  exact le_antisymm hLleM hMleL

/-- The place system of a separable closure detects finite normal subextensions. -/
theorem eq_of_stabilizer_le_fixingSubgroup {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    {N N' : IntermediateField K K'} [FiniteDimensional K N] [Normal K N] [NumberField ↥N]
    [FiniteDimensional K N'] [Normal K N'] [NumberField ↥N']
    (h : ∀ (B : ValuationSubring K'), B.comap (algebraMap K K') ≠ ⊤ →
      (MulAction.stabilizer Gal(K'/K) B ≤ N.fixingSubgroup ↔
        MulAction.stabilizer Gal(K'/K) B ≤ N'.fixingSubgroup)) :
    N = N' := by
  haveI hgal : IsGalois K K' := IsSepClosure.isGalois
  have hsplit : splitPrimesOf K ↥N = splitPrimesOf K ↥N' := by
    ext p
    obtain ⟨B, hB⟩ :=
      Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
        (K := K) (K' := K') p
    have hne : B.comap (algebraMap K K') ≠ ⊤ := by
      rw [hB]
      exact Submission.NeukirchUchida.Local.valuationSubringAtPrime_ne_top p
    have hiff := h B hne
    rw [stabilizer_le_fixingSubgroup_iff_splitCompletely p B hB,
      stabilizer_le_fixingSubgroup_iff_splitCompletely p B hB] at hiff
    simpa only [splitPrimesOf, Set.mem_ofPred_eq] using hiff
  exact eq_of_splitPrimesOf_eq hsplit

end NK.Reconstruct
