import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Basic
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem
import Submission.NK.HeckeL.Basic
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Placeholders for the two delegated inputs (removed once they land) -/

/-! ## The fractional ideal of the idèle of a prime -/

section Konly

variable {K : Type*} [Field K] [NumberField K]

/-- The fractional ideal of the idèle of a prime is that prime. -/
theorem idealOf_ideleOfPrime (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Idele.idealOf (NK.HeckeL.ideleOfPrime K 𝔭) = (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  refine IdeleClassGroup.fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _)
    (FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.ne_bot) fun q => ?_
  rw [Idele.count_idealOf, NK.HeckeL.ideleOfPrime, IdeleClassGroup.exp_ideleOfFun,
    FractionalIdeal.count_maximal]
  by_cases h : q = 𝔭
  · simp [h]
  · have h' : ¬ 𝔭 = q := fun h'' => h h''.symm
    simp [h, h']

/-- The idèle of a prime not dividing `m` lies in the congruence subgroup of modulus `m`. -/
theorem ideleOfPrime_mem_congruenceSubgroup (m : ℕ) (U : Subgroup (Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    NK.HeckeL.ideleOfPrime K 𝔭 ∈ U := by
  classical
  rw [hU.1 (NK.HeckeL.ideleOfPrime K 𝔭)]
  constructor
  · intro 𝔮 h𝔮
    have hne : 𝔮 ≠ 𝔭 := fun h => h𝔭 (h ▸ h𝔮)
    have hunit : (NK.HeckeL.ideleOfPrime K 𝔭) (Place.ofFinite 𝔮) = 1 := by
      show IdeleClassGroup.unifUnit K 𝔮 ^ (if 𝔮 = 𝔭 then (1 : ℤ) else 0) = 1
      rw [if_neg hne, zpow_zero]
    have hval : ((NK.HeckeL.ideleOfPrime K 𝔭 (Place.ofFinite 𝔮) :
        (𝔮.adicCompletion K)ˣ) : 𝔮.adicCompletion K) = 1 := by
      rw [hunit]
      rfl
    rw [hval, sub_self, map_zero]
    exact zero_le
  · intro w hw
    have h1 : ((NK.HeckeL.ideleOfPrime K 𝔭 (Place.ofInfinite w) : (w.Completion)ˣ) :
        w.Completion) = 1 := rfl
    rw [h1, map_one]
    exact zero_lt_one

end Konly

/-! ## The values of the idèlic Artin map -/

section Assembly

variable (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
  (U : Subgroup (Idele K))
  (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U)

/-- The crux input: the Artin symbol of the principal ideal of an element of the congruence
subgroup is trivial. -/
def Crux : Prop :=
  ∀ b : Kˣ, Idele.principalIdele K b ∈ U →
    artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K)) = 1

lemma ideleArtin_one (hstep : Crux hcomm U) :
    ideleArtin hcomm U hadj 1 = 1 := by
  show artinSym (K := K) (L := L) hcomm
    (Idele.idealOf (1 * Idele.principalIdele K (adjust U hadj 1))) = 1
  rw [one_mul, Idele.idealOf_principalIdele]
  exact hstep _ (by simpa using adjust_spec U hadj 1)

lemma ideleArtin_principal (hstep : Crux hcomm U) (a : Kˣ) :
    ideleArtin hcomm U hadj (Idele.principalIdele K a) = 1 := by
  show artinSym (K := K) (L := L) hcomm
    (Idele.idealOf (Idele.principalIdele K a *
      Idele.principalIdele K (adjust U hadj (Idele.principalIdele K a)))) = 1
  have hb : Idele.principalIdele K (a * adjust U hadj (Idele.principalIdele K a)) ∈ U := by
    rw [map_mul]
    exact adjust_spec U hadj (Idele.principalIdele K a)
  rw [← map_mul, Idele.idealOf_principalIdele]
  exact hstep _ hb

lemma ideleArtin_ideleOfPrime (m : ℕ)
    (hU : IsCongruenceSubgroup (K := K) m U) (hstep : Crux hcomm U)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    ideleArtin hcomm U hadj (NK.HeckeL.ideleOfPrime K 𝔭)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 := by
  show artinSym (K := K) (L := L) hcomm
    (Idele.idealOf (NK.HeckeL.ideleOfPrime K 𝔭 *
      Idele.principalIdele K (adjust U hadj (NK.HeckeL.ideleOfPrime K 𝔭)))) = _
  have h𝔭U : NK.HeckeL.ideleOfPrime K 𝔭 ∈ U :=
    ideleOfPrime_mem_congruenceSubgroup m U hU 𝔭 h𝔭
  have hbU : Idele.principalIdele K (adjust U hadj (NK.HeckeL.ideleOfPrime K 𝔭)) ∈ U := by
    have h2 := adjust_spec U hadj (NK.HeckeL.ideleOfPrime K 𝔭)
    have h3 := U.mul_mem (U.inv_mem h𝔭U) h2
    rwa [inv_mul_cancel_left] at h3
  have hA : (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.ne_bot
  have hB : FractionalIdeal.spanSingleton (𝓞 K)⁰
      ((adjust U hadj (NK.HeckeL.ideleOfPrime K 𝔭) : Kˣ) : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
  rw [Idele.idealOf_mul, idealOf_ideleOfPrime, Idele.idealOf_principalIdele,
    artinSym_mul (K := K) (L := L) hcomm hA hB, hstep _ hbU, mul_one, artinSym_prime]

lemma ideleArtin_mul (hstep : Crux hcomm U) (x y : Idele K) :
    ideleArtin hcomm U hadj (x * y)
      = ideleArtin hcomm U hadj x * ideleArtin hcomm U hadj y := by
  have hid : (x * Idele.principalIdele K (adjust U hadj x))
        * (y * Idele.principalIdele K (adjust U hadj y))
      = ((x * y) * Idele.principalIdele K (adjust U hadj (x * y)))
        * Idele.principalIdele K (adjust U hadj x * adjust U hadj y
            * (adjust U hadj (x * y))⁻¹) := by
    simp only [map_mul, map_inv, mul_assoc, mul_left_comm, mul_comm, mul_inv_cancel,
      inv_mul_cancel, mul_one, one_mul]
  have hcU : Idele.principalIdele K (adjust U hadj x * adjust U hadj y
      * (adjust U hadj (x * y))⁻¹) ∈ U := by
    have heq : Idele.principalIdele K (adjust U hadj x * adjust U hadj y
          * (adjust U hadj (x * y))⁻¹)
        = ((x * y) * Idele.principalIdele K (adjust U hadj (x * y)))⁻¹
          * ((x * Idele.principalIdele K (adjust U hadj x))
            * (y * Idele.principalIdele K (adjust U hadj y))) := by
      rw [hid, inv_mul_cancel_left]
    rw [heq]
    exact U.mul_mem (U.inv_mem (adjust_spec U hadj (x * y)))
      (U.mul_mem (adjust_spec U hadj x) (adjust_spec U hadj y))
  have hkey : Idele.idealOf (x * Idele.principalIdele K (adjust U hadj x))
        * Idele.idealOf (y * Idele.principalIdele K (adjust U hadj y))
      = Idele.idealOf ((x * y) * Idele.principalIdele K (adjust U hadj (x * y)))
        * FractionalIdeal.spanSingleton (𝓞 K)⁰
            ((adjust U hadj x * adjust U hadj y * (adjust U hadj (x * y))⁻¹ : Kˣ) : K) := by
    rw [← Idele.idealOf_mul, hid, Idele.idealOf_mul, Idele.idealOf_principalIdele]
  show artinSym (K := K) (L := L) hcomm
      (Idele.idealOf ((x * y) * Idele.principalIdele K (adjust U hadj (x * y))))
    = artinSym (K := K) (L := L) hcomm
        (Idele.idealOf (x * Idele.principalIdele K (adjust U hadj x)))
      * artinSym (K := K) (L := L) hcomm
        (Idele.idealOf (y * Idele.principalIdele K (adjust U hadj y)))
  exact (calc
      artinSym (K := K) (L := L) hcomm
            (Idele.idealOf (x * Idele.principalIdele K (adjust U hadj x)))
          * artinSym (K := K) (L := L) hcomm
            (Idele.idealOf (y * Idele.principalIdele K (adjust U hadj y)))
        = artinSym (K := K) (L := L) hcomm
            (Idele.idealOf (x * Idele.principalIdele K (adjust U hadj x))
              * Idele.idealOf (y * Idele.principalIdele K (adjust U hadj y))) :=
          (artinSym_mul (K := K) (L := L) hcomm (Idele.idealOf_ne_zero _)
            (Idele.idealOf_ne_zero _)).symm
      _ = artinSym (K := K) (L := L) hcomm
            (Idele.idealOf ((x * y) * Idele.principalIdele K (adjust U hadj (x * y)))
              * FractionalIdeal.spanSingleton (𝓞 K)⁰
                  ((adjust U hadj x * adjust U hadj y * (adjust U hadj (x * y))⁻¹ : Kˣ) : K)) := by
          rw [hkey]
      _ = artinSym (K := K) (L := L) hcomm
            (Idele.idealOf ((x * y) * Idele.principalIdele K (adjust U hadj (x * y))))
          * artinSym (K := K) (L := L) hcomm
            (FractionalIdeal.spanSingleton (𝓞 K)⁰
              ((adjust U hadj x * adjust U hadj y * (adjust U hadj (x * y))⁻¹ : Kˣ) : K)) :=
          artinSym_mul (K := K) (L := L) hcomm (Idele.idealOf_ne_zero _)
            (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _))
      _ = artinSym (K := K) (L := L) hcomm
            (Idele.idealOf ((x * y) * Idele.principalIdele K (adjust U hadj (x * y)))) := by
          rw [hstep _ hcU, mul_one]).symm

end Assembly

/-! ## Surjectivity -/

section Surjective

variable (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
  (U : Subgroup (Idele K))
  (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U)

/-- The finite set of primes of `K` dividing `(m)`. -/
noncomputable def primesDividing (m : ℕ) (hm : 0 < m) :
    Finset (NK.Chebotarev.PrimeIdeal K) := by
  classical
  have hm0 : ((m : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hfin : {𝔭 : HeightOneSpectrum (𝓞 K) | (m : 𝓞 K) ∈ 𝔭.asIdeal}.Finite := by
    refine (Ideal.finite_factors (R := 𝓞 K) (I := Ideal.span {((m : ℕ) : 𝓞 K)}) ?_).subset ?_
    · exact fun h => hm0 (Ideal.span_singleton_eq_bot.mp h)
    · intro 𝔭 h𝔭
      simp only [Set.mem_ofPred_eq] at h𝔭 ⊢
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact h𝔭
  exact hfin.toFinset

lemma mem_primesDividing (m : ℕ) (hm : 0 < m) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭 ∈ primesDividing (K := K) m hm ↔ (m : 𝓞 K) ∈ 𝔭.asIdeal := by
  rw [primesDividing]
  exact Set.Finite.mem_toFinset _

/-- **The idèlic Artin map is surjective**: the Frobenius elements at the primes `𝔭 ∤ (m)` generate
`Gal(L/K)`. -/
lemma surjective_ideleArtin (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1)
    (hU : IsCongruenceSubgroup (K := K) m U) (hstep : Crux hcomm U) :
    Function.Surjective (ideleArtin hcomm U hadj) := by
  classical
  let art : Idele K →* Gal(L/K) :=
    { toFun := ideleArtin hcomm U hadj
      map_one' := ideleArtin_one hcomm U hadj hstep
      map_mul' := ideleArtin_mul hcomm U hadj hstep }
  have hH : ∀ (p : NK.Chebotarev.PrimeIdeal K), p ∉ primesDividing (K := K) m hm →
      ∀ σ : Gal(L/K), NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ → σ ∈ art.range := by
    intro p hpT σ hσ
    have hpm : (m : 𝓞 K) ∉ p.asIdeal := fun h => hpT ((mem_primesDividing (K := K) m hm p).mpr h)
    have hunr : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
        P.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro P hP
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal P.asIdeal
        (Gal(L/K))]
      exact hram p hpm
    refine ⟨NK.HeckeL.ideleOfPrime K p, ?_⟩
    have h1 : art (NK.HeckeL.ideleOfPrime K p)
        = Chebotarev.frobAtPrime (K := K) (L := L) p :=
      ideleArtin_ideleOfPrime hcomm U hadj m hU hstep p hpm
    rw [h1]
    exact (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p hunr
      σ).mp hσ
  have htop : art.range = ⊤ :=
    eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L)
      (primesDividing (K := K) m hm) art.range hH
  exact MonoidHom.range_eq_top.mp htop

end Surjective

/-! ## The main theorem -/

theorem exists_monoidHom_ideleArtin {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : ∀ (a : NumberField.RingOfIntegers K),
      a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)} →
      (∀ φ : K →+* ℝ, 0 < φ ((a : K))) →
      ∀ (s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
        (e : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
        (σ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Gal(L/K)),
        (∀ p ∈ s, (m : NumberField.RingOfIntegers K) ∉ p.asIdeal) →
        Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
        (∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (L := L) p (σ p)) →
        (s.toList.map (fun p => σ p ^ e p)).prod = 1)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U) :
    ∃ art : NK.GlobalCFT.Idele K →* Gal(L/K),
      (∀ x : NK.GlobalCFT.Idele K, art x = NK.CFTLib.Arl.ideleArtin hcomm U hadj x) ∧
      (∀ a : Kˣ, art (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime 𝔭) ∧
      Function.Surjective art := by
  have hstep : Crux (K := K) (L := L) hcomm U := fun b hb =>
    artinSym_spanSingleton_eq_one hcomm m hm hram hprinc b ((hU.2 b).mp hb).1 ((hU.2 b).mp hb).2
  refine ⟨{ toFun := ideleArtin hcomm U hadj
            map_one' := ideleArtin_one hcomm U hadj hstep
            map_mul' := ideleArtin_mul hcomm U hadj hstep }, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro a
    exact ideleArtin_principal hcomm U hadj hstep a
  · intro 𝔭 h𝔭
    exact ideleArtin_ideleOfPrime hcomm U hadj m hU hstep 𝔭 h𝔭
  · exact surjective_ideleArtin hcomm U hadj m hm hram hU hstep

end NK.CFTLib.Arl
