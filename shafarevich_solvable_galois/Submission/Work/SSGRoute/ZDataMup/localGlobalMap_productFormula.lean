import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.CycleArl
import Submission.Work.SSGRoute.ZDataMup.CycleAuxField
import Submission.Work.SSGRoute.ZDataMup.CycleBaseChangeExists
import Submission.Work.SSGRoute.ZDataMup.cruxLang_cycleIndexInequality
import Submission.Work.SSGRoute.ZDataMup.CycleConductorDropOfIndex
import Submission.Work.SSGRoute.ZDataMup.cycleKernelLe_of_cycle
import Submission.Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- Commutativity of the Galois group of a cyclic extension. -/
theorem comm_of_isCyclic_lmpf {G : Type*} [Group G] [IsCyclic G] :
    ∀ a b : G, a * b = b * a := by
  intro a b
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← zpow_add, ← zpow_add, add_comm m n]

/-- **The ramification-index form of unramifiedness.**  If every prime of `𝓞 L` above `Q` has
ramification index `1`, then the relative ramification index of `Q` in `L/K` is `1`. -/
theorem ramificationIdxIn_eq_one_of_isUnramifiedIn_lmpf {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1 := by
  obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) Q.asIdeal P.asIdeal (Gal(L/K))]
  exact hunr P hP

/-- **The idèlic Artin map attached to a modulus whose support is exactly the ramified primes**
(self-contained copy of `Work.SSGRoute.ZDataMup.exists_artinMap_of_ramifiedSupport`): from a modulus
`m > 0` with (i) every prime `∤ (m)` unramified (`hram`), (ii) every unramified prime `∤ (m)`
(`hsupp2`) and (iii) the ideal-theoretic reciprocity law at `m` (`hprinc`), there is a monoid
homomorphism `Φ : 𝕀_K →* Gal(L/K)` killing the principal idèles and the idèlic norms, and
Frobenius-normalised at every unramified prime.

The construction is the idèlic Artin map of `NK.CFTLib.Arl.exists_monoidHom_ideleArtin`, whose
Frobenius normalisation holds at the primes not dividing `(m)` by design; the hypothesis `hsupp2`
is what upgrades it to all unramified primes. -/
theorem exists_artinMap_of_ramifiedSupport_lmpf
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) {m : ℕ} (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hsupp2 : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1 →
      (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1 →
          Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  obtain ⟨art, hagree, hprincipal, hgood, _hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hram hprinc U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hnorm : ∀ y : NK.GlobalCFT.Idele L, art (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hram hprinc
      U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm z
    exact ⟨d, hUeq ▸ hd⟩
  exact ⟨art, hprincipal, hnorm, fun Q hQ => hgood Q (hsupp2 Q hQ)⟩

/-- **Hilbert reciprocity in the product (Frobenius-normalised) form, modulo the conductor drop.**

If there is a modulus `m > 0` which is supported *exactly* on the primes ramified in `L/K`
(`hram` and `hsupp2`) and satisfies the ideal-theoretic reciprocity law at `m` (`hprinc`), then the
existence of the global Artin map `Φ` with the three clauses follows from
`exists_artinMap_of_ramifiedSupport_lmpf`; its Frobenius normalisation is stated in the
`ramificationIdxIn = 1` form, which agrees with `IsUnramifiedIn`. -/
theorem localGlobalMap_productFormula_of_ramifiedModulus
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L)) (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hsupp2 : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1 →
      (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
          Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a := fun a b => mul_comm a b
  -- the reciprocity datum at a natural-number modulus
  obtain ⟨m, hm, hramIn, hprincIn⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  have hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m :=
    Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal hcomm m hm hramIn hprincIn
  -- the cycle supported exactly on the ramified primes, with the levels of `m`
  let c : Cycle K :=
    { supp := NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)
      lev := fun 𝔭 => max 1 (cycleLevel (K := K) m 𝔭) }
  have hmem : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Q ∈ c.supp ↔ ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q := by
    intro Q
    constructor
    · intro h hunr
      obtain ⟨q, hq, hqq⟩ := Finset.mem_image.mp h
      rw [Set.Finite.mem_toFinset] at hq
      have hlies : q.asIdeal.LiesOver Q.asIdeal := by
        refine ⟨?_⟩
        rw [← HeightOneSpectrum.under_asIdeal, hqq]
      exact hq (hunr q hlies)
    · intro h
      by_contra hcon
      exact h fun q hq =>
        NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes
          (K := K) (L := L) hcon hq
  have hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭 := fun 𝔭 _ => le_max_left _ _
  have hcycAdm : Cycle.IsAdmissible K L c := by
    intro 𝔭 h𝔭 𝔮 h𝔮 x hx
    refine hadm 𝔭 ?_ 𝔮 h𝔮 x ?_
    · by_contra hcon
      have h1 : Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1 :=
        hramIn 𝔭 hcon
      obtain ⟨q, hq, hqq⟩ := Finset.mem_image.mp h𝔭
      rw [Set.Finite.mem_toFinset] at hq
      have hlies : q.asIdeal.LiesOver 𝔭.asIdeal := by
        refine ⟨?_⟩
        rw [← HeightOneSpectrum.under_asIdeal, hqq]
      haveI : q.asIdeal.LiesOver 𝔭.asIdeal := hlies
      have h2 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
        rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
          (B := NumberField.RingOfIntegers L) 𝔭.asIdeal q.asIdeal (L ≃ₐ[K] L)]
        exact h1
      exact hq h2
    · have h1 : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (((x : 𝔭.adicCompletion K)) - 1)
          ≤ (WithZero.exp (-(((max 1 (cycleLevel (K := K) m 𝔭) : ℕ) : ℤ))) :
              WithZero (Multiplicative ℤ)) := hx
      refine le_trans h1 ?_
      rw [valued_natCast_eq_exp_cycleLevel (K := K) m hm 𝔭, WithZero.exp_le_exp]
      have h2 : ((cycleLevel (K := K) m 𝔭 : ℕ) : ℤ)
          ≤ ((max 1 (cycleLevel (K := K) m 𝔭) : ℕ) : ℤ) := by
        exact_mod_cast (le_max_right 1 (cycleLevel (K := K) m 𝔭))
      linarith
  obtain ⟨cL, hbc⟩ := CycleBaseChangeExists (K := K) (L := L) c
  have hpos : ∀ 𝔭 ∈ c.supp, 0 < c.lev 𝔭 :=
    fun 𝔭 h𝔭 => lt_of_lt_of_le Nat.zero_lt_one (hlev 𝔭 h𝔭)
  have hIdx : Module.finrank K L ≤
      (c.principalRay ⊔ c.normRay K L cL).relIndex c.idealCoprimeGroup :=
    cruxLang_cycleIndexInequality (K := K) (L := L) c cL hbc hpos
      (fun Q hQ => (hmem Q).mpr hQ) hcycAdm
  have hKr : ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K, c.FracCoprime A →
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L) hcomm A = 1 →
      A ∈ c.principalRay ⊔ c.normRay K L cL :=
    Work.SSGRoute.ZDataMup.cycleKernelLe_of_cycle (K := K) (L := L) hcomm c cL hbc
      (fun Q hQ => (hmem Q).mpr hQ) hlev (Cycle.auxField_exists L c)
  have hdrop := CycleConductorDropOfIndex (K := K) (L := L) c cL hlev hIdx hKr
  have hdrop' : ∀ b : Kˣ, c.CongrOne b →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((b : Kˣ) : K)) = 1 := by
    intro b hb
    have h := hdrop b hb
    simpa only [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
      NK.CFTLib.ArtinReciprocityIdeal.coe_spanUnit] using h
  obtain ⟨Φ, h1, h2, h3⟩ := Cycle.localGlobalMap_productFormula_of_cycleDrop hcomm c
    (fun Q hQ => (hmem Q).mpr hQ) (fun Q hQ => (hmem Q).mp hQ) hlev hdrop'
  exact ⟨Φ, h1, h2, fun Q hunr => h3 Q (Cycle.isUnramified_of_isUnramifiedIn (K := K) (L := L) Q hunr)⟩


/-- **Hilbert reciprocity in the product (Frobenius-normalised) form.**

For a finite **cyclic** extension `L/K` of number fields the global Artin map is the product
`∏_v θ_v` of the local Artin maps: there is a monoid homomorphism `Φ : 𝕀_K →* Gal(L/K)` which kills
the principal idèles `K^× ⊂ 𝕀_K`, kills the idèles that are norms from `L`, and sends the idèle of a
prime `Q` to the Frobenius element at `Q` for *every* unramified `Q`.

The proof goes through the cycle (ideal-modulus) conductor drop: `CycleFromReciprocityModulus`
supplies the cycle `c` supported *exactly* on the primes ramified in `L/K` (with the levels of a
reciprocity modulus, so that `c` is admissible), `cruxLang_cycleIndexInequality` supplies Lang's
norm index inequality at `c`, `ArtinReciprocity.cycleKernelLe` (the ideal-modulus Lang transfer,
via `Work.SSGRoute.ZDataMup.Cycle.AuxField_exists`) supplies the kernel containment
`ker ψ ∩ I(c) ⊆ P(c)·𝔑(c)`, `CycleConductorDropOfIndex` assembles the two into the conductor drop
`∀ b, c.CongrOne b → ψ((b)) = 1`, and `Cycle.localGlobalMap_productFormula_of_cycleDrop` turns the
drop into the global Artin map with the three clauses. -/
theorem localGlobalMap_productFormula
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
          Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a := fun a b => mul_comm a b
  obtain ⟨m, hm, hramIn, hprincIn⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  have hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m :=
    Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal hcomm m hm hramIn hprincIn
  let c : Cycle K :=
    { supp := NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)
      lev := fun 𝔭 => max 1 (cycleLevel (K := K) m 𝔭) }
  have hmem : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Q ∈ c.supp ↔ ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q := by
    intro Q
    constructor
    · intro h hunr
      obtain ⟨q, hq, hqq⟩ := Finset.mem_image.mp h
      rw [Set.Finite.mem_toFinset] at hq
      have hlies : q.asIdeal.LiesOver Q.asIdeal := by
        refine ⟨?_⟩
        rw [← HeightOneSpectrum.under_asIdeal, hqq]
      exact hq (hunr q hlies)
    · intro h
      by_contra hcon
      exact h fun q hq =>
        NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes
          (K := K) (L := L) hcon hq
  have hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭 := fun 𝔭 _ => le_max_left _ _
  have hcycAdm : Cycle.IsAdmissible K L c := by
    intro 𝔭 h𝔭 𝔮 h𝔮 x hx
    refine hadm 𝔭 ?_ 𝔮 h𝔮 x ?_
    · by_contra hcon
      have h1 : Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1 :=
        hramIn 𝔭 hcon
      obtain ⟨q, hq, hqq⟩ := Finset.mem_image.mp h𝔭
      rw [Set.Finite.mem_toFinset] at hq
      have hlies : q.asIdeal.LiesOver 𝔭.asIdeal := by
        refine ⟨?_⟩
        rw [← HeightOneSpectrum.under_asIdeal, hqq]
      haveI : q.asIdeal.LiesOver 𝔭.asIdeal := hlies
      have h2 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
        rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
          (B := NumberField.RingOfIntegers L) 𝔭.asIdeal q.asIdeal (L ≃ₐ[K] L)]
        exact h1
      exact hq h2
    · have h1 : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (((x : 𝔭.adicCompletion K)) - 1)
          ≤ (WithZero.exp (-(((max 1 (cycleLevel (K := K) m 𝔭) : ℕ) : ℤ))) :
              WithZero (Multiplicative ℤ)) := hx
      refine le_trans h1 ?_
      rw [valued_natCast_eq_exp_cycleLevel (K := K) m hm 𝔭, WithZero.exp_le_exp]
      have h2 : ((cycleLevel (K := K) m 𝔭 : ℕ) : ℤ)
          ≤ ((max 1 (cycleLevel (K := K) m 𝔭) : ℕ) : ℤ) := by
        exact_mod_cast (le_max_right 1 (cycleLevel (K := K) m 𝔭))
      linarith
  -- ## the base change of `c`, Lang's index inequality at `c`, and Lang's transfer at `c`
  obtain ⟨cL, hbc⟩ := CycleBaseChangeExists (K := K) (L := L) c
  have hpos : ∀ 𝔭 ∈ c.supp, 0 < c.lev 𝔭 :=
    fun 𝔭 h𝔭 => lt_of_lt_of_le Nat.zero_lt_one (hlev 𝔭 h𝔭)
  have hIdx : Module.finrank K L ≤
      (c.principalRay ⊔ c.normRay K L cL).relIndex c.idealCoprimeGroup :=
    cruxLang_cycleIndexInequality (K := K) (L := L) c cL hbc hpos
      (fun Q hQ => (hmem Q).mpr hQ) hcycAdm
  have hKr : ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K, c.FracCoprime A →
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L) hcomm A = 1 →
      A ∈ c.principalRay ⊔ c.normRay K L cL :=
    Work.SSGRoute.ZDataMup.cycleKernelLe_of_cycle (K := K) (L := L) hcomm c cL hbc
      (fun Q hQ => (hmem Q).mpr hQ) hlev (Cycle.auxField_exists L c)
  -- ## the conductor drop at the cycle
  have hdrop := CycleConductorDropOfIndex (K := K) (L := L) c cL hlev hIdx hKr
  have hdrop' : ∀ b : Kˣ, c.CongrOne b →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((b : Kˣ) : K)) = 1 := by
    intro b hb
    have h := hdrop b hb
    simpa only [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
      NK.CFTLib.ArtinReciprocityIdeal.coe_spanUnit] using h
  -- ## the global Artin map
  obtain ⟨Φ, h1, h2, h3⟩ := Cycle.localGlobalMap_productFormula_of_cycleDrop (K := K) (L := L)
    hcomm c (fun Q hQ => (hmem Q).mpr hQ) (fun Q hQ => (hmem Q).mp hQ) hlev hdrop'
  exact ⟨Φ, h1, h2,
    fun Q hunr => h3 Q (Cycle.isUnramified_of_isUnramifiedIn (K := K) (L := L) Q hunr)⟩

/-!
## UPDATE (this session): the cycle (ideal-modulus) route, and what is on disk now

The target is *proved* above from `Work.SSGRoute.ZDataMup.cycleConductorDrop` (the conductor drop at
a cycle, `Submission/Work/SSGRoute/ZDataMup/cycleConductorDrop.lean`, still `sorry`), via
`Cycle.localGlobalMap_productFormula_of_cycleDrop`.  This session built the rest of the road:

* `Submission/Work/SSGRoute/ZDataMup/CycleAuxField.lean` (**sorry-free**):
  `Cycle.normProd` (the product of the norms of the primes of a cycle), `Cycle.AuxFieldHyp` (Artin's
  lemma's auxiliary-field hypothesis for a cycle) and `Cycle.auxField_exists` — Artin's lemma at an
  *ideal* modulus.  It is derived from the ℕ-modulus `NK.CFTLib.ARL.auxField_exists_B`; note the
  universe restriction `K L : Type` (not `Type*`), forced by `NK.CFTLib.ARL.auxField_arith`.

* `Submission/Work/SSGRoute/ZDataMup/CycleConductorDropAssembly.lean` (**sorry-free**):
  `Cycle.coprimeGroup` (`I(c)` as the `FracCoprime` subgroup) and the assembly
  `Cycle.conductorDrop_of_kernelLe_of_index` — from the two halves of Lang's Theorem 2
  (the crux `hA : ker ψ ⊓ I(c) ⊆ P(c)·𝔑(c)` and the index inequality `hB : [L:K] ≤ [I(c) : P(c)·𝔑(c)]`),
  together with the formal inputs `hPNI`, `hsurj`, it produces
  `∀ b, c.CongrOne b → artinSymFracHom hcomm (spanUnit b) = 1`, i.e. exactly the `hdrop` hypothesis
  consumed by `Cycle.localGlobalMap_productFormula_of_cycleDrop`.

* `Submission/Work/SSGRoute/ZDataMup/cycleArtinSymSurjective.lean` (**sorry-free**):
  `Cycle.exists_artinSym_eq_of_cycle` — the `hsurj` input, from
  `NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime` at a natural-number modulus `m`
  whose support is contained in `c.supp`.

* `Submission/Work/SSGRoute/ZDataMup/cycleRayLeCoprime.lean` (**sorry-free**):
  `Cycle.principalRay_le_coprimeGroup`, `Cycle.normRay_le_coprimeGroup` and
  `Cycle.principalRay_sup_normRay_le_coprimeGroup` — the `hPNI` input (`P(c) ⊔ 𝔑(c) ≤ I(c)`).

**The two remaining inputs** (both stated for ideal moduli/cycles, and both *delegated* to the
fleet as `Work.SSGRoute.ZDataMup.cycleKernelLe_of_cycle` and
`Work.SSGRoute.ZDataMup.cycleIndexInequality_of_cycle`):

* `Cycle.kernelLe_of_cycle` — Lang's transfer at a cycle, the cycle analogue of
  `NK.CFTLib.ArtinReciprocityIdeal.kernelLe_of_auxField` (port of
  `Submission/NK/NUV2/ChebAux/kernelLe_of_auxField.lean`, the proof behind
  `NK.CFTLib.artinReciprocityIdeal_proved`), with `haux := Cycle.auxField_exists c` free;
* `Cycle.cycleIndexInequality_of_cycle` — Lang's cyclic norm index inequality at a cycle, the cycle
  analogue of `NK.NUV2.ARL.Gap.langCyclicRelIndex` (port of
  `Submission/NK/CFTLib/ArtinReciprocityIdeal/indexIdealCoprimeLeNormClassIndex.lean` together with
  `NK.Existence.congruenceUnits_le_normImage`).

With those two, `Work.SSGRoute.ZDataMup.Cycle.conductorDrop_of_kernelLe_of_index` (fed by the two
modules above and by `m`, `hram`, `hIc` coming from `NK.CFTLib.artinReciprocityIdeal_proved` as in
`localGlobalMap_productFormula_of_ramifiedModulus`) gives `cycleConductorDrop`, and hence closes the
target without touching any `sorry` of the sibling lane.

*Why the cycle formulation is unavoidable*: for `m : ℕ` the support of `(m)` is saturated above
`ℚ` (`p | m` forces every prime above `p` to divide `(m)`), whereas the conductor drop needs the
congruence at the *ramified* primes only; the gap primes (unramified, above a rational prime that
also has a ramified prime above it) are exactly the content of the missing theorem.  See
`NOTE_conductorDrop_obstruction.md`.
-/

/-!
## State of the proof, and the exact remaining input (measured)

**Proved here** (self-contained copies, so that this module does not depend on the lane files that
are being edited concurrently):

* `exists_artinMap_of_ramifiedSupport_lmpf` — for a modulus `m > 0` with (i) every prime `∤ (m)`
  unramified, (ii) every unramified prime `∤ (m)`, and (iii) `artinKillsPrincipal K L m`, there is
  `Φ : 𝕀_K →* Gal(L/K)` killing the principal idèles and the idèles that are norms and
  Frobenius-normalised at *every* unramified prime;
* `localGlobalMap_productFormula_of_ramifiedModulus` — the target from such an `m`.

**The remaining input (updated).** The target is *reduced* (this stretch, fully proved) to the
following statement about a **cycle** (ideal modulus, `Work.SSGRoute.ZDataMup.Cycle`) supported
exactly on the ramified primes of `L/K`:

  `Work.SSGRoute.ZDataMup.Cycle.localGlobalMap_productFormula_of_cycleDrop`

takes a cycle `c` of `K` with `¬IsUnramified Q ↔ Q ∈ c.supp`, levels `≥ 1`, and the *conductor drop*
`∀ b, c.CongrOne b → artinSym ((b)) = 1`, and produces `∃ Φ : 𝕀 K →* Gal(L/K)` with the three
clauses of the target.  Its proof builds the idèlic Artin map of the congruence subgroup of a cycle
(`Work.SSGRoute.ZDataMup.Cycle.exists_monoidHom_congrSubgroup`, `CycleArl.lean`, from the cycle
conductor drop on the principal idèles), whose idèlic input is supplied in `CycleAux.lean`
(`Cycle.exists_auxModulus`, `Cycle.exists_adjust`, `Cycle.exists_norm_adjust`,
`Cycle.artinSym_idealOf_normIdeleHom_eq_one`; all proved) and whose congruence subgroup is studied in
`CycleCongr.lean` (`Cycle.congrSubgroup`).  Everything except the conductor drop is thus *proved*, and the
target itself is now *proved from it*: this file constructs the cycle supported exactly on the
ramified primes from the reciprocity datum `NK.CFTLib.artinReciprocityIdeal_proved` (whose modulus
`m` has `hram`/`hprinc`, hence `IsAdmissible K L m` by
`Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal`) with levels `max 1 (cycleLevel m 𝔭)`,
reads off the two support conditions from `NK.CFTLib.ExistsCongruence.ramPrimes` and
`ramificationIdx_eq_one_of_notMem_ramPrimes`, transfers admissibility to the cycle, and applies
`Cycle.localGlobalMap_productFormula_of_cycleDrop` to `cycleConductorDrop`.

**The single remaining input** is therefore

  `Work.SSGRoute.ZDataMup.cycleConductorDrop` (`Submission/Work/SSGRoute/ZDataMup/cycleConductorDrop.lean`):
  the *conductor drop at a cycle* — the classical "the conductor is supported on the ramified
  primes" (Neukirch V.6.1 / Lang X §4) for an *ideal* modulus.  Its natural proof generalises the
  on-disk `ℕ`-modulus Lang machinery (`NK.CFTLib.ARLTransfer.kernelLe_of_auxField`,
  `NK.NUV2.ARL.Gap.langCyclicRelIndex`) to cycles, which is exactly the content of the sibling
  statements `Work.SSGRoute.ZDataMup.cycleKernelLe_of_admissible` and
  `Work.SSGRoute.ZDataMup.cycleIndexInequality` (both stated, with proof plans, in this directory,
  together with the idèle–ideal dictionary `CycleIdele.lean`).

**The original remaining input.** The target is also equivalent (through the clean material on disk) to
Milne, *CFT*, Theorem 8.1(a) in its strong form: the glued local–global Artin map
`Φ₀ = ∏_v θ_v` of `NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists` kills `Kˣ`.  The obstacle to
reaching it inside the workspace's `ℕ`-modulus framework is *saturation*: for `m : ℕ` the ideal
`(m)` is a product of rational primes, so `supp (m) = {𝔮 : p(𝔮) ∣ m}` is always a union of fibres
over `ℚ`; since the ramified primes must lie in it, every unramified prime sharing a rational prime
with a ramified one also lies in it, and the Frobenius normalisation obtained from a congruence
datum (available only at the primes `∤ (m)`) never covers it.  Hence no `ℕ`-modulus datum can
supply the target, and the classical input is needed, in one of the three forms recorded in
`Submission/Work/SSGRoute/ZDataMup/NOTE_conductorDrop_obstruction.md`:

* (a) Milne *CFT* VII.8.1(a) — the strong form of Hilbert reciprocity (`∑_v inv_v = 0`), whose
  classical proof is Milne Ch. VII §8: the cyclotomic case (Example 8.2), descent/ascent
  (Lemma 8.4), the equivalence of (a) and (b) for cyclic `L/K` (Lemma 8.5), and Prop. 7.2 + the
  Hasse principle (Lemma 8.6);
* (b) the generalisation of the Lang transfer/index machinery (`NK.CFTLib.ArtinReciprocityIdeal`)
  and of the idèlic congruence-datum construction from `m : ℕ` to an *ideal* modulus
  `𝔪 = ∏_{𝔭 ∈ R} 𝔭^{e_𝔭}` (the most mechanical of the three: the Lang statements use `m` only
  through `(m : 𝓞 K) ∈ 𝔭` and `Valued.v ((m : ℕ))`, both meaningful for an element of `Frac K`);
* (c) a Chebotarev-type density statement for the global norm group at the gap primes.
-/

end

end Work.SSGRoute.ZDataMup
