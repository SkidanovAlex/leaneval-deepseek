import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleIdele
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Porting Lang's cyclic norm index theorem to cycles, I: the containment `P(c)·𝔑(c) ≤ I(c)`

The first piece of the `ℕ`-modulus chain `principalRay_sup_normRay_le_idealCoprimeGroup`
(`NK.NUV2/ARL/Gap/langCyclicRelIndex.lean`, proven and clean) ported to Lang's *cycle* (ideal
modulus) vocabulary of `CycleDefs`/`CycleIdele`:

* `Cycle.idealCoprimeGroup_le_Icoprime` — the closure-presented `I(c)` is the "coprime" subgroup;
* `Cycle.count_spanUnit_eq_zero_of_congrOne` — a congruence-`1` principal ideal is a local unit at
  the primes of the cycle (so is coprime to `c`);
* `Cycle.principalRay_le_idealCoprimeGroup` — `P(c) ≤ I(c)` (`hpos` on the levels is needed:
  at level `0` the congruence `a ≡ 1` only forces `a` integral);
* `Cycle.Icoprime_le_idealCoprimeGroup` — the converse, by the prime factorization of a fractional
  ideal;
* `Cycle.principalRay_sup_normRay_le_idealCoprimeGroup` — the two together.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.ArtinReciprocityIdeal
open NK.GlobalCFT

namespace Cycle

variable {K : Type} [Field K] [NumberField K]

/-- **The closure-presented `I(c)` lies in the "coprime" subgroup `I(c)`.**  Each generator is a
prime outside `c`, hence has zero `count` at every prime of `c`. -/
theorem idealCoprimeGroup_le_Icoprime (c : Cycle K) :
    c.idealCoprimeGroup ≤ c.Icoprime := by
  rw [idealCoprimeGroup, Subgroup.closure_le]
  rintro A ⟨𝔭, h𝔭, rfl⟩
  change c.FracCoprime (idealUnit 𝔭.asIdeal 𝔭.ne_bot)
  intro 𝔮 h𝔮
  have hne : 𝔭 ≠ 𝔮 := fun h => h𝔭 (h ▸ h𝔮)
  show FractionalIdeal.count K 𝔮 ((idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) :
    FractionalIdeal (𝓞 K)⁰ K) = 0
  rw [idealUnit, Units.val_mk0]
  exact FractionalIdeal.count_maximal_coprime (K := K) (v := 𝔮) (w := 𝔭) hne

/-- **A congruence-`1` principal ideal is a unit at the primes of the cycle.**  The hypothesis
`hpos` (positive levels on the support) is what makes the congruence force
`v_𝔭(a - 1) < v_𝔭(1)`, hence `v_𝔭(a) = 1`. -/
theorem count_spanUnit_eq_zero_of_congrOne (c : Cycle K) (hpos : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    {a : Kˣ} (ha : c.CongrOne a) (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : 𝔭 ∈ c.supp) :
    FractionalIdeal.count K 𝔭 ((spanUnit a : Frac K) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  classical
  rw [coe_spanUnit, ← Idele.idealOf_principalIdele, Idele.count_idealOf, Idele.exp_def]
  have ha' : Valued.v (R := Place.localField K (Place.ofFinite 𝔭))
      (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap K (Place.localField K (Place.ofFinite 𝔭)) (a : K) - 1) < 1 := by
    refine lt_of_le_of_lt (ha.1 𝔭 h𝔭) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    have h1 : (1 : ℤ) ≤ (c.lev 𝔭 : ℤ) := by exact_mod_cast hpos 𝔭 h𝔭
    linarith
  have hval : Valued.v (R := Place.localField K (Place.ofFinite 𝔭))
      (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap K (Place.localField K (Place.ofFinite 𝔭)) (a : K)) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (v := Valued.v (R := Place.localField K (Place.ofFinite 𝔭))
        (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : Place.localField K (Place.ofFinite 𝔭)))
      (y := algebraMap K (Place.localField K (Place.ofFinite 𝔭)) (a : K) - 1)
      (by simpa using ha')
    rw [map_one, show (1 : Place.localField K (Place.ofFinite 𝔭)) +
      (algebraMap K (Place.localField K (Place.ofFinite 𝔭)) (a : K) - 1) =
        algebraMap K (Place.localField K (Place.ofFinite 𝔭)) (a : K) from by ring] at h
    exact h
  rw [show (((Idele.principalIdele K a) (Place.ofFinite 𝔭) :
        (Place.localField K (Place.ofFinite 𝔭))ˣ) : Place.localField K (Place.ofFinite 𝔭))
      = algebraMap K (Place.localField K (Place.ofFinite 𝔭)) (a : K) from by
    rw [Idele.principalIdele_apply, Units.coe_map]
    rfl]
  rw [hval]
  simp

/-- **`P(c) ≤ I(c)`.**  A generator `(a)` with `a ≡ 1 mod c` has no prime factor in `c`. -/
theorem principalRay_le_Icoprime (c : Cycle K) (hpos : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    c.principalRay ≤ c.Icoprime := by
  rw [principalRay, Subgroup.closure_le]
  rintro A ⟨a, ha, rfl⟩
  change c.FracCoprime (spanUnit a)
  exact fun 𝔭 h𝔭 => count_spanUnit_eq_zero_of_congrOne c hpos ha 𝔭 h𝔭


/-- **Every fractional ideal coprime to `c` is the ideal of an idèle of the congruence
subgroup.**  Cycle analogue of `NK.CFTLib.ARL.exists_idealOf_eq_of_mem_Icoprime`: take the idèle
with `𝔭`-adic exponent `count 𝔭 A` (which vanishes on `c.supp`). -/
theorem exists_idealOf_eq_of_mem_Icoprime (c : Cycle K) {A : Frac K}
    (hA : A ∈ c.Icoprime) :
    ∃ x : Idele K, x ∈ c.congrSubgroup ∧ IdeleClassGroup.idealOfUnitHom K x = A := by
  classical
  set f : HeightOneSpectrum (𝓞 K) → ℤ :=
    fun 𝔭 => FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K) with hf_def
  have hf : ∀ᶠ 𝔭 in Filter.cofinite, f 𝔭 = 0 :=
    FractionalIdeal.finite_factors (K := K) (I := (A : FractionalIdeal (𝓞 K)⁰ K))
  refine ⟨IdeleClassGroup.ideleOfFun K f hf, ?_, ?_⟩
  · rw [mem_congrSubgroup_iff]
    constructor
    · intro 𝔭 h𝔭
      rw [congrAt_iff]
      have hf0 : f 𝔭 = 0 := by
        rw [hf_def]
        exact hA 𝔭 h𝔭
      have h1 : ((IdeleClassGroup.ideleOfFun K f hf (Place.ofFinite 𝔭) :
          (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) = 1 := by
        change ((IdeleClassGroup.unifUnit K 𝔭 ^ (f 𝔭) : (𝔭.adicCompletion K)ˣ) :
          𝔭.adicCompletion K) = 1
        rw [hf0, zpow_zero]
        rfl
      rw [h1, sub_self, map_zero]
      exact zero_le
    · intro w
      exact NK.CFTLib.Arl.posAtReal_one w
  · refine Units.ext ?_
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0]
    exact IdeleClassGroup.fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _) A.ne_zero
      (fun 𝔭 => by rw [IdeleClassGroup.count_idealOf_ideleOfFun])


/-- **The converse: a fractional ideal coprime to `c` lies in the subgroup generated by the primes
outside `c`.**  Port of the second direction of
`NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff`: `A` is the finitely supported
product `∏_𝔭 𝔭 ^ (count 𝔭 A)`, every factor with `𝔭 ∈ c.supp` has exponent `0`, and every other
factor is a generator. -/
theorem Icoprime_le_idealCoprimeGroup (c : Cycle K) :
    c.Icoprime ≤ c.idealCoprimeGroup := by
  intro A hA
  set e : HeightOneSpectrum (𝓞 K) → ℤ :=
    fun 𝔭 => FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K) with he
  set u : HeightOneSpectrum (𝓞 K) → Frac K :=
    fun 𝔭 => idealUnit 𝔭.asIdeal 𝔭.ne_bot with hu
  have hfin : Function.HasFiniteMulSupport fun 𝔭 : HeightOneSpectrum (𝓞 K) => u 𝔭 ^ e 𝔭 := by
    have hcount : {𝔭 : HeightOneSpectrum (𝓞 K) | e 𝔭 ≠ 0}.Finite := by
      have h1 := Filter.eventually_cofinite.mp
        (FractionalIdeal.finite_factors (K := K) (A : FractionalIdeal (𝓞 K)⁰ K))
      simpa [he] using h1
    exact hcount.subset fun 𝔭 h𝔭 he0 =>
      h𝔭 (by show u 𝔭 ^ e 𝔭 = 1; rw [he0, zpow_zero])
  have hmem : ∀ 𝔭, u 𝔭 ^ e 𝔭 ∈ c.idealCoprimeGroup := by
    intro 𝔭
    by_cases h𝔭 : 𝔭 ∈ c.supp
    · have h0 : e 𝔭 = 0 := hA 𝔭 h𝔭
      rw [h0, zpow_zero]
      exact Subgroup.one_mem _
    · have hgen : u 𝔭 ∈ c.idealCoprimeGroup := by
        rw [idealCoprimeGroup]
        exact Subgroup.subset_closure ⟨𝔭, h𝔭, rfl⟩
      exact Subgroup.zpow_mem _ hgen (e 𝔭)
  have hprod : (∏ᶠ 𝔭, u 𝔭 ^ e 𝔭) ∈ c.idealCoprimeGroup :=
    finprod_induction (fun x => x ∈ c.idealCoprimeGroup)
      (Subgroup.one_mem _) (fun _ _ hx hy => Subgroup.mul_mem _ hx hy) hmem
  have hAeq : A = ∏ᶠ 𝔭, u 𝔭 ^ e 𝔭 := by
    apply Units.ext
    change (A : FractionalIdeal (𝓞 K)⁰ K) =
      (Units.coeHom (FractionalIdeal (𝓞 K)⁰ K)) (∏ᶠ 𝔭, u 𝔭 ^ e 𝔭)
    rw [MonoidHom.map_finprod (Units.coeHom (FractionalIdeal (𝓞 K)⁰ K)) hfin,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
        (I := (A : FractionalIdeal (𝓞 K)⁰ K)) A.ne_zero]
    refine finprod_congr fun 𝔭 => ?_
    simp [u, e, idealUnit]
  rw [hAeq]
  exact hprod

/-- **`P(c) ≤ I(c)`** in the closure presentation. -/
theorem principalRay_le_idealCoprimeGroup (c : Cycle K) (hpos : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    c.principalRay ≤ c.idealCoprimeGroup :=
  le_trans (principalRay_le_Icoprime c hpos) (Icoprime_le_idealCoprimeGroup c)

/-- **`𝔑(c) ≤ I(c)`.**  The relative norm of an ideal of `L` coprime to `cL` is coprime to `c`,
as soon as `cL` contains the primes of `L` above the primes of `c` (`hbc`): the exponent of a prime
`𝔭 ∈ c.supp` in `N 𝔅` is `∑_{𝔮 | 𝔭} f(𝔮/𝔭)·v_𝔮(𝔅)`, and every `𝔮 | 𝔭` lies in `cL.supp`, so
every term vanishes. -/
theorem normRay_le_idealCoprimeGroup {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (c : Cycle K) (cL : Cycle L) (hbc : c.IsBaseChange K L cL) :
    normRay K L c cL ≤ c.idealCoprimeGroup := by
  rw [normRay]
  refine (Subgroup.closure_le c.idealCoprimeGroup).mpr ?_
  rintro A ⟨I, hI, hcop, rfl⟩
  refine Icoprime_le_idealCoprimeGroup c ?_
  change c.FracCoprime
    (idealUnit (K := K) (Ideal.relNorm (𝓞 K) I)
      (fun h => hI ((Ideal.relNorm_eq_bot_iff).mp h)))
  intro 𝔭 h𝔭
  show FractionalIdeal.count K 𝔭 ((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) :
    FractionalIdeal (𝓞 K)⁰ K) = 0
  rw [← NK.CFTLib.ARL.relNormFI_coeIdeal (K := K) (L := L) I hI,
    NK.CFTLib.ARL.count_relNormFI, NK.CFTLib.ARL.relNormExp]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hlies : q.asIdeal.LiesOver 𝔭.asIdeal :=
    (Place.mem_primesOverFinite (K := K) (L := L)).mp hq
  have hqsupp : q ∈ cL.supp := (hbc q).mpr ⟨𝔭, h𝔭, hlies⟩
  have h0 : FractionalIdeal.count L q ((idealUnit (K := L) I hI :
      Frac L) : FractionalIdeal (𝓞 L)⁰ L) = 0 := hcop q hqsupp
  rw [idealUnit, Units.val_mk0] at h0
  rw [h0, mul_zero]

/-- **`P(c)·𝔑(c) ≤ I(c)`** — the first piece of Lang's cyclic norm index theorem at a cycle
(port of `NK.NUV2.ARL.Gap.principalRay_sup_normRay_le_idealCoprimeGroup`). -/
theorem principalRay_sup_normRay_le_idealCoprimeGroup {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (c : Cycle K) (cL : Cycle L)
    (hpos : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) (hbc : c.IsBaseChange K L cL) :
    (c.principalRay ⊔ normRay K L c cL) ≤ c.idealCoprimeGroup :=
  sup_le (principalRay_le_idealCoprimeGroup c hpos) (normRay_le_idealCoprimeGroup c cL hbc)


end Cycle

end Work.SSGRoute.ZDataMup

/-! ## Axiom check -/

#print axioms Work.SSGRoute.ZDataMup.Cycle.principalRay_sup_normRay_le_idealCoprimeGroup
#print axioms Work.SSGRoute.ZDataMup.Cycle.exists_idealOf_eq_of_mem_Icoprime
#print axioms Work.SSGRoute.ZDataMup.Cycle.Icoprime_le_idealCoprimeGroup
#print axioms Work.SSGRoute.ZDataMup.Cycle.count_spanUnit_eq_zero_of_congrOne
