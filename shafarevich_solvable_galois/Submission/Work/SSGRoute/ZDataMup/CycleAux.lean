import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.Work.SSGRoute.ZDataMup.CycleCongr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèlic input of the Artin map of a cycle

`Work.SSGRoute.ZDataMup.Cycle` (an *ideal modulus*, `CycleDefs.lean`) is the modulus notion that
can be supported exactly on the ramified primes, unlike the natural-number moduli.  This module
supplies, for the congruence subgroup `Cycle.congrSubgroup c` of a cycle (`CycleCongr.lean`), the
input that the idèlic Artin map of `NK.CFTLib.Arl` consumes:

* `Cycle.exists_auxModulus` — an auxiliary natural-number modulus `m` whose congruence subgroup is
  contained in `Cycle.congrSubgroup c`;
* `Cycle.congrSubgroup_le_aux`, `Cycle.exists_adjust`, `Cycle.exists_norm_adjust` — the adjustment
  of idèles (resp. of idèlic norms) by principal idèles into `Cycle.congrSubgroup c`, transported
  from the `ℕ`-modulus machinery of `NK.CFTLib.Arl`;
* `Cycle.artinSym_idealOf_normIdeleHom_eq_one` — the Artin symbol of the ideal of an idèlic norm
  which is congruent to `1` modulo the cycle is trivial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain
open NK.GlobalCFT

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.Arl

namespace Cycle

variable {K : Type*} [Field K] [NumberField K]
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- **An auxiliary natural-number modulus dominating a cycle, valuation form.**  For a cycle `c`
whose levels on its support are `≥ 1` there is `m > 0` whose `𝔭`-adic value is at most the level of
`c` at every prime of `c`.  This implies `U(m) ≤ Cycle.congrSubgroup c`
(`Cycle.congrSubgroup_le_of_val`). -/
theorem exists_auxModulus_val (c : Cycle K) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    ∃ m : ℕ, 0 < m ∧ ∀ 𝔭 ∈ c.supp,
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : 𝔭.adicCompletion K)) ≤ c.level 𝔭 := by
  classical
  set M : ℕ := ∏ 𝔮 ∈ c.supp, Ideal.absNorm 𝔮.asIdeal with hM
  set K' : ℕ := c.supp.sup c.lev + 1 with hK'
  have hMpos : 0 < M := by
    rw [hM]
    refine Finset.prod_pos fun 𝔮 _ => Nat.pos_of_ne_zero ?_
    rw [Ideal.absNorm_ne_zero_iff]
    infer_instance
  refine ⟨M ^ K', pow_pos hMpos _, ?_⟩
  intro 𝔭 h𝔭
  have hmemM : ((M : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := by
    have hdvd : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 K) ∣ ((M : ℕ) : 𝓞 K) := by
      rw [hM, Nat.cast_prod]
      exact Finset.dvd_prod_of_mem _ h𝔭
    have hspan : Ideal.span {((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 K)} ≤ 𝔭.asIdeal :=
      (Ideal.span_singleton_le_iff_mem 𝔭.asIdeal).mpr (Ideal.absNorm_mem 𝔭.asIdeal)
    exact hspan (Ideal.mem_span_singleton.mpr hdvd)
  have hcM : 1 ≤ cycleLevel (K := K) M 𝔭 := by
    have hlt := NK.CFTLib.Arl.val_natCast_lt_one 𝔭 M hmemM
    rw [valued_natCast_eq_exp_cycleLevel (K := K) M hMpos 𝔭, ← WithZero.exp_zero,
      WithZero.exp_lt_exp] at hlt
    omega
  have hvM : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((M : ℕ) : 𝔭.adicCompletion K)) ≤ WithZero.exp (-(1 : ℤ)) := by
    rw [valued_natCast_eq_exp_cycleLevel (K := K) M hMpos 𝔭, WithZero.exp_le_exp]
    have h1 : (1 : ℤ) ≤ ((cycleLevel (K := K) M 𝔭 : ℕ) : ℤ) := by exact_mod_cast hcM
    linarith
  have hK'ge : max 1 (c.lev 𝔭) ≤ K' := by
    refine max_le ?_ ?_
    · rw [hK']; omega
    · rw [hK']
      exact le_trans (Finset.le_sup (f := c.lev) h𝔭) (Nat.le_succ _)
  calc Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((M ^ K' : ℕ) : 𝔭.adicCompletion K))
      = (Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (((M : ℕ) : 𝔭.adicCompletion K))) ^ K' := by
        rw [Nat.cast_pow, map_pow]
    _ ≤ (WithZero.exp (-(1 : ℤ))) ^ K' := pow_le_pow_left' hvM _
    _ = WithZero.exp (-((K' : ℕ) : ℤ)) := by
        rw [← WithZero.exp_nsmul]
        congr 1
        simp
    _ ≤ WithZero.exp (-(((max 1 (c.lev 𝔭) : ℕ) : ℤ))) := by
        rw [WithZero.exp_le_exp]
        have h1 : ((max 1 (c.lev 𝔭) : ℕ) : ℤ) ≤ ((K' : ℕ) : ℤ) := by exact_mod_cast hK'ge
        linarith
    _ = c.level 𝔭 := by rw [level]

/-- **An auxiliary natural-number modulus dominating a cycle.**  For every cycle `c` whose levels
on its support are `≥ 1` there is `m > 0` with `𝔭 | (m)` and `c.lev 𝔭 ≤ cycleLevel m 𝔭` for every
`𝔭 ∈ c.supp`. -/
theorem exists_auxModulus (c : Cycle K) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    ∃ m : ℕ, 0 < m ∧ ∀ 𝔭 ∈ c.supp,
      (m : 𝓞 K) ∈ 𝔭.asIdeal ∧ c.lev 𝔭 ≤ cycleLevel (K := K) m 𝔭 := by
  obtain ⟨m, hm, hval⟩ := exists_auxModulus_val (K := K) c hlev
  refine ⟨m, hm, fun 𝔭 h𝔭 => ⟨?_, ?_⟩⟩
  · have hlt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : 𝔭.adicCompletion K)) < 1 := lt_of_le_of_lt (hval 𝔭 h𝔭) (level_lt_one c 𝔭)
    have h1 : ((m : ℕ) : 𝔭.adicCompletion K)
        = algebraMap K (𝔭.adicCompletion K) ((m : ℕ) : K) := (map_natCast _ m).symm
    rw [h1, Commons.NumberTheory.NumberField.Completion.valued_alg_eq] at hlt
    have h2 : ((m : ℕ) : K) = algebraMap (𝓞 K) K ((m : ℕ) : 𝓞 K) := (map_natCast _ m).symm
    rw [h2] at hlt
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭 (m : 𝓞 K)).mp hlt
  · have h := hval 𝔭 h𝔭
    rw [valued_natCast_eq_exp_cycleLevel (K := K) m hm 𝔭, level, WithZero.exp_le_exp] at h
    have h2 : max 1 (c.lev 𝔭) ≤ cycleLevel (K := K) m 𝔭 := by
      have : ((max 1 (c.lev 𝔭) : ℕ) : ℤ) ≤ ((cycleLevel (K := K) m 𝔭 : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    exact le_trans (le_max_right _ _) h2

/-- **The congruence subgroup of an auxiliary modulus lies in the congruence subgroup of a
cycle.** -/
theorem congrSubgroup_le_aux (c : Cycle K) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    ∃ m : ℕ, 0 < m ∧ NK.CFTLib.Arl.congruenceSubgroup K m ≤ c.congrSubgroup := by
  obtain ⟨m, hm, hval⟩ := exists_auxModulus_val (K := K) c hlev
  exact ⟨m, hm, congrSubgroup_le_of_val (K := K) hm hval⟩

/-- **The adjustment of idèles by principal idèles into the congruence subgroup of a cycle.** -/
theorem exists_adjust (c : Cycle K) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ c.congrSubgroup := by
  obtain ⟨m, hm, hle⟩ := congrSubgroup_le_aux (K := K) c hlev
  intro x
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  obtain ⟨b, hb⟩ := hadj x
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun y => (hU.1 y).trans Iff.rfl
  exact ⟨b, hle (hUeq ▸ hb)⟩

/-- **The adjustment of idèlic norms.** -/
theorem exists_norm_adjust (c : Cycle K) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) :
    ∀ y : Idele L, ∃ d : Lˣ,
      Idele.normIdeleHom K L (y * Idele.principalIdele L d) ∈ c.congrSubgroup := by
  obtain ⟨m, hm, hle⟩ := congrSubgroup_le_aux (K := K) c hlev
  intro y
  obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm y
  exact ⟨d, hle hd⟩

/-- **Congruence to `1` modulo a cycle at a prime of the cycle makes the component a local
unit**, i.e. the `𝔮`-adic exponent of the idèle vanishes there. -/
theorem exp_eq_zero_of_mem_congrSubgroup {K : Type*} [Field K] [NumberField K]
    (c : Cycle K) (x : NK.GlobalCFT.Idele K) (hx : x ∈ c.congrSubgroup)
    (𝔮 : HeightOneSpectrum (𝓞 K)) (h𝔮 : 𝔮 ∈ c.supp) :
    NK.GlobalCFT.Idele.exp 𝔮 x = 0 := by
  have hcong : Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) - 1) ≤ c.level 𝔮 := hx.1 𝔮 h𝔮
  have hlt : Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) - 1) < 1 :=
    lt_of_le_of_lt hcong (level_lt_one c 𝔮)
  have hval : Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K)) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (v := Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : 𝔮.adicCompletion K))
      (y := ((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) - 1) (by simpa using hlt)
    rw [map_one, show (1 : 𝔮.adicCompletion K) +
      (((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) - 1) =
        ((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) from by ring] at h
    exact h
  have hmem : x (Place.ofFinite 𝔮) ∈ Place.localUnits K (Place.ofFinite 𝔮) :=
    (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mpr hval
  exact NK.GlobalCFT.Idele.exp_eq_zero_of_mem_localUnits hmem

/-- **The Artin symbol of the ideal of a congruence-`1` idèlic norm is trivial.**  The `𝔭`-adic
exponent of the ideal of `N_{L/K} w` is `∑_{𝔓 | 𝔭} f(𝔓|𝔭)·v_𝔓(w)`: at a prime of the cycle the
congruence forces it to vanish, and outside the cycle the prime is unramified and the exponent is a
multiple of the inertia degree, so the corresponding Frobenius power is trivial. -/
theorem artinSym_idealOf_normIdeleHom_eq_one [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (c : Cycle K)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p → p ∈ c.supp)
    (w : Idele L) (hw : Idele.normIdeleHom K L w ∈ c.congrSubgroup) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (Idele.idealOf (Idele.normIdeleHom K L w)) = 1 := by
  classical
  letI := NK.CFTLib.Arl.galCommMonoid hcomm
  have hunr : ∀ (𝔭 : HeightOneSpectrum (𝓞 K)), 𝔭 ∉ c.supp →
      ∀ 𝔓 : HeightOneSpectrum (𝓞 L), 𝔓.asIdeal.LiesOver 𝔭.asIdeal →
        𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro 𝔭 h𝔭 𝔓 h𝔓
    letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
      IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
      IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
    have hI : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) 𝔭 :=
      Classical.byContradiction fun hcon => h𝔭 (hram 𝔭 hcon)
    exact hI 𝔓 h𝔓
  have hcount : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      NK.CFTLib.Arl.exps (Idele.idealOf (Idele.normIdeleHom K L w)) 𝔭
        = ∑ 𝔓 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭,
            ((𝔓.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L 𝔓
              (Idele.idealOf w)) := by
    intro 𝔭
    rw [NK.CFTLib.Arl.exps_apply, Idele.count_idealOf,
      NK.CFTLib.Arl.exp_normIdeleHom_eq_sum_aux K L w 𝔭]
    exact Finset.sum_congr rfl fun 𝔓 _ => by rw [Idele.count_idealOf]
  have hterm : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
        ^ (NK.CFTLib.Arl.exps (Idele.idealOf (Idele.normIdeleHom K L w)) 𝔭) = 1 := by
    intro 𝔭
    by_cases h𝔭 : 𝔭 ∈ c.supp
    · rw [NK.CFTLib.Arl.exps_apply, Idele.count_idealOf,
        exp_eq_zero_of_mem_congrSubgroup c (Idele.normIdeleHom K L w) hw 𝔭 h𝔭, zpow_zero]
    · rw [hcount 𝔭]
      refine NK.CFTLib.Arl.zpow_sum_eq_one_of _ _ _ fun 𝔓 h𝔓 => ?_
      have hLies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
        (Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := 𝔓)).mp h𝔓
      obtain ⟨P, hP, hPFrob⟩ := NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm 𝔭
        (fun 𝔓 h => hunr 𝔭 h𝔭 𝔓 h)
      have hfrob : NK.Chebotarev.IsFrobAt 𝔓
          (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) :=
        NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver hcomm hP hLies hPFrob
      have horder : orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
          = 𝔓.asIdeal.inertiaDeg (𝓞 K) :=
        NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg hLies (hunr 𝔭 h𝔭 𝔓 hLies) hfrob
      rw [zpow_mul, zpow_natCast, ← horder, pow_orderOf_eq_one, one_zpow]
  have hprod : (NK.CFTLib.Arl.exps (Idele.idealOf (Idele.normIdeleHom K L w))).prod
      (fun (𝔭 : HeightOneSpectrum (𝓞 K)) (e : ℤ) =>
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e) = 1 := by
    rw [Finsupp.prod_congr
      (f := NK.CFTLib.Arl.exps (Idele.idealOf (Idele.normIdeleHom K L w)))
      (g1 := fun (𝔭 : HeightOneSpectrum (𝓞 K)) (e : ℤ) =>
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e)
      (g2 := fun (_ : HeightOneSpectrum (𝓞 K)) (_ : ℤ) => (1 : Gal(L/K)))
      (fun 𝔭 _ => hterm 𝔭)]
    rw [Finsupp.prod_of_support_subset
      (NK.CFTLib.Arl.exps (Idele.idealOf (Idele.normIdeleHom K L w)))
      (fun _ h => h) (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : ℤ) => (1 : Gal(L/K)))
      (fun _ _ => rfl)]
    exact Finset.prod_eq_one fun _ _ => rfl
  unfold NK.CFTLib.Arl.artinSym
  exact hprod

end Cycle
end Work.SSGRoute.ZDataMup
