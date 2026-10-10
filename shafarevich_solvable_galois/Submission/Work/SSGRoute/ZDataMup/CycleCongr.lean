import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The congruence subgroup of a cycle (ideal modulus)

`Work.SSGRoute.ZDataMup.Cycle` (see `CycleDefs.lean`) is the ideal-modulus analogue of the
natural-number moduli `m : ℕ`: a finite set of primes with an exponent attached to each.  The
Lang-era reciprocity machinery in `Submission/NK/` is pinned to `ℕ`-moduli and can therefore never
see a modulus with support exactly the ramified primes (the support of `(m)` is always saturated
above the rational primes).

This module provides the object that the idèlic Artin map of a cycle is built from: the
**congruence subgroup** `Cycle.congrSubgroup c ≤ 𝕀 K` of a cycle `c`, consisting of the idèles
which are `≡ 1` modulo the level of `c` at every prime of `c` and positive at every real place.

The level is *floored at `1`* (`Cycle.level`), so that `Cycle.congrSubgroup c` is a subgroup for
every cycle; for a cycle whose levels are already `≥ 1` (as are the levels of a conductor) the
congruence condition is the intended `v(x_𝔭 - 1) ≥ lev 𝔭`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.Arl
open NK.GlobalCFT

namespace Cycle

variable {K : Type*} [Field K] [NumberField K]

/-- **The level of a cycle at a prime, as an element of the value group.**  The exponent `c.lev 𝔭`
is floored at `1` so that the congruence subgroup is a subgroup for every cycle; for levels `≥ 1`
this is `exp (-(lev 𝔭))`. -/
noncomputable def level (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    WithZero (Multiplicative ℤ) :=
  WithZero.exp (-(((max 1 (c.lev 𝔭) : ℕ) : ℤ)))

lemma level_le_one (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K)) : c.level 𝔭 ≤ 1 := by
  rw [level, ← WithZero.exp_zero, WithZero.exp_le_exp]
  have : (0 : ℤ) ≤ ((max 1 (c.lev 𝔭) : ℕ) : ℤ) := by positivity
  linarith

lemma level_lt_one (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K)) : c.level 𝔭 < 1 := by
  rw [level, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have h : 0 < max 1 (c.lev 𝔭) := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have : (0 : ℤ) < ((max 1 (c.lev 𝔭) : ℕ) : ℤ) := by exact_mod_cast h
  linarith

lemma level_le_level_iff {c : Cycle K} {𝔭 : HeightOneSpectrum (𝓞 K)} (h : 1 ≤ c.lev 𝔭) :
    c.level 𝔭 = WithZero.exp (-((c.lev 𝔭 : ℕ) : ℤ)) := by
  rw [level, max_eq_right h]

/-- **The local congruence condition of a cycle at a finite place.** -/
def CongrAt (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K)) (y : (𝔭.adicCompletion K)ˣ) : Prop :=
  Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((y : 𝔭.adicCompletion K) - 1) ≤ c.level 𝔭

lemma congrAt_iff (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K)) (y : (𝔭.adicCompletion K)ˣ) :
    c.CongrAt 𝔭 y ↔ Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((y : 𝔭.adicCompletion K) - 1) ≤ c.level 𝔭 := Iff.rfl

lemma congrAt_one (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K)) : c.CongrAt 𝔭 1 := by
  unfold CongrAt
  rw [Units.val_one, sub_self, map_zero]
  exact zero_le

lemma congrAt_mul (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K)) {y z : (𝔭.adicCompletion K)ˣ}
    (hy : c.CongrAt 𝔭 y) (hz : c.CongrAt 𝔭 z) : c.CongrAt 𝔭 (y * z) := by
  unfold CongrAt at *
  have hL1 : c.level 𝔭 ≤ 1 := level_le_one c 𝔭
  have hLL : c.level 𝔭 * c.level 𝔭 ≤ c.level 𝔭 := by
    calc c.level 𝔭 * c.level 𝔭 ≤ c.level 𝔭 * 1 :=
          mul_le_mul_of_nonneg_left hL1 zero_le
      _ = c.level 𝔭 := mul_one _
  have hcross : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((y : 𝔭.adicCompletion K) - 1)
      * Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((z : 𝔭.adicCompletion K) - 1) ≤ c.level 𝔭 :=
    le_trans (mul_le_mul' hy hz) hLL
  have hdec : (((y * z : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) - 1)
      = ((y : 𝔭.adicCompletion K) - 1) + ((z : 𝔭.adicCompletion K) - 1)
        + ((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1) := by
    rw [Units.val_mul]; ring
  have hC : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1)) ≤ c.level 𝔭 := by
    rw [Valuation.map_mul]; exact hcross
  rw [hdec]
  calc Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((y : 𝔭.adicCompletion K) - 1) + ((z : 𝔭.adicCompletion K) - 1)
          + ((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1))
      ≤ max (Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((y : 𝔭.adicCompletion K) - 1) + ((z : 𝔭.adicCompletion K) - 1)))
          (Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1))) :=
        Valuation.map_add_le_max' _ _ _
    _ ≤ max (max (Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              ((y : 𝔭.adicCompletion K) - 1))
            (Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              ((z : 𝔭.adicCompletion K) - 1)))
          (Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1))) :=
        max_le_max (Valuation.map_add_le_max' _ _ _) le_rfl
    _ ≤ c.level 𝔭 := max_le (max_le hy hz) hC

lemma congrAt_inv (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K)) {y : (𝔭.adicCompletion K)ˣ}
    (hy : c.CongrAt 𝔭 y) : c.CongrAt 𝔭 y⁻¹ := by
  unfold CongrAt at *
  have hlt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((y : 𝔭.adicCompletion K) - 1) < 1 := lt_of_le_of_lt hy (level_lt_one c 𝔭)
  have hyv : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((y : 𝔭.adicCompletion K)) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left (v := Valued.v (R := 𝔭.adicCompletion K))
      (x := (1 : 𝔭.adicCompletion K)) (y := (y : 𝔭.adicCompletion K) - 1) (by simpa using hlt)
    simpa using h
  have hval : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((y⁻¹ : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) - 1)
      = Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((y : 𝔭.adicCompletion K) - 1) := by
    have hdecode : (((y⁻¹ : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) - 1)
        = ((y : 𝔭.adicCompletion K) - 1) * (-((y : 𝔭.adicCompletion K)⁻¹)) := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [hdecode, Valuation.map_mul, Valuation.map_neg, Valuation.map_inv, hyv, inv_one, mul_one]
  rw [hval]; exact hy

/-! ## The congruence subgroup of a cycle -/

/-- **The congruence subgroup of a cycle**: idèles which are `≡ 1` modulo the level of `c` at
every prime of `c` and positive at every real place. -/
def congrSubgroup (c : Cycle K) : Subgroup (Idele K) where
  carrier := {x | (∀ 𝔭 ∈ c.supp, c.CongrAt 𝔭 (x (Place.ofFinite 𝔭)))
    ∧ (∀ w : InfinitePlace K, NK.CFTLib.Arl.PosAtReal w (x (Place.ofInfinite w)))}
  one_mem' := ⟨fun 𝔭 _ => congrAt_one c 𝔭, fun w => NK.CFTLib.Arl.posAtReal_one w⟩
  mul_mem' := fun hx hy => ⟨fun 𝔭 h𝔭 => by
      rw [Idele.mul_apply]
      exact congrAt_mul c 𝔭 (hx.1 𝔭 h𝔭) (hy.1 𝔭 h𝔭),
    fun w => by
      rw [Idele.mul_apply]
      exact NK.CFTLib.Arl.posAtReal_mul (hx.2 w) (hy.2 w)⟩
  inv_mem' := fun hx => ⟨fun 𝔭 h𝔭 => by
      rw [Idele.inv_apply]
      exact congrAt_inv c 𝔭 (hx.1 𝔭 h𝔭),
    fun w => by
      rw [Idele.inv_apply]
      exact NK.CFTLib.Arl.posAtReal_inv (hx.2 w)⟩

@[simp] theorem mem_congrSubgroup_iff (c : Cycle K) (x : Idele K) :
    x ∈ c.congrSubgroup ↔ (∀ 𝔭 ∈ c.supp, c.CongrAt 𝔭 (x (Place.ofFinite 𝔭)))
      ∧ (∀ w : InfinitePlace K, NK.CFTLib.Arl.PosAtReal w (x (Place.ofInfinite w))) :=
  Iff.rfl

/-- **The idèle of a prime outside the cycle lies in the congruence subgroup.**  This is the
property of a cycle (as opposed to a natural-number modulus) that makes the Frobenius
normalisation of the idèlic Artin map available at *every* unramified prime. -/
theorem ideleOfPrime_mem_congrSubgroup (c : Cycle K) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : 𝔭 ∉ c.supp) : NK.HeckeL.ideleOfPrime K 𝔭 ∈ c.congrSubgroup := by
  classical
  rw [mem_congrSubgroup_iff]
  constructor
  · intro 𝔮 h𝔮
    rw [congrAt_iff]
    have hne : 𝔮 ≠ 𝔭 := fun h => h𝔭 (h ▸ h𝔮)
    have hunit : (NK.HeckeL.ideleOfPrime K 𝔭) (Place.ofFinite 𝔮) = 1 := by
      show NK.GlobalCFT.IdeleClassGroup.unifUnit K 𝔮 ^ (if 𝔮 = 𝔭 then (1 : ℤ) else 0) = 1
      rw [if_neg hne, zpow_zero]
    have hval : ((NK.HeckeL.ideleOfPrime K 𝔭 (Place.ofFinite 𝔮) :
        (𝔮.adicCompletion K)ˣ) : 𝔮.adicCompletion K) = 1 := by
      rw [hunit]; rfl
    rw [hval, sub_self, map_zero]
    exact zero_le
  · intro w hw
    have h1 : ((NK.HeckeL.ideleOfPrime K 𝔭 (Place.ofInfinite w) : (w.Completion)ˣ) :
        w.Completion) = 1 := rfl
    rw [h1, map_one]
    exact zero_lt_one

/-- **The principal idèles of the congruence subgroup of a cycle** are exactly the elements whose
underlying unit satisfies `Cycle.CongrOne`, in the case (the one that occurs for a conductor) where
the levels of the cycle are `≥ 1` on its support. -/
theorem principalIdele_mem_congrSubgroup_iff {c : Cycle K} (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (a : Kˣ) : Idele.principalIdele K a ∈ c.congrSubgroup ↔ c.CongrOne a := by
  rw [mem_congrSubgroup_iff]
  constructor
  · intro h
    refine ⟨fun 𝔭 h𝔭 => ?_, fun w hw => ?_⟩
    · have h1 := h.1 𝔭 h𝔭
      rw [congrAt_iff, level_le_level_iff (K := K) (c := c) (hlev 𝔭 h𝔭)] at h1
      simpa [Idele.principalIdele_apply, Units.coe_map] using h1
    · have h2 := h.2 w
      simpa [NK.CFTLib.Arl.PosAtReal, Idele.principalIdele_apply, Units.coe_map] using h2 hw
  · intro h
    refine ⟨fun 𝔭 h𝔭 => ?_, fun w => ?_⟩
    · rw [congrAt_iff, level_le_level_iff (K := K) (c := c) (hlev 𝔭 h𝔭)]
      simpa [Idele.principalIdele_apply, Units.coe_map] using h.1 𝔭 h𝔭
    · simpa [NK.CFTLib.Arl.PosAtReal, Idele.principalIdele_apply, Units.coe_map]
        using h.2 w

/-- **The congruence subgroup of an auxiliary natural-number modulus is contained in that of a
cycle.**  If every prime of the cycle divides `(m)` with the level of `m` at least the level of the
cycle, then `U(m) ≤ U(c)`.  This is what makes the idèlic input of the Artin map of a cycle
(the adjustment and the norm condition) available from the `ℕ`-modulus machinery. -/
theorem congrSubgroup_le_of_natCast_le {c : Cycle K} {m : ℕ} (hm : 0 < m)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (hsupp : ∀ 𝔭 ∈ c.supp, (m : 𝓞 K) ∈ 𝔭.asIdeal)
    (hcmp : ∀ 𝔭 ∈ c.supp, c.lev 𝔭 ≤ cycleLevel (K := K) m 𝔭) :
    NK.CFTLib.Arl.congruenceSubgroup K m ≤ c.congrSubgroup := by
  intro x hx
  rw [mem_congrSubgroup_iff]
  refine ⟨fun 𝔭 h𝔭 => ?_, hx.2⟩
  rw [congrAt_iff]
  have hxat := hx.1 𝔭 (hsupp 𝔭 h𝔭)
  have h1 : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) - 1)
      ≤ Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : 𝔭.adicCompletion K)) := hxat
  have h2 : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : 𝔭.adicCompletion K)) ≤ c.level 𝔭 := by
    rw [valued_natCast_eq_exp_cycleLevel (K := K) m hm 𝔭, level,
      max_eq_right (hlev 𝔭 h𝔭), WithZero.exp_le_exp]
    have h : ((c.lev 𝔭 : ℕ) : ℤ) ≤ ((cycleLevel (K := K) m 𝔭 : ℕ) : ℤ) := by
      exact_mod_cast hcmp 𝔭 h𝔭
    linarith
  exact le_trans h1 h2

/-- **The congruence subgroup of a natural-number modulus whose valuation is dominated by the level
lies in the congruence subgroup of the cycle.**  This form of the containment avoids the
`Work.SSGRoute.ZDataMup.cycleLevel` bookkeeping: it suffices to know that the `𝔭`-adic value of `m`
is at most the level of the cycle at each prime of the cycle. -/
theorem congrSubgroup_le_of_val {c : Cycle K} {m : ℕ} (hm : 0 < m)
    (hval : ∀ 𝔭 ∈ c.supp, Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((m : ℕ) : 𝔭.adicCompletion K)) ≤ c.level 𝔭) :
    NK.CFTLib.Arl.congruenceSubgroup K m ≤ c.congrSubgroup := by
  intro x hx
  rw [mem_congrSubgroup_iff]
  refine ⟨fun 𝔭 h𝔭 => ?_, hx.2⟩
  have hlt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((m : ℕ) : 𝔭.adicCompletion K)) < 1 := lt_of_le_of_lt (hval 𝔭 h𝔭) (level_lt_one c 𝔭)
  have hmem : (m : 𝓞 K) ∈ 𝔭.asIdeal := by
    have h1 : ((m : ℕ) : 𝔭.adicCompletion K) = algebraMap K (𝔭.adicCompletion K) ((m : ℕ) : K) :=
      (map_natCast _ m).symm
    rw [h1] at hlt
    rw [Commons.NumberTheory.NumberField.Completion.valued_alg_eq] at hlt
    have h2 : ((m : ℕ) : K) = algebraMap (𝓞 K) K ((m : ℕ) : 𝓞 K) := (map_natCast _ m).symm
    rw [h2] at hlt
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭 (m : 𝓞 K)).mp hlt
  have hxat : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) - 1)
      ≤ Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : 𝔭.adicCompletion K)) := hx.1 𝔭 hmem
  rw [congrAt_iff]
  exact le_trans hxat (hval 𝔭 h𝔭)


end Cycle
end Work.SSGRoute.ZDataMup
