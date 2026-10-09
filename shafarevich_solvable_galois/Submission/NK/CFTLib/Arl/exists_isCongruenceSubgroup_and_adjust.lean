import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.UchidaKummer.Approximation.isWeakApproximation
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
import Submission.NK.CFTLib.Arl.exists_integral_sign_adjust
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The congruence subgroup of a modulus, and the adjustment of an idèle

For a number field `K` and `0 < m`, the congruence subgroup `U ≤ 𝕀 K` of modulus `m` is the
subgroup of idèles which are `≡ 1 mod m` at the finite places `𝔭` with `m ∈ 𝔭` and positive at
every real place.  This file shows that this predicate determines a genuine subgroup
(`congruenceSubgroup`) and that it meets every class of the idèle class group:
`𝕀 K = U · Kˣ`, i.e. every idèle can be adjusted by a principal idèle into `U`.

The two ingredients are:

* the **congruence adjustment** (`exists_adjust_congruence`): weak approximation for `K` at the
  finitely many finite places with `m ∈ 𝔭` (the CRT step of
  `NK.UchidaKummer.Approximation.exists_valuation_sub_lt_exp` together with the single-place
  density `Commons.NumberTheory.NumberField.Completion.exists_algebraMap_mem_exp_ball`);
* the **sign adjustment** (`NK.CFTLib.Arl.exists_integral_sign_adjust`): with an integral `u`,
  the element `1 + m·u` is `≡ 1 mod m` at all the relevant primes, and the archimedean
  approximation of `K` in `∏_w K_w` makes its real values have any prescribed signs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

open NK.GlobalCFT

variable {K : Type*} [Field K] [NumberField K]

/-! ## Local lemmas at a finite place -/

lemma val_natCast_le_one (𝔭 : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) ≤ 1 := by
  have hcast : ((m : ℕ) : 𝔭.adicCompletion K)
      = algebraMap K (𝔭.adicCompletion K) ((m : ℕ) : K) := (map_natCast _ m).symm
  rw [hcast, Commons.NumberTheory.NumberField.Completion.valued_alg_eq]
  have hcast2 : ((m : ℕ) : K) = algebraMap (𝓞 K) K ((m : ℕ) : 𝓞 K) := (map_natCast _ m).symm
  rw [hcast2, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one 𝔭 _

lemma val_natCast_lt_one (𝔭 : HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (hmem : (m : 𝓞 K) ∈ 𝔭.asIdeal) :
    Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) < 1 := by
  have hcast : ((m : ℕ) : 𝔭.adicCompletion K)
      = algebraMap K (𝔭.adicCompletion K) ((m : ℕ) : K) := (map_natCast _ m).symm
  rw [hcast, Commons.NumberTheory.NumberField.Completion.valued_alg_eq]
  have hcast2 : ((m : ℕ) : K) = algebraMap (𝓞 K) K ((m : ℕ) : 𝓞 K) := (map_natCast _ m).symm
  rw [hcast2]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭 (m : 𝓞 K)).mpr hmem

lemma val_algebraMap_units_le_one (𝔭 : HeightOneSpectrum (𝓞 K)) (u : 𝓞 K) :
    Valued.v (algebraMap K (𝔭.adicCompletion K) ((u : 𝓞 K) : K)) ≤ 1 := by
  rw [Commons.NumberTheory.NumberField.Completion.valued_alg_eq,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one 𝔭 u

/-- The local congruence condition `y ≡ 1 mod m` at a finite place. -/
def CongrAt (𝔭 : HeightOneSpectrum (𝓞 K)) (m : ℕ) (y : (𝔭.adicCompletion K)ˣ) : Prop :=
  Valued.v ((y : 𝔭.adicCompletion K) - 1) ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K))

lemma congrAt_one (𝔭 : HeightOneSpectrum (𝓞 K)) (m : ℕ) : CongrAt 𝔭 m 1 := by
  unfold CongrAt
  rw [Units.val_one, sub_self, map_zero]
  exact zero_le

lemma congrAt_mul (𝔭 : HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (hmem : (m : 𝓞 K) ∈ 𝔭.asIdeal) {y z : (𝔭.adicCompletion K)ˣ}
    (hy : CongrAt 𝔭 m y) (hz : CongrAt 𝔭 m z) : CongrAt 𝔭 m (y * z) := by
  unfold CongrAt at *
  have hm1 : Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) ≤ 1 := val_natCast_le_one 𝔭 m
  have hm2 : Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) * Valued.v (((m : ℕ) : 𝔭.adicCompletion K))
      ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := by
    calc Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) * Valued.v (((m : ℕ) : 𝔭.adicCompletion K))
        ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) * 1 :=
          mul_le_mul_of_nonneg_left hm1 zero_le
      _ = Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := mul_one _
  have hcross : Valued.v ((y : 𝔭.adicCompletion K) - 1) * Valued.v ((z : 𝔭.adicCompletion K) - 1)
      ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) :=
    le_trans (mul_le_mul' hy hz) hm2
  have hdec : (((y * z : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) - 1)
      = ((y : 𝔭.adicCompletion K) - 1) + ((z : 𝔭.adicCompletion K) - 1)
        + ((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1) := by
    rw [Units.val_mul]; ring
  have hC : Valued.v (((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1))
      ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := by
    rw [Valuation.map_mul]; exact hcross
  rw [hdec]
  calc Valued.v (((y : 𝔭.adicCompletion K) - 1) + ((z : 𝔭.adicCompletion K) - 1)
        + ((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1))
      ≤ max (Valued.v (((y : 𝔭.adicCompletion K) - 1) + ((z : 𝔭.adicCompletion K) - 1)))
          (Valued.v (((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1))) :=
        Valuation.map_add_le_max' _ _ _
    _ ≤ max (max (Valued.v ((y : 𝔭.adicCompletion K) - 1))
          (Valued.v ((z : 𝔭.adicCompletion K) - 1)))
          (Valued.v (((y : 𝔭.adicCompletion K) - 1) * ((z : 𝔭.adicCompletion K) - 1))) :=
        max_le_max (Valuation.map_add_le_max' _ _ _) le_rfl
    _ ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := max_le (max_le hy hz) hC

lemma congrAt_inv (𝔭 : HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (hmem : (m : 𝓞 K) ∈ 𝔭.asIdeal) {y : (𝔭.adicCompletion K)ˣ}
    (hy : CongrAt 𝔭 m y) : CongrAt 𝔭 m y⁻¹ := by
  unfold CongrAt at *
  have hlt : Valued.v ((y : 𝔭.adicCompletion K) - 1) < 1 :=
    lt_of_le_of_lt hy (val_natCast_lt_one 𝔭 m hmem)
  have hyv : Valued.v ((y : 𝔭.adicCompletion K)) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left (v := Valued.v)
      (x := (1 : 𝔭.adicCompletion K)) (y := (y : 𝔭.adicCompletion K) - 1) (by simpa using hlt)
    simpa using h
  have hval : Valued.v (((y⁻¹ : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) - 1)
      = Valued.v ((y : 𝔭.adicCompletion K) - 1) := by
    have hdecode : (((y⁻¹ : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) - 1)
        = ((y : 𝔭.adicCompletion K) - 1) * (-((y : 𝔭.adicCompletion K)⁻¹)) := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [hdecode, Valuation.map_mul, Valuation.map_neg, Valuation.map_inv, hyv, inv_one, mul_one]
  rw [hval]; exact hy

lemma congrAt_unitsMap_add_one (𝔭 : HeightOneSpectrum (𝓞 K)) (m : ℕ) (u : 𝓞 K)
    (h : ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) ≠ 0) :
    CongrAt 𝔭 m (Units.map (algebraMap K (𝔭.adicCompletion K) : K →* (𝔭.adicCompletion K))
      (Units.mk0 ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) h)) := by
  unfold CongrAt
  rw [Units.coe_map, Units.val_mk0]
  change Valued.v (algebraMap K (𝔭.adicCompletion K) ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) - 1)
    ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K))
  have hdec : algebraMap K (𝔭.adicCompletion K) ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) - 1
      = ((m : ℕ) : 𝔭.adicCompletion K) * algebraMap K (𝔭.adicCompletion K) ((u : 𝓞 K) : K) := by
    rw [map_add, map_mul, map_one, map_natCast]
    ring
  rw [hdec, map_mul]
  calc Valued.v (((m : ℕ) : 𝔭.adicCompletion K))
        * Valued.v (algebraMap K (𝔭.adicCompletion K) ((u : 𝓞 K) : K))
      ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) * 1 :=
        mul_le_mul_of_nonneg_left (val_algebraMap_units_le_one 𝔭 u) zero_le
    _ = Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := mul_one _

/-! ## Positivity at the infinite places -/

lemma posAtReal_one (w : InfinitePlace K) : PosAtReal w (1 : (w.Completion)ˣ) := by
  intro hw
  rw [Units.val_one, map_one]
  norm_num

lemma posAtReal_mul {w : InfinitePlace K} {y z : (w.Completion)ˣ}
    (hy : PosAtReal w y) (hz : PosAtReal w z) : PosAtReal w (y * z) := by
  intro hw
  rw [Units.val_mul, map_mul]
  exact mul_pos (hy hw) (hz hw)

lemma posAtReal_inv {w : InfinitePlace K} {y : (w.Completion)ˣ}
    (hy : PosAtReal w y) : PosAtReal w y⁻¹ := by
  intro hw
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  exact inv_pos.mpr (hy hw)

/-! ## The congruence subgroup -/

/-- The congruence subgroup of the modulus `m`: the idèles congruent to `1` modulo `m` at the
finite places dividing `m` and positive at every real place. -/
def congruenceSubgroup (K : Type*) [Field K] [NumberField K] (m : ℕ) : Subgroup (Idele K) where
  carrier := {x | (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      Valued.v (((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1)
        ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)))
    ∧ (∀ w : InfinitePlace K, PosAtReal w (x (Place.ofInfinite w)))}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro 𝔭 _
      exact congrAt_one 𝔭 m
    · intro w
      rw [Idele.one_apply]
      exact posAtReal_one w
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_⟩
    · intro 𝔭 h𝔭
      rw [Idele.mul_apply]
      exact congrAt_mul 𝔭 m h𝔭 (hx.1 𝔭 h𝔭) (hy.1 𝔭 h𝔭)
    · intro w
      rw [Idele.mul_apply]
      exact posAtReal_mul (hx.2 w) (hy.2 w)
  inv_mem' := by
    intro x hx
    refine ⟨?_, ?_⟩
    · intro 𝔭 h𝔭
      rw [Idele.inv_apply]
      exact congrAt_inv 𝔭 m h𝔭 (hx.1 𝔭 h𝔭)
    · intro w
      rw [Idele.inv_apply]
      exact posAtReal_inv (hx.2 w)

/-! ## The congruence adjustment -/

/-- **Congruence adjustment.**  For `0 < m` and an idèle `x` there is `b : Kˣ` with `x_𝔭 · b ≡ 1`
modulo `m` at every finite place `𝔭` with `m ∈ 𝔭`. -/
theorem exists_adjust_congruence (K : Type*) [Field K] [NumberField K] (m : ℕ) (hm : 0 < m)
    (x : Idele K) :
    ∃ b : K, b ≠ 0 ∧ ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      Valued.v (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K)
          * algebraMap K (𝔭.adicCompletion K) b - 1)
        ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := by
  classical
  by_cases hS : ∃ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal
  · obtain ⟨𝔭₀, h𝔭₀⟩ := hS
    have hm0 : ((m : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
    have hfin : {𝔭 : HeightOneSpectrum (𝓞 K) | (m : 𝓞 K) ∈ 𝔭.asIdeal}.Finite := by
      refine (Ideal.finite_factors (R := 𝓞 K) (I := Ideal.span {((m : ℕ) : 𝓞 K)}) ?_).subset ?_
      · exact fun h => hm0 (Ideal.span_singleton_eq_bot.mp h)
      · intro 𝔭 h𝔭
        simp only [Set.mem_ofPred_eq] at h𝔭 ⊢
        rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
        exact h𝔭
    let S : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset
    have hSmem : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∈ S ↔ (m : 𝓞 K) ∈ 𝔭.asIdeal :=
      fun 𝔭 => Set.Finite.mem_toFinset hfin
    let am : S → ℤ := fun 𝔮 => WithZero.log (Valued.v (((m : ℕ) : 𝔮.1.adicCompletion K)))
    let bx : S → ℤ := fun 𝔮 => WithZero.log
      (Valued.v (((x (Place.ofFinite 𝔮.1) : (𝔮.1.adicCompletion K)ˣ) : 𝔮.1.adicCompletion K)))
    let lev : S → ℤ := fun 𝔮 => am 𝔮 - bx 𝔮 - 1
    have hm_ne : ∀ 𝔮 : S, Valued.v (((m : ℕ) : 𝔮.1.adicCompletion K)) ≠ 0 := by
      intro 𝔮
      haveI := Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔮.1
      exact (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm))
    have hx_ne : ∀ 𝔮 : S, Valued.v
        (((x (Place.ofFinite 𝔮.1) : (𝔮.1.adicCompletion K)ˣ) : 𝔮.1.adicCompletion K)) ≠ 0 := by
      intro 𝔮
      exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
    have hexp_am : ∀ 𝔮 : S,
        WithZero.exp (am 𝔮) = Valued.v (((m : ℕ) : 𝔮.1.adicCompletion K)) :=
      fun 𝔮 => WithZero.exp_log (hm_ne 𝔮)
    have hexp_bx : ∀ 𝔮 : S, WithZero.exp (bx 𝔮) = Valued.v
        (((x (Place.ofFinite 𝔮.1) : (𝔮.1.adicCompletion K)ˣ) : 𝔮.1.adicCompletion K)) :=
      fun 𝔮 => WithZero.exp_log (hx_ne 𝔮)
    choose c hc using fun 𝔮 : S =>
      Commons.NumberTheory.NumberField.Completion.exists_algebraMap_mem_exp_ball 𝔮.1
        (((x (Place.ofFinite 𝔮.1) : (𝔮.1.adicCompletion K)ˣ) : 𝔮.1.adicCompletion K))⁻¹ (lev 𝔮)
    have hind : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
        HeightOneSpectrum.valuationSubringAtPrime K p ⊔
          HeightOneSpectrum.valuationSubringAtPrime K q = ⊤ :=
      fun p _ q _ hpq => NK.UchidaKummer.Approximation.sup_valuationSubringAtPrime_eq_top p q hpq
    obtain ⟨t, ht⟩ := NK.UchidaKummer.Approximation.exists_valuation_sub_lt_exp S hind c lev
    have hkey : ∀ 𝔮 : S,
        Valued.v (((x (Place.ofFinite 𝔮.1) : (𝔮.1.adicCompletion K)ˣ) : 𝔮.1.adicCompletion K))
            * WithZero.exp (lev 𝔮)
          = Valued.v (((m : ℕ) : 𝔮.1.adicCompletion K)) * WithZero.exp (-1) := by
      intro 𝔮
      have hsum : bx 𝔮 + lev 𝔮 = am 𝔮 + (-1) := by
        simp only [lev]
        ring
      calc Valued.v (((x (Place.ofFinite 𝔮.1) : (𝔮.1.adicCompletion K)ˣ) :
              𝔮.1.adicCompletion K)) * WithZero.exp (lev 𝔮)
          = WithZero.exp (bx 𝔮) * WithZero.exp (lev 𝔮) := by rw [hexp_bx 𝔮]
        _ = WithZero.exp (bx 𝔮 + lev 𝔮) := (WithZero.exp_add _ _).symm
        _ = WithZero.exp (am 𝔮 + (-1)) := by rw [hsum]
        _ = WithZero.exp (am 𝔮) * WithZero.exp (-1) := WithZero.exp_add _ _
        _ = Valued.v (((m : ℕ) : 𝔮.1.adicCompletion K)) * WithZero.exp (-1) := by rw [hexp_am 𝔮]
    have hineq : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
        Valued.v (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K)
            * algebraMap K (𝔭.adicCompletion K) t - 1)
          < Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := by
      intro 𝔭 h𝔭
      have h𝔭S : 𝔭 ∈ S := (hSmem 𝔭).mpr h𝔭
      set 𝔮 : S := ⟨𝔭, h𝔭S⟩ with h𝔮
      have hct : 𝔭.valuation K (t - c 𝔮) < WithZero.exp (lev 𝔮) := ht 𝔮
      have hcp : Valued.v (algebraMap K (𝔭.adicCompletion K) (c 𝔮)
          - (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))⁻¹)
          < WithZero.exp (lev 𝔮) := hc 𝔮
      have hclose : Valued.v (algebraMap K (𝔭.adicCompletion K) t
          - (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))⁻¹)
          < WithZero.exp (lev 𝔮) := by
        have h1 : Valued.v (algebraMap K (𝔭.adicCompletion K) t
            - algebraMap K (𝔭.adicCompletion K) (c 𝔮)) < WithZero.exp (lev 𝔮) := by
          rw [← map_sub, Commons.NumberTheory.NumberField.Completion.valued_alg_eq]
          exact hct
        rw [show algebraMap K (𝔭.adicCompletion K) t
            - (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))⁻¹
            = (algebraMap K (𝔭.adicCompletion K) t - algebraMap K (𝔭.adicCompletion K) (c 𝔮))
              + (algebraMap K (𝔭.adicCompletion K) (c 𝔮)
                - (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))⁻¹)
            from by ring]
        exact lt_of_le_of_lt (Commons.NumberTheory.NumberField.Completion.val_add_le_max 𝔭 _ _)
          (max_lt h1 hcp)
      have hfac : (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K)
            * algebraMap K (𝔭.adicCompletion K) t - 1)
          = (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))
            * (algebraMap K (𝔭.adicCompletion K) t
              - (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))⁻¹) := by
        rw [mul_sub, mul_inv_cancel₀ (Units.ne_zero _)]
      rw [hfac, Valuation.map_mul]
      calc Valued.v (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))
            * Valued.v (algebraMap K (𝔭.adicCompletion K) t
              - (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))⁻¹)
          < Valued.v (((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K))
            * WithZero.exp (lev 𝔮) :=
              mul_lt_mul_of_pos_left hclose ((Valuation.pos_iff _).mpr (Units.ne_zero _))
        _ = Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) * WithZero.exp (-1) := hkey 𝔮
        _ < Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := by
            haveI := Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
            have hpos : (0 : ℤᵐ⁰) < Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) :=
              (Valuation.pos_iff _).mpr (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm))
            have hone : WithZero.exp (-1) < (1 : ℤᵐ⁰) := by
              rw [← WithZero.exp_zero]
              exact WithZero.exp_lt_exp.mpr (by norm_num)
            calc Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) * WithZero.exp (-1)
                < Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) * 1 :=
                  mul_lt_mul_of_pos_left hone hpos
              _ = Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := mul_one _
    refine ⟨t, ?_, fun 𝔭 h𝔭 => le_of_lt (hineq 𝔭 h𝔭)⟩
    intro h0
    have h := hineq 𝔭₀ h𝔭₀
    rw [h0, map_zero, mul_zero, zero_sub, Valuation.map_neg, Valuation.map_one] at h
    exact absurd h (not_lt.mpr (val_natCast_le_one 𝔭₀ m))
  · refine ⟨1, one_ne_zero, fun 𝔭 h𝔭 => absurd ⟨𝔭, h𝔭⟩ hS⟩

/-! ## The main theorem -/

theorem exists_isCongruenceSubgroup_and_adjust (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (hm : 0 < m) :
    ∃ U : Subgroup (NK.GlobalCFT.Idele K),
      NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U ∧
      ∀ x : NK.GlobalCFT.Idele K,
        ∃ b : Kˣ, x * NK.GlobalCFT.Idele.principalIdele K b ∈ U := by
  classical
  refine ⟨congruenceSubgroup K m, ⟨?_, ?_⟩, ?_⟩
  · intro x
    exact Iff.rfl
  · intro b
    constructor
    · intro h
      exact h
    · intro h
      exact h
  · intro x
    obtain ⟨a, ha, haval⟩ := exists_adjust_congruence K m hm x
    let a' : Kˣ := Units.mk0 a ha
    let R : Idele K := x * Idele.principalIdele K a'
    have hRcong : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
        CongrAt 𝔭 m (R (Place.ofFinite 𝔭)) := by
      intro 𝔭 h𝔭
      have h1 : (R (Place.ofFinite 𝔭) : 𝔭.adicCompletion K)
          = ((x (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K)
            * algebraMap K (𝔭.adicCompletion K) a := by
        simp only [R, a', Idele.mul_apply, Units.val_mul, Idele.principalIdele_apply, Units.coe_map,
          Units.val_mk0]
        rfl
      show Valued.v ((R (Place.ofFinite 𝔭) : 𝔭.adicCompletion K) - 1)
        ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K))
      rw [h1]
      exact haval 𝔭 h𝔭
    by_cases hreal : ∃ w : InfinitePlace K, w.IsReal
    · obtain ⟨w₀, hw₀⟩ := hreal
      let r : InfinitePlace K → ℝ := fun w => if h : w.IsReal then
          (InfinitePlace.Completion.ringEquivRealOfIsReal h)
            ((R (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) else 1
      have hr : ∀ w : InfinitePlace K, w.IsReal → r w ≠ 0 := by
        intro w hw
        have hval : r w = (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            ((R (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) := dif_pos hw
        rw [hval]
        intro h0
        have h1 : ((R (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) = 0 :=
          (InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective
            (by rw [h0]; exact (map_zero _).symm)
        exact (Units.ne_zero (R (Place.ofInfinite w))) h1
      obtain ⟨u, hu⟩ := exists_integral_sign_adjust K m hm r hr
      have hne : ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) ≠ 0 := by
        intro h0
        have h := hu w₀ hw₀
        rw [h0] at h
        simp only [map_zero, mul_zero] at h
        exact absurd h (lt_irrefl 0)
      refine ⟨a' * Units.mk0 ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) hne, ?_⟩
      refine ⟨?_, ?_⟩
      · intro 𝔭 h𝔭
        have hb : ((x * Idele.principalIdele K (a' * Units.mk0 ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) hne))
              (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ)
            = R (Place.ofFinite 𝔭) * Units.map
                (algebraMap K (𝔭.adicCompletion K) : K →* (𝔭.adicCompletion K))
                (Units.mk0 ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) hne) := by
          simp only [R, a', Idele.mul_apply, Idele.principalIdele_apply, map_mul, mul_assoc]
        rw [hb]
        exact congrAt_mul 𝔭 m h𝔭 (hRcong 𝔭 h𝔭) (congrAt_unitsMap_add_one 𝔭 m u hne)
      · intro w
        by_cases hw : w.IsReal
        · intro hw'
          rw [show (InfinitePlace.Completion.ringEquivRealOfIsReal hw') =
            (InfinitePlace.Completion.ringEquivRealOfIsReal hw) from
              congrArg _ (Subsingleton.elim hw' hw)]
          have hb : ((x * Idele.principalIdele K (a' * Units.mk0 ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) hne))
                (Place.ofInfinite w) : (w.Completion)ˣ)
              = R (Place.ofInfinite w) * Units.map
                  (algebraMap K (w.Completion) : K →* (w.Completion))
                  (Units.mk0 ((1 : K) + (m : K) * ((u : 𝓞 K) : K)) hne) := by
            simp only [R, a', Idele.mul_apply, Idele.principalIdele_apply, map_mul, mul_assoc]
          rw [hb, Units.val_mul, map_mul, Units.coe_map, Units.val_mk0]
          have h1 : (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              ((R (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) = r w := by
            simp only [r]
            rw [dif_pos hw]
          rw [h1]
          exact hu w hw
        · exact fun hw' => absurd hw' hw
    · refine ⟨a', ?_⟩
      refine ⟨?_, ?_⟩
      · intro 𝔭 h𝔭
        exact hRcong 𝔭 h𝔭
      · intro w
        exact fun hw' => absurd ⟨w, hw'⟩ hreal

end NK.CFTLib.Arl
