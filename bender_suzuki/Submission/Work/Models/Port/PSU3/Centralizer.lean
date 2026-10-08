/-
**The centralizer of an involution of `SU(3, 2ⁿ)` is not a `2`-group.**

The unipotent radical `U ≤ SU(3, 2ⁿ)` is a special `2`-group of order `q³` (`q = 2ⁿ`), and the
involutions of `U` are exactly the elements `u(0, c)` with `c` in the fixed field of the
Frobenius `x ↦ x^q` and `c ≠ 0` (`Submission/PSU3/Involutions.lean`).  The Borel subgroup
`B = U ⋊ T` is strongly embedded in `SU(3, 2ⁿ)`, the torus `T ≅ Fˣ` acting on `U` by

  `t(a) · u(b, c) · t(a)⁻¹ = u(a · b · β⁻¹, a^{q+1} · c)`,  `β = a^{q-1}`.

In particular a torus element `t(a)` centralizes the involution `u(0, c)` (`c ≠ 0`) exactly when
`a^{q+1} = 1`.  Writing `T₁ = {a ∈ Fˣ : a^{q+1} = 1}` (a subgroup of `Fˣ` of order `q + 1`), the
general "centralizer in a semidirect product" lemma
`Commons.GroupTheory.Subgroup.centralizer_inf_eq_sup_of_eq_sup_of_le_normalizer_of_central`
gives

  `C_G(u(0, c)) = U · T₁`,  of order `q³ (q + 1)`.

This centralizer is therefore **not** a `2`-group (contrast with `PSL(2, 2ⁿ)` and
`Sz(2^(2n+1))`, where the centralizer of an involution is a Sylow `2`-subgroup) — the standard
`2`-local obstruction separating `PSU(3, q)` from the other two families of the Bender–Suzuki
classification.  (In the projective group `PSU(3, q) = SU(3, q)/Z` with `|Z| = gcd(3, q + 1)`
the centralizer has order `q³ (q + 1)/gcd(3, q + 1)`.)
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Involutions
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.centralizer_le_of_isStronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.centralizer_inf_eq_sup_of_eq_sup_of_le_normalizer_of_central
import Submission.Work.Models.Port.Commons.FieldTheory.Finite.fixed_card_pow_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.PSU3

/-! ## The torus of `SU(3,2^n)` and the subgroup `T₁` -/

/-- The torus `Fˣ → SU(3,2^n)`, `a ↦ diag(a, a^(q-1), a^(-q))`. -/
noncomputable def suTgSU (n : ℕ) : (F n)ˣ →* ↥(SU3 n) where
  toFun a := ⟨suTg n a, suTg_isSU3 n a⟩
  map_one' := Subtype.ext (suTg_one n)
  map_mul' a b := Subtype.ext (suTg_mul n a b).symm

lemma suTgSU_injective (n : ℕ) : Function.Injective (suTgSU n) :=
  fun _ _ h => suTg_injective n (Subtype.ext_iff.mp h)

/-- `T₁ = {a ∈ Fˣ : a^(q+1) = 1}`, the part of the torus centralising the involution `u(0,c)`. -/
noncomputable def suT1 (n : ℕ) : Subgroup (F n)ˣ where
  carrier := {a | a ^ (2 ^ n + 1) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [inv_pow, ha, inv_one]

/-- `T₁` as a subgroup of `SU(3,2^n)`. -/
noncomputable def suTS1 (n : ℕ) : Subgroup (↥(SU3 n)) := (suT1 n).map (suTgSU n)

lemma suTS1_le_suTS (n : ℕ) : suTS1 n ≤ suTS n := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_subgroupOf.mpr ⟨a, rfl⟩

/-! ## The torus action on `U` -/

/-- `suTg n a` commutes with `u(0,c)` exactly when `a^(q+1) = 1`. -/
lemma suTg_mul_suUg_zero_iff (n : ℕ) {c : F n} (hc0 : c ≠ 0) (a : (F n)ˣ) :
    suTg n a * suUg n 0 c = suUg n 0 c * suTg n a ↔ (a : F n) ^ (2 ^ n + 1) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : (a : F n) * c * (a : F n) ^ (2 ^ n) = (a : F n) ^ (2 ^ n + 1) * c := by
    rw [pow_succ']; ring
  constructor
  · intro h
    rw [suTg_mul_suUg, mul_zero, zero_mul, hsq] at h
    have h1 : suUg n 0 ((a : F n) ^ (2 ^ n + 1) * c) = suUg n 0 c := by
      have hh := congrArg (fun z : GL (Fin 3) (F n) => z * (suTg n a)⁻¹) h
      simpa [mul_assoc] using hh
    have h2 : ((0 : F n), (a : F n) ^ (2 ^ n + 1) * c) = ((0 : F n), c) :=
      suUg_injective n h1
    have h3 : (a : F n) ^ (2 ^ n + 1) * c = c := (Prod.ext_iff.mp h2).2
    exact mul_right_cancel₀ hc0 (by rw [h3, one_mul])
  · intro ha
    rw [suTg_mul_suUg, mul_zero, zero_mul, hsq, ha, one_mul]

/-! ## The centralizer of `u(0,c)` -/

/-- **The centralizer of the involution `u(0,c)` of `SU(3,2^n)` is `U · T₁`, where
`T₁ = {a : a^(q+1) = 1}`.** -/
theorem suUS_sup_suTS1_eq_centralizer (n : ℕ) (hn : 1 ≤ n) {c : F n} (hc : c ^ (2 ^ n) = c)
    (hc0 : c ≠ 0) :
    suUS n ⊔ suTS1 n =
      Subgroup.centralizer
        ({⟨suUg n 0 c, suU_le_SU3 n (suUg_zero_mem n c hc)⟩} : Set (↥(SU3 n))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t : ↥(SU3 n) := ⟨suUg n 0 c, suU_le_SU3 n (suUg_zero_mem n c hc)⟩ with htdef
  have htcoe : (t : GL (Fin 3) (F n)) = suUg n 0 c :=
    congrArg (fun z : ↥(SU3 n) => (z : GL (Fin 3) (F n))) htdef
  -- `t` is an involution
  have htU : t ∈ suUS n := Subgroup.mem_subgroupOf.mpr (suUg_zero_mem n c hc)
  have htB : t ∈ suBS n := suUS_le_suBS n htU
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    show (suUg n 0 c) ^ 2 = (1 : GL (Fin 3) (F n))
    rw [pow_two, suUg_mul_self, zero_pow (show 2 ^ n + 1 ≠ 0 by positivity), suUg_zero]
  have ht_ne : t ≠ 1 := by
    intro h
    have h1 : suUg n 0 c = (1 : GL (Fin 3) (F n)) := by
      have := congrArg (fun z : ↥(SU3 n) => (z : GL (Fin 3) (F n))) h
      simpa [htcoe] using this
    have h2 : ((0 : F n), c) = ((0 : F n), (0 : F n)) :=
      suUg_injective n (h1.trans (suUg_zero n).symm)
    exact hc0 (Prod.ext_iff.mp h2).2
  have hord : orderOf t = 2 := (orderOf_eq_prime_iff (p := 2)).mpr ⟨ht2, ht_ne⟩
  -- `t` is central in `U` (every element of `U` commutes with `u(0,c)`)
  have huc : ∀ a ∈ suUS n, a * t = t * a := by
    intro a ha
    obtain ⟨b, c', _, haeq⟩ := Subgroup.mem_subgroupOf.mp ha
    apply Subtype.ext
    show (a : GL (Fin 3) (F n)) * suUg n 0 c = suUg n 0 c * (a : GL (Fin 3) (F n))
    rw [← htcoe, ← htcoe] at *
    rw [haeq, suUg_mul, suUg_mul]
    congr 1 <;> ring
  -- strong embedding gives `C_G(t) ≤ B`
  obtain ⟨hMtop, hMeven, hModd⟩ := suB_stronglyEmbedded n hn
  have hcle : Subgroup.centralizer ({t} : Set (↥(SU3 n))) ≤ suBS n :=
    Commons.GroupTheory.StronglyEmbedded.centralizer_le_of_isStronglyEmbedded (suBS n) hModd htB hord
  -- the general semidirect-product centralizer formula
  have hcentral :=
    Commons.GroupTheory.Subgroup.centralizer_inf_eq_sup_of_eq_sup_of_le_normalizer_of_central
      (suBS n) (suUS n) (suTS n) (suBS_eq_sup n) (suTS_inf_suUS n) (suTS_le_normalizer_suUS n)
      htU huc
  rw [inf_eq_left.mpr hcle] at hcentral
  -- `T ⊓ C_G(t) = T₁`
  have hTinf : suTS n ⊓ Subgroup.centralizer ({t} : Set (↥(SU3 n))) = suTS1 n := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.mp hxT
      have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
      have hsu : suTg n a * suUg n 0 c = suUg n 0 c * suTg n a := by
        have := congrArg (fun z : ↥(SU3 n) => (z : GL (Fin 3) (F n))) hcomm
        simp only [Subgroup.coe_mul] at this
        rwa [ha, htcoe] at this
      have hcond : (a : F n) ^ (2 ^ n + 1) = 1 :=
        (suTg_mul_suUg_zero_iff n hc0 a).mp hsu
      have hmem : a ∈ suT1 n := by
        show a ^ (2 ^ n + 1) = 1
        rw [← Units.val_eq_one, Units.val_pow_eq_pow_val]
        simpa using hcond
      refine Subgroup.mem_map.mpr ⟨a, hmem, ?_⟩
      exact Subtype.ext ha.symm
    · intro x hx
      obtain ⟨a, ha1, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr ⟨a, rfl⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        show suTg n a * suUg n 0 c = suUg n 0 c * suTg n a
        refine (suTg_mul_suUg_zero_iff n hc0 a).mpr ?_
        have ha1' : a ^ (2 ^ n + 1) = 1 := ha1
        rw [← Units.val_pow_eq_pow_val, ha1', Units.val_one]
  rw [hTinf] at hcentral
  exact hcentral.symm

/-- `T₁` has order `q + 1`. -/
theorem card_suT1 (n : ℕ) (hn : 1 ≤ n) : Nat.card ↥(suT1 n) = 2 ^ n + 1 := by
  have h0 : Nat.card ↥(suT1 n) = Nat.card {u : (F n)ˣ // u ^ (2 ^ n + 1) = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun u => Iff.rfl))
  rw [h0, Commons.FieldTheory.Finite.fixedPowTwo.card_units_pow_eq_one_gcd (K := F n) (2 ^ n + 1),
    Nat.card_units, card_F n (by omega)]
  have hdvd : (2 : ℕ) ^ n + 1 ∣ (2 : ℕ) ^ (2 * n) - 1 := by
    refine ⟨2 ^ n - 1, ?_⟩
    have h1 : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (2 * n) = (2 ^ n) * (2 ^ n) := by
      rw [show (2 : ℕ) * n = n + n by ring, pow_add]
    have h3 : (2 ^ n - 1) * (2 ^ n + 1) = (2 ^ n) * (2 ^ n) - 1 := by
      have : (2 ^ n - 1) * (2 ^ n + 1) + 1 = (2 ^ n) * (2 ^ n) := by
        obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le h1
        rw [hb]
        have : 1 + b - 1 = b := by omega
        rw [this]; ring
      exact Nat.eq_sub_of_add_eq this
    rw [mul_comm (2 ^ n + 1) (2 ^ n - 1), h3, h2]
  rw [Nat.gcd_eq_right hdvd]

lemma suUS_inf_suTS1 (n : ℕ) : suUS n ⊓ suTS1 n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  have h3 : x ∈ suUS n ⊓ suTS n := Subgroup.mem_inf.mpr ⟨h1, suTS1_le_suTS n h2⟩
  rw [suTS_inf_suUS n] at h3
  exact h3

lemma suTS1_le_normalizer_suUS (n : ℕ) :
    suTS1 n ≤ Subgroup.normalizer (suUS n : Set (↥(SU3 n))) :=
  (suTS1_le_suTS n).trans (suTS_le_normalizer_suUS n)

/-- **The centralizer of the involution `u(0,c)` of `SU(3,2ⁿ)` has order `q³(q+1)`.** -/
theorem card_centralizer_suUg_zero (n : ℕ) (hn : 1 ≤ n) {c : F n} (hc : c ^ (2 ^ n) = c)
    (hc0 : c ≠ 0) :
    Nat.card ↥(Subgroup.centralizer
        ({⟨suUg n 0 c, suU_le_SU3 n (suUg_zero_mem n c hc)⟩} : Set (↥(SU3 n)))) =
      2 ^ (3 * n) * (2 ^ n + 1) := by
  rw [← suUS_sup_suTS1_eq_centralizer n hn hc hc0,
    Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer (suUS n) (suTS1 n)
      (suTS1_le_normalizer_suUS n) (suUS_inf_suTS1 n),
    card_suUS n hn, suTS1, Subgroup.card_map_of_injective (suTgSU_injective n), card_suT1 n hn]

/-- **The centralizer of an involution of `SU(3,2ⁿ)` is not a `2`-group**: `T₁` is
nontrivial (it has order `q + 1 ≥ 3`). -/
theorem suTS1_ne_bot (n : ℕ) (hn : 1 ≤ n) : suTS1 n ≠ ⊥ := by
  intro h
  have hcard : Nat.card ↥(suTS1 n) = 2 ^ n + 1 := by
    rw [suTS1, Subgroup.card_map_of_injective (suTgSU_injective n), card_suT1 n hn]
  rw [h, Subgroup.card_bot] at hcard
  have h2 : 2 ≤ (2 : ℕ) ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

end Submission.PSU3
