import Mathlib
import Submission.Commons.NumberTheory.ZMod.card_ker_unitsMap_prime_pow

namespace Commons.NumberTheory.DirichletCharacter

open MulChar

/-- `1 + p^(e-1)` is coprime to `p^e` for `2 ≤ e`. -/
lemma coprime_one_add_prime_pow_pred {p e : ℕ} (_hp : p.Prime) (he : 2 ≤ e) :
    Nat.Coprime (1 + p ^ (e - 1)) (p ^ e) := by
  have hpow : p ^ (e - 1) = p * p ^ (e - 2) := by
    rw [show e - 1 = 1 + (e - 2) by omega, pow_add, pow_one]
  rw [hpow]
  exact ((Nat.coprime_add_mul_left_left 1 p (p ^ (e - 2))).mpr
    (Nat.coprime_one_left p)).pow_right e

/-- For `p` an odd prime, `e ≥ 2` and `χ` a primitive Dirichlet character modulo `p ^ e`,
the value of `χ` at `1 + p ^ (e-1)` is a **primitive `p`-th root of unity**.

Indeed `(1 + p^(e-1))^p = 1` in `ZMod (p^e)`, so `χ (1+p^(e-1)) ^ p = 1`; and
`1 + p^(e-1)` generates the kernel of the reduction `(ZMod (p^e))ˣ → (ZMod (p^(e-1)))ˣ`
(a cyclic group of prime order `p`), on which a primitive character is non-trivial because
its conductor is `p ^ e`. -/
lemma chi_one_add_primePow_isPrimitiveRoot (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) :
    IsPrimitiveRoot (χ ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e))) p := by
  have hp : p.Prime := Fact.out
  have hd : p ^ (e - 1) ∣ p ^ e := pow_dvd_pow p (Nat.sub_le e 1)
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  -- The unit `a = 1 + p^(e-1)` of `(ZMod (p^e))ˣ`.
  set a : (ZMod (p ^ e))ˣ :=
    ZMod.unitOfCoprime (1 + p ^ (e - 1)) (coprime_one_add_prime_pow_pred hp he) with ha
  -- `χ` of that unit is `χ (1 + p^(e-1))`.
  have hcoe : (χ.toUnitHom a : ℂ) = χ ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e)) := by
    rw [MulChar.coe_toUnitHom, ha, ZMod.coe_unitOfCoprime]
  -- `a` lies in the kernel of the reduction `(ZMod (p^e))ˣ → (ZMod (p^(e-1)))ˣ`.
  have hmem : a ∈ (ZMod.unitsMap hd).ker := by
    rw [MonoidHom.mem_ker]
    ext
    rw [ZMod.unitsMap_val, ha, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]
    simp
  have hcardk : Nat.card (ZMod.unitsMap hd).ker = p :=
    Commons.NumberTheory.ZMod.card_ker_unitsMap_prime_pow hp he hd
  -- `a ≠ 1`, since `p ^ (e-1) ≠ 0` in `ZMod (p^e)`.
  have hne : a ≠ 1 := by
    intro h
    have hv : ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e)) = 1 := by
      have key : ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e)) = ↑a := by
        rw [ha, ZMod.coe_unitOfCoprime]
      rw [key, h, Units.val_one]
    have hz : ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) = 0 := by
      have h1 : (1 : ZMod (p ^ e)) + ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) = 1 := by
        simpa using hv
      have h2 := congrArg (fun t : ZMod (p ^ e) => t - 1) h1
      simpa using h2
    have hdvd' : p ^ e ∣ p ^ (e - 1) := (ZMod.natCast_eq_zero_iff (p ^ (e - 1)) (p ^ e)).mp hz
    have hlt : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd') (not_le.mpr hlt)
  have hle : Subgroup.zpowers a ≤ (ZMod.unitsMap hd).ker := Subgroup.zpowers_le.mpr hmem
  -- Injectivity against the cyclic quotient: `a` has order exactly `p`.
  have hord : orderOf a = p := by
    have h1 : Nat.card ↥(Subgroup.zpowers a) ∣ Nat.card ↥(ZMod.unitsMap hd).ker :=
      Subgroup.card_dvd_of_le hle
    rw [hcardk] at h1
    rw [Nat.card_zpowers a] at h1
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hne
    · exact h2
  -- Hence `a` generates the kernel (whose order is the prime `p`).
  have hker_eq : Subgroup.zpowers a = (ZMod.unitsMap hd).ker := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardk, Nat.card_zpowers, hord]
  -- Primitivity forces `χ` to be non-trivial on the kernel, hence `χ a ≠ 1`.
  have hχa_ne : χ ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e)) ≠ 1 := by
    intro h
    have hunt : χ.toUnitHom a = 1 := by
      apply Units.ext
      rw [hcoe, h, Units.val_one]
    have hk : (ZMod.unitsMap hd).ker ≤ χ.toUnitHom.ker := by
      rw [← hker_eq]
      exact Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr hunt)
    have hfac : χ.FactorsThrough (p ^ (e - 1)) :=
      (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr hk
    have hmem' : p ^ (e - 1) ∈ χ.conductorSet :=
      (DirichletCharacter.mem_conductorSet_iff χ).mpr hfac
    have hdvd : χ.conductor ∣ p ^ (e - 1) :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mp hmem'
    rw [hχ] at hdvd
    have hlt : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd) (not_le.mpr hlt)
  -- `χ a` then has order exactly `p`.
  rw [← hcoe]
  refine (IsPrimitiveRoot.coe_units_iff).mpr ?_
  refine IsPrimitiveRoot.iff_orderOf.mpr ?_
  have hdvd : orderOf (χ.toUnitHom a) ∣ p := by
    have h := orderOf_map_dvd χ.toUnitHom a
    rw [hord] at h
    exact h
  have hyne : χ.toUnitHom a ≠ 1 := by
    intro h
    exact hχa_ne (by rw [← hcoe, h, Units.val_one])
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hyne
  · exact h1

end Commons.NumberTheory.DirichletCharacter
