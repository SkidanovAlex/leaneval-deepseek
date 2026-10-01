/-
# Elementary `2`-power character API, in a bubble compatible with the `lfSmall` counting chain

The workspace contains two mutually incompatible clusters of `Commons` modules: those that import
`Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_twoPow` (`charCorrelation_twoPow`
declares `Commons.NumberTheory.DirichletCharacter.sum_zmod_eq_sum_range`) and those that import
`Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_normSq_eq_conductor` (which declares the
same name).  A file may import only one of them.

The `p = 2` counting lemmas of `Submission/Work/LinnikBurgess/lfSmall/` live in the *second* cluster,
while the `p = 2` two-digit decomposition of the cubic correlation
(`Submission/Work/LinnikBurgess/thetaTwo_core.lean`, `twoPow_innerSum_factor.lean`,
`corr6_twoPow_gaussTwo_le.lean`) lives in the first.  This file re-proves, in the second cluster,
the handful of elementary `2`-power character facts those files use from the first cluster
(`chi_one_add_twoPow_sub_one`, `isUnit_of_odd`, `chi_natCast_eq_zero_of_even`,
`sum_range_mul_pow_two`), so that both halves can be used in a single development.
-/
import Mathlib
import Submission.Commons.NumberTheory.ZMod.card_ker_unitsMap_prime_pow

open scoped BigOperators

namespace Work.ZeroFreeTables.P9F

/-- A sum over `ZMod n` is a sum over `Finset.range n`. -/
lemma sum_zmod_eq_sum_range' {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : ZMod n → M) : ∑ x : ZMod n, f x = ∑ i ∈ Finset.range n, f ((i : ZMod n)) := by
  refine Finset.sum_bij (fun (x : ZMod n) _ => x.val) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a _ b _ h; exact ZMod.val_injective n h
  · intro b hb
    refine ⟨(b : ZMod n), Finset.mem_univ _, ?_⟩
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
  · intro a _
    rw [ZMod.natCast_zmod_val]

/-- Decomposition of a sum over `range (2^(j+m))` as a double sum. -/
lemma sum_range_mul_pow_two {j m : ℕ} {M : Type*} [AddCommMonoid M] (G : ℕ → M) :
    ∑ X ∈ Finset.range (2^(j+m)), G X
      = ∑ Y ∈ Finset.range (2^j), ∑ T ∈ Finset.range (2^m), G (Y + 2^j * T) := by
  have hpos : 0 < 2^j := pow_pos (by norm_num) j
  rw [pow_add]
  rw [show (∑ Y ∈ Finset.range (2^j), ∑ T ∈ Finset.range (2^m), G (Y + 2^j * T))
      = ∑ p ∈ (Finset.range (2^j)).product (Finset.range (2^m)),
          G (p.1 + 2^j * p.2) from
    (Finset.sum_product (Finset.range (2^j)) (Finset.range (2^m))
      (fun p : ℕ × ℕ => G (p.1 + 2^j * p.2))).symm]
  refine Finset.sum_bij' (fun (X : ℕ) _ => (X % 2^j, X / 2^j))
    (fun (p : ℕ × ℕ) _ => p.1 + 2^j * p.2) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    change (X % 2^j, X / 2^j) ∈ Finset.range (2^j) ×ˢ Finset.range (2^m)
    rw [Finset.mem_product]
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hpos), Finset.mem_range.mpr ?_⟩
    rw [Nat.div_lt_iff_lt_mul hpos, mul_comm]
    exact Finset.mem_range.mp hX
  · intro p hp
    obtain ⟨Y, T⟩ := p
    have hp' : (Y, T) ∈ Finset.range (2^j) ×ˢ Finset.range (2^m) := hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp'
    refine Finset.mem_range.mpr ?_
    calc Y + 2^j * T < 2^j + 2^j * T := by omega
      _ = 2^j * (T + 1) := by ring
      _ ≤ 2^j * 2^m := by
          apply Nat.mul_le_mul_left; omega
  · intro X _
    show ((X % 2^j) + 2^j * (X / 2^j)) = X
    rw [Nat.mod_add_div]
  · intro p hp
    obtain ⟨Y, T⟩ := p
    have hp' : (Y, T) ∈ Finset.range (2^j) ×ˢ Finset.range (2^m) := hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp'
    have h1 : (Y + 2^j * T) % 2^j = Y := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hp'.1
    have h2 : (Y + 2^j * T) / 2^j = T := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hp'.1, zero_add]
    rw [h1, h2]
  · intro X _
    rw [Nat.mod_add_div]

/-- An odd natural number is a unit in `ZMod (2^e)`. -/
lemma isUnit_of_odd {e n : ℕ} (hn : Odd n) : IsUnit ((n : ℕ) : ZMod (2^e)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hn)

/-- A character modulo `2^e` vanishes on even inputs. -/
lemma chi_natCast_eq_zero_of_even {e : ℕ} (he : 1 ≤ e) (χ : DirichletCharacter ℂ (2^e))
    {n : ℕ} (hn : 2 ∣ n) : χ ((n : ℕ) : ZMod (2^e)) = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega : 0 < e)]
  exact fun h => h hn

/-- **The value of a primitive character modulo `2^e` at `1 + 2^(e-1)` is `-1`.**
`(1 + 2^(e-1))² = 1`, and `1 + 2^(e-1)` generates the kernel of the reduction
`(ZMod (2^e))ˣ → (ZMod (2^(e-1)))ˣ`, namely a group of order `2` on which a primitive character is
non-trivial (its conductor is `2^e`).  Hence `χ (1 + 2^(e-1)) = -1`. -/
theorem chi_one_add_twoPow_sub_one {e : ℕ} (he : 2 ≤ e) (χ : DirichletCharacter ℂ (2^e))
    (hχ : χ.IsPrimitive) : χ (((1 + 2^(e-1) : ℕ)) : ZMod (2^e)) = -1 := by
  haveI : NeZero (2^e) := ⟨pow_ne_zero e (by norm_num)⟩
  have hd : 2^(e-1) ∣ 2^e := pow_dvd_pow 2 (by omega)
  have hodd : Odd (1 + 2^(e-1)) := ⟨2^(e-2), by
    rw [show 2^(e-1) = 2 * 2^(e-2) by rw [← pow_succ']; congr 1; omega]
    ring⟩
  have hcop : Nat.Coprime (1 + 2^(e-1)) (2^e) :=
    (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)).symm
  set u : (ZMod (2^e))ˣ := ZMod.unitOfCoprime (1 + 2^(e-1)) hcop with hu
  have huval : ((u : ZMod (2^e))) = ((1 + 2^(e-1) : ℕ) : ZMod (2^e)) := ZMod.coe_unitOfCoprime _ _
  have hu2val : (((1 + 2^(e-1) : ℕ)) : ZMod (2^e)) * (((1 + 2^(e-1) : ℕ)) : ZMod (2^e)) = 1 := by
    rw [← Nat.cast_mul, show (1 : ZMod (2^e)) = ((1:ℕ) : ZMod (2^e)) by simp,
      ZMod.natCast_eq_natCast_iff]
    have hA : (1 + 2^(e-1)) * (1 + 2^(e-1)) = 1 + 2^e + 2^(2*(e-1)) := by
      have h2e : 2^e = 2 * 2^(e-1) := by rw [← pow_succ']; congr 1; omega
      have hsq : 2^(2*(e-1)) = 2^(e-1) * 2^(e-1) := by rw [← pow_add]; congr 1; omega
      rw [h2e, hsq]; ring
    rw [hA]
    refine (Nat.modEq_iff_dvd.mpr ?_).symm
    have hz : ((1 + 2^e + 2^(2*(e-1)) : ℕ) : ℤ) - ((1:ℕ) : ℤ)
        = (2^e : ℤ) + ((2^(2*(e-1)) : ℕ) : ℤ) := by
      push_cast; ring
    rw [hz]
    exact dvd_add (dvd_refl _)
      (by exact_mod_cast Nat.pow_dvd_pow 2 (show e ≤ 2*(e-1) by omega))
  have hu2 : u * u = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one, huval]
    exact hu2val
  have hmem : u ∈ (ZMod.unitsMap hd).ker := by
    rw [MonoidHom.mem_ker, Units.ext_iff]
    have h1 : (ZMod.unitsMap hd u : ZMod (2^(e-1))) = ((1 + 2^(e-1) : ℕ) : ZMod (2^(e-1))) := by
      rw [ZMod.unitsMap_val, huval, ZMod.cast_natCast hd]
    have h2 : ((1 + 2^(e-1) : ℕ) : ZMod (2^(e-1))) = 1 := by
      have h3 : ((2^(e-1) : ℕ) : ZMod (2^(e-1))) = 0 := ZMod.natCast_self _
      rw [Nat.cast_add, Nat.cast_one, h3]
      ring
    rw [h1, h2, Units.val_one]
  have hune : u ≠ 1 := by
    intro h1
    have h2 : ((1 + 2^(e-1) : ℕ) : ZMod (2^e)) = ((1:ℕ) : ZMod (2^e)) := by
      rw [← huval, h1]
      simp
    rw [ZMod.natCast_eq_natCast_iff] at h2
    have h3 := (Nat.modEq_iff_dvd' (show 1 ≤ 1 + 2^(e-1) by omega)).mp h2.symm
    have hsub : 1 + 2^(e-1) - 1 = 2^(e-1) := by omega
    rw [hsub] at h3
    have hlt : 2^(e-1) < 2^e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hpos : 0 < 2^(e-1) := pow_pos (by norm_num) _
    exact absurd (Nat.le_of_dvd hpos h3) (not_le.mpr hlt)
  have hker_eq : (ZMod.unitsMap hd).ker = Subgroup.zpowers u := by
    have hcard : Nat.card (ZMod.unitsMap hd).ker = 2 :=
      Commons.NumberTheory.ZMod.card_ker_unitsMap_prime_pow Nat.prime_two he hd
    have hord : orderOf u = 2 := by
      have h1 : orderOf u ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, sq]
        exact hu2
      rcases Nat.dvd_prime Nat.prime_two |>.mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hune
      · exact h
    have hcardz : Nat.card (Subgroup.zpowers u) = 2 := by rw [Nat.card_zpowers, hord]
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by
      rw [hcard, hcardz])).symm
  have hnf : ¬ χ.FactorsThrough (2^(e-1)) := by
    intro hf
    have hmem' : 2^(e-1) ∈ χ.conductorSet := (DirichletCharacter.mem_conductorSet_iff χ).mpr hf
    have hdvd : χ.conductor ∣ 2^(e-1) :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mp hmem'
    rw [(DirichletCharacter.isPrimitive_def χ).mp hχ] at hdvd
    have hle := Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
    have hlt : 2^(e-1) < 2^e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hsq : (χ.toUnitHom u : ℂ) * (χ.toUnitHom u : ℂ) = 1 := by
    have h2 : ((χ.toUnitHom u * χ.toUnitHom u : ℂˣ) : ℂ) = 1 := by
      rw [← map_mul, hu2, map_one]; rfl
    simpa using h2
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exfalso
    apply hnf
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, hker_eq]
    intro v hv
    rw [MonoidHom.mem_ker]
    rw [Subgroup.mem_zpowers_iff] at hv
    obtain ⟨k, hk⟩ := hv
    have h1' : χ.toUnitHom u = 1 := Units.ext h1
    rw [← hk, map_zpow, h1', one_zpow]
  · rw [← huval, ← MulChar.coe_toUnitHom χ u]
    exact h1

end Work.ZeroFreeTables.P9F
