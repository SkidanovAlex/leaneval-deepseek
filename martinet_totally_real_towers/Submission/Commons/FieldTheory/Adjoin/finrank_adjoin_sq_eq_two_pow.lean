import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.FieldTheory.KummerExtension.finrank_adjoin_nthRoots_eq_pow

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Adjoin

theorem finrank_adjoin_sq_eq_two_pow {F L : Type*} [Field F] [Field L] [Algebra F L]
    [CharZero F] {ι : Type*} [Fintype ι] (a : ι → F) (c : ι → L)
    (ha : ∀ i, a i ≠ 0)
    (hsq : ∀ i, c i ^ 2 = algebraMap F L (a i))
    (hgen : IntermediateField.adjoin F (Set.range c) = ⊤)
    (hns : ∀ T : Finset ι, T.Nonempty → ∀ r : F, r ^ 2 ≠ ∏ i ∈ T, a i) :
    Module.finrank F L = 2 ^ Fintype.card ι := by
  classical
  -- `L` is generated over `F` by finitely many integral (= algebraic) elements.
  haveI hfd : FiniteDimensional F ↥(IntermediateField.adjoin F (Set.range c)) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro x ⟨i, rfl⟩
    exact ⟨Polynomial.X ^ 2 - Polynomial.C (a i),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), by simp [hsq i]⟩
  haveI htop : FiniteDimensional F ↥(⊤ : IntermediateField F L) := hgen ▸ hfd
  haveI : FiniteDimensional F L :=
    (IntermediateField.topEquiv (F := F) (E := L)).toLinearEquiv.finiteDimensional
  -- `-1` is a primitive square root of unity in characteristic zero.
  have hζ : IsPrimitiveRoot (-1 : F) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  -- The independence hypothesis in the form required by Kummer theory.
  have hind : ∀ j : ι → ℕ, (∃ r : F, ∏ i, a i ^ (j i) = r ^ 2) → ∀ i, 2 ∣ j i := by
    intro j hj i
    by_contra hji
    obtain ⟨r, hr⟩ := hj
    have hmem : i ∈ Finset.univ.filter (fun i => ¬ 2 ∣ j i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hji⟩
    have hTne : (Finset.univ.filter (fun i => ¬ 2 ∣ j i)).Nonempty := ⟨i, hmem⟩
    have hprod_ne : (∏ i, a i ^ (j i / 2)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (ha i))
    -- splitting each exponent into its even and odd part
    have hone : ∀ i, a i ^ (j i) = a i ^ (j i % 2) * (a i ^ (j i / 2)) ^ 2 := by
      intro i
      conv_lhs => rw [← Nat.mod_add_div (j i) 2]
      rw [pow_add, Nat.mul_comm 2 (j i / 2), pow_mul]
    have hstep1 : (∏ i, a i ^ (j i)) =
        ∏ i, (a i ^ (j i % 2) * (a i ^ (j i / 2)) ^ 2) :=
      Finset.prod_congr rfl (fun i _ => hone i)
    have hmod : (∏ i, a i ^ (j i % 2)) =
        ∏ i ∈ Finset.univ.filter (fun i => ¬ 2 ∣ j i), a i := by
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases h : 2 ∣ j i
      · rw [if_neg (not_not.mpr h), Nat.dvd_iff_mod_eq_zero.mp h, pow_zero]
      · rw [if_pos h]
        have h2 : j i % 2 ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
        have h1 : j i % 2 < 2 := Nat.mod_lt _ (by norm_num)
        have : j i % 2 = 1 := by omega
        rw [this, pow_one]
    have hdecomp : (∏ i, a i ^ (j i)) =
        (∏ i, a i ^ (j i / 2)) ^ 2 * ∏ i ∈ Finset.univ.filter (fun i => ¬ 2 ∣ j i), a i := by
      rw [hstep1, Finset.prod_mul_distrib, Finset.prod_pow, hmod, mul_comm]
    refine hns _ hTne (r / (∏ i, a i ^ (j i / 2))) ?_
    calc (r / (∏ i, a i ^ (j i / 2))) ^ 2
        = r ^ 2 / (∏ i, a i ^ (j i / 2)) ^ 2 := by rw [div_pow]
      _ = (∏ i, a i ^ (j i)) / (∏ i, a i ^ (j i / 2)) ^ 2 := by rw [hr]
      _ = (∏ i, a i ^ (j i / 2)) ^ 2
            * (∏ i ∈ Finset.univ.filter (fun i => ¬ 2 ∣ j i), a i)
            / (∏ i, a i ^ (j i / 2)) ^ 2 := by rw [hdecomp]
      _ = ∏ i ∈ Finset.univ.filter (fun i => ¬ 2 ∣ j i), a i :=
          mul_div_cancel_left₀ _ (pow_ne_zero 2 hprod_ne)
  exact Commons.FieldTheory.KummerExtension.finrank_adjoin_nthRoots_eq_pow 2 hζ c ha hsq hind hgen

end Commons.FieldTheory.Adjoin