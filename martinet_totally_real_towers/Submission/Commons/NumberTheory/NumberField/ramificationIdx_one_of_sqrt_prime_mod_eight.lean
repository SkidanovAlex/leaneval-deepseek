import Mathlib
import Submission.Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr
import Submission.Commons.NumberTheory.Rat.not_square_of_prime_dvd_once

open Polynomial
open scoped NumberField

noncomputable section
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.NumberField

theorem discr_eq_of_sq_eq_of_prime_mod_four {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : Nat.Prime q) (hq4 : q % 4 = 1) (x : K)
    (hx : x ^ 2 = algebraMap ℚ K (q : ℚ))
    (hgen : Algebra.adjoin ℚ ({x} : Set K) = ⊤) :
    (NumberField.discr K).natAbs = q := by
  -- arithmetic
  obtain ⟨c, hc⟩ : ∃ c : ℕ, 4 * c = q - 1 := by
    have h : 4 ∣ q - 1 := by omega
    exact ⟨(q - 1) / 4, Nat.mul_div_cancel' h⟩
  have hq1 : 1 ≤ q := hq.one_le
  have hcq : (q : ℚ) = 4 * (c : ℚ) + 1 := by
    have h1 : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by
      rw [Nat.cast_sub hq1]; norm_num
    have h2 : ((4 * c : ℕ) : ℚ) = (q : ℚ) - 1 := by rw [hc]; exact h1
    push_cast at h2
    linarith [h2]
  have hq_eq : algebraMap ℚ K (q : ℚ) = 4 * algebraMap ℚ K (c : ℚ) + 1 := by
    have := congr_arg (algebraMap ℚ K) hcq
    simpa using this
  -- define y
  set y : K := (1 + x) / 2 with hy_def
  have hy_root : y ^ 2 - y - algebraMap ℚ K (c : ℚ) = 0 := by
    rw [hy_def]
    field_simp
    ring_nf
    rw [hx, hq_eq]
    ring
  -- y is integral over ℤ
  have hcast : (algebraMap ℤ K (c : ℤ)) = algebraMap ℚ K (c : ℚ) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ K (c : ℤ)]
    simp
  have hyintZ : IsIntegral ℤ y := by
    refine ⟨X ^ 2 - X - C (c : ℤ), ?_, ?_⟩
    · monicity!
    · simpa [Polynomial.aeval_def, hcast] using hy_root
  have hyintQ : IsIntegral ℚ y := by
    refine ⟨X ^ 2 - X - C (c : ℚ), ?_, ?_⟩
    · monicity!
    · simpa [Polynomial.aeval_def] using hy_root
  -- adjoin
  have hy_mem : y ∈ Algebra.adjoin ℚ ({y} : Set K) := Algebra.subset_adjoin (Set.mem_singleton y)
  have h2mem : (2 : K) ∈ Algebra.adjoin ℚ ({y} : Set K) := by
    simpa using Subalgebra.algebraMap_mem (Algebra.adjoin ℚ ({y} : Set K)) (2 : ℚ)
  have hx_eq : x = 2 * y - 1 := by rw [hy_def]; field_simp; ring
  have hxmem : x ∈ Algebra.adjoin ℚ ({y} : Set K) := by
    rw [hx_eq]
    exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ h2mem hy_mem) (Subalgebra.one_mem _)
  have hgen_y : Algebra.adjoin ℚ ({y} : Set K) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact Algebra.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxmem)
  -- power basis
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop (K := ℚ) (S := K) hyintQ hgen_y
  have hpbgen : pb.gen = y := PowerBasis.ofAdjoinEqTop_gen hyintQ hgen_y
  -- minpoly of y
  have hqnot : ¬ q ^ 2 ∣ q := by
    intro h
    have hle : q ^ 2 ≤ q := Nat.le_of_dvd hq.pos h
    nlinarith [hq.two_le]
  have hIrred : Irreducible (X ^ 2 - X - C (c : ℚ) : ℚ[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have : (X ^ 2 - X - C (c : ℚ) : ℚ[X]).natDegree = 2 := by compute_degree!
      rw [this]; norm_num
    · intro b hb
      rw [Polynomial.IsRoot.def] at hb
      have hb' : b ^ 2 - b - (c : ℚ) = 0 := by
        simpa [map_sub, map_pow, map_one] using hb
      have hsq : (2 * b - 1) ^ 2 = (q : ℚ) := by nlinarith [hcq]
      exact Commons.NumberTheory.Rat.not_square_of_prime_dvd_once hq dvd_rfl hqnot (2 * b - 1) hsq
  have hmin_y : minpoly ℚ y = X ^ 2 - X - C (c : ℚ) := by
    refine (minpoly.eq_of_irreducible_of_monic hIrred ?_ ?_).symm
    · simpa [map_sub, map_pow, map_one, aeval_def] using hy_root
    · monicity!
  have hdiscpoly : (X ^ 2 - X - C (c : ℚ) : ℚ[X]).discr = (q : ℚ) := by
    rw [Polynomial.discr_of_degree_eq_two (by compute_degree! : (X ^ 2 - X - C (c : ℚ) : ℚ[X]).degree = 2)]
    simp only [coeff_sub, coeff_X_pow, coeff_X, coeff_C, coeff_one]
    norm_num
    linarith [hcq]
  have hdiscpb : Algebra.discr ℚ pb.basis = (q : ℚ) := by
    rw [← Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr (F := ℚ) (S := K) (pb := pb)]
    rw [hpbgen, hmin_y, hdiscpoly]
  -- finrank
  have hpb_dim : pb.dim = 2 := by
    rw [PowerBasis.ofAdjoinEqTop_dim, hmin_y]
    compute_degree!
  have hfin : Module.finrank ℚ K = 2 := by
    rw [PowerBasis.finrank pb, hpb_dim]
  -- integral basis
  have hpb_int : ∀ i : Fin pb.dim, IsIntegral ℤ (pb.basis i) := by
    intro i
    rw [PowerBasis.basis_eq_pow, hpbgen]
    exact hyintZ.pow _
  obtain ⟨m, hm⟩ := discr_dvd_of_isIntegral_basis (K := K) pb.basis hpb_int
  have hmq : (q : ℚ) = (NumberField.discr K : ℚ) * m := by rw [← hdiscpb]; exact hm
  have hmZ : (q : ℤ) = NumberField.discr K * m := by exact_mod_cast hmq
  have hnat : (NumberField.discr K).natAbs ∣ q := by
    refine ⟨m.natAbs, ?_⟩
    have : (NumberField.discr K).natAbs * m.natAbs = q := by
      rw [← Int.natAbs_mul, ← hmZ]
      simp
    exact this.symm
  have hfin_gt : 1 < Module.finrank ℚ K := by rw [hfin]; norm_num
  have hlower := NumberField.abs_discr_ge (K := K) hfin_gt
  have hlower_gt : (1 : ℝ) < 4 / 9 * (3 * Real.pi / 4) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hlow2 : 4 / 9 * (3 * Real.pi / 4) ^ 2 ≤ |(NumberField.discr K : ℝ)| := by
    simpa [hfin] using hlower
  have hD_gt_one : (1 : ℝ) < |(NumberField.discr K : ℝ)| := lt_of_lt_of_le hlower_gt hlow2
  have hnat_gt_one : 1 < (NumberField.discr K).natAbs := by
    have : (1 : ℝ) < ((NumberField.discr K).natAbs : ℝ) := by
      simpa [Nat.cast_natAbs] using hD_gt_one
    exact_mod_cast this
  have hnat_ge2 : 2 ≤ (NumberField.discr K).natAbs := by omega
  exact (Nat.dvd_prime_two_le hq hnat_ge2).mp hnat

theorem ramificationIdx_one_of_sqrt_prime_mod_eight {K : Type*} [Field K] [NumberField K]
    {q p : ℕ} (hq : Nat.Prime q) (hq8 : q % 8 = 1) (hp : Nat.Prime p) (hpq : p ≠ q)
    (x : K) (hx : x ^ 2 = algebraMap ℚ K (q : ℚ)) (hgen : Algebra.adjoin ℚ ({x} : Set K) = ⊤)
    (𝔭 : Ideal (NumberField.RingOfIntegers ℚ)) (h𝔭 : 𝔭.IsPrime) (h𝔭ne : 𝔭 ≠ ⊥)
    (h𝔭p : (p : NumberField.RingOfIntegers ℚ) ∈ 𝔭)
    (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hPlies : P.LiesOver 𝔭) :
    P.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1 := by
  have hq4 : q % 4 = 1 := by omega
  have hdiscr : (NumberField.discr K).natAbs = q :=
    discr_eq_of_sq_eq_of_prime_mod_four hq hq4 x hx hgen
  have hndvd : ¬ (p : ℤ) ∣ NumberField.discr K := by
    intro h
    have h' : (p : ℤ) ∣ ((NumberField.discr K).natAbs : ℤ) := (Int.dvd_natAbs).mpr h
    rw [hdiscr] at h'
    have hpq' : p ∣ q := Int.ofNat_dvd.mp h'
    rcases (Nat.dvd_prime hq).mp hpq' with h1 | h2
    · exact hp.ne_one h1
    · exact hpq h2
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI hPliesI : P.LiesOver 𝔭 := hPlies
  haveI hPprime : P.IsPrime := hP
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭ne P
  have hPmax : P.IsMaximal := hP.isMaximal hPne
  have hPliesInt : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hmem_under : (p : ℤ) ∈ P.under ℤ := by
      show algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) ∈ P
      have hmem : algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)
          (p : NumberField.RingOfIntegers ℚ) ∈ P :=
        (Ideal.mem_of_liesOver P 𝔭 (p : NumberField.RingOfIntegers ℚ)).mp h𝔭p
      simpa [map_natCast] using hmem
    have hspan : Ideal.span {(p : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_le]
      exact Set.singleton_subset_iff.mpr hmem_under
    have hne : P.under ℤ ≠ ⊤ := by
      intro h
      have h1 : (1 : NumberField.RingOfIntegers K) ∈ P := by
        have hmem : (1 : ℤ) ∈ P.under ℤ := by rw [h]; simp
        have : algebraMap ℤ (NumberField.RingOfIntegers K) (1 : ℤ) ∈ P := hmem
        simpa using this
      exact hP.ne_top (Ideal.eq_top_iff_one P |>.mpr h1)
    exact ⟨Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) hne hspan⟩
  have hunr : Algebra.IsUnramifiedAt ℤ P :=
    ((NumberField.not_dvd_discr_iff_forall_liesOver K (NumberField.RingOfIntegers K)
      (Nat.prime_iff_prime_int.mp hp)).mp hndvd) P hPmax hPliesInt
  haveI : Algebra.IsUnramifiedAt ℤ P := hunr
  haveI : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers ℚ) P :=
    Algebra.IsUnramifiedAt.of_restrictScalars ℤ P
  exact Ideal.ramificationIdx_eq_one P (NumberField.RingOfIntegers ℚ)

end Commons.NumberTheory.NumberField
