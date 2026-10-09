import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive
import Submission.Commons.NumberTheory.DirichletCharacter.isPrimitive_inv
import Submission.Commons.NumberTheory.JacobiSymbol.modEight_of_selfRelation
import Submission.Commons.NumberTheory.NumberField.discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.no_inertiaDeg_one_two_of_mod
import Submission.Commons.NumberTheory.NumberField.torsionOrder_le_six_of_finrank_two
import Submission.Commons.NumberTheory.NumberField.exists_regulator_lower_bound_of_finrank_two
import Submission.Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_quadratic
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_X_sq_sub_C
import Submission.Commons.NumberTheory.QuadraticExtension.numberField_adjoinRoot_X_sq_sub_C
import Submission.Commons.NumberTheory.QuadraticExtension.finrank_adjoinRoot_X_sq_sub_C
import Submission.Commons.NumberTheory.QuadraticExtension.irreducible_X_sq_sub_C_iff_not_square
import Submission.Commons.NumberTheory.NumberField.exists_mod_eight_one_of_split_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open _root_.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

open Complex
open Polynomial

/-- For a primitive quadratic Dirichlet character `χ` of modulus `N`, the square of its
Gauss sum against the standard additive character equals `χ(-1) * N`. -/
theorem gaussSum_sq_of_mul_self_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) :
    gaussSum χ (ZMod.stdAddChar (N := N)) ^ 2 = χ (-1) * (N : ℂ) := by
  set τ := gaussSum χ (ZMod.stdAddChar (N := N)) with hτ
  have hinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right hsq
  have hstar : star τ = χ (-1) * τ := by
    have h1 : star τ = gaussSum χ⁻¹ ((ZMod.stdAddChar (N := N)).mulShift (-1)) := by
      rw [hτ, star_gaussSum_eq, AddChar.inv_mulShift]
    rw [h1, gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := N))
      (Commons.NumberTheory.DirichletCharacter.isPrimitive_inv hχ) (-1)]
    simp only [hinv, hτ]
  have hnorm : τ * star τ = ((N : ℝ) : ℂ) := by
    have h : ‖τ‖ ^ 2 = (N : ℝ) := by
      rw [hτ]; exact Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive χ hχ
    calc τ * star τ = ((Complex.normSq τ : ℝ) : ℂ) := by simpa using Complex.mul_conj τ
      _ = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.normSq_eq_norm_sq]
      _ = ((N : ℝ) : ℂ) := by rw [h]
  have hsquinv : χ (-1 : ZMod N) * χ (-1 : ZMod N) = 1 := by
    rw [← map_mul, show (-1 : ZMod N) * (-1) = 1 by ring, MulChar.map_one]
  have key : χ (-1) * τ ^ 2 = ((N : ℝ) : ℂ) := by
    calc χ (-1) * τ ^ 2 = τ * (χ (-1) * τ) := by ring
      _ = τ * star τ := by rw [← hstar]
      _ = ((N : ℝ) : ℂ) := hnorm
  have hmm : τ ^ 2 = χ (-1) * ((N : ℝ) : ℂ) := by
    calc τ ^ 2 = 1 * τ ^ 2 := by ring
      _ = (χ (-1) * χ (-1)) * τ ^ 2 := by rw [hsquinv]
      _ = χ (-1) * (χ (-1) * τ ^ 2) := by ring
      _ = χ (-1) * ((N : ℝ) : ℂ) := by rw [key]
  rw [hmm]
  push_cast
  ring

/-- A quadratic (`χ * χ = 1`) Dirichlet character takes only the values `0`, `1`, `-1`. -/
theorem quadratic_chi_values {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1)
    (a : ZMod N) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases ha : IsUnit a
  · have h1 : χ a * χ a = 1 := by
      have := congrArg (fun f : DirichletCharacter ℂ N => f a) hsq
      rwa [MulChar.mul_apply, MulChar.one_apply ha] at this
    rcases mul_self_eq_one_iff.mp h1 with h | h <;> tauto
  · left
    exact MulChar.map_nonunit' χ a ha

/-- The integer-valued "shadow" of a quadratic Dirichlet character. -/
noncomputable def chiZ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1) :
    ZMod N → ℤ :=
  fun a => if χ a = 1 then 1 else if χ a = -1 then -1 else 0

lemma chiZ_spec {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1) (a : ZMod N) :
    χ a = (chiZ χ hsq a : ℂ) := by
  rcases quadratic_chi_values χ hsq a with h | h | h <;> simp [chiZ, h]

lemma chiZ_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1)
    (a b : ZMod N) : chiZ χ hsq (a * b) = chiZ χ hsq a * chiZ χ hsq b := by
  have h1 : ((chiZ χ hsq (a * b) : ℤ) : ℂ) =
      ((chiZ χ hsq a : ℤ) : ℂ) * ((chiZ χ hsq b : ℤ) : ℂ) := by
    rw [← chiZ_spec χ hsq (a * b), ← chiZ_spec χ hsq a, ← chiZ_spec χ hsq b, map_mul]
  have h2 : ((chiZ χ hsq (a * b) : ℤ) : ℂ) =
      ((chiZ χ hsq a * chiZ χ hsq b : ℤ) : ℂ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h2


/-- **Polynomial identity behind the Gauss lemma.**  For a primitive quadratic character `χ`
modulo `N` with `χ(-1) = ε ∈ {±1}`, the cyclotomic polynomial `Φ_N` divides
`(Σ_a χ(a)X^a)² - ε·N`. -/
theorem cyclotomic_dvd_gauss_poly {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) {ε : ℤ}
    (hε : χ (-1 : ZMod N) = (ε : ℂ)) :
    Polynomial.cyclotomic N ℤ ∣
      (∑ a : ZMod N, Polynomial.C (chiZ χ hsq a) * Polynomial.X ^ (a.val)) ^ 2
        - Polynomial.C (ε * (N : ℤ)) := by
  set P : Polynomial ℤ := (∑ a : ZMod N, Polynomial.C (chiZ χ hsq a) * Polynomial.X ^ (a.val)) ^ 2
      - Polynomial.C (ε * (N : ℤ)) with hP
  set ζ : ℂ := ZMod.stdAddChar (1 : ZMod N) with hζ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hprim : IsPrimitiveRoot ζ N := by
    refine IsPrimitiveRoot.mk ?_ ?_
    · have h1 : ζ ^ N = ZMod.stdAddChar ((N : ℕ) • (1 : ZMod N)) := by
        rw [hζ]; exact (AddChar.map_nsmul_eq_pow _ N 1).symm
      rw [h1, show (N : ℕ) • (1 : ZMod N) = 0 by simp]
      exact AddChar.map_zero_eq_one _
    · intro l hl
      have h1 : ζ ^ l = ZMod.stdAddChar ((l : ℕ) • (1 : ZMod N)) := by
        rw [hζ]; exact (AddChar.map_nsmul_eq_pow _ l 1).symm
      rw [h1] at hl
      have h2 : ((l : ZMod N)) = 0 :=
        ((ZMod.isPrimitive_stdAddChar N).zmod_char_eq_one_iff N (l : ZMod N)).mp (by
          simpa using hl)
      have h3 : ((l : ℤ) : ZMod N) = 0 := by push_cast; exact h2
      have h4 : (N : ℤ) ∣ (l : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (l : ℤ) N).mp h3
      exact_mod_cast h4
  have hcomposite : ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) = Int.castRingHom ℂ := by
    ext x; simp
  have hzeta : ∀ a : ZMod N, ζ ^ (a.val) = ZMod.stdAddChar a := by
    intro a
    have h1 : (a.val : ℕ) • (1 : ZMod N) = a := by
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    conv_rhs => rw [← h1]
    rw [AddChar.map_nsmul_eq_pow, hζ]
  have hroot : Polynomial.aeval ζ (P.map (Int.castRingHom ℚ)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomposite]
    have hsum : Polynomial.eval₂ (Int.castRingHom ℂ) ζ P =
        (∑ a : ZMod N, χ a * ζ ^ (a.val)) ^ 2 - (ε : ℂ) * (N : ℂ) := by
      have hbase : Polynomial.eval₂ (Int.castRingHom ℂ) ζ P =
          (∑ a : ZMod N, ((chiZ χ hsq a : ℤ) : ℂ) * ζ ^ (a.val)) ^ 2
            - (((ε * (N : ℤ) : ℤ)) : ℂ) := by
        simp only [hP, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum,
          Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rfl
      rw [hbase]
      have hs : (∑ a : ZMod N, ((chiZ χ hsq a : ℤ) : ℂ) * ζ ^ (a.val)) =
          ∑ a : ZMod N, χ a * ζ ^ (a.val) :=
        Finset.sum_congr rfl (fun a _ => by rw [chiZ_spec χ hsq a])
      have hc : (((ε * (N : ℤ) : ℤ)) : ℂ) = (ε : ℂ) * (N : ℂ) := by push_cast; ring
      rw [hs, hc]
    rw [hsum]
    have hS : (∑ a : ZMod N, χ a * ζ ^ (a.val)) = ∑ a : ZMod N, χ a * ZMod.stdAddChar a :=
      Finset.sum_congr rfl (fun a _ => by rw [hzeta a])
    rw [hS]
    have hgs : (∑ a : ZMod N, χ a * ZMod.stdAddChar a) =
        gaussSum χ (ZMod.stdAddChar (N := N)) := rfl
    rw [hgs, gaussSum_sq_of_mul_self_eq_one χ hχ hsq, hε]
    ring
  have hdvdQ : Polynomial.cyclotomic N ℚ ∣ P.map (Int.castRingHom ℚ) := by
    have h := IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible hprim
      (Polynomial.cyclotomic.irreducible_rat hNpos)
    rw [h]
    exact minpoly.dvd ℚ ζ hroot
  have hmon : (Polynomial.cyclotomic N ℤ).Monic := Polynomial.cyclotomic.monic N ℤ
  refine (Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp ?_
  have hmap0 : ((P %ₘ Polynomial.cyclotomic N ℤ).map (Int.castRingHom ℚ)) = 0 := by
    rw [Polynomial.map_modByMonic _ hmon]
    rw [Polynomial.modByMonic_eq_zero_iff_dvd ((hmon.map (Int.castRingHom ℚ)))]
    rwa [Polynomial.map_cyclotomic]
  exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective (by simpa using hmap0)

/-- Evaluation at `mk I X` is the reduction `mk I`. -/
lemma eval₂_mk_eq {p : ℕ} (I : Ideal (ZMod p)[X]) (Q : (ZMod p)[X]) :
    Polynomial.eval₂ ((Ideal.Quotient.mk I).comp Polynomial.C) (Ideal.Quotient.mk I Polynomial.X) Q
      = Ideal.Quotient.mk I Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.eval₂_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      rfl

theorem tau_sq_eq_C {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) {ε : ℤ}
    (hε : χ (-1 : ZMod N) = (ε : ℂ)) (p : ℕ) [Fact p.Prime]
    (I : Ideal (ZMod p)[X]) (hI : Polynomial.cyclotomic N (ZMod p) ∈ I) :
    (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) ^ 2
      = ((Ideal.Quotient.mk I).comp Polynomial.C) (((ε * (N : ℤ) : ℤ)) : ZMod p) := by
  classical
  set Pz : Polynomial ℤ := (∑ a : ZMod N, Polynomial.C
      (_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a) * Polynomial.X ^ (a.val)) ^ 2
        - Polynomial.C (ε * (N : ℤ)) with hPz
  have hdvd : Polynomial.cyclotomic N (ZMod p) ∣ Polynomial.map (Int.castRingHom (ZMod p)) Pz := by
    have h := _root_.Commons.NumberTheory.DirichletCharacter.cyclotomic_dvd_gauss_poly χ hχ hsq hne hε
    have h2 := Polynomial.map_dvd (Int.castRingHom (ZMod p)) h
    rwa [Polynomial.map_cyclotomic] at h2
  obtain ⟨Q, hQ⟩ := hdvd
  have hΦ : Polynomial.eval₂ ((Ideal.Quotient.mk I).comp Polynomial.C)
      (Ideal.Quotient.mk I Polynomial.X) (Polynomial.cyclotomic N (ZMod p)) = 0 := by
    rw [eval₂_mk_eq]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hI
  have hkey : Polynomial.eval₂ ((Ideal.Quotient.mk I).comp Polynomial.C)
      (Ideal.Quotient.mk I Polynomial.X) (Polynomial.map (Int.castRingHom (ZMod p)) Pz) = 0 := by
    rw [hQ, Polynomial.eval₂_mul, hΦ, zero_mul]
  have hcomp : Polynomial.eval₂ ((Ideal.Quotient.mk I).comp Polynomial.C)
      (Ideal.Quotient.mk I Polynomial.X) (Polynomial.map (Int.castRingHom (ZMod p)) Pz) =
      (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
          ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
          * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) ^ 2
        - ((Ideal.Quotient.mk I).comp Polynomial.C) (((ε * (N : ℤ) : ℤ)) : ZMod p) := by
    simp only [hPz, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.eval₂_sub,
      Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_map]
    rfl
  rw [hcomp] at hkey
  exact sub_eq_zero.mp hkey

/-- **Frobenius expansion (Step 2).**  In `R := (ZMod p)[X] ⧸ I` with `Φ_N ∈ I`, raising the
Gauss sum to the `p`-th power multiplies the exponent by `p`. -/
theorem tau_pow_char {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1)
    (p : ℕ) [Fact p.Prime] (I : Ideal (ZMod p)[X])
    (hI : Polynomial.cyclotomic N (ZMod p) ∈ I) :
    (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) ^ p
      = ∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * (Ideal.Quotient.mk I Polynomial.X) ^ (((p : ZMod N) * a).val) := by
  classical
  haveI hC : CharP ((ZMod p)[X]) p := inferInstance
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hXN : Polynomial.X ^ N - 1 ∈ I := by
    have hdvd : Polynomial.cyclotomic N (ZMod p) ∣ Polynomial.X ^ N - 1 := by
      rw [← Polynomial.prod_cyclotomic_eq_X_pow_sub_one hNpos (ZMod p)]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self N (NeZero.ne N))
    obtain ⟨Q, hQ⟩ := hdvd
    rw [hQ]
    exact Ideal.mul_mem_right Q I hI
  have hζN : (Ideal.Quotient.mk I Polynomial.X) ^ N = 1 := by
    have h0 : Ideal.Quotient.mk I (Polynomial.X ^ N - 1) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hXN
    rw [map_sub, map_pow, map_one, sub_eq_zero] at h0
    exact h0
  have hterm : ∀ a : ZMod N, (Polynomial.C ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
      * Polynomial.X ^ (a.val)) ^ p
      = Polynomial.C ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * Polynomial.X ^ (a.val * p) := by
    intro a
    rw [mul_pow, ← map_pow, ZMod.pow_card, ← pow_mul]
  have hfrob : (∑ a : ZMod N, Polynomial.C
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * Polynomial.X ^ (a.val)) ^ p
      = ∑ a : ZMod N, Polynomial.C
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * Polynomial.X ^ (a.val * p) := by
    have hgen : ∀ (s : Finset (ZMod N)), (∑ a ∈ s, Polynomial.C
          ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
          * Polynomial.X ^ (a.val)) ^ p
        = ∑ a ∈ s, Polynomial.C
          ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
          * Polynomial.X ^ (a.val * p) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, zero_pow (Fact.out (p := Nat.Prime p)).ne_zero]
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char, ih, hterm a]
    simpa using hgen Finset.univ
  have hval : ∀ a : ZMod N, (((p : ZMod N) * a).val) = (a.val * p) % N := by
    intro a
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mul_comm a.val p]
    simp [Nat.mod_eq_of_lt (ZMod.val_lt a)]
  have hmap := congrArg (Ideal.Quotient.mk I) hfrob
  simp only [map_pow, map_sum, map_mul] at hmap
  simp only [RingHom.comp_apply]
  rw [hmap]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hval a, pow_eq_pow_mod (a.val * p) hζN]

/-- Summation against multiplication by a unit is a bijective reindexing. -/
theorem sum_units_mul_shift {N p : ℕ} [NeZero N] {M : Type*} [AddCommMonoid M]
    (hp : p.Coprime N) (f : ZMod N → M) :
    (∑ a : ZMod N, f ((p : ZMod N) * a)) = ∑ a : ZMod N, f a := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime p N).mpr hp
  rw [← hu]
  have hinj : Function.Injective (fun a : ZMod N => (↑u : ZMod N) * a) := by
    intro a b h
    have h2 := congrArg (fun x : ZMod N => (↑u⁻¹ : ZMod N) * x) h
    simpa [mul_assoc] using h2
  have hsurj : Function.Surjective (fun a : ZMod N => (↑u : ZMod N) * a) :=
    fun b => ⟨(↑u⁻¹ : ZMod N) * b, by simp [mul_assoc]⟩
  exact Fintype.sum_bijective _ ⟨hinj, hsurj⟩ (fun a : ZMod N => f ((↑u : ZMod N) * a)) f
    (fun _ => rfl)

/-- A quadratic `χ` does not vanish on units, so its integer shadow is `±1` there. -/
lemma chiZ_eq_one_or_neg_one_of_isUnit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hsq : χ * χ = 1) {a : ZMod N} (ha : IsUnit a) :
    _root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a = 1 ∨
      _root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a = -1 := by
  have hne : χ a ≠ 0 := by
    obtain ⟨u, rfl⟩ := ha
    intro h0
    have h1 : χ (↑u : ZMod N) * χ (↑u⁻¹ : ZMod N) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm
  rcases _root_.Commons.NumberTheory.DirichletCharacter.quadratic_chi_values χ hsq a with h | h | h
  · exact absurd h hne
  · refine Or.inl ?_
    have h2 := _root_.Commons.NumberTheory.DirichletCharacter.chiZ_spec χ hsq a
    rw [h] at h2
    exact_mod_cast h2.symm
  · refine Or.inr ?_
    have h2 := _root_.Commons.NumberTheory.DirichletCharacter.chiZ_spec χ hsq a
    rw [h] at h2
    exact_mod_cast h2.symm

/-- **Step 2b (Frobenius action).**  In `R = (ZMod p)[X] ⧸ I` with `Φ_N ∈ I` and `p ∤ N`,
`τ^p = c(p) · τ`. -/
theorem tau_pow_eq_chiZ_mul_tau {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hsq : χ * χ = 1) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (I : Ideal (ZMod p)[X]) (hI : Polynomial.cyclotomic N (ZMod p) ∈ I) :
    (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) ^ p
      = ((Ideal.Quotient.mk I).comp Polynomial.C)
          ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) : ℤ) : ZMod p)
        * (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
            ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
            * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) := by
  classical
  have hp : p.Coprime N := (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hpN
  have hunit : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).mpr hp
  set mkC : ZMod p →+* (ZMod p)[X] ⧸ I := (Ideal.Quotient.mk I).comp Polynomial.C with hmkC
  set ζ : (ZMod p)[X] ⧸ I := Ideal.Quotient.mk I Polynomial.X with hζ
  set cp : ZMod p := ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) : ℤ) : ZMod p)
    with hcp
  have hS : mkC cp * (∑ a : ZMod N, mkC ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * ζ ^ (((p : ZMod N) * a).val))
      = ∑ b : ZMod N, mkC ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq b : ℤ) : ZMod p)
          * ζ ^ (b.val) := by
    rw [Finset.mul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_)
      (_root_.Commons.NumberTheory.DirichletCharacter.sum_units_mul_shift hp (fun b : ZMod N => mkC ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq b : ℤ) : ZMod p) * ζ ^ (b.val)))
    rw [← mul_assoc, ← map_mul, hcp, ← Int.cast_mul,
      ← _root_.Commons.NumberTheory.DirichletCharacter.chiZ_mul]
  have hcp2 : mkC cp * mkC cp = 1 := by
    rcases chiZ_eq_one_or_neg_one_of_isUnit χ hsq hunit with h | h
    · have h1 : ((1 : ℤ) : ZMod p) = 1 := by norm_num
      rw [hcp, h, h1, map_one, mul_one]
    · have h1 : ((-1 : ℤ) : ZMod p) = -1 := by norm_num
      rw [hcp, h, h1, map_neg, map_one]
      ring
  have hSp : (∑ a : ZMod N, mkC ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * ζ ^ (((p : ZMod N) * a).val))
      = mkC cp * ∑ b : ZMod N, mkC ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq b : ℤ) : ZMod p)
          * ζ ^ (b.val) := by
    have h := congrArg (fun x => mkC cp * x) hS
    rw [← mul_assoc, hcp2, one_mul] at h
    exact h
  rw [_root_.Commons.NumberTheory.DirichletCharacter.tau_pow_char χ hsq p I hI, hSp, hmkC, hζ, hcp]

/-- **`τ` is a unit.**  In `R = (ZMod p)[X] ⧸ I` with `Φ_N ∈ I` and `p ∤ N`, the Gauss sum `τ`
satisfies `τ² = ε·N` with `ε·N` a unit of `ZMod p`, hence `τ` is a unit of `R`. -/
theorem isUnit_tau {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hsq : χ * χ = 1) (hne : χ ≠ 1) {ε : ℤ} (hε : χ (-1 : ZMod N) = (ε : ℂ))
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (I : Ideal (ZMod p)[X])
    (hI : Polynomial.cyclotomic N (ZMod p) ∈ I) :
    IsUnit (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) := by
  classical
  have hp : p.Coprime N := (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hpN
  -- ε is ±1
  have hεpm : ε = 1 ∨ ε = -1 := by
    have h1 : (ε : ℂ) = (_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) : ℂ) := by
      rw [← hε]
      exact _root_.Commons.NumberTheory.DirichletCharacter.chiZ_spec χ hsq (-1 : ZMod N)
    have h2 : ε = _root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) := by
      exact_mod_cast h1
    rw [h2]
    exact _root_.Commons.NumberTheory.DirichletCharacter.chiZ_eq_one_or_neg_one_of_isUnit χ hsq
      isUnit_neg_one
  -- N is a unit mod p
  have hNunit : IsUnit ((N : ℤ) : ZMod p) := by
    have h1 : IsUnit ((N : ℕ) : ZMod p) := (ZMod.isUnit_iff_coprime N p).mpr hp.symm
    simpa using h1
  -- ε·N is a unit mod p
  have hC0 : IsUnit (((ε * (N : ℤ) : ℤ)) : ZMod p) := by
    rcases hεpm with h | h
    · rw [h]; simpa using hNunit
    · rw [h]; simpa using hNunit.neg
  set mkC : ZMod p →+* (ZMod p)[X] ⧸ I := (Ideal.Quotient.mk I).comp Polynomial.C with hmkC
  set τ : (ZMod p)[X] ⧸ I := ∑ a : ZMod N, mkC
      ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
      * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val) with hτ
  have hτ2 : τ ^ 2 = mkC (((ε * (N : ℤ) : ℤ)) : ZMod p) := by
    rw [hτ, hmkC]
    exact _root_.Commons.NumberTheory.DirichletCharacter.tau_sq_eq_C χ hχ hsq hne hε p I hI
  obtain ⟨u, hu⟩ := hC0
  have hu' : mkC (((ε * (N : ℤ) : ℤ)) : ZMod p) = mkC (↑u : ZMod p) := by rw [hu]
  let U : ((ZMod p)[X] ⧸ I)ˣ :=
    ⟨mkC (↑u : ZMod p), mkC (↑u⁻¹ : ZMod p),
      by rw [← map_mul, Units.mul_inv, map_one],
      by rw [← map_mul, Units.inv_mul, map_one]⟩
  have hU : (↑U : (ZMod p)[X] ⧸ I) = mkC (((ε * (N : ℤ) : ℤ)) : ZMod p) := by
    show mkC (↑u : ZMod p) = mkC (((ε * (N : ℤ) : ℤ)) : ZMod p)
    rw [hu]
  refine isUnit_iff_exists_inv.mpr ⟨τ * ↑(U⁻¹), ?_⟩
  calc τ * (τ * ↑(U⁻¹)) = τ ^ 2 * ↑(U⁻¹) := by ring
    _ = mkC (((ε * (N : ℤ) : ℤ)) : ZMod p) * ↑(U⁻¹) := by rw [hτ2]
    _ = ↑U * ↑(U⁻¹) := by rw [hU]
    _ = 1 := Units.mul_inv U

/-- **Cancelling `τ`.**  In `R = (ZMod p)[X] ⧸ I` with `Φ_N ∈ I`, `p ∤ N`,
`τ^{p-1} = c(p)` where `c(p) = chiZ χ hsq (p : ZMod N)`. -/
theorem tau_pow_pred_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hsq : χ * χ = 1) (hne : χ ≠ 1) {ε : ℤ} (hε : χ (-1 : ZMod N) = (ε : ℂ))
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (I : Ideal (ZMod p)[X])
    (hI : Polynomial.cyclotomic N (ZMod p) ∈ I) :
    (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) ^ (p - 1)
      = ((Ideal.Quotient.mk I).comp Polynomial.C)
          ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) : ℤ) : ZMod p) := by
  classical
  set mkC : ZMod p →+* (ZMod p)[X] ⧸ I := (Ideal.Quotient.mk I).comp Polynomial.C with hmkC
  set cp : ZMod p :=
    ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) : ℤ) : ZMod p) with hcp
  set τ : (ZMod p)[X] ⧸ I := ∑ a : ZMod N, mkC
      ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
      * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val) with hτ
  have hunit : IsUnit τ := by
    rw [hτ, hmkC]
    exact _root_.Commons.NumberTheory.DirichletCharacter.isUnit_tau χ hχ hsq hne hε p hpN I hI
  have hpow : τ ^ p = mkC cp * τ := by
    rw [hτ, hmkC, hcp]
    exact _root_.Commons.NumberTheory.DirichletCharacter.tau_pow_eq_chiZ_mul_tau χ hsq p hpN I hI
  have hcp2 : mkC cp * mkC cp = 1 := by
    have hp : p.Coprime N := (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hpN
    have hpp : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).mpr hp
    rcases _root_.Commons.NumberTheory.DirichletCharacter.chiZ_eq_one_or_neg_one_of_isUnit χ hsq hpp
      with h | h
    · rw [hcp, h, show ((1 : ℤ) : ZMod p) = 1 by norm_num, map_one, mul_one]
    · rw [hcp, h, show ((-1 : ℤ) : ZMod p) = -1 by norm_num, map_neg, map_one]
      ring
  obtain ⟨w, hw⟩ := hunit
  let U : ((ZMod p)[X] ⧸ I)ˣ := ⟨mkC cp, mkC cp, hcp2, hcp2⟩
  have hU : (↑U : (ZMod p)[X] ⧸ I) = mkC cp := rfl
  have hwpow : w ^ p = U * w := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, hU, hw]
    exact hpow
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hwp : w ^ (p - 1) = U := by
    have h1 : w ^ (p - 1) * w = U * w := by
      rw [← pow_succ, show p - 1 + 1 = p by omega]
      exact hwpow
    exact mul_right_cancel h1
  have hfinal : (τ : (ZMod p)[X] ⧸ I) ^ (p - 1) = mkC cp := by
    rw [← hw, ← Units.val_pow_eq_pow_val, hwp]
  rw [hτ, hmkC, hcp]
  exact hfinal

/-- **Piece (1).**  For odd `p`, `τ^{p-1} = C^{(p-1)/2}` in `R`, where `C = ε·N`. -/
theorem tau_pow_pred_eq_C_pow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hsq : χ * χ = 1) (hne : χ ≠ 1) {ε : ℤ} (hε : χ (-1 : ZMod N) = (ε : ℂ))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) (I : Ideal (ZMod p)[X])
    (hI : Polynomial.cyclotomic N (ZMod p) ∈ I) :
    (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
        * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) ^ (p - 1)
      = (((Ideal.Quotient.mk I).comp Polynomial.C)
          (((ε * (N : ℤ) : ℤ)) : ZMod p)) ^ ((p - 1) / 2) := by
  classical
  set mkC : ZMod p →+* (ZMod p)[X] ⧸ I := (Ideal.Quotient.mk I).comp Polynomial.C with hmkC
  set τ : (ZMod p)[X] ⧸ I := ∑ a : ZMod N, mkC
      ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
      * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val) with hτ
  have hτ2 : τ ^ 2 = mkC (((ε * (N : ℤ) : ℤ)) : ZMod p) := by
    rw [hτ, hmkC]
    exact _root_.Commons.NumberTheory.DirichletCharacter.tau_sq_eq_C χ hχ hsq hne hε p I hI
  obtain ⟨k, hk⟩ := (Fact.out : Nat.Prime p).eq_two_or_odd'.resolve_left hp2
  have hk2 : p - 1 = 2 * k := by omega
  rw [hτ, hmkC, hk2, pow_mul, show 2 * k / 2 = k by omega]
  exact congrArg (fun x => x ^ k) hτ2

/-- **Pieces (2)+(3).**  `C^((p-1)/2)` is the Legendre symbol of `C = ε·N` for odd `p`. -/
theorem quadratic_chi_pow_eq_legendre {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) {ε : ℤ}
    (hε : χ (-1 : ZMod N) = (ε : ℂ)) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    (((ε * ((N : ℤ)) : ℤ) : ZMod p) ^ ((p - 1) / 2)) =
      ((quadraticChar (ZMod p) (((ε * ((N : ℤ))) : ℤ) : ZMod p) : ℤ) : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨k, hk⟩ := (Fact.out : Nat.Prime p).eq_two_or_odd'.resolve_left hp2
  have h := quadraticChar_eq_pow_of_char_ne_two' (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2) (((ε * ((N : ℤ)) : ℤ) : ZMod p))
  rw [ZMod.card p, show p / 2 = (p - 1) / 2 by omega] at h
  exact h.symm

/-- The map `mkC : ZMod p → (ZMod p)[X] ⧸ (Φ_N)` is injective. -/
lemma mkC_injective {N p : ℕ} [NeZero N] [Fact p.Prime] :
    Function.Injective (fun z : ZMod p =>
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.cyclotomic N (ZMod p)})).comp Polynomial.C) z) := by
  intro z w hzw
  have h0a : ((Ideal.Quotient.mk (Ideal.span {Polynomial.cyclotomic N (ZMod p)})).comp Polynomial.C) z
      - ((Ideal.Quotient.mk (Ideal.span {Polynomial.cyclotomic N (ZMod p)})).comp Polynomial.C) w = 0 :=
    sub_eq_zero.mpr hzw
  have h0 : ((Ideal.Quotient.mk (Ideal.span {Polynomial.cyclotomic N (ZMod p)})).comp Polynomial.C)
      (z - w) = 0 := by
    rw [map_sub]; exact h0a
  have hmem : Polynomial.C (z - w) ∈ Ideal.span {Polynomial.cyclotomic N (ZMod p)} :=
    (Ideal.Quotient.eq_zero_iff_mem).mp h0
  rw [Ideal.mem_span_singleton] at hmem
  have hsub : z - w = 0 := by
    by_contra hne
    have hCz : (Polynomial.C (z - w) : (ZMod p)[X]) ≠ 0 := by
      intro h
      exact hne (Polynomial.C_eq_zero.mp h)
    have hdeg : (Polynomial.cyclotomic N (ZMod p)).natDegree ≤ (Polynomial.C (z - w)).natDegree :=
      Polynomial.natDegree_le_of_dvd hmem hCz
    rw [Polynomial.natDegree_C] at hdeg
    have hphi : (Polynomial.cyclotomic N (ZMod p)).natDegree = N.totient :=
      Polynomial.natDegree_cyclotomic N (ZMod p)
    have htot : 0 < N.totient := Nat.totient_pos.mpr (NeZero.pos N)
    omega
  exact sub_eq_zero.mp hsub

/-- **The integral Gauss lemma.**  `c(p) = (χ(-1)·N / p)` for odd `p ∤ N`. -/
theorem chiZ_prime_eq_legendre {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    _root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N)
      = quadraticChar (ZMod p)
          (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
            ZMod p) := by
  classical
  set I : Ideal (ZMod p)[X] := Ideal.span {Polynomial.cyclotomic N (ZMod p)} with hI'
  have hI : Polynomial.cyclotomic N (ZMod p) ∈ I := Ideal.mem_span_singleton_self _
  have hε : χ (-1 : ZMod N) =
      (_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) : ℂ) :=
    _root_.Commons.NumberTheory.DirichletCharacter.chiZ_spec χ hsq (-1 : ZMod N)
  have hchain : ((Ideal.Quotient.mk I).comp Polynomial.C)
        ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) : ℤ) : ZMod p)
      = ((Ideal.Quotient.mk I).comp Polynomial.C)
        (((quadraticChar (ZMod p)
            (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
              ZMod p)) : ℤ) : ZMod p) := by
    calc ((Ideal.Quotient.mk I).comp Polynomial.C)
          ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) : ℤ) : ZMod p)
        = (∑ a : ZMod N, ((Ideal.Quotient.mk I).comp Polynomial.C)
            ((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq a : ℤ) : ZMod p)
            * (Ideal.Quotient.mk I Polynomial.X) ^ (a.val)) ^ (p - 1) :=
          (_root_.Commons.NumberTheory.DirichletCharacter.tau_pow_pred_eq χ hχ hsq hne hε p hpN I hI).symm
      _ = (((Ideal.Quotient.mk I).comp Polynomial.C)
            (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
              ZMod p)) ^ ((p - 1) / 2) :=
          _root_.Commons.NumberTheory.DirichletCharacter.tau_pow_pred_eq_C_pow χ hχ hsq hne hε p hp2 hpN I hI
      _ = ((Ideal.Quotient.mk I).comp Polynomial.C)
            (((((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
              ZMod p)) ^ ((p - 1) / 2)) := (map_pow _ _ _).symm
      _ = ((Ideal.Quotient.mk I).comp Polynomial.C)
            (((quadraticChar (ZMod p)
              (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
                ZMod p)) : ℤ) : ZMod p) := by
          rw [_root_.Commons.NumberTheory.DirichletCharacter.quadratic_chi_pow_eq_legendre χ hχ hsq hne hε p hp2 hpN]
  rw [hI'] at hchain
  have hcast : (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N)) : ℤ) : ZMod p)
      = (((quadraticChar (ZMod p)
          (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
            ZMod p)) : ℤ) : ZMod p) := mkC_injective hchain
  have ha : _root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) = 1 ∨
      _root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) = -1 :=
    _root_.Commons.NumberTheory.DirichletCharacter.chiZ_eq_one_or_neg_one_of_isUnit χ hsq
      ((ZMod.isUnit_iff_coprime p N).mpr ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hpN))
  have hb : quadraticChar (ZMod p)
        (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
          ZMod p) = 0 ∨
      quadraticChar (ZMod p)
        (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
          ZMod p) = 1 ∨
      quadraticChar (ZMod p)
        (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
          ZMod p) = -1 := by
    rcases eq_or_ne (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
        ZMod p) 0 with h | h
    · exact Or.inl ((quadraticChar_eq_zero_iff).mpr h)
    · have hsq1 : (quadraticChar (ZMod p)
            (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
              ZMod p)) * (quadraticChar (ZMod p)
            (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
              ZMod p)) = 1 := by
        simpa [pow_two] using quadraticChar_sq_one h
      rcases mul_self_eq_one_iff.mp hsq1 with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
  have hbound : |_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N)
      - quadraticChar (ZMod p)
        (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
          ZMod p)| ≤ 2 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb] <;> norm_num
  have hdvd : (p : ℤ) ∣ (_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N)
      - quadraticChar (ZMod p)
        (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
          ZMod p)) := by
    have h0 : (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N)
        - quadraticChar (ZMod p)
          (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
            ZMod p)) : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub, hcast, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  rcases eq_or_ne (_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N))
      (quadraticChar (ZMod p)
        (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
          ZMod p)) with h | h
  · exact h
  · exfalso
    obtain ⟨t, ht⟩ := hdvd
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [mul_zero] at ht
      exact h (sub_eq_zero.mp ht)
    have ht1 : (1 : ℤ) ≤ |t| := by have := abs_pos.mpr ht0; omega
    have habs : |_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N)
        - quadraticChar (ZMod p)
          (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
            ZMod p)| = |(p : ℤ)| * |t| := by rw [ht, abs_mul]
    have hpabs : |(p : ℤ)| = (p : ℤ) := abs_of_nonneg (by positivity)
    have hp3 : (3 : ℤ) ≤ (p : ℤ) := by
      have := (Fact.out : Nat.Prime p).two_le
      omega
    nlinarith [habs, hpabs, ht1, hbound, hp3]

/-- **The Gauss lemma.**
  For a primitive quadratic character `χ` modulo `N` and an
odd prime `p ∤ N`, the value `χ(p)` is the Legendre symbol of `χ(-1)·N` modulo `p`. -/
theorem quadratic_chi_prime_value {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ)
    [Fact p.Prime] (hp : p ≠ 2) (hpN : ¬ p ∣ N) (hχ : χ.IsPrimitive) (hsq : χ * χ = 1)
    (hne : χ ≠ 1) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ χ (-1 : ZMod N) = (ε : ℂ) ∧
      χ (p : ZMod N) = ((quadraticChar (ZMod p) (((ε * (N : ℤ)) : ℤ) : ZMod p) : ℤ) : ℂ) := by
  refine ⟨_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N), ?_, ?_, ?_⟩
  · exact _root_.Commons.NumberTheory.DirichletCharacter.chiZ_eq_one_or_neg_one_of_isUnit χ hsq
      isUnit_neg_one
  · exact _root_.Commons.NumberTheory.DirichletCharacter.chiZ_spec χ hsq (-1 : ZMod N)
  · rw [_root_.Commons.NumberTheory.DirichletCharacter.chiZ_spec χ hsq (p : ZMod N)]
    exact congrArg (fun m : ℤ => (m : ℂ))
      (chiZ_prime_eq_legendre χ hχ hsq hne p hp hpN)

/-- **Splitting law at primes (root count).**  For an odd prime `p ∤ N`, the number of square
roots of `χ(-1)·N` modulo `p` is `1 + χ(p)`: this is the local splitting datum of the quadratic
field `ℚ(√(χ(-1)N))`. -/
theorem card_sqrt_eq_one_add_chiZ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    ((Finset.univ.filter (fun x : ZMod p =>
        x ^ 2 = (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N)
          * (N : ℤ) : ℤ)) : ZMod p))).card : ℤ)
      = 1 + _root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h := quadraticChar_card_sqrts (F := ZMod p) hchar
    (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N) * (N : ℤ) : ℤ)) :
      ZMod p)
  rw [Set.toFinset_setOf] at h
  rw [h, ← _root_.Commons.NumberTheory.DirichletCharacter.chiZ_prime_eq_legendre χ hχ hsq hne p hp2 hpN]
  ring

/-- The monic linear divisors of `X² - c` are exactly the `X - r` with `r² = c`. -/
theorem ncard_linear_monic_divisors_eq_card_roots (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (c : ZMod p) :
    Set.ncard {d : Polynomial (ZMod p) |
        d.Monic ∧ d ∣ (Polynomial.X ^ 2 - Polynomial.C c) ∧ d.natDegree = 1}
      = Nat.card {r : ZMod p // r ^ 2 = c} := by
  classical
  have hinj : Function.Injective (fun r : ZMod p => Polynomial.X - Polynomial.C r) := by
    intro a b h
    have h' := congrArg (fun q : Polynomial (ZMod p) => q.coeff 0) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub] at h'
    exact neg_inj.mp h'
  have hset : {d : Polynomial (ZMod p) |
        d.Monic ∧ d ∣ (Polynomial.X ^ 2 - Polynomial.C c) ∧ d.natDegree = 1}
      = (fun r : ZMod p => Polynomial.X - Polynomial.C r) '' {r : ZMod p | r ^ 2 = c} := by
    ext d
    constructor
    · rintro ⟨hmon, hdvd, hdeg⟩
      refine ⟨-(d.coeff 0), ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        have hd : d = Polynomial.X - Polynomial.C (-(d.coeff 0)) := by
          rw [hmon.eq_X_add_C hdeg]
          simp
        rw [hd, Polynomial.dvd_iff_isRoot] at hdvd
        have := hdvd
        simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C] at this
        linear_combination this
      · rw [hmon.eq_X_add_C hdeg]
        simp
    · rintro ⟨r, hr, rfl⟩
      refine ⟨Polynomial.monic_X_sub_C r, ?_, ?_⟩
      · rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
          sub_eq_zero]
        rw [hr]
      · simp
  rw [hset, Set.ncard_image_of_injective _ hinj]
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- **Splitting law at primes, ideal form.**  For an odd prime `p ∤ N`, the number of monic
linear divisors of `X² - χ(-1)·N` over `ZMod p` is `1 + χ(p)` (equivalently: the number of
ideals of index `p` in `(ZMod p)[X]/(X² - χ(-1)·N)`, i.e. the local splitting datum of
`ℚ(√(χ(-1)N))`). -/
theorem card_linear_monic_divisors_eq_one_add_chiZ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    (Set.ncard {d : Polynomial (ZMod p) |
        d.Monic ∧ d ∣ (Polynomial.X ^ 2 - Polynomial.C
          (((_root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (-1 : ZMod N)
            * (N : ℤ) : ℤ)) : ZMod p)) ∧ d.natDegree = 1} : ℤ)
      = 1 + _root_.Commons.NumberTheory.DirichletCharacter.chiZ χ hsq (p : ZMod N) := by
  classical
  rw [ncard_linear_monic_divisors_eq_card_roots p hp2 _]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_sqrt_eq_one_add_chiZ χ hχ hsq hne p hp2 hpN

/-- **Item 1, first piece.**  An ideal whose quotient has `p` elements contains `p`. -/
theorem prime_mem_ideal_of_card_quotient {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime]
    (I : Ideal A) (h : Nat.card (A ⧸ I) = p) : (p : A) ∈ I := by
  haveI : Finite (A ⧸ I) :=
    Nat.finite_of_card_ne_zero (by rw [h]; exact (Fact.out : Nat.Prime p).ne_zero)
  haveI : Fintype (A ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (A ⧸ I) = p := by
    rw [← Nat.card_eq_fintype_card]; exact h
  have h2 : (p : A ⧸ I) = 0 := by
    have h3 : (p : A ⧸ I) = p • (1 : A ⧸ I) := by rw [nsmul_eq_mul, mul_one]
    rw [h3, ← hcard]
    exact card_nsmul_eq_zero
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h2
/-- The defining relation of the order `ℤ[√C] = AdjoinRoot (X² - C)`: the root squares to `C`. -/
theorem adjoinRoot_root_sq (C : ℤ) :
    (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ)) ^ 2
      = algebraMap ℤ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ)) C := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  exact sub_eq_zero.mp h
/-- The image of `root` in `A ⧸ pA` still squares to `C`: this is the well-definedness input for
the base change `(ZMod p)[X] →+* A ⧸ pA`, `X ↦ image of root`. -/
theorem quotient_root_sq (C : ℤ) (p : ℕ) :
    (Ideal.Quotient.mk (Ideal.span {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))})
        (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))) ^ 2
      = algebraMap ℤ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ) ⧸
          Ideal.span {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))}) C := by
  rw [← map_pow, _root_.Commons.NumberTheory.DirichletCharacter.adjoinRoot_root_sq]
  rfl
/-- **The base-change scalar hom.**  `σ : ZMod p →+* A ⧸ pA` for `A = ℤ[√C]`, built by
descending the composite `ℤ → A → A ⧸ pA` (which kills `p`) through `ZMod p = ℤ ⧸ (p)`.
No `Algebra (ZMod p) (A ⧸ pA)` instance is needed (there is none). -/
noncomputable def sigma (C : ℤ) (p : ℕ) :
    ZMod p →+* (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ)) ⧸
      Ideal.span {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))} :=
  (Ideal.Quotient.lift (Ideal.span {((p : ℕ) : ℤ)})
    ((Ideal.Quotient.mk (Ideal.span
        {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))})).comp
      (algebraMap ℤ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨k, rfl⟩ := ha
      simp only [RingHom.comp_apply, map_mul]
      have hp0 : (Ideal.Quotient.mk (Ideal.span
          {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))})
          (algebraMap ℤ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))
            ((p : ℕ) : ℤ))) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        simpa using Ideal.mem_span_singleton_self
          ((p : ℕ) : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))
      rw [hp0, zero_mul])).comp
    (Int.quotientSpanNatEquivZMod p).symm.toRingHom
/-- The value of the base-change scalar hom on integer classes. -/
lemma sigma_intCast_spec (C : ℤ) (p : ℕ) (a : ℤ) :
    sigma C p ((a : ℤ) : ZMod p)
      = Ideal.Quotient.mk (Ideal.span {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))})
        (algebraMap ℤ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ)) a) := by
  have h := Int.quotientSpanNatEquivZMod_comp_castRingHom p
  have h2 : (Int.quotientSpanNatEquivZMod p).symm.toRingHom ((a : ℤ) : ZMod p)
      = Ideal.Quotient.mk (Ideal.span {((p : ℕ) : ℤ)}) a := by
    have h3 := congrArg (fun f : ℤ →+* (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) => f a) h
    simpa using h3
  rw [sigma, RingHom.comp_apply, h2, Ideal.Quotient.lift_mk]
  rfl

/-- The base-change evaluation kills `X² - C` (mod `p`). -/
lemma eval₂_X_sq_sub_C_eq_zero (C : ℤ) (p : ℕ) :
    Polynomial.eval₂ (sigma C p)
      (Ideal.Quotient.mk (Ideal.span {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))})
        (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ)))
      (Polynomial.X ^ 2 - Polynomial.C (((C : ℤ)) : ZMod p)) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    sigma_intCast_spec, quotient_root_sq, sub_eq_zero]
  exact IsScalarTower.algebraMap_apply ℤ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))
    (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ) ⧸
      Ideal.span {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))}) C

/-- **The base change.**  `(ZMod p)[X] ⧸ (X² - C) →+* ℤ[√C] ⧸ p`. -/
noncomputable def baseChange (C : ℤ) (p : ℕ) :
    (ZMod p)[X] ⧸ Ideal.span {Polynomial.X ^ 2 - Polynomial.C (((C : ℤ)) : ZMod p)} →+*
      AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ) ⧸
        Ideal.span {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))} :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (sigma C p)
    (Ideal.Quotient.mk (Ideal.span {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))})
      (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ)))) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, show Polynomial.eval₂RingHom (sigma C p)
        (Ideal.Quotient.mk (Ideal.span
          {(p : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ))})
          (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C C : Polynomial ℤ)))
        (Polynomial.X ^ 2 - Polynomial.C (((C : ℤ)) : ZMod p)) = 0
      from eval₂_X_sq_sub_C_eq_zero C p, zero_mul])

lemma exists_finset_lattice_disc (ω : ℂ) {R : ℝ} (hR : 16 * (‖ω‖ + 1) ≤ R) :
    ∃ S : Finset (ℤ × ℤ), R ^ 2 / (16 * (‖ω‖ + 1)) ≤ (S.card : ℝ) ∧
      ∀ x ∈ S, ‖(x.1 : ℂ) + (x.2 : ℂ) * ω‖ ≤ R := by
  have hω1 : (0:ℝ) < ‖ω‖ + 1 := by positivity
  have hRpos : 0 < R := by nlinarith
  have hA16 : 16 ≤ R := by nlinarith [norm_nonneg ω]
  set A : ℕ := ⌊R / 4⌋₊ with hA
  set B : ℕ := ⌊R / (4 * (‖ω‖ + 1))⌋₊ with hB
  have hA_ge : R / 8 ≤ (A : ℝ) := by
    rw [hA]
    have h1 : R / 4 - 1 ≤ (⌊R / 4⌋₊ : ℝ) := by
      have := Nat.floor_le (show (0:ℝ) ≤ R / 4 by positivity)
      have h2 : (⌊R / 4⌋₊ : ℝ) + 1 > R / 4 := Nat.lt_floor_add_one _
      linarith
    have h3 : R / 8 ≤ R / 4 - 1 := by linarith
    linarith
  have hB_ge : R / (8 * (‖ω‖ + 1)) ≤ (B : ℝ) := by
    rw [hB]
    have hpos : 0 < 4 * (‖ω‖ + 1) := by positivity
    have h1 : R / (4 * (‖ω‖ + 1)) - 1 ≤ (⌊R / (4 * (‖ω‖ + 1))⌋₊ : ℝ) := by
      have := Nat.floor_le (show (0:ℝ) ≤ R / (4 * (‖ω‖ + 1)) by positivity)
      have h2 : (⌊R / (4 * (‖ω‖ + 1))⌋₊ : ℝ) + 1 > R / (4 * (‖ω‖ + 1)) :=
        Nat.lt_floor_add_one _
      linarith
    have h3 : R / (8 * (‖ω‖ + 1)) ≤ R / (4 * (‖ω‖ + 1)) - 1 := by
      have h4 : (0:ℝ) < 4 * (‖ω‖ + 1) := by positivity
      have h8 : (0:ℝ) < 8 * (‖ω‖ + 1) := by positivity
      rw [div_le_iff₀ h8, div_sub_one h4.ne']
      rw [show (R - 4 * (‖ω‖ + 1)) / (4 * (‖ω‖ + 1)) * (8 * (‖ω‖ + 1))
          = 2 * (R - 4 * (‖ω‖ + 1)) by
        field_simp
        ring]
      nlinarith [hR]
    linarith
  refine ⟨(Finset.Icc (-(A : ℤ)) (A : ℤ)) ×ˢ (Finset.Icc (-(B : ℤ)) (B : ℤ)), ?_, ?_⟩
  · rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    have h1 : ((A : ℤ) + 1 - -(A : ℤ)).toNat = 2 * A + 1 := by
      have : ((A : ℤ) + 1 - -(A : ℤ)) = 2 * (A : ℤ) + 1 := by ring
      rw [this]
      omega
    have h2 : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by
      have : ((B : ℤ) + 1 - -(B : ℤ)) = 2 * (B : ℤ) + 1 := by ring
      rw [this]
      omega
    rw [h1, h2]
    push_cast
    have hA1 : 1 ≤ (A : ℝ) := by linarith [hA_ge, hRpos]
    have hB1 : 0 ≤ (B : ℝ) := by positivity
    have hexp : (2 * (A:ℝ) + 1) * (2 * (B:ℝ) + 1) ≥ 4 * (A:ℝ) * (B:ℝ) := by nlinarith
    have hAB : 4 * (A:ℝ) * (B:ℝ) ≥ 4 * (R / 8) * (R / (8 * (‖ω‖ + 1))) := by
      have h4 : (0:ℝ) ≤ R / (8 * (‖ω‖ + 1)) := by positivity
      have h5 : (0:ℝ) ≤ (A:ℝ) := by positivity
      have := mul_le_mul hA_ge hB_ge h4 h5
      nlinarith [this]
    have : 4 * (R / 8) * (R / (8 * (‖ω‖ + 1))) = R ^ 2 / (16 * (‖ω‖ + 1)) := by
      field_simp
      ring
    linarith [hexp, hAB, this.le, this.ge]
  · rintro ⟨a, b⟩ hx
    rw [Finset.mem_product] at hx
    obtain ⟨ha, hb⟩ := hx
    rw [Finset.mem_Icc] at ha hb
    have ha1 : |(a : ℝ)| ≤ R / 4 := by
      have hA' : (A : ℝ) ≤ R / 4 := Nat.floor_le (by positivity)
      have : (a : ℝ) ≤ (A : ℝ) := by exact_mod_cast ha.2
      have : -(A : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.1
      rw [abs_le]
      constructor <;> linarith
    have hb1 : |(b : ℝ)| ≤ R / (4 * (‖ω‖ + 1)) := by
      have hB' : (B : ℝ) ≤ R / (4 * (‖ω‖ + 1)) := Nat.floor_le (by positivity)
      have : (b : ℝ) ≤ (B : ℝ) := by exact_mod_cast hb.2
      have : -(B : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.1
      rw [abs_le]
      constructor <;> linarith
    have h1 : ((a : ℤ) : ℂ) = (a : ℂ) := by simp
    simp only [h1]
    calc ‖(a : ℂ) + (b : ℂ) * ω‖ ≤ ‖(a : ℂ)‖ + ‖(b : ℂ) * ω‖ := norm_add_le _ _
      _ = |(a : ℝ)| + |(b : ℝ)| * ‖ω‖ := by
          rw [Complex.norm_intCast, norm_mul, Complex.norm_intCast]
      _ ≤ R / 4 + R / (4 * (‖ω‖ + 1)) * ‖ω‖ := by
          have := mul_le_mul_of_nonneg_right hb1 (norm_nonneg ω)
          linarith
      _ ≤ R := by
          have hωnn : 0 ≤ ‖ω‖ := norm_nonneg ω
          have h1 : R / (4 * (‖ω‖ + 1)) * ‖ω‖ ≤ R / 4 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (‖ω‖ + 1))]
            nlinarith [hωnn, hRpos]
          linarith

/-- **The `ℤ`-span of `{1, ω}` is closed under multiplication.**  For any commutative ring `R`
with `ω ^ 2 - ω + (1 - D) / 4 = 0`, the product of `a + bω` and `c + dω` is again of that form,
with witnesses `p = ac - bd(1-D)/4` and `q = ad + bc + bd`. -/
theorem mul_zspan_root_quadratic (R : Type*) [CommRing R] (D : ℤ) (ω : R)
    (hω : ω ^ 2 - ω + ((1 - D) / 4 : ℤ) = 0) (a b c d : ℤ) :
    ∃ p q : ℤ, ((a : R) + (b : R) * ω) * ((c : R) + (d : R) * ω)
      = (p : R) + (q : R) * ω := by
  refine ⟨a * c - b * d * ((1 - D) / 4), a * d + b * c + b * d, ?_⟩
  have h : ω * ω = ω - ((1 - D) / 4 : ℤ) := by linear_combination hω
  push_cast
  rw [show ((a : R) + (b : R) * ω) * ((c : R) + (d : R) * ω)
      = (a : R) * (c : R) + (a : R) * (d : R) * ω + (b : R) * ω * (c : R)
        + (b : R) * (d : R) * (ω * ω) from by ring]
  rw [h]
  ring

/-- **The order `ℤ[ω]`**, as a named subring: the `ℤ`-span of `{1, ω}` inside a commutative ring
with an element `ω` satisfying `ω ^ 2 - ω + (1 - D) / 4 = 0`.  (`ω = (1 + √D)/2` in the intended
application; the multiplication closure is `mul_zspan_root_quadratic`.) -/
def zspanRoot (R : Type*) [CommRing R] (D : ℤ) (ω : R)
    (hω : ω ^ 2 - ω + ((1 - D) / 4 : ℤ) = 0) : Subring R where
  carrier := {x : R | ∃ a b : ℤ, x = (a : R) + (b : R) * ω}
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact mul_zspan_root_quadratic R D ω hω a b c d
  one_mem' := ⟨1, 0, by ring⟩
  zero_mem' := ⟨0, 0, by ring⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩

/-- **The `⊆` half of maximality: elements of `ℤ[ω]` are integral over `ℤ`.**

Every `x = a + bω` (`a b : ℤ`) satisfies the *monic* quadratic
`T ^ 2 - (2a + b) T + (a ^ 2 + a b + b ^ 2 (1 - D) / 4) = 0`, whose coefficients are integers —
here written out as an identity in an arbitrary commutative ring `R` with
`ω ^ 2 - ω + (1 - D) / 4 = 0`.  (The two coefficients are `tr` and `N` of `x`: `x + x' = 2a + b`
and `x x' = a ^ 2 + a b + b ^ 2 (1 - D) / 4`.) -/
theorem sq_sub_mul_add_eq_zero_zspan_root (R : Type*) [CommRing R] (D : ℤ) (ω : R)
    (hω : ω ^ 2 - ω + ((1 - D) / 4 : ℤ) = 0) (a b : ℤ) :
    ((a : R) + (b : R) * ω) ^ 2 - ((2 * a + b : ℤ) : R) * ((a : R) + (b : R) * ω)
      + ((a ^ 2 + a * b + b ^ 2 * ((1 - D) / 4) : ℤ) : R) = 0 := by
  have h : ω ^ 2 = ω - ((1 - D) / 4 : ℤ) := by linear_combination hω
  push_cast
  ring_nf
  rw [h]
  ring

/-- **Wrapper: elements of `ℤ[ω]` have a monic integer annihilating polynomial.**

Packages `sq_sub_mul_add_eq_zero_zspan_root` as the statement that `x ∈ ℤ[ω]` is a root of a
monic polynomial with integer coefficients: the witnesses are `X ^ 2 - C (tr x) * X + C (N x)`,
which are integers because `tr x = 2a + b` and `N x = a ^ 2 + a b + b ^ 2 (1 - D) / 4`. -/
theorem exists_monic_int_aeval_eq_zero_of_mem_zspanRoot (R : Type*) [CommRing R] (D : ℤ) (ω : R)
    (hω : ω ^ 2 - ω + ((1 - D) / 4 : ℤ) = 0) {x : R} (hx : x ∈ zspanRoot R D ω hω) :
    ∃ p : Polynomial ℤ, p.Monic ∧ Polynomial.aeval x (p.map (algebraMap ℤ R)) = 0 := by
  rcases hx with ⟨a, b, rfl⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 * a + b) * Polynomial.X
      + Polynomial.C (a ^ 2 + a * b + b ^ 2 * ((1 - D) / 4)), ?_, ?_⟩
  · monicity <;> norm_num
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact sq_sub_mul_add_eq_zero_zspan_root R D ω hω a b

noncomputable def quadPoly (D : ℤ) : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((1 - D) / 4 : ℤ) : ℚ)

example (D : ℤ) : (quadPoly D).Monic := by
  rw [quadPoly]
  monicity <;> norm_num

/-- **Extraction of rational coordinates in a quadratic `AdjoinRoot` (Route A).**

Every class `AdjoinRoot.mk (quadPoly D) P` is also `AdjoinRoot.mk (quadPoly D) (C p + C q * X)`.
(The `ℚ`-linear form `algebraMap ℚ _ p + algebraMap ℚ _ q * root` is recovered by
`AdjoinRoot.mk_C`, `mk_X`, `algebraMap_eq`.) -/
lemma exists_rat_coeff_adjoinRoot_mk (D : ℤ) (P : Polynomial ℚ) :
    ∃ p q : ℚ, AdjoinRoot.mk (quadPoly D) P
      = AdjoinRoot.mk (quadPoly D) (Polynomial.C p + Polynomial.C q * Polynomial.X) := by
  have hfmonic : (quadPoly D).Monic := by rw [quadPoly]; monicity <;> norm_num
  have hfdeg : (quadPoly D).natDegree = 2 := by rw [quadPoly]; compute_degree!
  have hfne : quadPoly D ≠ 1 := by
    intro h1
    have h2 : (quadPoly D).natDegree = (1 : Polynomial ℚ).natDegree := by rw [h1]
    rw [hfdeg] at h2
    simp at h2
  refine ⟨(P %ₘ quadPoly D).coeff 0, (P %ₘ quadPoly D).coeff 1, ?_⟩
  have hmain : AdjoinRoot.mk (quadPoly D) P = AdjoinRoot.mk (quadPoly D) (P %ₘ quadPoly D) := by
    have h2 : P = P %ₘ quadPoly D + quadPoly D * (P /ₘ quadPoly D) :=
      (Polynomial.modByMonic_add_div P (quadPoly D)).symm
    conv_lhs => rw [h2]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  rw [hmain]
  refine congrArg (AdjoinRoot.mk (quadPoly D)) ?_
  have hlt : (P %ₘ quadPoly D).natDegree < 2 := by
    have h := Polynomial.natDegree_modByMonic_lt P hfmonic hfne
    rwa [hfdeg] at h
  ext n
  rcases n with _ | _ | k
  · simp [Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_monomial]
  · simp [Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_monomial]
  · have hz : (P %ₘ quadPoly D).coeff (k + 2) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_monomial, hz]

/-- **The `ℚ`-linear form of the extraction.**  Every `x` in `AdjoinRoot (quadPoly D)` is
`algebraMap ℚ _ p + algebraMap ℚ _ q * AdjoinRoot.root (quadPoly D)` for some `p q : ℚ`
(obtained from `exists_rat_coeff_adjoinRoot_mk` via `mk_C`, `mk_X`, `algebraMap_eq`). -/
lemma exists_rat_coeff_root (D : ℤ) (x : AdjoinRoot (quadPoly D)) :
    ∃ p q : ℚ, x = algebraMap ℚ (AdjoinRoot (quadPoly D)) p
      + algebraMap ℚ (AdjoinRoot (quadPoly D)) q * AdjoinRoot.root (quadPoly D) := by
  refine AdjoinRoot.induction_on (quadPoly D) x ?_
  intro P
  obtain ⟨p, q, hpq⟩ := exists_rat_coeff_adjoinRoot_mk D P
  refine ⟨p, q, ?_⟩
  rw [hpq]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]

/-- **The defining relation of `ω = root (quadPoly D)`:** `ω ^ 2 - ω + (1 - D) / 4 = 0`. -/
lemma root_quadPoly_sq (D : ℤ) :
    (AdjoinRoot.root (quadPoly D)) ^ 2 - AdjoinRoot.root (quadPoly D)
      + algebraMap ℚ (AdjoinRoot (quadPoly D)) (((1 - D) / 4 : ℤ) : ℚ) = 0 := by
  have h := AdjoinRoot.eval₂_root (quadPoly D)
  rw [quadPoly] at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at h
  exact h

/-- The degree of `quadPoly D` is `2`. -/
lemma quadPoly_natDegree (D : ℤ) : (quadPoly D).natDegree = 2 := by
  rw [quadPoly]; compute_degree!

/-- **Expansion in the `{1, ω}` basis (abstract form).** -/
theorem zspan_root_quadratic_expansion (R : Type*) [CommRing R] (D : ℤ) (ω : R)
    (hω : ω ^ 2 - ω + ((1 - D) / 4 : ℤ) = 0) (u v A B : R) :
    (u + v * ω) ^ 2 + A * (u + v * ω) + B
      = (u ^ 2 - v ^ 2 * (((1 - D) / 4 : ℤ) : R) + A * u + B)
        + (2 * u * v + v ^ 2 + A * v) * ω := by
  linear_combination (v ^ 2) * hω

/-- **`{1, ω}` is `ℚ`-linearly independent in `AdjoinRoot (quadPoly D)`.** -/
lemma root_add_mul_root_eq_zero (D : ℤ) {A B : ℚ}
    (h : algebraMap ℚ (AdjoinRoot (quadPoly D)) A
      + algebraMap ℚ (AdjoinRoot (quadPoly D)) B * AdjoinRoot.root (quadPoly D) = 0) :
    A = 0 ∧ B = 0 := by
  have h' : AdjoinRoot.mk (quadPoly D) (Polynomial.C A + Polynomial.C B * Polynomial.X) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    exact h
  have hdvd : quadPoly D ∣ (Polynomial.C A + Polynomial.C B * Polynomial.X : Polynomial ℚ) :=
    (AdjoinRoot.mk_eq_zero (f := quadPoly D)).mp h'
  have hdeg : (Polynomial.C A + Polynomial.C B * Polynomial.X : Polynomial ℚ).natDegree < 2 := by
    compute_degree!
  have hP : (Polynomial.C A + Polynomial.C B * Polynomial.X : Polynomial ℚ) = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (by rw [quadPoly_natDegree]; exact hdeg)
  constructor
  · simpa using congrArg (fun p : Polynomial ℚ => p.coeff 0) hP
  · simpa using congrArg (fun p : Polynomial ℚ => p.coeff 1) hP
open scoped ComplexOrder
open Filter Topology

variable {N : ℕ} [NeZero N]

lemma LSeries_zetaMul_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (χ.zetaMul : ℕ → ℂ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have h2 : LSeriesSummable (↑(toArithmeticFunction (fun n : ℕ => χ (n : ZMod N))) : ℕ → ℂ) s :=
    (LSeriesSummable_congr s fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  rw [DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul, LSeries_convolution']
  · rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    congr 1
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact (LSeries_congr (fun {n} hn => χ.apply_eq_toArithmeticFunction_apply hn) s).symm
  · exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  · exact h2

lemma zetaMul_im_eq_zero (χ : DirichletCharacter ℂ N) (hχ : χ ^ 2 = 1) (n : ℕ) :
    (χ.zetaMul n).im = 0 := by
  have h := zetaMul_nonneg hχ n
  simpa using h.2.symm

lemma div_ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) (m : ℝ) :
    (z / (m : ℂ)).re = z.re / m := by
  rw [Complex.div_re, hz, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  by_cases hm : m = 0
  · simp [hm]
  · field_simp
    ring

lemma LSeries_zetaMul_re_eq (χ : DirichletCharacter ℂ N) (hχ : χ ^ 2 = 1) {σ : ℝ} (hσ : 1 < σ) :
    (LSeries (χ.zetaMul : ℕ → ℂ) (σ : ℂ)).re = ∑' n : ℕ, (χ.zetaMul n).re / (n : ℝ) ^ σ := by
  have hsum : LSeriesSummable (χ.zetaMul : ℕ → ℂ) (σ : ℂ) :=
    DirichletCharacter.LSeriesSummable_zetaMul χ (by simpa using hσ)
  rw [LSeries, Complex.re_tsum hsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    have hcast : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by simp
    rw [hcast, ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
    exact div_ofReal_re_of_im_eq_zero (zetaMul_im_eq_zero χ hχ n) _

lemma rpow_diff_bound {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) {j : ℕ} (hj : 2 ≤ j) :
    σ * (j : ℝ) ^ (-σ) ≤ (((j : ℝ) - 1) ^ (-σ) - (j : ℝ) ^ (-σ)) * ((j : ℝ) - 1) := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
  have hj1pos : (0 : ℝ) < (j : ℝ) - 1 := by linarith
  have hle : -1 ≤ 1 / ((j : ℝ) - 1) := by
    rw [le_div_iff₀ hj1pos]
    linarith
  have hber : 1 + σ * (1 / ((j : ℝ) - 1)) ≤ (1 + 1 / ((j : ℝ) - 1)) ^ σ :=
    one_add_mul_self_le_rpow_one_add hle (le_of_lt h1)
  have hratio : (1 : ℝ) + 1 / ((j : ℝ) - 1) = (j : ℝ) / ((j : ℝ) - 1) := by
    field_simp
    ring
  have hkey : ((j : ℝ) - 1) ^ (-σ) =
      (j : ℝ) ^ (-σ) * ((j : ℝ) / ((j : ℝ) - 1)) ^ σ := by
    rw [Real.rpow_neg (le_of_lt hjpos), ← Real.inv_rpow (le_of_lt hjpos) σ,
      ← Real.mul_rpow (inv_nonneg.mpr (le_of_lt hjpos)) (by positivity :
        0 ≤ (j : ℝ) / ((j : ℝ) - 1)),
      Real.rpow_neg (by linarith : (0:ℝ) ≤ (j : ℝ) - 1),
      ← Real.inv_rpow (by linarith : (0:ℝ) ≤ (j : ℝ) - 1) σ]
    congr 1
    field_simp
  have hb1 : σ / ((j : ℝ) - 1) ≤ ((j : ℝ) / ((j : ℝ) - 1)) ^ σ - 1 := by
    have h := hber
    rw [hratio, mul_one_div] at h
    linarith
  have h4 : σ / ((j : ℝ) - 1) * ((j : ℝ) - 1) = σ := by
    field_simp
  have h3 : σ ≤ (((j : ℝ) / ((j : ℝ) - 1)) ^ σ - 1) * ((j : ℝ) - 1) := by
    have := mul_le_mul_of_nonneg_right hb1 (le_of_lt hj1pos)
    rw [h4] at this
    exact this
  rw [hkey, show (j : ℝ) ^ (-σ) * ((j : ℝ) / ((j : ℝ) - 1)) ^ σ - (j : ℝ) ^ (-σ)
      = (j : ℝ) ^ (-σ) * (((j : ℝ) / ((j : ℝ) - 1)) ^ σ - 1) by ring,
    show (j : ℝ) ^ (-σ) * (((j : ℝ) / ((j : ℝ) - 1)) ^ σ - 1) * ((j : ℝ) - 1)
      = (j : ℝ) ^ (-σ) * ((((j : ℝ) / ((j : ℝ) - 1)) ^ σ - 1) * ((j : ℝ) - 1)) by ring]
  have := mul_le_mul_of_nonneg_left h3 (le_of_lt (Real.rpow_pos_of_pos hjpos (-σ)))
  simpa [mul_comm] using this

lemma sum_Ico_succ_shift (f : ℕ → ℝ) {T n : ℕ} (h : T + 1 ≤ n) :
    ∑ j ∈ Finset.Ico (T + 1) n, f j = ∑ i ∈ Finset.Ico T (n - 1), f (i + 1) := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr ?_ ?_
  · congr 1
    omega
  · intro k _
    congr 1
    omega

lemma by_parts_ineq {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (hb0 : b 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    {T : ℕ} (hT : 2 ≤ T) (hpart : ∀ k, T ≤ k → A * (k : ℝ) ≤ ∑ j ∈ Finset.Icc 1 k, b j)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) {n : ℕ} (hn : T + 1 ≤ n) :
    A * σ * (∑ j ∈ Finset.Ico (T + 1) n, (j : ℝ) ^ (-σ)) ≤
      ∑ i ∈ Finset.range n, b i * (i : ℝ) ^ (-σ) := by
  have hpart' : ∀ k, T ≤ k → A * (k : ℝ) ≤ ∑ j ∈ Finset.range (k + 1), b j := by
    intro k hk
    have h2 : ∑ j ∈ Finset.range (k + 1), b j = ∑ j ∈ Finset.Icc 1 k, b j := by
      rw [Finset.sum_range_succ', hb0, add_zero,
        ← Finset.Ico_add_one_right_eq_Icc (a := 1) (b := k), Finset.sum_Ico_eq_sum_range,
        Nat.add_sub_cancel]
      exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])
    rw [h2]
    exact hpart k hk
  have hbp := Finset.sum_range_by_parts (fun i : ℕ => (i : ℝ) ^ (-σ)) b n
  simp only [smul_eq_mul] at hbp
  have hmain : ∑ i ∈ Finset.range n, b i * (i : ℝ) ^ (-σ)
      = ((n : ℝ) - 1) ^ (-σ) * (∑ j ∈ Finset.range n, b j)
        + ∑ i ∈ Finset.range (n - 1),
            ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * (∑ j ∈ Finset.range (i + 1), b j) := by
    rw [show (∑ i ∈ Finset.range n, b i * (i : ℝ) ^ (-σ))
        = ∑ i ∈ Finset.range n, (i : ℝ) ^ (-σ) * b i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _), hbp]
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast
    ring
  rw [hmain]
  -- pointwise bound
  have hterm : ∀ i ∈ Finset.Ico T (n - 1),
      A * σ * ((i + 1 : ℕ) : ℝ) ^ (-σ) ≤
        ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * (∑ j ∈ Finset.range (i + 1), b j) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have hiT : T ≤ i := hi.1
    have h1 : A * (i : ℝ) ≤ ∑ j ∈ Finset.range (i + 1), b j := hpart' i hiT
    have hD : 0 ≤ (i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ) := by
      have hi1 : (0 : ℝ) < (i : ℝ) := by
        have : 1 ≤ i := by omega
        exact_mod_cast this
      have hle : ((i : ℝ) + 1) ^ (-σ) ≤ (i : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hi1 (by linarith) (by linarith : -σ ≤ 0)
      linarith
    have h2 : σ * ((i : ℝ) + 1) ^ (-σ) ≤
        ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * (i : ℝ) := by
      have hb := rpow_diff_bound hσ1 hσ2 (j := i + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hb
      rw [show ((i : ℝ) + 1 - 1) = (i : ℝ) by ring] at hb
      exact hb
    rw [show ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 by push_cast; ring]
    calc A * σ * ((i : ℝ) + 1) ^ (-σ)
        = A * (σ * ((i : ℝ) + 1) ^ (-σ)) := by ring
      _ ≤ A * (((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * (i : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hA
      _ = ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * (A * (i : ℝ)) := by ring
      _ ≤ ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * (∑ j ∈ Finset.range (i + 1), b j) :=
          mul_le_mul_of_nonneg_left h1 hD
  set term : ℕ → ℝ := fun i =>
    ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * (∑ j ∈ Finset.range (i + 1), b j) with htermdef
  have hnn : ∀ i ∈ Finset.Ico 1 (n - 1), 0 ≤ term i := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [htermdef]
    have hD : 0 ≤ (i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ) := by
      have hi1 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi.1
      have hle : ((i : ℝ) + 1) ^ (-σ) ≤ (i : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hi1 (by linarith) (by linarith : -σ ≤ 0)
      linarith
    exact mul_nonneg hD (Finset.sum_nonneg (fun j _ => hb j))
  have hzero : ∑ i ∈ Finset.range (n - 1), term i = ∑ i ∈ Finset.Ico 1 (n - 1), term i := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_Ico] at hx
      simp only [Finset.mem_range]
      omega
    · intro x hx hxnot
      simp only [Finset.mem_range] at hx
      have hx1 : x < 1 := by
        by_contra h
        exact hxnot (by simp only [Finset.mem_Ico]; omega)
      have hx0 : x = 0 := by omega
      subst hx0
      simp only [htermdef, Nat.cast_zero, Nat.cast_one]
      rw [Real.zero_rpow (by linarith : (-σ) ≠ 0)]
      simp [hb0]
  have hsub : Finset.Ico T (n - 1) ⊆ Finset.Ico 1 (n - 1) := by
    intro x hx
    simp only [Finset.mem_Ico] at hx ⊢
    omega
  have hA : A * σ * (∑ j ∈ Finset.Ico (T + 1) n, (j : ℝ) ^ (-σ))
      = ∑ i ∈ Finset.Ico T (n - 1), A * σ * ((i + 1 : ℕ) : ℝ) ^ (-σ) := by
    rw [sum_Ico_succ_shift (fun j : ℕ => (j : ℝ) ^ (-σ)) hn]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Finset.mul_sum]
  have hterm' : ∀ i ∈ Finset.Ico T (n - 1), A * σ * ((i + 1 : ℕ) : ℝ) ^ (-σ) ≤ term i := by
    intro i hi
    simpa only [htermdef] using hterm i hi
  have hpos : 0 ≤ ((n : ℝ) - 1) ^ (-σ) * (∑ j ∈ Finset.range n, b j) := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : 1 ≤ n := by omega
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    exact mul_nonneg (Real.rpow_nonneg h1 _) (Finset.sum_nonneg (fun j _ => hb j))
  rw [hA]
  have hstep1 : ∑ i ∈ Finset.Ico T (n - 1), A * σ * ((i + 1 : ℕ) : ℝ) ^ (-σ) ≤
      ∑ i ∈ Finset.Ico T (n - 1), term i := Finset.sum_le_sum hterm'
  have hstep2 : ∑ i ∈ Finset.Ico T (n - 1), term i ≤ ∑ i ∈ Finset.Ico 1 (n - 1), term i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnn i hi)
  have hstep3 : ∑ i ∈ Finset.Ico 1 (n - 1), term i = (Finset.range (n - 1)).sum term :=
      hzero.symm
  have hstep4 : (Finset.range (n - 1)).sum term ≤
      ((n : ℝ) - 1) ^ (-σ) * (∑ j ∈ Finset.range n, b j)
        + (Finset.range (n - 1)).sum term := le_add_of_nonneg_left hpos
  exact le_trans (le_trans (le_trans hstep1 hstep2) (le_of_eq hstep3)) hstep4


lemma tsum_tail_rpow_ge (K : ℕ) (hK : 1 ≤ K) {σ : ℝ} (hσ : 1 < σ) :
    (K : ℝ) ^ (1 - σ) / (σ - 1) ≤ ∑' k : ℕ, (if K ≤ k then (k : ℝ) ^ (-σ) else 0) := by
  set d : ℕ → ℝ := fun k => if K ≤ k then (k : ℝ) ^ (-σ) else 0 with hd
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hdK : ∀ k, K ≤ k → d k = (k : ℝ) ^ (-σ) := by
    intro k hk; simp only [hd]; rw [if_pos hk]
  have hdz : ∀ k, ¬ (K ≤ k) → d k = 0 := by
    intro k hk; simp only [hd]; rw [if_neg hk]
  have hdnn : ∀ k, 0 ≤ d k := by
    intro k
    by_cases hk : K ≤ k
    · rw [hdK k hk]; exact Real.rpow_nonneg (Nat.cast_nonneg k) _
    · rw [hdz k hk]
  have hsumm_d : Summable d := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ (-σ)) :=
      (Real.summable_nat_rpow_inv (p := σ)).mpr hσ |>.congr fun k => by
        rw [Real.rpow_neg (Nat.cast_nonneg k)]
    exact Summable.of_nonneg_of_le hdnn (fun k => by
      by_cases hk : K ≤ k
      · rw [hdK k hk]
      · rw [hdz k hk]; exact Real.rpow_nonneg (Nat.cast_nonneg k) _) h1
  have hint : ∀ a : ℕ, ((K : ℝ) ^ (1 - σ) - ((K : ℝ) + (a : ℕ)) ^ (1 - σ)) / (σ - 1) ≤
      ∑ k ∈ Finset.range a, d (K + k) := by
    intro a
    have hanti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Icc (K : ℝ) ((K : ℝ) + (a : ℕ))) := by
      refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono ?_
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ioi]
      linarith [hx.1, hKpos]
    have h := AntitoneOn.integral_le_sum (x₀ := (K : ℝ)) (a := a) hanti
    have hcond : (-1 : ℝ) < -σ ∨ -σ ≠ -1 ∧ 0 ∉ Set.uIcc (K : ℝ) ((K : ℝ) + (a : ℕ)) :=
      Or.inr ⟨by linarith, by
        intro hmem
        rcases (Set.mem_uIcc.mp hmem) with ⟨h1, _⟩ | ⟨h1, _⟩
        · linarith [hKpos, h1]
        · linarith [hKpos, h1]⟩
    rw [integral_rpow hcond] at h
    have heq : ((K : ℝ) ^ (1 - σ) - ((K : ℝ) + (a : ℕ)) ^ (1 - σ)) / (σ - 1)
        = (((K : ℝ) + (a : ℕ)) ^ (-σ + 1) - (K : ℝ) ^ (-σ + 1)) / (-σ + 1) := by
      rw [div_eq_div_iff (by linarith : (σ - 1) ≠ 0) (by linarith : (-σ + 1) ≠ 0)]
      ring
    rw [heq]
    have hsum_eq : ∑ i ∈ Finset.range a, ((K : ℝ) + (i : ℕ)) ^ (-σ) =
        ∑ k ∈ Finset.range a, d (K + k) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hdK (K + i) (by omega)]
      norm_num
    rw [hsum_eq] at h
    exact h
  have hf_lim : Tendsto (fun a : ℕ =>
      ((K : ℝ) ^ (1 - σ) - ((K : ℝ) + (a : ℕ)) ^ (1 - σ)) / (σ - 1)) atTop
      (𝓝 ((K : ℝ) ^ (1 - σ) / (σ - 1))) := by
    have h1 : Tendsto (fun a : ℕ => ((K : ℝ) + (a : ℕ))) atTop atTop :=
      Filter.tendsto_atTop_add_const_left Filter.atTop (K : ℝ) tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun a : ℕ => ((K : ℝ) + (a : ℕ)) ^ (1 - σ)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun x : ℝ => (x ^ (σ - 1))⁻¹) atTop (𝓝 0) :=
        (tendsto_rpow_atTop (by linarith : (0:ℝ) < σ - 1)).inv_tendsto_atTop
      refine (h3.comp h1).congr' ?_
      filter_upwards [eventually_ge_atTop (0:ℕ)] with a _
      simp only [Function.comp_apply]
      rw [← Real.rpow_neg (by positivity : (0:ℝ) ≤ (K:ℝ) + (a:ℕ)) (σ - 1),
        show -(σ - 1) = (1:ℝ) - σ by ring]
    have h4 := (tendsto_const_nhds (x := (K:ℝ)^(1-σ))).sub h2
    simpa using h4.div_const (σ - 1)
  have hg_lim : Tendsto (fun a : ℕ => ∑ k ∈ Finset.range a, d (K + k)) atTop (𝓝 (∑' k, d k)) := by
    have hmap : Tendsto (fun a : ℕ => K + a) atTop atTop :=
      (tendsto_add_atTop_nat K).congr' (Eventually.of_forall fun a => by simp [Nat.add_comm])
    have h1 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, d k) atTop (𝓝 (∑' k, d k)) :=
      hsumm_d.hasSum.tendsto_sum_nat
    refine (h1.comp hmap).congr' ?_
    filter_upwards [eventually_ge_atTop K] with a _
    simp only [Function.comp_apply]
    have h2 : ∑ k ∈ Finset.range (K + a), d k = ∑ k ∈ Finset.Ico K (K + a), d k :=
      (Finset.sum_subset (fun x hx => Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2)
        (fun x hx hxnot => by
          refine hdz x ?_
          intro hxK
          exact hxnot (Finset.mem_Ico.mpr ⟨hxK, Finset.mem_range.mp hx⟩))).symm
    rw [h2, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

  exact le_of_tendsto_of_tendsto hf_lim hg_lim (Eventually.of_forall fun a => by
    dsimp only
    exact hint a)

lemma tsum_rpow_lower {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (hb0 : b 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    {T : ℕ} (hT : 2 ≤ T) (hpart : ∀ k, T ≤ k → A * (k : ℝ) ≤ ∑ j ∈ Finset.Icc 1 k, b j)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hsumm : Summable (fun n : ℕ => b n * (n : ℝ) ^ (-σ))) :
    A * σ * (((T + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1)) ≤
      ∑' n : ℕ, b n * (n : ℝ) ^ (-σ) := by
  set d : ℕ → ℝ := fun k => if T + 1 ≤ k then (k : ℝ) ^ (-σ) else 0 with hd
  have hdnn : ∀ k, 0 ≤ d k := by
    intro k
    simp only [hd]
    split_ifs with h
    · exact Real.rpow_nonneg (Nat.cast_nonneg k) _
    · exact le_rfl
  have hsumm_d : Summable d := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ (-σ)) :=
      (Real.summable_nat_rpow_inv (p := σ)).mpr hσ1 |>.congr fun k => by
        rw [Real.rpow_neg (Nat.cast_nonneg k)]
    exact Summable.of_nonneg_of_le hdnn (fun k => by
      simp only [hd]
      split_ifs with h
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg k) _) h1
  have hfin : ∀ n : ℕ, T + 1 ≤ n →
      A * σ * (∑ j ∈ Finset.range n, d j) ≤ ∑ i ∈ Finset.range n, b i * (i : ℝ) ^ (-σ) := by
    intro n hn
    have h1 : ∑ j ∈ Finset.range n, d j = ∑ j ∈ Finset.Ico (T + 1) n, (j : ℝ) ^ (-σ) := by
      have h2 : ∑ j ∈ Finset.range n, d j = ∑ j ∈ Finset.Ico (T + 1) n, d j :=
        (Finset.sum_subset (fun x hx => Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2)
          (fun x hx hxnot => by
            have hxlt : ¬ (T + 1 ≤ x) := by
              intro hxT
              exact hxnot (Finset.mem_Ico.mpr ⟨hxT, Finset.mem_range.mp hx⟩)
            simp only [hd]
            rw [if_neg hxlt])).symm
      rw [h2]
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      simp only [hd]
      rw [if_pos hx.1]
    rw [h1]
    exact by_parts_ineq hb hb0 hA hT hpart hσ1 hσ2 hn
  have hf_lim : Tendsto (fun n : ℕ => A * σ * (∑ j ∈ Finset.range n, d j)) atTop
      (𝓝 (A * σ * (∑' j, d j))) :=
    (hsumm_d.hasSum.tendsto_sum_nat.const_mul (A * σ))
  have hg_lim : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, b i * (i : ℝ) ^ (-σ)) atTop
      (𝓝 (∑' i, b i * (i : ℝ) ^ (-σ))) := hsumm.hasSum.tendsto_sum_nat
  have hle : A * σ * (∑' j, d j) ≤ ∑' i, b i * (i : ℝ) ^ (-σ) :=
    le_of_tendsto_of_tendsto hf_lim hg_lim
      (eventually_atTop.mpr ⟨T + 1, fun n hn => hfin n hn⟩)
  have hd_ge : ((T + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1) ≤ ∑' j, d j := by
    rw [hd]
    exact tsum_tail_rpow_ge (T + 1) (by omega) hσ1
  have hAσ : 0 ≤ A * σ := mul_nonneg hA (by linarith)
  exact le_trans (mul_le_mul_of_nonneg_left hd_ge hAσ) hle


lemma zetaMul_eq_ofReal_re (χ : DirichletCharacter ℂ N) (hχ : χ ^ 2 = 1) (n : ℕ) :
    χ.zetaMul n = ((χ.zetaMul n).re : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp
  · simp [zetaMul_im_eq_zero χ hχ n]

theorem LFunction_one_lower_bound_of_partial_sums :
    ∀ c : ℝ, 0 < c → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ * χ = 1 → χ ≠ 1 → ∀ (T : ℕ),
      (∀ X : ℕ, T ≤ X → c * (X : ℝ) / Real.sqrt (N : ℝ) ≤
        (∑ n ∈ Finset.Icc 1 X, χ.zetaMul n).re) →
      c / (2 * Real.sqrt (N : ℝ)) ≤ ‖DirichletCharacter.LFunction χ (1 : ℂ)‖ := by
  intro c hc N hN χ hsq hne T hpart
  have hpow : χ ^ 2 = 1 := by rw [pow_two]; exact hsq
  set b : ℕ → ℝ := fun n => (χ.zetaMul n).re with hbdef
  have hb : ∀ n, 0 ≤ b n := fun n => (zetaMul_nonneg hpow n).1
  have hb0 : b 0 = 0 := by simp [hbdef]
  set A : ℝ := c / Real.sqrt (N : ℝ) with hAdef
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact div_nonneg (le_of_lt hc) (Real.sqrt_nonneg _)
  have hApos : 0 < A := by
    rw [hAdef]
    exact div_pos hc (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N))
  set T' : ℕ := max T 2 with hT'def
  have hT'2 : 2 ≤ T' := le_max_right _ _
  have hpart' : ∀ k, T' ≤ k → A * (k : ℝ) ≤ ∑ j ∈ Finset.Icc 1 k, b j := by
    intro k hk
    have hkT : T ≤ k := le_trans (le_max_left _ _) hk
    have h := hpart k hkT
    have hsum : (∑ n ∈ Finset.Icc 1 k, χ.zetaMul n).re = ∑ j ∈ Finset.Icc 1 k, b j :=
      Complex.re_sum _ _
    rw [show c * (k:ℝ) / Real.sqrt (N:ℝ) = A * (k:ℝ) from by rw [hAdef]; ring] at h
    rw [hsum] at h
    exact h
  -- the key bound for σ ∈ (1,2]
  have hmain : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      A * σ * (((T' + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1)) ≤
        (riemannZeta (σ : ℂ) * DirichletCharacter.LFunction χ (σ : ℂ)).re := by
    intro σ hσ1 hσ2
    have hLS : LSeriesSummable (χ.zetaMul : ℕ → ℂ) (σ : ℂ) :=
      DirichletCharacter.LSeriesSummable_zetaMul χ (by simpa using hσ1)
    have hsummσ : Summable (fun n : ℕ => b n * (n : ℝ) ^ (-σ)) := by
      have hval : ∀ n : ℕ, b n * (n : ℝ) ^ (-σ) =
          (LSeries.term (χ.zetaMul : ℕ → ℂ) (σ : ℂ) n).re := by
        intro n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [hb0]
        · rw [LSeries.term_of_ne_zero hn]
          have hcast : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by simp
          rw [hcast, ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ,
            zetaMul_eq_ofReal_re χ hpow n, ← Complex.ofReal_div, Complex.ofReal_re,
            div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hLS.norm
      · exact mul_nonneg (hb n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      · rw [hval n]
        exact Complex.re_le_norm _
    have hLval : (riemannZeta (σ : ℂ) * DirichletCharacter.LFunction χ (σ : ℂ)).re =
        ∑' n : ℕ, b n * (n : ℝ) ^ (-σ) := by
      rw [← LSeries_zetaMul_eq χ (by simpa using hσ1), LSeries_zetaMul_re_eq χ hpow hσ1]
      refine tsum_congr fun n => ?_
      rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
    rw [hLval]
    exact tsum_rpow_lower hb hb0 hA hT'2 hpart' hσ1 hσ2 hsummσ
  -- the limit at σ → 1+
  have hcont : Tendsto (fun σ : ℝ => DirichletCharacter.LFunction χ (σ : ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 (DirichletCharacter.LFunction χ (1 : ℂ))) :=
    ((DirichletCharacter.differentiable_LFunction hne).continuous.tendsto (1:ℂ)).comp
      ((Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
  have hres : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 1) := by
    have hσmem : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1:ℝ)) (𝓝[≠] (1:ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      exact (ne_of_gt hσ) (Complex.ofReal_injective h)
    exact riemannZeta_residue_one.comp hσmem
  have hprod : Tendsto (fun σ : ℝ => (((σ : ℂ) - 1) * riemannZeta (σ : ℂ)) *
      DirichletCharacter.LFunction χ (σ : ℂ)) (𝓝[>] (1:ℝ))
      (𝓝 (DirichletCharacter.LFunction χ (1 : ℂ))) := by
    have h := hres.mul hcont
    simpa using h
  have hlim : Tendsto (fun σ : ℝ => (σ - 1) *
      (riemannZeta (σ : ℂ) * DirichletCharacter.LFunction χ (σ : ℂ)).re) (𝓝[>] (1:ℝ))
      (𝓝 (DirichletCharacter.LFunction χ (1 : ℂ)).re) := by
    have hre : Tendsto (fun σ : ℝ => ((((σ : ℂ) - 1) * riemannZeta (σ : ℂ)) *
        DirichletCharacter.LFunction χ (σ : ℂ)).re) (𝓝[>] (1:ℝ))
        (𝓝 (DirichletCharacter.LFunction χ (1 : ℂ)).re) :=
      (Complex.continuous_re.tendsto _).comp hprod
    refine hre.congr' ?_
    filter_upwards with σ
    simp [Complex.mul_re, mul_assoc]
  -- the eventual lower bound
  have hKpos : (0:ℝ) < ((T' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos T'
  have hlim2 : Tendsto (fun σ : ℝ => A * σ * (((T' + 1 : ℕ) : ℝ) ^ (1 - σ)))
      (𝓝[>] (1:ℝ)) (𝓝 A) := by
    have h1 : Tendsto (fun σ : ℝ => ((T' + 1 : ℕ) : ℝ) ^ (1 - σ))
        (𝓝[>] (1:ℝ)) (𝓝 1) := by
      have hlog : Tendsto (fun σ : ℝ => (1 - σ) * Real.log ((T' + 1 : ℕ) : ℝ))
          (𝓝[>] (1:ℝ)) (𝓝 0) := by
        have h1 : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] (1:ℝ)) (𝓝 1) := tendsto_const_nhds
        have h2 : Tendsto (fun σ : ℝ => σ) (𝓝[>] (1:ℝ)) (𝓝 1) :=
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
        simpa using (h1.sub h2).mul_const (Real.log ((T' + 1 : ℕ) : ℝ))
      have hexp : Tendsto (Real.exp ∘ fun σ : ℝ => (1 - σ) * Real.log ((T' + 1 : ℕ) : ℝ))
          (𝓝[>] (1:ℝ)) (𝓝 1) := by
        have h := Real.continuous_exp.continuousAt.tendsto.comp hlog
        simpa only [Function.comp_apply, Real.exp_zero] using h
      refine hexp.congr' ?_
      filter_upwards with σ
      simp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos hKpos]
      congr 1
      ring
    have h2 : Tendsto (fun σ : ℝ => A * σ) (𝓝[>] (1:ℝ)) (𝓝 (A * 1)) :=
      tendsto_const_nhds.mul (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    simpa using h2.mul h1
  have hev1 : ∀ᶠ σ in 𝓝[>] (1:ℝ), A / 2 ≤ A * σ * (((T' + 1 : ℕ) : ℝ) ^ (1 - σ)) := by
    have hA2 : A / 2 < A := by linarith
    have h := hlim2.eventually (isOpen_Ioi.mem_nhds hA2)
    filter_upwards [h] with σ hσ
    exact le_of_lt hσ
  have hev2 : ∀ᶠ σ in 𝓝[>] (1:ℝ), σ ≤ 2 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((eventually_lt_nhds (by norm_num : (1:ℝ) < 2)).mono fun σ h => le_of_lt h)
  have hev3 : ∀ᶠ σ in 𝓝[>] (1:ℝ), 1 < σ := self_mem_nhdsWithin
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1:ℝ), A / 2 ≤ (σ - 1) *
      (riemannZeta (σ : ℂ) * DirichletCharacter.LFunction χ (σ : ℂ)).re := by
    filter_upwards [hev1, hev2, hev3] with σ h1 h2 h3
    have hσ1 : 1 < σ := h3
    have hσ2 : σ ≤ 2 := h2
    have hσpos : 0 < σ - 1 := by linarith
    have hkey := hmain σ hσ1 hσ2
    have hmult : (σ - 1) * (A * σ * (((T' + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1)))
        = A * σ * (((T' + 1 : ℕ) : ℝ) ^ (1 - σ)) := by
      field_simp
    calc A / 2 ≤ A * σ * (((T' + 1 : ℕ) : ℝ) ^ (1 - σ)) := h1
      _ = (σ - 1) * (A * σ * (((T' + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1))) := hmult.symm
      _ ≤ (σ - 1) * (riemannZeta (σ : ℂ) *
          DirichletCharacter.LFunction χ (σ : ℂ)).re :=
          mul_le_mul_of_nonneg_left hkey (le_of_lt hσpos)
  have hfinal : A / 2 ≤ (DirichletCharacter.LFunction χ (1 : ℂ)).re := ge_of_tendsto hlim hev
  have : A / 2 ≤ ‖DirichletCharacter.LFunction χ (1 : ℂ)‖ :=
    le_trans hfinal (Complex.re_le_norm _)
  have hAeq : A / 2 = c / (2 * Real.sqrt (N : ℝ)) := by
    rw [hAdef, div_div, mul_comm 2 (Real.sqrt (N : ℝ))]
  rwa [hAeq] at this

section ChiAux

noncomputable def chiD (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1) : ℤ :=
  chiZ χ hsq (-1 : ZMod N) * (N : ℤ)

lemma chiD_cast (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1) :
    ((chiD χ hsq : ℤ) : ℂ) = χ (-1 : ZMod N) * (N : ℂ) := by
  rw [chiD, Int.cast_mul, Int.cast_natCast, chiZ_spec]

lemma chiD_abs (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1) :
    (chiD χ hsq).natAbs = N := by
  rw [chiD]
  have h := chiZ_eq_one_or_neg_one_of_isUnit χ hsq isUnit_neg_one
  rcases h with h | h <;> rw [h] <;> simp

lemma chiD_odd {χ : DirichletCharacter ℂ N} {hsq : χ * χ = 1} (hN : Odd N) : Odd (chiD χ hsq) := by
  rw [chiD]
  have h := chiZ_eq_one_or_neg_one_of_isUnit χ hsq isUnit_neg_one
  rcases h with h | h <;> rw [h] <;> simpa using hN

lemma chiD_sign {χ : DirichletCharacter ℂ N} {hsq : χ * χ = 1} (hN : 0 < N) :
    (if 0 < chiD χ hsq then (1 : ℤ) else -1) = chiZ χ hsq (-1 : ZMod N) := by
  have h := chiZ_eq_one_or_neg_one_of_isUnit χ hsq isUnit_neg_one
  rcases h with h | h
  · rw [chiD, h, one_mul, if_pos (by exact_mod_cast hN)]
  · rw [chiD, h, neg_one_mul, if_neg (by simp)]

theorem chi_eq_jacobiSym_of_prime_values {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (_hsq : χ * χ = 1) {D : ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ N → χ (p : ZMod N) = (jacobiSym D p : ℂ)) :
    ∀ {a : ℕ}, _root_.Odd a → a.Coprime N → χ (a : ZMod N) = (jacobiSym D a : ℂ) := by
  classical
  intro a
  induction' a using Nat.strong_induction_on with a ih
  intro ha haN
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h] at ha
      obtain ⟨k, hk⟩ := ha
      omega
    · exact h
  rcases eq_or_ne a 1 with rfl | ha1
  · simp [jacobiSym.one_right]
  have hpval : ∀ p : ℕ, p.Prime → p ∣ a → χ (p : ZMod N) = (jacobiSym D p : ℂ) := by
    intro p hp hpa
    refine h p hp ?_ ?_
    · rintro rfl
      exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hpa)
    · intro hpN
      have h1 : p ∣ Nat.gcd a N := Nat.dvd_gcd hpa hpN
      rw [haN.gcd_eq_one] at h1
      exact hp.not_dvd_one h1
  by_cases hp : a.Prime
  · exact hpval a hp dvd_rfl
  · obtain ⟨p, hpp, hpa⟩ := Nat.exists_prime_and_dvd ha1
    set b : ℕ := a / p with hbdef
    have hmul : p * b = a := Nat.mul_div_cancel' hpa
    have hbpos : 0 < b := by
      rw [hbdef]
      exact Nat.div_pos (Nat.le_of_dvd ha0 hpa) hpp.pos
    have hblt : b < a := by
      rw [← hmul]
      exact lt_mul_of_one_lt_left hbpos hpp.one_lt
    have hbodd : _root_.Odd b := by
      have hpodd : _root_.Odd p := hpp.odd_of_ne_two (by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hpa))
      have hodd_prod : _root_.Odd (p * b) := by rw [hmul]; exact ha
      exact (Nat.odd_mul.mp hodd_prod).2
    have hbdvd : b ∣ a := ⟨p, by rw [mul_comm]; exact hmul.symm⟩
    have hbN : b.Coprime N := Nat.Coprime.of_dvd_left hbdvd haN
    have hb' : χ (b : ZMod N) = (jacobiSym D b : ℂ) := ih b hblt hbodd hbN
    have hp' : χ (p : ZMod N) = (jacobiSym D p : ℂ) := hpval p hpp hpa
    have hb0 : b ≠ 0 := hbpos.ne'
    calc χ (a : ZMod N) = χ ((p * b : ℕ) : ZMod N) := by rw [hmul]
      _ = χ (p : ZMod N) * χ (b : ZMod N) := by rw [Nat.cast_mul, map_mul]
      _ = (jacobiSym D p : ℂ) * (jacobiSym D b : ℂ) := by rw [hp', hb']
      _ = ((jacobiSym D p * jacobiSym D b : ℤ) : ℂ) := by push_cast; ring
      _ = (jacobiSym D (p * b) : ℂ) := by
          rw [jacobiSym.mul_right' D hpp.ne_zero hb0]
      _ = (jacobiSym D a : ℂ) := by rw [hmul]


/-- The Gauss lemma, in Jacobi-symbol form: for an odd prime `p ∤ N`, the value `χ(p)` is the
Jacobi symbol `(D | p)` with `D = χ(-1)·N`. -/
theorem chiPrimeJacobi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ (p : ZMod N) = (jacobiSym (chiD χ hsq) p : ℂ) := by
  rw [chiZ_spec χ hsq (p : ZMod N)]
  congr 1
  rw [chiZ_prime_eq_legendre χ hχ hsq hne p hp2 hpN]
  rw [← jacobiSym.legendreSym.to_jacobiSym p (chiD χ hsq)]
  rfl

/-- For odd `N`, the relation `(D | N+2) = χ(-1)·(D | N-2)` between the two ways of
evaluating `χ(2)`. -/
theorem jacobiSym_self_relation {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) (hNodd : _root_.Odd N) :
    jacobiSym (chiD χ hsq) (N + 2) =
      chiZ χ hsq (-1 : ZMod N) * jacobiSym (chiD χ hsq) (N - 2) := by
  have hN3 : 3 ≤ N := by
    rcases eq_or_ne N 1 with h | h
    · exact absurd (DirichletCharacter.level_one' χ h) hne
    · obtain ⟨k, hk⟩ := hNodd
      omega
  have hN2 : 2 ≤ N := by omega
  have hnotdvd : ¬ 2 ∣ N := fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h)
  have hcop1 : (N + 2).Coprime N := by
    rw [add_comm N 2, Nat.coprime_add_self_left]
    exact Nat.prime_two.coprime_iff_not_dvd.mpr hnotdvd
  have hcop2 : (N - 2).Coprime N := by
    have h : N = (N - 2) + 2 := (Nat.sub_add_cancel hN2).symm
    conv_rhs => rw [h]
    rw [Nat.coprime_self_add_right]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by
      rintro ⟨j, hj⟩
      obtain ⟨k, hk⟩ := hNodd
      omega)).symm
  have hodd1 : _root_.Odd (N + 2) := hNodd.add_even (by norm_num : Even 2)
  have hodd2 : _root_.Odd (N - 2) := by
    obtain ⟨k, hk⟩ := hNodd
    exact ⟨k - 1, by omega⟩
  have hjac1 : χ ((N + 2 : ℕ) : ZMod N) = (jacobiSym (chiD χ hsq) (N + 2) : ℂ) :=
    chi_eq_jacobiSym_of_prime_values χ hsq
      (fun p hp hp2 hpN => by
        haveI : Fact p.Prime := ⟨hp⟩
        exact chiPrimeJacobi χ hχ hsq hne p hp2 hpN) hodd1 hcop1
  have hjac2 : χ ((N - 2 : ℕ) : ZMod N) = (jacobiSym (chiD χ hsq) (N - 2) : ℂ) :=
    chi_eq_jacobiSym_of_prime_values χ hsq
      (fun p hp hp2 hpN => by
        haveI : Fact p.Prime := ⟨hp⟩
        exact chiPrimeJacobi χ hχ hsq hne p hp2 hpN) hodd2 hcop2
  have hcast1 : ((N + 2 : ℕ) : ZMod N) = (2 : ZMod N) := by
    simp [Nat.cast_add, ZMod.natCast_self]
  have hcast2 : ((N - 2 : ℕ) : ZMod N) = (-2 : ZMod N) := by
    have h : ((N - 2 : ℕ) : ZMod N) + (2 : ZMod N) = 0 := by
      rw [← Nat.cast_ofNat (R := ZMod N), ← Nat.cast_add, Nat.sub_add_cancel hN2,
        ZMod.natCast_self]
    rw [eq_neg_iff_add_eq_zero]; exact h
  have hmain : (jacobiSym (chiD χ hsq) (N + 2) : ℂ) =
      χ (-1 : ZMod N) * (jacobiSym (chiD χ hsq) (N - 2) : ℂ) := by
    rw [← hjac1, hcast1, ← hjac2, hcast2, ← map_mul]
    congr 1
    ring
  have hchi : χ (-1 : ZMod N) = (chiZ χ hsq (-1 : ZMod N) : ℂ) := chiZ_spec χ hsq _
  rw [hchi] at hmain
  push_cast at hmain
  exact_mod_cast hmain


open Commons.NumberTheory.JacobiSymbol in
/-- For odd `N`: the discriminant `D = χ(-1)·N` of a primitive quadratic character is
`1` or `5` mod `8`, `χ(2)` is the Jacobi symbol `(D | N+2)`, and `χ(2) = -1` exactly when
`D ≡ 5 (mod 8)`. -/
theorem chi_two_and_mod_eight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) (hNodd : _root_.Odd N) :
    (chiD χ hsq % 8 = 1 ∨ chiD χ hsq % 8 = 5) ∧
      (χ (2 : ZMod N) = (jacobiSym (chiD χ hsq) (N + 2) : ℂ)) ∧
      (χ (2 : ZMod N) = -1 ↔ chiD χ hsq % 8 = 5) := by
  have hN3 : 3 ≤ N := by
    rcases eq_or_ne N 1 with h | h
    · exact absurd (DirichletCharacter.level_one' χ h) hne
    · obtain ⟨k, hk⟩ := hNodd
      omega
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have habs : (chiD χ hsq).natAbs = N := chiD_abs χ hsq
  have hodd : _root_.Odd (chiD χ hsq) := chiD_odd hNodd
  have hsign : (if 0 < chiD χ hsq then (1 : ℤ) else -1) = chiZ χ hsq (-1 : ZMod N) :=
    chiD_sign hNpos
  have hrel : jacobiSym (chiD χ hsq) ((chiD χ hsq).natAbs + 2) =
      (if 0 < chiD χ hsq then (1 : ℤ) else -1) *
        jacobiSym (chiD χ hsq) ((chiD χ hsq).natAbs - 2) := by
    rw [habs, hsign]
    exact jacobiSym_self_relation χ hχ hsq hne hNodd
  have hkey := modEight_of_selfRelation hodd (by rw [habs]; exact hN3) hrel
  have h2 : χ (2 : ZMod N) = (jacobiSym (chiD χ hsq) (N + 2) : ℂ) := by
    have hcast1 : ((N + 2 : ℕ) : ZMod N) = (2 : ZMod N) := by
      simp [Nat.cast_add, ZMod.natCast_self]
    rw [← hcast1]
    refine chi_eq_jacobiSym_of_prime_values χ hsq ?_ ?_ ?_
    · intro p hp hp2 hpN
      haveI : Fact p.Prime := ⟨hp⟩
      exact chiPrimeJacobi χ hχ hsq hne p hp2 hpN
    · exact hNodd.add_even (by norm_num : Even 2)
    · rw [add_comm N 2, Nat.coprime_add_self_left]
      exact Nat.prime_two.coprime_iff_not_dvd.mpr
        (fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h))
  have hiff : (jacobiSym (chiD χ hsq) ((chiD χ hsq).natAbs + 2) = 1) ↔
      chiD χ hsq % 8 = 1 := hkey.2
  have hiff' : (jacobiSym (chiD χ hsq) (N + 2) = 1) ↔ chiD χ hsq % 8 = 1 := by
    have harg : (chiD χ hsq).natAbs + 2 = N + 2 := by rw [habs]
    rw [← harg]; exact hiff
  have hcop : (chiD χ hsq).gcd ((N + 2 : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs, habs, Int.natAbs_natCast]
    rw [show N + 2 = 2 + N from by omega, Nat.gcd_comm, Nat.gcd_add_self_left]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h))).gcd_eq_one
  refine ⟨hkey.1, h2, ?_⟩
  rw [h2]
  constructor
  · intro h
    rcases hkey.1 with h1 | h5
    · exfalso
      have : (jacobiSym (chiD χ hsq) (N + 2) : ℂ) = 1 := by
        rw [hiff'.mpr h1]
        norm_num
      rw [this] at h
      norm_num at h
    · exact h5
  · intro h5
    have hne1 : jacobiSym (chiD χ hsq) (N + 2) ≠ 1 := by
      intro h1
      have := hiff'.mp h1
      omega
    rcases jacobiSym.trichotomy (chiD χ hsq) (N + 2) with h0 | h1 | hm1
    · exact absurd h0 (fun h0 => by
        rcases jacobiSym.eq_one_or_neg_one hcop with h | h <;> rw [h] at h0 <;> norm_num at h0)
    · exact absurd h1 hne1
    · norm_num [hm1]


end ChiAux

section DsqAux

/-- Binomial divisibility: for a prime `p` dividing `m`, we have `m * p ∣ p.choose i * m ^ i`
whenever `1 ≤ i ≤ p`. -/
lemma mul_self_dvd_choose_mul_pow {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) {i : ℕ}
    (hi1 : 1 ≤ i) (hip : i ≤ p) : m * p ∣ p.choose i * m ^ i := by
  have h1 : p ∣ m ^ (i - 1) * p.choose i := by
    rcases eq_or_lt_of_le hip with h | h
    · rw [h, Nat.choose_self, mul_one]
      have hp2 : 2 ≤ p := hp.two_le
      have hcast : m ^ (p - 1) = m ^ (p - 2) * m := by
        rw [show p - 1 = p - 2 + 1 by omega, pow_succ]
      rw [hcast]
      exact dvd_mul_of_dvd_right hpm _
    · exact dvd_mul_of_dvd_right (hp.dvd_choose_self (by omega) h) _
  have h2 : m * p ∣ m * (m ^ (i - 1) * p.choose i) := Nat.mul_dvd_mul_left m h1
  have h4 : m ^ i = m ^ (i - 1) * m := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega]
    rw [pow_succ]
  have h3 : m * (m ^ (i - 1) * p.choose i) = p.choose i * m ^ i := by
    rw [h4]; ring
  rwa [h3] at h2

variable {N : ℕ} [NeZero N]

/-- A primitive quadratic Dirichlet character at an odd prime divisor `p` of its modulus has
`p ^ 2 ∤ N`. -/
theorem not_dvd_sq_of_isPrimitive (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive)
    (hsq : χ * χ = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p * p ∣ N := by
  intro hpp
  obtain ⟨k, hk⟩ : ∃ k : ℕ, N = p * p * k := hpp
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; exact absurd hk (NeZero.ne N)
    · exact h
  set m : ℕ := p * k with hmdef
  have hp1 : 1 < p := hp.one_lt
  have hmul : m * p = N := by rw [hmdef, hk]; ring
  have hmN : m ∣ N := ⟨p, hmul.symm⟩
  have hpm : p ∣ m := by rw [hmdef]; exact dvd_mul_right p k
  have hmpos : 0 < m := by rw [hmdef]; positivity
  have hm3 : 3 ≤ m := by
    rw [hmdef]
    calc 3 = 3 * 1 := (mul_one 3).symm
      _ ≤ p * k := Nat.mul_le_mul (by omega) hkpos
  -- χ factors through level `m = N / p`
  have hfac : χ.FactorsThrough m := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) hmN]
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    -- `x ≡ 1 mod m`
    have hcast : ZMod.cast ((x : (ZMod N)ˣ) : ZMod N) = (1 : ZMod m) := by
      have h1 : (((ZMod.unitsMap hmN x : (ZMod m)ˣ)) : ZMod m) = 1 := by rw [hx]; simp
      rwa [ZMod.unitsMap_val hmN x] at h1
    have hval : (((x : (ZMod N)ˣ) : ZMod N).val : ZMod m) = 1 := by
      rw [← ZMod.cast_eq_val (R := ZMod m) ((x : (ZMod N)ˣ) : ZMod N)]
      exact hcast
    have hmod : ((x : (ZMod N)ˣ) : ZMod N).val % m = 1 := by
      have hh : (((x : (ZMod N)ˣ) : ZMod N).val : ZMod m) = ((1 : ℕ) : ZMod m) := by
        simpa using hval
      have h1 : ((x : (ZMod N)ˣ) : ZMod N).val % m = 1 % m :=
        (ZMod.natCast_eq_natCast_iff' _ 1 m).mp hh
      rwa [Nat.mod_eq_of_lt (by omega : 1 < m)] at h1
    -- write `x = 1 + m * t`
    set t : ℕ := (((x : (ZMod N)ˣ) : ZMod N).val) / m with htdef
    have hxval : ((x : (ZMod N)ˣ) : ZMod N).val = m * t + 1 := by
      rw [htdef]
      have h := Nat.div_add_mod (((x : (ZMod N)ˣ) : ZMod N).val) m
      omega
    have hv : ((x : (ZMod N)ˣ) : ZMod N) = 1 + (m : ZMod N) * (t : ZMod N) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val ((x : (ZMod N)ˣ) : ZMod N)]
      rw [hxval]
      push_cast
      ring
    -- `x ^ p = 1`
    have hpow : ((x : (ZMod N)ˣ) : ZMod N) ^ p = 1 := by
      rw [hv, show (1 : ZMod N) + (m : ZMod N) * (t : ZMod N)
        = (m : ZMod N) * (t : ZMod N) + 1 by ring, add_pow]
      have hterm : ∀ i ∈ Finset.range (p + 1),
          ((m : ZMod N) * (t : ZMod N)) ^ i * 1 ^ (p - i) * ((p.choose i : ℕ) : ZMod N)
            = (if i = 0 then (1 : ZMod N) else 0) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · subst h0; simp
        · rw [if_neg (Nat.pos_iff_ne_zero.mp h0), one_pow, mul_one]
          have hi1 : 1 ≤ i := h0
          have hdvd : N ∣ p.choose i * m ^ i := by
            rw [← hmul]
            exact mul_self_dvd_choose_mul_pow hp hpm hi1 (by omega)
          have hzero : ((p.choose i * m ^ i : ℕ) : ZMod N) = 0 := by
            rw [ZMod.natCast_eq_zero_iff]
            exact hdvd
          have hcast2 : ((m : ZMod N) * (t : ZMod N)) ^ i * ((p.choose i : ℕ) : ZMod N)
              = ((p.choose i * m ^ i : ℕ) : ZMod N) * ((t : ZMod N) ^ i) := by
            push_cast; ring
          rw [hcast2, hzero, zero_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      simp
    have hxp : x ^ p = 1 := by
      apply Units.ext
      simpa using hpow
    -- conclude `χ x = 1`
    have hchi : χ.toUnitHom x = 1 := by
      refine Units.ext ?_
      rw [MulChar.coe_toUnitHom, Units.val_one]
      have h1 : (χ (((x : (ZMod N)ˣ) : ZMod N))) ^ p = 1 := by
        have h2 : (χ.toUnitHom x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
        simpa [MulChar.coe_toUnitHom] using congrArg (fun y : ℂˣ => (y : ℂ)) h2
      rcases quadratic_chi_values χ hsq (((x : (ZMod N)ˣ) : ZMod N)) with h0 | h1' | hm1
      · exact absurd x.isUnit (MulChar.apply_eq_zero_iff.mp h0)
      · exact h1'
      · rw [hm1, Odd.neg_one_pow (hp.odd_of_ne_two hp2)] at h1
        norm_num at h1
    exact hchi
  -- but then the conductor divides `m < N`, contradicting primitivity
  have hdvd : N ∣ m := by
    rw [← hprim]
    exact DirichletCharacter.conductor_dvd_of_mem_conductorSet (n := N) (χ := χ) hfac
  have hlt : m < N := by
    rw [← hmul]
    calc m = m * 1 := (mul_one m).symm
      _ < m * p := Nat.mul_lt_mul_of_pos_left hp1 hmpos
  have := Nat.le_of_dvd hmpos hdvd
  omega

end DsqAux

section NfAux

open scoped _root_.NumberField
open Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

theorem sum_ramification_inertia_eq_two (hfin : Module.finrank ℚ K = 2) (p : ℕ) [Fact p.Prime] :
    ∑ 𝔭 : (Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K),
      𝔭.1.ramificationIdx ℤ * 𝔭.1.inertiaDeg ℤ = 2 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal
      hpne
  have h := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers K)
  rw [show Module.finrank ℤ (NumberField.RingOfIntegers K) = Module.finrank ℚ K from
    NumberField.RingOfIntegers.rank K, hfin] at h
  exact h

/-- `absNorm` is multiplicative over a finite product of ideals. -/
lemma absNorm_finset_prod {ι : Type*} (s : Finset ι) (f : ι → Ideal (𝓞 K)) :
    Ideal.absNorm (∏ i ∈ s, f i) = ∏ i ∈ s, Ideal.absNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.absNorm_top]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      simp only [Ideal.absNorm_apply] at ih ⊢
      rw [cardQuot_mul, ih]

/-- The prime factors of a nonzero ideal of norm `p^k` lie over `p`. -/
lemma mem_primesOverFinset_of_mem_normalizedFactors {p : ℕ} [Fact p.Prime] {I : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) {k : ℕ} (hk : Ideal.absNorm I = p ^ k) {P : Ideal (𝓞 K)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) := by
  have hPif := (Ideal.mem_normalizedFactors_iff hI).mp hP
  have hPmax : P.IsMaximal := Commons.NumberTheory.NumberField.isMaximal_of_mem_normalizedFactors hI hP
  have hdiv : Ideal.absNorm P ∣ Ideal.absNorm I := Ideal.absNorm_dvd_absNorm_of_le hPif.2
  rw [hk] at hdiv
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp hdiv
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exfalso
      rw [h, pow_zero] at hj
      have := Ideal.absNorm_eq_one_iff.mp hj
      exact hPmax.ne_top this
    · exact h
  have hpdvd : p ∣ Ideal.absNorm P := by
    rw [hj]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hj1)
  have hlO := Commons.NumberTheory.NumberField.liesOver_of_dvd_absNorm p P hPmax hpdvd
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne
  exact (IsDedekindDomain.mem_primesOverFinset_iff (B := NumberField.RingOfIntegers K) hpne).mpr
    ⟨hPif.1, hlO⟩


section Counting

variable {K : Type*} [Field K] [NumberField K]

open scoped _root_.NumberField

/-- `absNorm` is multiplicative over powers. -/
lemma absNorm_pow (I : Ideal (𝓞 K)) (n : ℕ) :
    Ideal.absNorm (I ^ n) = (Ideal.absNorm I) ^ n := by
  induction n with
  | zero => simp [Ideal.absNorm_top]
  | succ n ih =>
      rw [pow_succ, pow_succ]
      simp only [Ideal.absNorm_apply] at ih ⊢
      rw [cardQuot_mul, ih]

/-- The primes over `p` as a finset. -/
noncomputable abbrev primesOverF (p : ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)

/-- A nonzero ideal of norm `p^k` is the product of the primes over `p` raised to the
exponents of its prime factorization. -/
lemma eq_prod_primesOverFinset {p : ℕ} [Fact p.Prime] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    {k : ℕ} (hk : Ideal.absNorm I = p ^ k) :
    I = ∏ P ∈ primesOverF (K := K) p,
      P ^ (UniqueFactorizationMonoid.normalizedFactors I).count P := by
  have hsub : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      P ∈ primesOverF (K := K) p :=
    fun P hP => mem_primesOverFinset_of_mem_normalizedFactors (K := K) hI hk hP
  calc I = (UniqueFactorizationMonoid.normalizedFactors I).prod :=
        (Ideal.prod_normalizedFactors_eq_self hI).symm
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
          P ^ (UniqueFactorizationMonoid.normalizedFactors I).count P :=
        Finset.prod_multiset_count _
    _ = ∏ P ∈ primesOverF (K := K) p,
          P ^ (UniqueFactorizationMonoid.normalizedFactors I).count P :=
        Finset.prod_subset (fun P hP => hsub P (Multiset.mem_toFinset.mp hP))
          (fun P _ hPnotin => by
            rw [Multiset.count_eq_zero_of_notMem
              (fun hmem => hPnotin (Multiset.mem_toFinset.mpr hmem)), pow_zero])

/-- The exponent sum identity: for a nonzero ideal of norm `p^k`, the sum of the exponents of the
primes over `p` weighted by inertia degrees is `k`. -/
lemma sum_count_mul_inertiaDeg_eq {p : ℕ} [Fact p.Prime] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    {k : ℕ} (hk : Ideal.absNorm I = p ^ k) :
    ∑ P ∈ primesOverF (K := K) p,
      (UniqueFactorizationMonoid.normalizedFactors I).count P * P.inertiaDeg ℤ = k := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne
  set c : Ideal (𝓞 K) → ℕ := fun P => (UniqueFactorizationMonoid.normalizedFactors I).count P
    with hc
  have hprod : I = ∏ P ∈ primesOverF (K := K) p, P ^ c P := by
    rw [hc]
    exact eq_prod_primesOverFinset (K := K) hI hk
  have hmem : ∀ P ∈ primesOverF (K := K) p,
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ P.IsPrime := by
    intro P hP
    have h := (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne).mp hP
    exact ⟨h.2, h.1⟩
  have hnorm : ∀ P ∈ primesOverF (K := K) p, Ideal.absNorm P = p ^ (P.inertiaDeg ℤ) := by
    intro P hP
    haveI : P.IsPrime := (hmem P hP).2
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := (hmem P hP).1
    exact (Ideal.pow_inertiaDeg p P).symm
  have key : p ^ k = p ^ ∑ P ∈ primesOverF (K := K) p, c P * P.inertiaDeg ℤ := by
    rw [← hk, hprod, absNorm_finset_prod]
    calc ∏ P ∈ primesOverF (K := K) p, Ideal.absNorm (P ^ c P)
        = ∏ P ∈ primesOverF (K := K) p, (p ^ (P.inertiaDeg ℤ)) ^ c P := by
          refine Finset.prod_congr rfl fun P hP => ?_
          rw [absNorm_pow, hnorm P hP]
      _ = ∏ P ∈ primesOverF (K := K) p, p ^ (P.inertiaDeg ℤ * c P) := by
          refine Finset.prod_congr rfl fun P _ => ?_
          rw [← pow_mul]
      _ = p ^ ∑ P ∈ primesOverF (K := K) p, P.inertiaDeg ℤ * c P :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ = p ^ ∑ P ∈ primesOverF (K := K) p, c P * P.inertiaDeg ℤ := by
          congr 1
          exact Finset.sum_congr rfl fun P _ => mul_comm _ _
  exact (Nat.pow_right_injective hp2 key).symm


/-- The number of primes over `p` is at most two in a quadratic field. -/
lemma card_primesOverF_le_two (hfin : Module.finrank ℚ K = 2) (p : ℕ) [Fact p.Prime] :
    (primesOverF (K := K) p).card ≤ 2 := by
  classical
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne
  have hsum := sum_ramification_inertia_eq_two (K := K) hfin p
  have hterm : ∀ x : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      1 ≤ x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ := by
    intro x
    have h1 := Ideal.ramificationIdx_pos ℤ x.1
    have h2 := Ideal.inertiaDeg_pos x.1 ℤ
    nlinarith
  have hcard := Finset.card_nsmul_le_sum (Finset.univ : Finset ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
    (fun x => x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ) 1 (fun x _ => hterm x)
  rw [hsum] at hcard
  have hcard' : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard ≤ 2 := by
    rw [← Set.fintypeCard_eq_ncard]
    simpa [Finset.card_univ] using hcard
  have hfinv : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).Finite :=
    IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [Set.ncard_eq_toFinset_card _ hfinv] at hcard'
  have heq : hfinv.toFinset = primesOverF (K := K) p := by
    ext x
    rw [Set.Finite.mem_toFinset, ← IsDedekindDomain.coe_primesOverFinset (B := 𝓞 K) hpne]
    rfl
  rw [heq] at hcard'
  exact hcard'


/-- The ramification-inertia sum, phrased over the finset of primes over `p`. -/
lemma sum_primesOverF_ramification (hfin : Module.finrank ℚ K = 2) (p : ℕ) [Fact p.Prime] :
    ∑ P ∈ primesOverF (K := K) p, P.ramificationIdx ℤ * P.inertiaDeg ℤ = 2 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne
  rw [← sum_ramification_inertia_eq_two (K := K) hfin p]
  refine Finset.sum_subtype _ ?_ _
  intro x
  exact IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne

/-- Ideals of the same `p`-power norm with the same exponents of the primes over `p` coincide. -/
lemma eq_of_count_eq_on_primesOverF {p : ℕ} [Fact p.Prime] {k : ℕ} {I I' : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = p ^ k) (hI' : Ideal.absNorm I' = p ^ k)
    (h : ∀ P ∈ primesOverF (K := K) p,
      (UniqueFactorizationMonoid.normalizedFactors I).count P =
        (UniqueFactorizationMonoid.normalizedFactors I').count P) :
    I = I' := by
  have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hI
    exact (pow_ne_zero k hpne) hI.symm
  have hne' : I' ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hI'
    exact (pow_ne_zero k hpne) hI'.symm
  rw [eq_prod_primesOverFinset (K := K) hne hI, eq_prod_primesOverFinset (K := K) hne' hI']
  exact Finset.prod_congr rfl fun P hP => by rw [h P hP]

/-- If there is at most one prime over `p`, the number of ideals of norm `p^k` is at most one. -/
lemma subsingleton_ideals_absNorm_prime_pow_of_card_le_one {p : ℕ} [Fact p.Prime] {k : ℕ}
    (h1 : (primesOverF (K := K) p).card ≤ 1) :
    Subsingleton {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} := by
  classical
  have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hfpos : ∀ P ∈ primesOverF (K := K) p, 0 < P.inertiaDeg ℤ := by
    intro P hP
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpne
    have hpne' : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
      (Ideal.span_singleton_eq_bot).not.mpr hp0
    haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
      ((Ideal.span_singleton_prime hp0).mpr
        (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne'
    have hmem := (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp hP
    haveI : P.IsPrime := hmem.1
    exact Ideal.inertiaDeg_pos P ℤ
  refine ⟨fun I I' => ?_⟩
  rcases Nat.eq_zero_or_pos (primesOverF (K := K) p).card with h0 | hpos
  · -- empty finset
    have hempty : primesOverF (K := K) p = ∅ := Finset.card_eq_zero.mp h0
    have hcount : ∀ P ∈ primesOverF (K := K) p,
        (UniqueFactorizationMonoid.normalizedFactors I.1).count P =
          (UniqueFactorizationMonoid.normalizedFactors I'.1).count P := by
      simp [hempty]
    exact Subtype.ext (eq_of_count_eq_on_primesOverF I.2 I'.2 hcount)
  · obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp (by omega : (primesOverF (K := K) p).card = 1)
    have hneI : I.1 ≠ ⊥ := by
      rintro h
      have h2 : Ideal.absNorm (⊥ : Ideal (𝓞 K)) = p ^ k := by rw [← h]; exact I.2
      rw [Ideal.absNorm_bot] at h2
      exact (pow_ne_zero k hpne) h2.symm
    have hneI' : I'.1 ≠ ⊥ := by
      rintro h
      have h2 : Ideal.absNorm (⊥ : Ideal (𝓞 K)) = p ^ k := by rw [← h]; exact I'.2
      rw [Ideal.absNorm_bot] at h2
      exact (pow_ne_zero k hpne) h2.symm
    have hsumI := sum_count_mul_inertiaDeg_eq (K := K) (k := k) (I := I.1) hneI I.2
    have hsumI' := sum_count_mul_inertiaDeg_eq (K := K) (k := k) (I := I'.1) hneI' I'.2
    rw [hQ, Finset.sum_singleton] at hsumI hsumI'
    have hcount : ∀ P ∈ primesOverF (K := K) p,
        (UniqueFactorizationMonoid.normalizedFactors I.1).count P =
          (UniqueFactorizationMonoid.normalizedFactors I'.1).count P := by
      intro P hP
      rw [hQ, Finset.mem_singleton] at hP
      rw [hP]
      have hf := hfpos Q (by rw [hQ]; exact Finset.mem_singleton_self Q)
      have : (UniqueFactorizationMonoid.normalizedFactors I.1).count Q * Q.inertiaDeg ℤ =
          (UniqueFactorizationMonoid.normalizedFactors I'.1).count Q * Q.inertiaDeg ℤ := by
        rw [hsumI, hsumI']
      exact Nat.mul_right_cancel hf this
    exact Subtype.ext (eq_of_count_eq_on_primesOverF I.2 I'.2 hcount)

/-- If there is at most one prime over `p`, there is at most one ideal of norm `p^k`. -/
lemma card_ideals_absNorm_prime_pow_le_one_of_card_le_one {p : ℕ} [Fact p.Prime] (k : ℕ)
    (h1 : (primesOverF (K := K) p).card ≤ 1) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} ≤ 1 := by
  haveI := subsingleton_ideals_absNorm_prime_pow_of_card_le_one (K := K) (k := k) h1
  have hinj : Function.Injective
      (fun _ : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} => (0 : Fin 1)) :=
    fun a b _ => Subsingleton.elim a b
  have h := Nat.card_le_card_of_injective _ hinj
  simpa using h


/-- The number of ideals of norm `p^k` in a quadratic field is at most `k+1`. -/
lemma card_ideals_absNorm_prime_pow_le (hfin : Module.finrank ℚ K = 2) (p : ℕ) [Fact p.Prime]
    (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} ≤ k + 1 := by
  classical
  have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpne
  have hpne' : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne'
  rcases lt_or_eq_of_le (card_primesOverF_le_two (K := K) hfin p) with hlt | heq
  · exact le_trans (card_ideals_absNorm_prime_pow_le_one_of_card_le_one (K := K) k (by omega))
      (by omega)
  · obtain ⟨𝔭, 𝔮, hpq, hFeq⟩ := Finset.card_eq_two.mp heq
    have h𝔭mem : 𝔭 ∈ primesOverF (K := K) p := by
      rw [hFeq]; exact Finset.mem_insert_self _ _
    have h𝔮mem : 𝔮 ∈ primesOverF (K := K) p := by
      rw [hFeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    haveI : 𝔭.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp h𝔭mem).1
    haveI : 𝔮.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp h𝔮mem).1
    have hfp : 0 < 𝔭.inertiaDeg ℤ := Ideal.inertiaDeg_pos 𝔭 ℤ
    have hfq : 0 < 𝔮.inertiaDeg ℤ := Ideal.inertiaDeg_pos 𝔮 ℤ
    have hne_of : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}, I.1 ≠ ⊥ := by
      intro I h
      have h2 : Ideal.absNorm (⊥ : Ideal (𝓞 K)) = p ^ k := by rw [← h]; exact I.2
      rw [Ideal.absNorm_bot] at h2
      exact (pow_ne_zero k hpne) h2.symm
    have hsum : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k},
        (UniqueFactorizationMonoid.normalizedFactors I.1).count 𝔭 * 𝔭.inertiaDeg ℤ
          + (UniqueFactorizationMonoid.normalizedFactors I.1).count 𝔮 * 𝔮.inertiaDeg ℤ = k := by
      intro I
      have h := sum_count_mul_inertiaDeg_eq (K := K) (hne_of I) I.2
      rwa [hFeq, Finset.sum_pair hpq] at h
    have hinj : Function.Injective (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} =>
        (⟨(UniqueFactorizationMonoid.normalizedFactors I.1).count 𝔮, by
          have h := hsum I
          have h2 : (UniqueFactorizationMonoid.normalizedFactors I.1).count 𝔮 ≤
              (UniqueFactorizationMonoid.normalizedFactors I.1).count 𝔮 * 𝔮.inertiaDeg ℤ :=
            Nat.le_mul_of_pos_right _ hfq
          omega⟩ : Fin (k + 1))) := by
      intro I I' hII'
      have hc : (UniqueFactorizationMonoid.normalizedFactors I.1).count 𝔮 =
          (UniqueFactorizationMonoid.normalizedFactors I'.1).count 𝔮 := by
        simpa using congrArg Fin.val hII'
      refine Subtype.ext (eq_of_count_eq_on_primesOverF (K := K) I.2 I'.2 ?_)
      intro P hP
      rw [hFeq, Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with hP | hP
      · rw [hP]
        have h1 := hsum I
        have h2 := hsum I'
        have e2 : (UniqueFactorizationMonoid.normalizedFactors I.1).count 𝔮 * 𝔮.inertiaDeg ℤ =
            (UniqueFactorizationMonoid.normalizedFactors I'.1).count 𝔮 * 𝔮.inertiaDeg ℤ := by
          rw [hc]
        have e1 : (UniqueFactorizationMonoid.normalizedFactors I.1).count 𝔭 * 𝔭.inertiaDeg ℤ =
            (UniqueFactorizationMonoid.normalizedFactors I'.1).count 𝔭 * 𝔭.inertiaDeg ℤ := by
          omega
        exact Nat.mul_right_cancel hfp e1
      · rw [hP]; exact hc
    have hcard := Nat.card_le_card_of_injective _ hinj
    simpa using hcard


/-- If no prime over `p` has inertia degree one, there is exactly one prime over `p`, and its
inertia degree is two. -/
lemma eq_single_of_no_inertiaDeg_one (hfin : Module.finrank ℚ K = 2) {p : ℕ} [Fact p.Prime]
    (h : ∀ P ∈ primesOverF (K := K) p, P.inertiaDeg ℤ ≠ 1) :
    ∃ P : Ideal (𝓞 K), primesOverF (K := K) p = {P} ∧ P.inertiaDeg ℤ = 2 := by
  classical
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpne' : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne'
  have hsum := sum_primesOverF_ramification (K := K) hfin p
  have hterm : ∀ P ∈ primesOverF (K := K) p, 2 ≤ P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
    intro P hP
    haveI : P.IsPrime :=
      ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp hP).1
    have h1 : 1 ≤ P.ramificationIdx ℤ := Ideal.ramificationIdx_pos ℤ P
    have h2 : 2 ≤ P.inertiaDeg ℤ := by
      have := Ideal.inertiaDeg_pos P ℤ
      have := h P hP
      omega
    nlinarith
  have hcardle : (primesOverF (K := K) p).card ≤ 1 := by
    have hc := Finset.card_nsmul_le_sum (primesOverF (K := K) p)
      (fun P => P.ramificationIdx ℤ * P.inertiaDeg ℤ) 2 hterm
    rw [hsum] at hc
    simpa using hc
  have hcardne : (primesOverF (K := K) p).card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty] at hsum
    omega
  have hcard : (primesOverF (K := K) p).card = 1 := by omega
  obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hcard
  refine ⟨P, hP, ?_⟩
  have hPmem : P ∈ primesOverF (K := K) p := by rw [hP]; exact Finset.mem_singleton_self P
  have h1 : 1 ≤ P.ramificationIdx ℤ := by
    haveI : P.IsPrime :=
      ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp hPmem).1
    exact Ideal.ramificationIdx_pos ℤ P
  have h2 : 2 ≤ P.inertiaDeg ℤ := by
    have := h P hPmem
    have hpos : 0 < P.inertiaDeg ℤ := by
      haveI : P.IsPrime :=
        ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp hPmem).1
      exact Ideal.inertiaDeg_pos P ℤ
    omega
  have := hterm P hPmem
  rw [hP, Finset.sum_singleton] at hsum
  nlinarith

/-- If no prime over `p` has inertia degree one, there is at most one ideal of norm `p^k`. -/
lemma card_ideals_absNorm_prime_pow_le_one_of_no_inertiaDeg_one (hfin : Module.finrank ℚ K = 2)
    {p : ℕ} [Fact p.Prime]
    (h : ∀ P ∈ primesOverF (K := K) p, P.inertiaDeg ℤ ≠ 1) (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} ≤ 1 := by
  obtain ⟨P, hP, _⟩ := eq_single_of_no_inertiaDeg_one (K := K) hfin h
  exact card_ideals_absNorm_prime_pow_le_one_of_card_le_one (K := K) k (by rw [hP]; simp)

/-- If no prime over `p` has inertia degree one, there is no ideal of norm `p^k` for odd `k`. -/
lemma card_ideals_absNorm_prime_pow_eq_zero_of_odd_of_no_inertiaDeg_one
    (hfin : Module.finrank ℚ K = 2) {p : ℕ} [Fact p.Prime]
    (h : ∀ P ∈ primesOverF (K := K) p, P.inertiaDeg ℤ ≠ 1) {k : ℕ} (hk : Odd k) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} = 0 := by
  classical
  obtain ⟨P, hP, hfP⟩ := eq_single_of_no_inertiaDeg_one (K := K) hfin h
  have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hPmem : P ∈ primesOverF (K := K) p := by rw [hP]; exact Finset.mem_singleton_self P
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpne
  have hpne' : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI : P.IsPrime :=
    ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp hPmem).1
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun I => ?_⟩
  exfalso
  have hneI : I.1 ≠ ⊥ := by
    rintro h
    have h2 : Ideal.absNorm (⊥ : Ideal (𝓞 K)) = p ^ k := by rw [← h]; exact I.2
    rw [Ideal.absNorm_bot] at h2
    exact (pow_ne_zero k hpne) h2.symm
  have hsum := sum_count_mul_inertiaDeg_eq (K := K) hneI I.2
  rw [hP, Finset.sum_singleton, hfP] at hsum
  obtain ⟨m, hm⟩ := hk
  omega


/-! ### Splitting of primes in `ℚ(√D)` -/

/-- If a prime `P` over `(p)` has inertia degree one, then any element of `𝓞 K` whose square is
`D` produces a square root of `D` modulo `p`. -/
theorem isSquare_mod_of_inertiaDeg_one {p : ℕ} [Fact p.Prime] {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hlies : P.LiesOver (Ideal.span {(p : ℤ)})) (hf : P.inertiaDeg ℤ = 1)
    {D : ℤ} {u : 𝓞 K} (hu : u ^ 2 = algebraMap ℤ (𝓞 K) D) :
    IsSquare ((D : ℤ) : ZMod p) := by
  haveI := hP
  haveI := hlies
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  haveI : P.IsMaximal := by
    have hpne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
      (Ideal.span_singleton_eq_bot).not.mpr hp0
    exact Ideal.isMaximal_of_isPrime_of_ne_bot P
      (Ideal.ne_bot_of_liesOver_of_ne_bot hpne P)
  have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hcard : Nat.card (𝓞 K ⧸ P) = p := by
    have h2 : Nat.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h2, ← Ideal.pow_inertiaDeg p P, hf, pow_one]
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hpne)
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcardN : Nat.card (𝓞 K ⧸ P) = Nat.card (ZMod p) := by
    rw [hcard]
    exact (Nat.card_eq_fintype_card.trans (ZMod.card p)).symm
  have hcard' : Fintype.card (𝓞 K ⧸ P) = Fintype.card (ZMod p) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardN
  letI hfield : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let e : (𝓞 K ⧸ P) ≃+* ZMod p := FiniteField.ringEquivOfCardEq hcard'
  have hx : ((u : 𝓞 K) : 𝓞 K ⧸ P) ^ 2 = ((D : ℤ) : 𝓞 K ⧸ P) := by
    rw [← map_pow, hu]
    exact map_intCast _ _
  have hfinal : e (((D : ℤ) : 𝓞 K ⧸ P)) = ((D : ℤ) : ZMod p) := map_intCast e D
  refine ⟨e ((u : 𝓞 K) : 𝓞 K ⧸ P), ?_⟩
  rw [← map_mul, ← pow_two, hx]
  exact hfinal.symm


/-- For an odd prime `p ∤ N` with `χ(p) = -1`, no prime over `p` has inertia degree one. -/
theorem no_inertiaDeg_one_of_jacobiSym_eq_neg_one (u : 𝓞 K) {D : ℤ}
    (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ)) {p : ℕ} [Fact p.Prime]
    (hJ : jacobiSym D p = -1) :
    ∀ 𝔭 ∈ primesOverF (K := K) p, 𝔭.inertiaDeg ℤ ≠ 1 := by
  have huO : u ^ 2 = algebraMap ℤ (𝓞 K) D := by
    apply Subtype.coe_injective
    change ((u : K)) ^ 2 = ((D : ℤ) : K)
    rw [hu]
    simp
  intro 𝔭 h𝔭 hf
  have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpne
  have hpne' : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  have hmem := (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp h𝔭
  have hsq : IsSquare ((D : ℤ) : ZMod p) :=
    isSquare_mod_of_inertiaDeg_one (K := K) hmem.1 hmem.2 hf huO
  have hpD : ¬ (p : ℤ) ∣ D := by
    intro h
    have h0 : jacobiSym D p = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym p D]
      exact (legendreSym.eq_zero_iff p D).mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr h)
    omega
  have hne0 : ((D : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    exact hpD ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h0)
  have hqc : quadraticChar (ZMod p) ((D : ℤ) : ZMod p) = 1 :=
    (quadraticChar_one_iff_isSquare hne0).mpr hsq
  have : jacobiSym D p = 1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym p D]
    exact hqc
  omega


/-- For a prime `p` with `p ∣ D` and `p² ∤ D`, there is at most one prime over `p`. -/
theorem card_primesOverF_le_one_of_dvd_not_dvd_sq (u : 𝓞 K) {D : ℤ}
    (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ)) (hfin : Module.finrank ℚ K = 2)
    {p : ℕ} [Fact p.Prime] (hpD : (p : ℤ) ∣ D) (hpsq : ¬ (p : ℤ) ^ 2 ∣ D) :
    (primesOverF (K := K) p).card ≤ 1 := by
  classical
  have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpne
  have hpne' : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot).not.mpr hp0
  haveI hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))).isMaximal hpne'
  have huO : u ^ 2 = algebraMap ℤ (𝓞 K) D := by
    apply Subtype.coe_injective
    change ((u : K)) ^ 2 = ((D : ℤ) : K)
    rw [hu]; simp
  -- the norm of the principal ideal `(u)` is `|D|`
  have hnorm : Ideal.absNorm (Ideal.span ({u} : Set (𝓞 K))) = D.natAbs := by
    have hspan : Ideal.span ({u} : Set (𝓞 K)) ^ 2 =
        Ideal.span ({algebraMap ℤ (𝓞 K) D} : Set (𝓞 K)) := by
      rw [Ideal.span_singleton_pow, huO]
    have hbase : Ideal.absNorm (Ideal.span ({algebraMap ℤ (𝓞 K) D} : Set (𝓞 K))) =
        D.natAbs ^ 2 := by
      rw [Ideal.absNorm_span_singleton, Algebra.norm_algebraMap,
        NumberField.RingOfIntegers.rank, hfin, Int.natAbs_pow]
    have hsq : Ideal.absNorm (Ideal.span ({u} : Set (𝓞 K))) ^ 2 = D.natAbs ^ 2 := by
      rw [← absNorm_pow, hspan, hbase]
    exact Nat.mul_self_inj.mp (by simpa [pow_two] using hsq)
  by_contra hcon
  have hlt : 1 < (primesOverF (K := K) p).card := not_le.mp hcon
  obtain ⟨𝔭, h𝔭mem, 𝔮, h𝔮mem, hne⟩ := Finset.one_lt_card.mp hlt
  have h𝔭lies : 𝔭.LiesOver (Ideal.span {(p : ℤ)}) :=
    ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp h𝔭mem).2
  have h𝔮lies : 𝔮.LiesOver (Ideal.span {(p : ℤ)}) :=
    ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp h𝔮mem).2
  haveI h𝔭prime : 𝔭.IsPrime :=
    ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp h𝔭mem).1
  haveI h𝔮prime : 𝔮.IsPrime :=
    ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hpne').mp h𝔮mem).1
  haveI h𝔭max : 𝔭.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot 𝔭
    (Ideal.ne_bot_of_liesOver_of_ne_bot hpne' 𝔭)
  haveI h𝔮max : 𝔮.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot 𝔮
    (Ideal.ne_bot_of_liesOver_of_ne_bot hpne' 𝔮)
  -- `(p) ⊆ 𝔭` and `(p) ⊆ 𝔮`, hence `(p) ⊆ 𝔭 * 𝔮`
  have hle𝔭 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≤ 𝔭 :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq h𝔭lies.over)
  have hle𝔮 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≤ 𝔮 :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq h𝔮lies.over)
  have hcop : IsCoprime 𝔭 𝔮 := Ideal.isCoprime_of_isMaximal hne
  have hpprod : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≤ 𝔭 * 𝔮 := by
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf hle𝔭 hle𝔮
  have hpSpan : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) =
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp
  -- consequently `p ^ (f_𝔭 + f_𝔮) ∣ p ^ 2`
  have hdivp : p ^ (𝔭.inertiaDeg ℤ + 𝔮.inertiaDeg ℤ) ∣ p ^ 2 := by
    have h1 : Ideal.absNorm (𝔭 * 𝔮) ∣
        Ideal.absNorm ((Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K))) :=
      Ideal.absNorm_dvd_absNorm_of_le hpprod
    rw [hpSpan, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hfin] at h1
    have h2 : Ideal.absNorm (𝔭 * 𝔮) = p ^ (𝔭.inertiaDeg ℤ + 𝔮.inertiaDeg ℤ) := by
      rw [show Ideal.absNorm (𝔭 * 𝔮) = Ideal.absNorm 𝔭 * Ideal.absNorm 𝔮 from cardQuot_mul 𝔭 𝔮,
        ← Ideal.pow_inertiaDeg p 𝔭, ← Ideal.pow_inertiaDeg p 𝔮, ← pow_add]
    rwa [h2] at h1
  have hfsum : 𝔭.inertiaDeg ℤ + 𝔮.inertiaDeg ℤ = 2 := by
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp hdivp
    have h1 : 1 ≤ 𝔭.inertiaDeg ℤ := Ideal.inertiaDeg_pos 𝔭 ℤ
    have h2 : 1 ≤ 𝔮.inertiaDeg ℤ := Ideal.inertiaDeg_pos 𝔮 ℤ
    have h3 : p ^ (𝔭.inertiaDeg ℤ + 𝔮.inertiaDeg ℤ) = p ^ j := hj'
    have := Nat.pow_right_injective (Fact.out : Nat.Prime p).two_le h3
    omega
  -- `p ∈ 𝔭 * 𝔮`, and `D = p * c`, so `D ∈ 𝔭 * 𝔮`
  have hp_mem' : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ 𝔭 * 𝔮 :=
    hpprod (Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 K)) (Ideal.mem_span_singleton_self (p : ℤ)))
  have hp_mem : ((p : ℤ) : 𝓞 K) ∈ 𝔭 * 𝔮 := by simpa using hp_mem'
  have hD_mem : (D : 𝓞 K) ∈ 𝔭 * 𝔮 := by
    obtain ⟨c, hc⟩ := hpD
    have hthis : (D : 𝓞 K) = ((p : ℤ) : 𝓞 K) * ((c : ℤ) : 𝓞 K) := by
      rw [hc]; push_cast; ring
    rw [hthis]
    exact Ideal.mul_mem_right _ (𝔭 * 𝔮) hp_mem
  have hu2 : u ^ 2 ∈ 𝔭 * 𝔮 := by rw [huO]; exact hD_mem
  have hu_mem : u ∈ 𝔭 * 𝔮 := by
    have h1 : u ∈ 𝔭 := h𝔭prime.mem_of_pow_mem 2 (by
      rw [huO]
      exact (Ideal.mul_le_left : 𝔭 * 𝔮 ≤ 𝔭) hD_mem)
    have h2 : u ∈ 𝔮 := h𝔮prime.mem_of_pow_mem 2 (by
      rw [huO]
      exact (Ideal.mul_le_right : 𝔭 * 𝔮 ≤ 𝔮) hD_mem)
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact ⟨h1, h2⟩
  -- hence `p^2 ∣ |D|`, contradiction
  have hdivD : p ^ 2 ∣ D.natAbs := by
    have h1 : Ideal.absNorm (𝔭 * 𝔮) ∣ Ideal.absNorm (Ideal.span ({u} : Set (𝓞 K))) :=
      Ideal.absNorm_dvd_absNorm_of_le (Ideal.span_singleton_le_iff_mem _ |>.mpr hu_mem)
    have h2 : Ideal.absNorm (𝔭 * 𝔮) = p ^ 2 := by
      rw [show Ideal.absNorm (𝔭 * 𝔮) = Ideal.absNorm 𝔭 * Ideal.absNorm 𝔮 from cardQuot_mul 𝔭 𝔮,
        ← Ideal.pow_inertiaDeg p 𝔭, ← Ideal.pow_inertiaDeg p 𝔮, ← pow_add, hfsum]
    rwa [h2, hnorm] at h1
  exact hpsq (by
    have : ((p : ℤ)) ^ 2 = ((p ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
    exact Int.natCast_dvd.mpr hdivD)

end Counting


section Multiplicativity

variable {K : Type*} [Field K] [NumberField K]

/-- `(m)` and `(n)` are comaximal when `m` and `n` are coprime. -/
lemma sup_span_eq_top_of_coprime {m n : ℕ} (hcop : m.Coprime n) :
    Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) ⊔
      Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) = ⊤ := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (m : ℤ) + b * (n : ℤ) = 1 := hcop.isCoprime
  have hbez : algebraMap ℤ (𝓞 K) a * (m : 𝓞 K) + algebraMap ℤ (𝓞 K) b * (n : 𝓞 K) = 1 := by
    have h := congrArg (algebraMap ℤ (𝓞 K)) hab
    push_cast at h
    simpa using h
  rw [Ideal.eq_top_iff_one, ← Ideal.add_eq_sup, ← hbez]
  exact Submodule.add_mem_sup
    (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self (m : 𝓞 K)))
    (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self (n : 𝓞 K)))

/-- The product `(I + (m)) * (I + (n))` equals `I` when `m` and `n` are coprime and `m * n ∈ I`. -/
lemma sup_mul_sup_eq_self {m n : ℕ} (hcop : m.Coprime n) {I : Ideal (𝓞 K)}
    (hmn : (m : 𝓞 K) * (n : 𝓞 K) ∈ I) :
    (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) *
      (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) = I := by
  refine le_antisymm ?_ ?_
  · rw [← Ideal.add_eq_sup, ← Ideal.add_eq_sup, add_mul, mul_add, mul_add]
    rw [add_le_iff]
    refine ⟨?_, ?_⟩
    · rw [add_le_iff]
      exact ⟨Ideal.mul_le_left, Ideal.mul_le_left⟩
    · rw [add_le_iff]
      refine ⟨Ideal.mul_le_right, ?_⟩
      rw [Ideal.span_singleton_mul_span_singleton]
      exact (Ideal.span_singleton_le_iff_mem I).mpr hmn
  · obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (m : ℤ) + b * (n : ℤ) = 1 := hcop.isCoprime
    have hbez : algebraMap ℤ (𝓞 K) a * (m : 𝓞 K) + algebraMap ℤ (𝓞 K) b * (n : 𝓞 K) = 1 := by
      have h := congrArg (algebraMap ℤ (𝓞 K)) hab
      push_cast at h
      simpa using h
    intro x hx
    have hx' : x = (m : 𝓞 K) * (x * algebraMap ℤ (𝓞 K) a) +
        (n : 𝓞 K) * (x * algebraMap ℤ (𝓞 K) b) := by
      calc x = x * 1 := (mul_one x).symm
        _ = x * (algebraMap ℤ (𝓞 K) a * (m : 𝓞 K) +
              algebraMap ℤ (𝓞 K) b * (n : 𝓞 K)) := by rw [hbez]
        _ = (m : 𝓞 K) * (x * algebraMap ℤ (𝓞 K) a) +
              (n : 𝓞 K) * (x * algebraMap ℤ (𝓞 K) b) := by ring
    rw [hx']
    have hxm : x * algebraMap ℤ (𝓞 K) a ∈ I := by
      simpa [mul_comm] using Ideal.mul_mem_left I (algebraMap ℤ (𝓞 K) a) hx
    have hxn : x * algebraMap ℤ (𝓞 K) b ∈ I := by
      simpa [mul_comm] using Ideal.mul_mem_left I (algebraMap ℤ (𝓞 K) b) hx
    refine Ideal.add_mem ((I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) *
      (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)))) ?_ ?_
    · exact Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_left hxm)
    · rw [mul_comm (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)))
        (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)))]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_left hxn)

/-- If `I` has norm `m * n` with `m`, `n` coprime, then `𝓞 K / (I + (m))` has `m` elements. -/
lemma absNorm_sup_span_eq {m n : ℕ} (hfin : Module.finrank ℚ K = 2) (hm : m ≠ 0)
    (hn : n ≠ 0) (hcop : m.Coprime n) {I : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) = m := by
  have hmn : (m : 𝓞 K) * (n : 𝓞 K) ∈ I := by
    have h := Ideal.span_singleton_absNorm_le I
    rw [hI] at h
    have := h (Ideal.mem_span_singleton_self _)
    simpa [Nat.cast_mul] using this
  have hprod := sup_mul_sup_eq_self (K := K) hcop hmn
  have hci : IsCoprime (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)))
      (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff]
    calc ⊤ = Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) ⊔
          Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) :=
          (sup_span_eq_top_of_coprime (K := K) hcop).symm
      _ ≤ (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) ⊔
          (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) := sup_le_sup le_sup_right le_sup_right
  set A : ℕ := Ideal.absNorm (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) with hA
  set B : ℕ := Ideal.absNorm (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) with hB
  have hAB : A * B = m * n := by
    have h1 : Submodule.cardQuot ((I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) *
        (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)))) =
        Submodule.cardQuot (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) *
          Submodule.cardQuot (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) :=
      cardQuot_mul_of_coprime hci
    rw [hA, hB, Ideal.absNorm_apply, Ideal.absNorm_apply, ← h1, hprod,
      ← Ideal.absNorm_apply]
    exact hI
  have hAm : A ∣ m * m := by
    have h : Ideal.absNorm (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) ∣
        Ideal.absNorm (Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) :=
      Ideal.absNorm_dvd_absNorm_of_le le_sup_right
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hfin] at h
    rw [hA]
    simpa [pow_two] using h
  have hBn : B ∣ n * n := by
    have h : Ideal.absNorm (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) ∣
        Ideal.absNorm (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) :=
      Ideal.absNorm_dvd_absNorm_of_le le_sup_right
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hfin] at h
    rw [hB]
    simpa [pow_two] using h
  have hAcop : A.Coprime n := by
    have h1 : n.Coprime m := hcop.symm
    have h2 : n.Coprime (m * m) := by simpa [pow_two] using h1.pow_right 2
    exact (h2.coprime_dvd_right hAm).symm
  have hA_m : A ∣ m := by
    have h : A ∣ m * n := ⟨B, hAB.symm⟩
    exact hAcop.dvd_of_dvd_mul_right h
  have hB_n : B ∣ n := by
    have hBcop : B.Coprime m := by
      have h2 : m.Coprime (n * n) := by simpa [pow_two] using hcop.pow_right 2
      exact (h2.coprime_dvd_right hBn).symm
    have h : B ∣ n * m := ⟨A, by rw [mul_comm n m, hAB.symm, mul_comm]⟩
    exact hBcop.dvd_of_dvd_mul_right h
  obtain ⟨t, ht⟩ := hA_m
  obtain ⟨u, hu⟩ := hB_n
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hAB
    exact (mul_ne_zero hm hn) hAB.symm
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hAB
    exact (mul_ne_zero hm hn) hAB.symm
  have htu : t * u = 1 := by
    have h1 : m * n = A * t * (B * u) := by rw [← ht, ← hu]
    have h2 : A * t * (B * u) = A * B * (t * u) := by ring
    have h3 : A * B = A * B * (t * u) := by
      calc A * B = m * n := hAB
        _ = A * t * (B * u) := h1
        _ = A * B * (t * u) := h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero hA0 hB0))
      (by simpa using h3.symm)
  have ht1 : t = 1 := Nat.dvd_one.mp ⟨u, htu.symm⟩
  have hm : m = A := by rw [ht, ht1, mul_one]
  exact hm.symm


/-- `(I + (m))` and `(I + (n))` are coprime when `m`, `n` are. -/
lemma isCoprime_sup_span_sup_span {m n : ℕ} (hcop : m.Coprime n) (I : Ideal (𝓞 K)) :
    IsCoprime (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)))
      (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) := by
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff]
  calc ⊤ = Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) ⊔
        Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) :=
        (sup_span_eq_top_of_coprime (K := K) hcop).symm
    _ ≤ (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) ⊔
        (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) := sup_le_sup le_sup_right le_sup_right

/-- If `I` has norm `m * n`, then `m * n ∈ I`. -/
lemma mul_mem_of_absNorm_eq {m n : ℕ} {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = m * n) :
    (m : 𝓞 K) * (n : 𝓞 K) ∈ I := by
  have h := Ideal.span_singleton_absNorm_le I
  rw [hI] at h
  have := h (Ideal.mem_span_singleton_self _)
  simpa [Nat.cast_mul] using this

/-- Ideals of norm `m * n` with `m`, `n` coprime are determined by their `m`- and `n`-parts. -/
lemma eq_inf_sup_span {m n : ℕ} (hcop : m.Coprime n) {I : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = m * n) :
    I = (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) ⊓
      (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) := by
  have hprod := sup_mul_sup_eq_self (K := K) hcop (mul_mem_of_absNorm_eq (K := K) hI)
  exact hprod.symm.trans (Ideal.mul_eq_inf_of_isCoprime
    (isCoprime_sup_span_sup_span (K := K) hcop I))

/-- The number of ideals of norm `m * n` is at most the product of the numbers of ideals of
norm `m` and of norm `n`, for coprime `m` and `n`. -/
lemma card_ideals_absNorm_mul_le (hfin : Module.finrank ℚ K = 2) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hcop : m.Coprime n) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n} ≤
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} *
        Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
  classical
  have hmn : ∀ {J : Ideal (𝓞 K)}, Ideal.absNorm J = m * n →
      Ideal.absNorm J = n * m := fun h => by rw [h, mul_comm]
  let Φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n} →
      {J : Ideal (𝓞 K) // Ideal.absNorm J = m} ×
        {J : Ideal (𝓞 K) // Ideal.absNorm J = n} :=
    fun I => (⟨I.1 ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)),
        absNorm_sup_span_eq (K := K) hfin hm hn hcop I.2⟩,
      ⟨I.1 ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)),
        absNorm_sup_span_eq (K := K) hfin hn hm hcop.symm (hmn I.2)⟩)
  have hinj : Function.Injective Φ := by
    intro I I' h
    have h1 : I.1 ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) =
        I'.1 ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) := by
      simpa using congrArg (fun t => (t.1 : Ideal (𝓞 K))) h
    have h2 : I.1 ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) =
        I'.1 ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) := by
      simpa using congrArg (fun t => (t.2 : Ideal (𝓞 K))) h
    refine Subtype.ext ?_
    rw [eq_inf_sup_span (K := K) hcop I.2, eq_inf_sup_span (K := K) hcop I'.2, h1, h2]
  haveI : Fintype {J : Ideal (𝓞 K) // Ideal.absNorm J = m} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) m).fintype
  haveI : Fintype {J : Ideal (𝓞 K) // Ideal.absNorm J = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).fintype
  have hle := Nat.card_le_card_of_injective Φ hinj
  rwa [Nat.card_prod] at hle

end Multiplicativity

section Comparison

/-- The number of ideals of norm `n` is at most the product over the prime powers dividing `n`. -/
lemma card_ideals_absNorm_le_factorization (hfin : Module.finrank ℚ K = 2) {n : ℕ} (hn : n ≠ 0) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ≤
      ∏ p ∈ n.primeFactors,
        Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ n.factorization p} := by
  classical
  have hmain : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = ∏ p ∈ s, p ^ n.factorization p} ≤
        ∏ p ∈ s, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ n.factorization p} := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
        intro hs
        have ha' : a.Prime := hs a (Finset.mem_insert_self a s)
        have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
        have hcop : a.Coprime (∏ p ∈ s, p ^ n.factorization p) := by
          refine Nat.Coprime.prod_right fun p hp => ?_
          have hne : p ≠ a := fun h => ha (h ▸ hp)
          exact (ha'.coprime_iff_not_dvd.mpr fun hdvd =>
            hne ((Nat.Prime.dvd_iff_eq (hs' p hp) ha'.ne_one).mp hdvd)).pow_right _
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        refine le_trans (card_ideals_absNorm_mul_le (K := K) hfin ?_ ?_
          (hcop.pow_left (n.factorization a))) ?_
        · exact pow_ne_zero _ ha'.ne_zero
        · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hs' p hp).ne_zero
        · exact Nat.mul_le_mul_left _ (ih hs')
  have h1 : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    rw [← Nat.support_factorization n]
    exact Nat.prod_factorization_pow_eq_self hn
  have h2 := hmain n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rwa [h1] at h2

/-- The number of ideals of norm `n` is at most `Re (χ * ζ)(n)` for a quadratic character `χ`. -/
theorem card_ideals_absNorm_le_zetaMul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hsq : χ * χ = 1) (hfin : Module.finrank ℚ K = 2)
    (hlocal : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} ≤ (χ.zetaMul (p ^ k)).re)
    {n : ℕ} (hn : n ≠ 0) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ≤ (χ.zetaMul n).re := by
  classical
  have hfac := card_ideals_absNorm_le_factorization (K := K) hfin hn
  have hzeta : χ.zetaMul n = n.factorization.prod fun p k => χ.zetaMul (p ^ k) :=
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ χ.isMultiplicative_zetaMul hn
  have hre : (n.factorization.prod fun p k => χ.zetaMul (p ^ k)).re =
      ∏ p ∈ n.factorization.support, (χ.zetaMul (p ^ n.factorization p)).re := by
    rw [Finsupp.prod]
    have hterm : ∀ p ∈ n.factorization.support, χ.zetaMul (p ^ n.factorization p) =
        ((χ.zetaMul (p ^ n.factorization p)).re : ℂ) :=
      fun p _ => zetaMul_eq_ofReal_re χ (by rw [pow_two]; exact hsq) _
    rw [Finset.prod_congr rfl hterm, ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [hzeta, hre, Nat.support_factorization n]
  have hcast : ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)) ≤
      ∏ p ∈ n.primeFactors, ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I =
        p ^ n.factorization p} : ℝ)) := by exact_mod_cast hfac
  refine le_trans hcast ?_
  refine Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg _) fun p hp => ?_
  exact_mod_cast hlocal p (Nat.prime_of_mem_primeFactors hp) (n.factorization p)

end Comparison

section LocalBounds

variable {K : Type*} [Field K] [NumberField K]

/-- The value of `ζ * χ` at a prime power. -/
lemma zetaMul_prime_pow_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    χ.zetaMul (p ^ k) = ∑ i ∈ Finset.range (k + 1), (χ (p : ZMod N)) ^ i := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk]
  rw [if_neg (pow_ne_zero i hp.ne_zero), Nat.cast_pow, map_pow]

lemma zetaMul_prime_pow_eq_of_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {p : ℕ}
    (hp : p.Prime) (k : ℕ) (h : χ (p : ZMod N) = 1) :
    χ.zetaMul (p ^ k) = (k + 1 : ℂ) := by
  rw [zetaMul_prime_pow_eq χ hp k, Finset.sum_congr rfl (fun i _ => by rw [h, one_pow]),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

lemma zetaMul_prime_pow_eq_of_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {p : ℕ}
    (hp : p.Prime) (k : ℕ) (h : χ (p : ZMod N) = 0) :
    χ.zetaMul (p ^ k) = 1 := by
  rw [zetaMul_prime_pow_eq χ hp k, Finset.sum_eq_single 0]
  · rw [h, pow_zero]
  · intro i hi h0
    rw [h, zero_pow h0]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0

lemma sum_neg_one_pow (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), ((-1 : ℂ)) ^ i) = if _root_.Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd k with hk | hk
      · have hk1 : _root_.Odd (k + 1) := hk.add_one
        rw [if_pos hk, if_neg (Nat.not_even_iff_odd.mpr hk1), hk1.neg_one_pow]
        ring
      · have hk1 : _root_.Even (k + 1) := hk.add_one
        rw [if_neg (Nat.not_even_iff_odd.mpr hk), if_pos hk1, hk1.neg_one_pow]
        ring

lemma zetaMul_prime_pow_eq_of_eq_neg_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) (k : ℕ) (h : χ (p : ZMod N) = -1) :
    χ.zetaMul (p ^ k) = if _root_.Even k then 1 else 0 := by
  rw [zetaMul_prime_pow_eq χ hp k,
    Finset.sum_congr rfl (fun i _ => by rw [h]), sum_neg_one_pow]


/-- `χ(p) = 0` forces `p ∣ N`. -/
lemma dvd_of_chi_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {p : ℕ}
    (hp : p.Prime) (h : χ (p : ZMod N) = 0) : p ∣ N := by
  by_contra hpN
  have hunit : IsUnit (p : ZMod N) :=
    (ZMod.isUnit_iff_coprime p N).mpr (hp.coprime_iff_not_dvd.mpr hpN)
  exact (MulChar.apply_eq_zero_iff.mp h) hunit

/-- The value of `χ(-1)` determines `|D| = N`. -/
lemma natAbs_of_chiD {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hsq : χ * χ = 1)
    {D : ℤ} (hD : (D : ℂ) = χ (-1 : ZMod N) * (N : ℂ)) : D.natAbs = N := by
  rcases quadratic_chi_values χ hsq (-1 : ZMod N) with h0 | h1 | h1
  · exfalso
    exact (MulChar.apply_eq_zero_iff.mp h0) isUnit_neg_one
  · have : (D : ℂ) = (N : ℂ) := by rw [hD, h1, one_mul]
    have hD' : D = N := by exact_mod_cast this
    rw [hD', Int.natAbs_natCast]
  · have : (D : ℂ) = -(N : ℂ) := by rw [hD, h1, neg_one_mul]
    have hD' : D = -N := by exact_mod_cast this
    rw [hD', Int.natAbs_neg, Int.natAbs_natCast]

/-- The local bound: the number of ideals of norm `p^k` is at most `Re (χ * ζ)(p^k)`. -/
theorem card_ideals_absNorm_prime_pow_le_zetaMul {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1)
    {K : Type*} [Field K] [NumberField K] (hfin : Module.finrank ℚ K = 2)
    (u : 𝓞 K) {D : ℤ} (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ))
    (hgen : Algebra.adjoin ℚ ({(u : K)} : Set K) = ⊤)
    (hD : (D : ℂ) = χ (-1 : ZMod N) * (N : ℂ))
    (hGauss : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ N →
      χ (p : ZMod N) = (jacobiSym D p : ℂ))
    (hnotdvd : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p * p ∣ N)
    (h2 : (2 : ℤ) ∣ D → (primesOverF (K := K) 2).card ≠ 2)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} ≤ (χ.zetaMul (p ^ k)).re := by
  have hp : Nat.Prime p := Fact.out
  have hDchi : D = chiD χ hsq := by
    have h1 : (D : ℂ) = ((chiD χ hsq : ℤ) : ℂ) := by rw [hD, chiD_cast]
    exact Int.cast_injective h1
  have habs := natAbs_of_chiD χ hsq hD
  have hDN : D = (N : ℤ) ∨ D = -(N : ℤ) := by
    have h2 : (D.natAbs : ℤ) = (N : ℤ) := by exact_mod_cast habs
    rcases Int.natAbs_eq D with h | h
    · left; rw [h]; exact h2
    · right; rw [h, h2]
  rcases quadratic_chi_values χ hsq (p : ZMod N) with h0 | h1 | hm1
  · -- `χ(p) = 0`, so `p ∣ N`
    have hpN : p ∣ N := dvd_of_chi_eq_zero χ hp h0
    rw [zetaMul_prime_pow_eq_of_eq_zero χ hp k h0]
    simp only [Complex.ofReal_one, Complex.one_re]
    rcases eq_or_ne p 2 with rfl | hp2
    · -- `p = 2`: at most one prime over `2`
      have h2D : (2 : ℤ) ∣ D := by
        have h1 : (2 : ℤ) ∣ (N : ℤ) := Int.natCast_dvd.mpr (by simpa using hpN)
        rcases hDN with h | h
        · rw [h]; exact h1
        · rw [h]; exact dvd_neg.mpr h1
      have hle : (primesOverF (K := K) 2).card ≤ 2 := card_primesOverF_le_two (K := K) hfin 2
      have hle1 : (primesOverF (K := K) 2).card ≤ 1 := by
        have := h2 h2D
        omega
      exact_mod_cast card_ideals_absNorm_prime_pow_le_one_of_card_le_one (K := K) k hle1
    · -- `p` odd: `p ∣ D`, `p² ∤ D`
      have hpD : (p : ℤ) ∣ D := by
        have h1 : (p : ℤ) ∣ (N : ℤ) := Int.natCast_dvd.mpr hpN
        rcases hDN with h | h
        · rw [h]; exact h1
        · rw [h]; exact dvd_neg.mpr h1
      have hpsq : ¬ (p : ℤ) ^ 2 ∣ D := by
        intro hdiv
        rcases hDN with h | h
        · rw [h] at hdiv
          have h1 : (p ^ 2 : ℕ) ∣ N := by
            have := Int.natCast_dvd.mp hdiv
            simpa using this
          exact hnotdvd p hp hp2 (by simpa [pow_two] using h1)
        · rw [h] at hdiv
          have h1 : ((p : ℤ) ^ 2) ∣ (N : ℤ) := dvd_neg.mp hdiv
          have h2 : (p ^ 2 : ℕ) ∣ N := by
            have := Int.natCast_dvd.mp h1
            simpa using this
          exact hnotdvd p hp hp2 (by simpa [pow_two] using h2)
      have hcard := card_primesOverF_le_one_of_dvd_not_dvd_sq (K := K) u hu hfin hpD hpsq
      exact_mod_cast card_ideals_absNorm_prime_pow_le_one_of_card_le_one (K := K) k hcard
  · -- `χ(p) = 1`
    have hcast : ((k : ℂ) + 1) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [zetaMul_prime_pow_eq_of_eq_one χ hp k h1, hcast, Complex.ofReal_re]
    exact_mod_cast card_ideals_absNorm_prime_pow_le (K := K) hfin p k
  · -- `χ(p) = -1`: no prime over `p` has inertia degree one
    have hno : ∀ 𝔭 ∈ primesOverF (K := K) p, 𝔭.inertiaDeg ℤ ≠ 1 := by
      rcases eq_or_ne p 2 with rfl | hp2
      · have hNodd : _root_.Odd N := by
          refine Nat.not_even_iff_odd.mp fun he => ?_
          have h2dvd : (2 : ℕ) ∣ N := even_iff_two_dvd.mp he
          have hnu : ¬ IsUnit (2 : ZMod N) := fun hc =>
            (Nat.prime_two.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime 2 N).mp hc)) h2dvd
          have hzero : χ (2 : ZMod N) = 0 := MulChar.apply_eq_zero_iff.mpr hnu
          have hc0 : (0 : ℂ) = -1 := by rw [← hzero]; exact hm1
          exact absurd hc0 (by norm_num)
        have hdata := chi_two_and_mod_eight χ hprim hsq hne hNodd
        have h85 : D % 8 = 5 := by
          have := hdata.2.2.mp hm1
          rwa [← hDchi] at this
        have h4 : D % 4 = 1 := by omega
        exact Commons.NumberTheory.NumberField.no_inertiaDeg_one_two_of_mod (K := K) u D hu
          hgen h4 h85
      · have hpN : ¬ p ∣ N := by
          intro hdiv
          have hnotunit : ¬ IsUnit (p : ZMod N) := by
            rw [ZMod.isUnit_iff_coprime]
            intro hcop
            have h1 : p ∣ Nat.gcd p N := Nat.dvd_gcd dvd_rfl hdiv
            rw [hcop.gcd_eq_one] at h1
            exact hp.not_dvd_one h1
          have hzero : χ (p : ZMod N) = 0 := MulChar.apply_eq_zero_iff.mpr hnotunit
          rw [hzero] at hm1
          norm_num at hm1
        have hJ : jacobiSym D p = -1 := by
          have h := hGauss p hp hp2 hpN
          rw [h] at hm1
          exact_mod_cast hm1
        exact no_inertiaDeg_one_of_jacobiSym_eq_neg_one (K := K) u hu hJ
    rw [zetaMul_prime_pow_eq_of_eq_neg_one χ hp k hm1]
    by_cases hk : _root_.Even k
    · rw [if_pos hk, Complex.one_re]
      exact_mod_cast card_ideals_absNorm_prime_pow_le_one_of_no_inertiaDeg_one (K := K) hfin hno k
    · rw [if_neg hk, Complex.zero_re]
      exact_mod_cast le_of_eq (card_ideals_absNorm_prime_pow_eq_zero_of_odd_of_no_inertiaDeg_one
        (K := K) hfin hno (Nat.not_even_iff_odd.mp hk))


section CharacterAux

/-- A quadratic character that is trivial at `-1` and at all primes not dividing the level is
trivial. -/
theorem chi_eq_one_of_prime_values_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h1 : χ (-1 : ZMod N) = 1) (h : ∀ p : ℕ, p.Prime → ¬ p ∣ N → χ (p : ZMod N) = 1) :
    χ = 1 := by
  classical
  rcases eq_or_ne N 1 with hN1 | hN1
  · subst hN1
    exact DirichletCharacter.level_one χ
  · haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN1
    refine MulChar.ext fun u => ?_
    have hcop : ((u : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime u
    have hval : (((u : ZMod N).val : ℕ) : ZMod N) = (u : ZMod N) :=
      ZMod.natCast_zmod_val (u : ZMod N)
    rcases eq_or_ne ((u : ZMod N)).val 0 with h0 | h0
    · exfalso
      apply u.ne_zero
      rw [← hval, h0, Nat.cast_zero]
    · have hfac : (∏ p ∈ ((u : ZMod N).val).primeFactors,
          p ^ (((u : ZMod N).val).factorization p)) = ((u : ZMod N).val) := by
        rw [← Nat.support_factorization _]
        exact Nat.prod_factorization_pow_eq_self h0
      have hgoal : χ ((((u : ZMod N).val : ℕ)) : ZMod N) = 1 := by
        rw [← hfac, Nat.cast_prod, map_prod]
        refine Finset.prod_eq_one fun p hp => ?_
        rw [Nat.cast_pow, map_pow]
        have hpN : ¬ p ∣ N := by
          intro hdiv
          have h1 : p ∣ Nat.gcd ((u : ZMod N).val) N :=
            Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hdiv
          rw [hcop] at h1
          exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one h1
        rw [h p (Nat.prime_of_mem_primeFactors hp) hpN]
        exact one_pow _
      rw [← hval, hgoal]
      exact (MulChar.one_apply (R := ZMod N) (R' := ℂ)
        (x := (((u : ZMod N).val : ℕ) : ZMod N)) (by rw [hval]; exact u.isUnit)).symm


/-- A rational square that is an integer is an integer square. -/
lemma exists_int_sq_of_rat_sq {q : ℚ} {D : ℤ} (h : q ^ 2 = (D : ℚ)) : ∃ m : ℤ, D = m ^ 2 := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_ne_zero q
  have hq' : (q.num : ℚ) = q * q.den := by
    have h0 := Rat.num_div_den q
    field_simp at h0
    linarith [h0]
  have h2 : ((q.num : ℤ)) ^ 2 = D * ((q.den : ℤ)) ^ 2 := by
    have h1 : (q.num : ℚ) ^ 2 = (D : ℚ) * (q.den : ℚ) ^ 2 := by
      rw [hq', mul_pow, h]
    exact_mod_cast h1
  have h4 : ((q.den : ℤ)) ^ 2 ∣ (q.num : ℤ) ^ 2 := ⟨D, by rw [h2, mul_comm]⟩
  have h5 : q.den ^ 2 ∣ q.num.natAbs ^ 2 := by
    have := Int.natAbs_dvd_natAbs.mpr h4
    simpa [Int.natAbs_pow] using this
  have h6 : q.den ∣ q.num.natAbs ^ 2 := dvd_trans (by exact ⟨q.den, by ring⟩) h5
  have h7 : q.den = 1 := by
    refine Nat.Coprime.eq_one_of_dvd ?_ h6
    simpa [pow_two] using (Rat.reduced q).symm.pow_right 2
  refine ⟨q.num, ?_⟩
  have := h2
  rw [h7, Nat.cast_one, one_pow, mul_one] at this
  linarith [this]

/-- For a primitive quadratic character with `D = χ(-1)·N` a square, `χ` is trivial. -/
theorem not_square_rat_of_chiD {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive) (hsq : χ * χ = 1) (hne : χ ≠ 1) {D : ℤ}
    (hD : (D : ℂ) = χ (-1 : ZMod N) * (N : ℂ))
    (hGauss : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ N → χ (p : ZMod N) = (jacobiSym D p : ℂ)) :
    ∀ q : ℚ, q ^ 2 ≠ (D : ℚ) := by
  intro q hq
  obtain ⟨m, hm⟩ := exists_int_sq_of_rat_sq hq
  have hDchi : D = chiD χ hsq := by
    have h1 : (D : ℂ) = ((chiD χ hsq : ℤ) : ℂ) := by rw [hD, chiD_cast]
    exact Int.cast_injective h1
  -- `D` is a positive square
  have hDN : D = (N : ℤ) ∨ D = -(N : ℤ) := by
    have h2 : (D.natAbs : ℤ) = (N : ℤ) := by exact_mod_cast natAbs_of_chiD χ hsq hD
    rcases Int.natAbs_eq D with hh | hh
    · left; rw [hh]; exact h2
    · right; rw [hh, h2]
  have hDpos : 0 < D := by
    rw [hm]
    rcases eq_or_ne m 0 with rfl | hm0
    · exfalso
      have h1 : (D : ℂ) = 0 := by rw [hm]; norm_num
      rw [hD] at h1
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
      rcases quadratic_chi_values χ hsq (-1 : ZMod N) with hχ | hχ | hχ
      · exact (MulChar.apply_eq_zero_iff.mp hχ) isUnit_neg_one
      · rw [hχ] at h1; simp [hN0] at h1
      · rw [hχ] at h1; simp [hN0] at h1
    · exact sq_pos_of_ne_zero hm0
  have hsign : χ (-1 : ZMod N) = 1 := by
    rcases quadratic_chi_values χ hsq (-1 : ZMod N) with hχ | hχ | hχ
    · exact absurd (MulChar.apply_eq_zero_iff.mp hχ) (not_not.mpr isUnit_neg_one)
    · exact hχ
    · exfalso
      have h1 : (D : ℂ) = -(N : ℂ) := by rw [hD, hχ, neg_one_mul]
      have h2 : D = -(N : ℤ) := by exact_mod_cast h1
      have hN : 0 < N := NeZero.pos N
      omega
  -- `D` is not `5` mod `8`
  have hsq8 : D % 8 ≠ 5 := by
    intro h5
    have h1 : ((D : ℤ) : ZMod 8) = 5 := by
      have h1' : ((D : ℤ) : ZMod 8) = ((5 : ℤ) : ZMod 8) := by
        rw [ZMod.intCast_eq_intCast_iff']
        omega
      rw [h1']; norm_num
    have h3 : ((D : ℤ) : ZMod 8) = (((m : ℤ)) : ZMod 8) ^ 2 := by
      rw [hm]; push_cast; ring
    have h2 : (((m : ℤ)) : ZMod 8) ^ 2 = 5 := by
      rw [← h3, h1]
    exact (by decide : ∀ y : ZMod 8, y ^ 2 ≠ 5) _ h2
  -- the character is trivial at all primes coprime to the level
  have hchar : ∀ p : ℕ, p.Prime → ¬ p ∣ N → χ (p : ZMod N) = 1 := by
    intro p hp hpN
    have hcop : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
    rcases eq_or_ne p 2 with rfl | hp2
    · rcases quadratic_chi_values χ hsq (2 : ZMod N) with h0 | h1 | hm1
      · exfalso
        exact (MulChar.apply_eq_zero_iff (χ := χ)).mp h0
          ((ZMod.isUnit_iff_coprime 2 N).mpr hcop)
      · exact h1
      · exfalso
        have hNodd : _root_.Odd N := by
          refine Nat.not_even_iff_odd.mp fun he => ?_
          exact hpN (even_iff_two_dvd.mp he)
        have hdata := chi_two_and_mod_eight χ hprim hsq hne hNodd
        have h5 : D % 8 = 5 := by
          have := hdata.2.2.mp hm1
          rwa [← hDchi] at this
        exact absurd h5 hsq8
    · have hpm : ¬ (p : ℤ) ∣ m := by
        intro hdiv
        have h1 : (p : ℤ) ∣ D := by
          rw [hm]
          simpa [pow_two] using dvd_mul_of_dvd_left hdiv ((m : ℤ))
        have h2 : p ∣ N := by
          rcases hDN with h | h
          · rw [h] at h1
            exact Int.natCast_dvd.mp h1
          · rw [h] at h1
            exact Int.natCast_dvd.mp (dvd_neg.mp h1)
        exact hpN h2
      have hg : m.gcd (p : ℤ) = 1 := by
        have hpm' : ¬ p ∣ m.natAbs := fun hdiv => hpm (Int.natCast_dvd.mpr hdiv)
        have h : m.natAbs.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm').symm
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
        exact h.gcd_eq_one
      have hDm : jacobiSym D p = 1 := by
        rw [hm, jacobiSym.pow_left]
        rcases jacobiSym.trichotomy m p with h0 | h1 | h1
        · exact absurd h0 (jacobiSym.ne_zero hg)
        · rw [h1]; norm_num
        · rw [h1]; norm_num
      rw [hGauss p hp hp2 hpN, hDm]
      norm_num
  exact hne (chi_eq_one_of_prime_values_eq_one χ hsign hchar)


/-- The Jacobi symbol `J(D' | a)` is one when `D' ≡ 1 (mod 8)` and `a ≡ 1 (mod |D'|)`. -/
lemma jacobiSym_eq_one_of_mod_eight_one {D' : ℤ} {a : ℕ} (ha : _root_.Odd a)
    (hD'8 : D' % 8 = 1) (hD'0 : D' ≠ 0) (ha1 : a % D'.natAbs = 1 % D'.natAbs) :
    jacobiSym D' a = 1 := by
  have ha2 : a % 2 = 1 := Nat.odd_iff.mp ha
  have hJ1 : jacobiSym a D'.natAbs = 1 := by
    have hgoal : (((a : ℕ)) : ℤ) % (((D'.natAbs : ℕ)) : ℤ) =
        (((1 : ℕ)) : ℤ) % (((D'.natAbs : ℕ)) : ℤ) := by
      rw [← Int.natCast_emod, ← Int.natCast_emod, ha1]
    rw [jacobiSym.mod_left' hgoal]
    exact jacobiSym.one_left _
  rcases lt_or_gt_of_ne hD'0 with hneg | hpos
  · have hneg' : 0 ≤ -D' := by omega
    have h1 : (D'.natAbs : ℤ) = -D' := by
      rw [← Int.natAbs_neg, Int.natAbs_of_nonneg hneg']
    have hD'eq : D' = -((D'.natAbs : ℕ) : ℤ) := by omega
    have hmod8 : D'.natAbs % 8 = 7 := by omega
    rw [hD'eq, jacobiSym.neg (D'.natAbs) ha]
    have hqr := jacobiSym.quadratic_reciprocity
      (Nat.odd_iff.mpr (by omega : D'.natAbs % 2 = 1)) ha
    have hχ : ZMod.χ₄ ((a : ℕ)) = (-1 : ℤ) ^ (a / 2) := ZMod.χ₄_eq_neg_one_pow ha2
    have hodd : _root_.Odd (D'.natAbs / 2) := Nat.odd_iff.mpr (by omega : D'.natAbs / 2 % 2 = 1)
    have he : (-1 : ℤ) ^ (D'.natAbs / 2 * (a / 2)) = (-1 : ℤ) ^ (a / 2) := by
      rw [pow_mul, hodd.neg_one_pow]
    rw [hχ, hqr, hJ1, he]
    rcases Nat.even_or_odd (a / 2) with h | h <;> rw [h.neg_one_pow] <;> ring
  · have h1 : (D'.natAbs : ℤ) = D' := Int.natAbs_of_nonneg hpos.le
    have hD'eq : D' = ((D'.natAbs : ℕ) : ℤ) := by omega
    have hmod4 : D'.natAbs % 4 = 1 := by omega
    rw [hD'eq, jacobiSym.quadratic_reciprocity_one_mod_four hmod4 ha, hJ1]


/-- If `2` splits and `D = 4^j * D'` with `j ≥ 1`, `D' ≡ 1 (mod 8)`, then `χ` is not
primitive. -/
theorem not_isPrimitive_of_two_split {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hsq : χ * χ = 1) {D D' : ℤ} (hD : (D : ℂ) = χ (-1 : ZMod N) * (N : ℂ))
    {j : ℕ} (hj : 1 ≤ j) (hfac : D = 4 ^ j * D') (hD'odd : D' % 2 = 1) (hD'8 : D' % 8 = 1)
    (hval : ∀ a : ℕ, _root_.Odd a → a.Coprime N → χ (a : ZMod N) = (jacobiSym D a : ℂ)) :
    ¬ χ.IsPrimitive := by
  have habs : D.natAbs = N := natAbs_of_chiD χ hsq hD
  have hD'0 : D' ≠ 0 := by
    rintro rfl
    rw [Int.zero_emod] at hD'8
    norm_num at hD'8
  have h3 : D.natAbs = 4 ^ j * D'.natAbs := by
    rw [hfac, Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  have hN : N = 4 ^ j * D'.natAbs := by
    rw [← habs, h3]
  have hdvd : D'.natAbs ∣ N := ⟨4 ^ j, by rw [hN, mul_comm]⟩
  have h4j : 1 < 4 ^ j := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj)
  have hlt : D'.natAbs < N := by
    rw [hN]
    calc D'.natAbs = D'.natAbs * 1 := (mul_one _).symm
      _ < D'.natAbs * 4 ^ j := Nat.mul_lt_mul_of_pos_left h4j (Nat.pos_of_ne_zero (by
          intro h; exact hD'0 (Int.natAbs_eq_zero.mp h)))
      _ = 4 ^ j * D'.natAbs := mul_comm _ _
  have hker : ∀ u : (ZMod N)ˣ, ZMod.unitsMap hdvd u = 1 → χ ↑u = 1 := by
    intro u hu
    have hcop : ((u : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime u
    have hcast : ((((u : ZMod N).val : ℕ)) : ZMod N) = (u : ZMod N) :=
      ZMod.natCast_zmod_val (u : ZMod N)
    have h2N : 2 ∣ N := ⟨2 ^ (2 * j - 1) * D'.natAbs, by
      rw [hN]
      have : 4 ^ j = 2 ^ (2 * j) := by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      rw [this]
      rcases Nat.eq_zero_or_pos j with h | h
      · omega
      · rw [show 2 ^ (2 * j) = 2 ^ (2 * j - 1) * 2 from by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]] 
        ring⟩
    have haodd : _root_.Odd ((u : ZMod N).val) := by
      have h : ((u : ZMod N).val).Coprime 2 := by
        have := hcop.coprime_dvd_right h2N
        exact this
      exact Nat.coprime_two_right.mp h
    have hp : ((u : ZMod N).val) % D'.natAbs = 1 % D'.natAbs := by
      have h2 : ZMod.cast (u : ZMod N) = (1 : ZMod D'.natAbs) := by
        have h := congrArg (fun v : (ZMod D'.natAbs)ˣ => (v : ZMod D'.natAbs)) hu
        have h' : ((ZMod.unitsMap hdvd u : (ZMod D'.natAbs)ˣ) : ZMod D'.natAbs) = 1 := by
          simpa using h
        rwa [ZMod.unitsMap_val hdvd u] at h'
      have h3' : ((((u : ZMod N).val : ℕ)) : ZMod D'.natAbs) = ((1 : ℕ) : ZMod D'.natAbs) := by
        rw [← ZMod.cast_natCast hdvd ((u : ZMod N).val), hcast]
        simpa using h2
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h3'
    rw [← hcast, hval _ haodd hcop]
    have hJ : jacobiSym D ((u : ZMod N).val) = 1 := by
      rw [hfac, jacobiSym.mul_left]
      have h4 : jacobiSym ((4 : ℤ) ^ j) ((u : ZMod N).val) = 1 := by
        rw [jacobiSym.pow_left, jacobiSym.at_four haodd, one_pow]
      rw [h4, one_mul]
      exact jacobiSym_eq_one_of_mod_eight_one haodd hD'8 hD'0 hp
    rw [hJ]
    norm_num
  have hft : χ.FactorsThrough D'.natAbs :=
    (factorsThrough_iff_ker_unitsMap hdvd).mpr fun u hu => by
      rw [MonoidHom.mem_ker]
      refine Units.ext ?_
      simpa using hker u hu
  have hcond : χ.conductor ≤ D'.natAbs := by
    have := Nat.sInf_le ((mem_conductorSet_iff χ).mpr hft)
    simpa [DirichletCharacter.conductor] using this
  intro hprim
  rw [DirichletCharacter.isPrimitive_def] at hprim
  omega

end CharacterAux


end LocalBounds




section ResidueBound

/-- The residue of the Dedekind zeta function of a quadratic field is at least `c/√|disc|`. -/
theorem dedekindZeta_residue_ge_of_finrank_two :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : Type*) [Field K] [NumberField K],
      Module.finrank ℚ K = 2 →
        c / Real.sqrt |(NumberField.discr K : ℝ)| ≤ NumberField.dedekindZeta_residue K := by
  obtain ⟨cR, hcR, hR⟩ :=
    Commons.NumberTheory.NumberField.exists_regulator_lower_bound_of_finrank_two
  refine ⟨2 * cR / 3, by positivity, ?_⟩
  intro K hfield hNF hfin
  have hw : (NumberField.Units.torsionOrder K : ℝ) ≤ 6 := by
    exact_mod_cast Commons.NumberTheory.NumberField.torsionOrder_le_six_of_finrank_two K hfin
  have hwpos : (0 : ℝ) < (NumberField.Units.torsionOrder K : ℝ) := by
    exact_mod_cast NumberField.Units.torsionOrder_pos K
  have hRpos : (0 : ℝ) < NumberField.Units.regulator K := NumberField.Units.regulator_pos K
  have hR' : cR ≤ NumberField.Units.regulator K := hR K hfin
  have hh : (1 : ℝ) ≤ (NumberField.classNumber K : ℝ) := by
    exact_mod_cast NumberField.classNumber_pos K
  have hd : 0 < Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K))
  have hpl : (4 : ℝ) ≤ 2 ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
    have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [hfin] at hrank
    rcases Nat.eq_zero_or_pos (NumberField.InfinitePlace.nrComplexPlaces K) with h0 | h0
    · have h2 : NumberField.InfinitePlace.nrRealPlaces K = 2 := by omega
      rw [h2, h0]
      norm_num
    · have h1 : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
      have h2 : NumberField.InfinitePlace.nrRealPlaces K = 0 := by omega
      rw [h1, h2]
      norm_num
      nlinarith [Real.pi_gt_three]
  rw [NumberField.dedekindZeta_residue_def]
  set X : ℝ := 2 ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K with hXdef
  have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  have hX4 : (4 : ℝ) ≤ X := by rw [hXdef]; exact hpl
  have hnum : (4 : ℝ) * cR ≤ X * NumberField.Units.regulator K *
      (NumberField.classNumber K : ℝ) := by
    have h1 : (4 : ℝ) * cR ≤ X * cR := mul_le_mul_of_nonneg_right hX4 hcR.le
    have h2 : X * cR ≤ X * NumberField.Units.regulator K :=
      mul_le_mul_of_nonneg_left hR' hX0
    have h3 : X * NumberField.Units.regulator K ≤ X * NumberField.Units.regulator K *
        (NumberField.classNumber K : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg hX0 hRpos.le) hh
    linarith
  have hkey : 2 * cR / 3 * (NumberField.Units.torsionOrder K : ℝ) ≤
      X * NumberField.Units.regulator K * (NumberField.classNumber K : ℝ) := by
    have h4 : 2 * cR / 3 * (NumberField.Units.torsionOrder K : ℝ) ≤ 4 * cR := by
      nlinarith [hw, hcR]
    linarith
  rw [div_le_div_iff₀ hd (mul_pos hwpos hd)]
  calc 2 * cR / 3 * ((NumberField.Units.torsionOrder K : ℝ) *
        Real.sqrt |(NumberField.discr K : ℝ)|)
      = (2 * cR / 3 * (NumberField.Units.torsionOrder K : ℝ)) *
        Real.sqrt |(NumberField.discr K : ℝ)| := by ring
    _ ≤ (X * NumberField.Units.regulator K * (NumberField.classNumber K : ℝ)) *
        Real.sqrt |(NumberField.discr K : ℝ)| :=
        mul_le_mul_of_nonneg_right hkey hd.le

end ResidueBound

end NfAux

section Assembly

open scoped _root_.NumberField nonZeroDivisors
open Filter Topology

/-- The main theorem: a lower bound for `L(1,χ)` for primitive quadratic characters. -/
theorem LFunction_one_lower_bound_quadratic :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ * χ = 1 → χ ≠ 1 →
      c / Real.sqrt (N : ℝ) ≤ ‖DirichletCharacter.LFunction χ (1 : ℂ)‖ := by
  obtain ⟨c₁, hc₁, hres⟩ := dedekindZeta_residue_ge_of_finrank_two
  refine ⟨c₁ / 8, by positivity, ?_⟩
  intro N hN χ hprim hsq hne
  have hGaussD : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ N →
      χ (p : ZMod N) = (jacobiSym (chiD χ hsq) p : ℂ) := by
    intro p hp hp2 hpN
    haveI : Fact p.Prime := ⟨hp⟩
    exact chiPrimeJacobi χ hprim hsq hne p hp2 hpN
  have hDabsD : (chiD χ hsq).natAbs = N := chiD_abs χ hsq
  have hDneD : (chiD χ hsq : ℤ) ≠ 0 := by
    intro h; rw [h] at hDabsD; simp at hDabsD; exact absurd hDabsD.symm (NeZero.ne N)
  have hnotsqD : ∀ q : ℚ, q ^ 2 ≠ ((chiD χ hsq : ℤ) : ℚ) :=
    not_square_rat_of_chiD χ hprim hsq hne (chiD_cast χ hsq) hGaussD
  have hnotdvd : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p * p ∣ N :=
    fun p hp hp2 => not_dvd_sq_of_isPrimitive χ hprim hsq hp hp2
  set D : ℤ := chiD χ hsq with hDdef
  have hDneq : D ≠ 0 := by rw [hDdef]; exact hDneD
  have hDabs : D.natAbs = N := by rw [hDdef]; exact hDabsD
  have hDcast : (D : ℂ) = χ (-1 : ZMod N) * (N : ℂ) := by
    rw [hDdef]; exact chiD_cast χ hsq
  have hnotsq : ∀ q : ℚ, q ^ 2 ≠ (D : ℚ) := by
    intro q hq; exact hnotsqD q (by rw [hq])
  have hGauss : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ N →
      χ (p : ZMod N) = (jacobiSym D p : ℂ) := by
    intro p hp hp2 hpN; rw [hDdef]; exact hGaussD p hp hp2 hpN
  have hDq0 : ((D : ℤ) : ℚ) ≠ 0 := fun h => hDneq (Int.cast_injective h)
  haveI hIrr : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) :=
    ⟨(_root_.Commons.NumberTheory.QuadraticExtension.irreducible_X_sq_sub_C_iff_not_square
      hDq0).mpr hnotsq⟩
  have hfne : (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]) ≠ 0 := (Polynomial.monic_X_pow_sub_C _ (by norm_num : (2:ℕ) ≠ 0)).ne_zero
  haveI : NumberField (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) :=
    _root_.Commons.NumberTheory.QuadraticExtension.numberField_adjoinRoot_X_sq_sub_C
      (K := ℚ) (a := ((D : ℤ) : ℚ)) hDq0
  have hfin : Module.finrank ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) = 2 :=
    _root_.Commons.NumberTheory.QuadraticExtension.finrank_adjoinRoot_X_sq_sub_C
      (K := ℚ) (a := ((D : ℤ) : ℚ)) hDq0
  have hrootsq : (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) ^ 2 = algebraMap ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) ((D : ℤ) : ℚ) := by
    have h : Polynomial.aeval (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]) = 0 := by
      rw [show Polynomial.aeval (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])
            = AdjoinRoot.mk (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]) (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]) from AdjoinRoot.aeval_eq _,
        AdjoinRoot.mk_self]
    simp only [map_sub, map_pow, aeval_X, aeval_C] at h
    exact sub_eq_zero.mp h
  have hint : IsIntegral ℤ (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) := by
    refine IsIntegral.of_pow (R := ℤ) (n := 2) (by norm_num) ?_
    rw [hrootsq]
    have h2 : IsIntegral ℤ (algebraMap ℤ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) D) := isIntegral_algebraMap
    convert h2 using 1
    exact (IsScalarTower.algebraMap_apply ℤ ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) D).symm
  let u : 𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) := ⟨AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]), hint⟩
  have hu : ((u : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))) ^ 2 = algebraMap ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) ((D : ℤ) : ℚ) := hrootsq
  have hgen : Algebra.adjoin ℚ ({(u : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))} : Set (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))) = ⊤ := by
    exact AdjoinRoot.adjoinRoot_eq_top (R := ℚ)
      (f := (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))
  have hdisc : |(NumberField.discr (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) : ℝ)| ≤ 4 * |((D : ℤ) : ℝ)| := by
    have hpb := _root_.Commons.FieldTheory.Discriminant.discr_powerBasis_X_sq_sub_C
      (a := ((D : ℤ) : ℚ)) hfne
    have hintb : ∀ i, IsIntegral ℤ ((AdjoinRoot.powerBasis hfne).basis i) := by
      intro i
      rw [(AdjoinRoot.powerBasis hfne).basis_eq_pow]
      exact hint.pow i
    obtain ⟨m, hm⟩ := _root_.Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis
      (AdjoinRoot.powerBasis hfne).basis hintb
    have hm' : (4 : ℚ) * ((D : ℤ) : ℚ) =
        (NumberField.discr (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) : ℚ) *
          (m : ℚ) := hpb.symm.trans hm
    have hm := hm'
    have hmR : (4 : ℝ) * ((D : ℤ) : ℝ) =
        (NumberField.discr (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) : ℝ) * (m : ℝ) := by
      exact_mod_cast hm
    have hmne : m ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, mul_zero] at hmR
      have hD0 : ((D : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hDneq
      have : ((D : ℤ) : ℝ) = 0 := by linarith
      exact hD0 this
    have hkey : (NumberField.discr (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) : ℝ)
        = 4 * ((D : ℤ) : ℝ) / (m : ℝ) := by
      rw [eq_div_iff (by exact_mod_cast hmne)]
      linarith [hmR]
    rw [hkey]
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have h : (1 : ℤ) ≤ |m| := Int.one_le_abs hmne
      exact_mod_cast h
    have hmpos : (0 : ℝ) < |(m : ℝ)| := lt_of_lt_of_le one_pos hm1
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), div_le_iff₀ hmpos]
    nlinarith [hm1, abs_nonneg ((D : ℤ) : ℝ)]
  have hresK : c₁ / (2 * Real.sqrt (N : ℝ)) ≤
      NumberField.dedekindZeta_residue (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) := by
    refine le_trans ?_ (hres (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) hfin)
    have hDN : |((D : ℤ) : ℝ)| = (N : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, hDabs]
      norm_num
    have h4N : (2 * Real.sqrt (N : ℝ)) ^ 2 = 4 * (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    have hle : |(NumberField.discr (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) : ℝ)| ≤ (2 * Real.sqrt (N : ℝ)) ^ 2 := by
      rw [h4N, ← hDN]; exact hdisc
    have hsle : Real.sqrt |(NumberField.discr (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) : ℝ)| ≤ 2 * Real.sqrt (N : ℝ) := by
      have h1 : Real.sqrt |(NumberField.discr (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) : ℝ)| ≤
          Real.sqrt ((2 * Real.sqrt (N : ℝ)) ^ 2) := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq (by positivity)] at h1
    have hspos : (0 : ℝ) < Real.sqrt |(NumberField.discr (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) : ℝ)| :=
      Real.sqrt_pos_of_pos (abs_pos.mpr (by
        exact_mod_cast NumberField.discr_ne_zero (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))
    exact div_le_div_of_nonneg_left hc₁.le hspos hsle
  have hlim : Tendsto (fun s : ℝ => (Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
      Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ s} : ℝ) / s) atTop
      (𝓝 (NumberField.dedekindZeta_residue (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) := by
    have h := NumberField.Ideal.tendsto_norm_le_div_atTop₀ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))
    rwa [← NumberField.dedekindZeta_residue_def] at h
  have hev : ∀ᶠ X : ℕ in atTop,
      NumberField.dedekindZeta_residue (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) / 2 * (X : ℝ) ≤
        (Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ X} : ℝ) := by
    have h0 : ∀ᶠ s : ℝ in atTop,
        NumberField.dedekindZeta_residue (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) / 2 <
          (Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
            Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ s} : ℝ) / s :=
      (tendsto_order.1 hlim).1 (NumberField.dedekindZeta_residue (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) / 2)
        (by linarith [NumberField.dedekindZeta_residue_pos (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))])
    have h1 : ∀ᶠ X : ℕ in atTop,
        NumberField.dedekindZeta_residue (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) / 2 <
          (Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
            Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ (X : ℝ)} : ℝ) / (X : ℝ) :=
      Filter.Tendsto.eventually (f := fun X : ℕ => ((X : ℕ) : ℝ)) tendsto_natCast_atTop_atTop h0
    filter_upwards [h1, eventually_ge_atTop 1] with X hX hX1
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX1
    have h2 := (le_div_iff₀ hXpos).mp (le_of_lt hX)
    have hcongr : (Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ (X : ℝ)})
        = Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ X} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun I => Nat.cast_le))
    rwa [hcongr] at h2
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  have hone : ∀ I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰,
      1 ≤ Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) := by
    intro I
    have hI : (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≠ 0 := nonZeroDivisors.coe_ne_zero I
    rw [Ideal.zero_eq_bot] at hI
    rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  have hcount : ∀ X : ℕ, max T 1 ≤ X → c₁ / (4 * Real.sqrt (N : ℝ)) * (X : ℝ) ≤
      (Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ X} : ℝ) := by
    intro X hX
    have h1 := hT X (le_trans (le_max_left _ _) hX)
    have h2 : c₁ / (4 * Real.sqrt (N : ℝ)) ≤
        NumberField.dedekindZeta_residue (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) / 2 := by
      have h3 : c₁ / (4 * Real.sqrt (N : ℝ)) = (c₁ / (2 * Real.sqrt (N : ℝ))) / 2 := by
        rw [div_div]; ring
      rw [h3]; linarith [hresK]
    calc c₁ / (4 * Real.sqrt (N : ℝ)) * (X : ℝ)
        ≤ (NumberField.dedekindZeta_residue (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) / 2) * (X : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ _ := h1
  have h2card : (2 : ℤ) ∣ D → (primesOverF (K := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) 2).card ≠ 2 := by
    intro h2D hsplit
    obtain ⟨j, D', hfac, hD'odd, hD'8⟩ :=
      _root_.Commons.NumberTheory.NumberField.exists_mod_eight_one_of_split_two
        (K := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) u D hu hgen hDneq hsplit
    have hj : 1 ≤ j := by
      by_contra hj
      have hj0 : j = 0 := by omega
      rw [hj0, pow_zero, one_mul] at hfac
      have hDmod : D % 2 = 1 := by rw [hfac]; exact hD'odd
      have h0 : D % 2 = 0 := by
        obtain ⟨c, hc⟩ := h2D
        rw [hc]; omega
      omega
    exact not_isPrimitive_of_two_split χ hsq hDcast hj hfac hD'odd hD'8
      (fun a ha haN => chi_eq_jacobiSym_of_prime_values χ hsq
        (fun p hp hp2 hpN => by
          haveI : Fact p.Prime := ⟨hp⟩
          exact chiPrimeJacobi χ hprim hsq hne p hp2 hpN) ha haN) hprim
  have hlocal : ∀ (p : ℕ), p.Prime → ∀ k : ℕ,
      Nat.card {I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))) // Ideal.absNorm I = p ^ k} ≤
        (χ.zetaMul (p ^ k)).re := by
    intro p hp k
    haveI : Fact p.Prime := ⟨hp⟩
    exact card_ideals_absNorm_prime_pow_le_zetaMul (K := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) (D := D) χ hprim hsq
      hne hfin u hu hgen hDcast hGauss hnotdvd h2card p k
  have hsum : ∀ X : ℕ, max T 1 ≤ X →
      c₁ / (4 * Real.sqrt (N : ℝ)) * (X : ℝ) ≤ (∑ n ∈ Finset.Icc 1 X, χ.zetaMul n).re := by
    intro X hX
    refine le_trans (hcount X hX) ?_
    have hnat : Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ X}
        = ∑ n ∈ Finset.Icc 1 X, Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
            Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) = n} := by
      have hpre := Finset.card_preimage_eq_sum_card_image_eq
        (f := fun I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ =>
          Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))))
        (s := Finset.Icc 1 X)
        (fun b _ => (Ideal.finite_setOfPred_absNorm_le₀ b).subset
          (fun I hI => by rw [Set.mem_setOf_eq] at hI ⊢; exact le_of_eq hI))
      rw [← hpre]
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun I => ?_))
      simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_Icc]
      exact ⟨fun h => ⟨hone I, h⟩, fun h => h.2⟩
    have hreindex : (Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) ≤ X} : ℝ)
        = ∑ n ∈ Finset.Icc 1 X, (Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
            Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) = n} : ℝ) := by
      rw [hnat, Nat.cast_sum]
    rw [hreindex, Complex.re_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    haveI : Finite {I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    let g : {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) = n} →
        {J : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))) // Ideal.absNorm J = n} :=
      fun I => ⟨(I.1 : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))), I.2⟩
    have hinj : Nat.card {I : (Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) = n}
        ≤ Nat.card {J : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X]))) // Ideal.absNorm J = n} :=
      Nat.card_le_card_of_injective g (fun a b h => by
        have h2 : (g a).val = (g b).val := congrArg Subtype.val h
        have h1 : (a.1 : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) = (b.1 : Ideal (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])))) := by
          simpa [g] using h2
        exact Subtype.ext (Subtype.ext h1))
    exact le_trans (by exact_mod_cast hinj)
      (card_ideals_absNorm_le_zetaMul (K := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C ((D : ℤ) : ℚ) : ℚ[X])) χ hsq hfin hlocal hn0)
  have hpart : ∀ X : ℕ, max T 1 ≤ X → (c₁ / 4) * (X : ℝ) / Real.sqrt (N : ℝ) ≤
      (∑ n ∈ Finset.Icc 1 X, χ.zetaMul n).re := by
    intro X hX
    have h := hsum X hX
    have h2 : (c₁ / 4) * (X : ℝ) / Real.sqrt (N : ℝ)
        = c₁ / (4 * Real.sqrt (N : ℝ)) * (X : ℝ) := by
      ring
    rw [h2]; exact h
  have hglue := LFunction_one_lower_bound_of_partial_sums (c₁ / 4) (by positivity) N χ hsq hne
    (max T 1) hpart
  have hfin2 : c₁ / 8 / Real.sqrt (N : ℝ) = (c₁ / 4) / (2 * Real.sqrt (N : ℝ)) := by
    ring
  rw [hfin2]
  exact hglue

end Assembly

end Commons.NumberTheory.DirichletCharacter
