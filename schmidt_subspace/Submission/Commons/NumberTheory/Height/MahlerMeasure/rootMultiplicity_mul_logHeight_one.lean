import Mathlib.NumberTheory.Height.NumberField
import Submission.Commons.Algebra.Polynomial.isPrimitive_pow_C_mul_X_sub_C
import Submission.Commons.NumberTheory.Height.MahlerMeasure.coeff_abs_ge_of_dvd_C_mul_X_sub_C
import Submission.Commons.NumberTheory.Height.mulHeight_finsupp_coe_eq

namespace Commons.NumberTheory.Height.MahlerMeasure

open Polynomial

/-- The height of the padded coefficient vector `(1, P.coeff 0, P.coeff 1, …)` of `P` is at
least the absolute value of any of its coefficients. -/
lemma mulHeight_coeff_ge {P : Polynomial ℤ} (k : ℕ) (hk : k ≤ P.natDegree) :
    (↑(P.coeff k).natAbs : ℝ) ≤
      Height.mulHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) := by
  classical
  set N := P.natDegree with hN
  set s : Finset (Option ℕ) := {none} ∪ (Finset.range (N+1)).image Option.some with hs
  have hsvanish : ∀ i, i ∉ s →
      (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) i = 0 := by
    intro i hi
    cases i with
    | none => exact absurd (by simp [s]) hi
    | some m =>
      have hm : P.coeff m = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [← hN]
        by_contra h
        push Not at h
        exact hi (by
          simp only [s, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
            Finset.mem_range]
          exact Or.inr ⟨m, Nat.lt_succ_iff.mpr h, rfl⟩)
      simp [hm]
  have hmul1 : Height.mulHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) =
      Height.mulHeight (fun i : ↥s =>
        (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) ↑i) :=
    Commons.NumberTheory.Height.mulHeight_eq_mulHeight_finset s hsvanish
  set ψ : Option (Fin (N+1)) → ↥s := fun o => o.elim ⟨none, by simp [s]⟩
      (fun j => ⟨some j.val, by
        simp only [s, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
          Finset.mem_range]
        exact Or.inr ⟨j.val, j.isLt, rfl⟩⟩) with hψ
  have hmul2 : Height.mulHeight (fun i : ↥s =>
        (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) ↑i) ≥
      Height.mulHeight ((fun i : ↥s =>
        (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) ↑i) ∘ ψ) :=
    Height.mulHeight_comp_le ψ _
  set y : Option (Fin (N+1)) → ℤ := fun o => o.elim 1 (fun j => P.coeff j.val) with hy
  have hcomp : (fun i : ↥s =>
        (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) ↑i) ∘ ψ =
      fun o : Option (Fin (N+1)) => (y o : ℚ) := by
    funext o
    cases o with
    | none => simp [Function.comp_apply, ψ, y]
    | some j => simp [Function.comp_apply, ψ, y]
  have hgcd : (Finset.univ : Finset (Option (Fin (N+1)))).gcd y = 1 := by
    have hdvd : (Finset.univ : Finset (Option (Fin (N+1)))).gcd y ∣ 1 := by
      have h := Finset.gcd_dvd (s := (Finset.univ : Finset (Option (Fin (N+1)))))
        (f := y) (b := none) (Finset.mem_univ none)
      simpa [y] using h
    have hnn : 0 ≤ (Finset.univ : Finset (Option (Fin (N+1)))).gcd y :=
      Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
    exact Int.eq_one_of_dvd_one hnn hdvd
  have hmul3 : Height.mulHeight (fun o : Option (Fin (N+1)) => (y o : ℚ)) =
      ↑(⨆ o : Option (Fin (N+1)), |y o|) := by
    have := Rat.mulHeight_eq_max_abs_of_gcd_eq_one (x := y) hgcd
    simpa [Function.comp_def] using this
  have hk' : k < N + 1 := by omega
  have hsup : (|y (some ⟨k, hk'⟩)| : ℝ) ≤ ↑(⨆ o : Option (Fin (N+1)), |y o|) := by
    have h : |y (some ⟨k, hk'⟩)| ≤ ⨆ o : Option (Fin (N+1)), |y o| :=
      Finite.le_ciSup (fun o : Option (Fin (N+1)) => |y o|) (some ⟨k, hk'⟩)
    exact_mod_cast h
  have hyval : y (some ⟨k, hk'⟩) = P.coeff k := by simp [y]
  have hstep : (↑(P.coeff k).natAbs : ℝ) ≤ ↑(⨆ o : Option (Fin (N+1)), |y o|) := by
    rw [← hyval]
    simpa using hsup
  calc (↑(P.coeff k).natAbs : ℝ) ≤ ↑(⨆ o : Option (Fin (N+1)), |y o|) := hstep
    _ = Height.mulHeight (fun o : Option (Fin (N+1)) => (y o : ℚ)) := hmul3.symm
    _ = Height.mulHeight ((fun i : ↥s =>
          (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) ↑i) ∘ ψ) := by
        rw [hcomp]
    _ ≤ Height.mulHeight (fun i : ↥s =>
          (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) ↑i) := hmul2
    _ = Height.mulHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) :=
        hmul1.symm

/-- `Height.logHeight` of the padded coefficient vector of an integer polynomial is
nonnegative. -/
lemma zero_le_logHeight_coeff {P : Polynomial ℤ} :
    0 ≤ Height.logHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) := by
  classical
  set N := P.natDegree with hN
  set s : Finset (Option ℕ) := {none} ∪ (Finset.range (N+1)).image Option.some with hs
  have hsvanish : ∀ i, i ∉ s →
      (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) i = 0 := by
    intro i hi
    cases i with
    | none => exact absurd (by simp [s]) hi
    | some m =>
      have hm : P.coeff m = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [← hN]
        by_contra h
        push Not at h
        exact hi (by
          simp only [s, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
            Finset.mem_range]
          exact Or.inr ⟨m, Nat.lt_succ_iff.mpr h, rfl⟩)
      simp [hm]
  have hmul1 : Height.mulHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) =
      Height.mulHeight (fun i : ↥s =>
        (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) ↑i) :=
    Commons.NumberTheory.Height.mulHeight_eq_mulHeight_finset s hsvanish
  rw [Height.logHeight_eq_log_mulHeight, hmul1]
  exact Real.log_nonneg (Height.one_le_mulHeight _)

/-- **Root multiplicity and logarithmic height.**

Let `P ∈ ℤ[X]` be nonzero and let `β ∈ ℚ` be a root of `P` of multiplicity `l`. Then `l` times
the logarithmic height of `β` is at most the logarithmic height of the coefficient vector of `P`
(padded with a `1` so that the finite places contribute trivially).

Writing `β = a/b` in lowest terms, `(b·X - a)^l` divides the primitive part of `P`, so `P` has a
coefficient whose absolute value is at least `max(|a|, b)^l = mulHeight₁ β ^ l`; all places of
`ℚ` then contribute at most that, giving the claim after taking logarithms. -/
theorem rootMultiplicity_mul_logHeight_one {P : Polynomial ℤ} (hP : P ≠ 0) {β : ℚ}
    (hβ : (P.map (Int.castRingHom ℚ)).IsRoot β) :
    (Polynomial.rootMultiplicity β (P.map (Int.castRingHom ℚ)) : ℝ) * Height.logHeight₁ β ≤
      Height.logHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) := by
  classical
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [Height.logHeight₁_zero, mul_zero]
    exact zero_le_logHeight_coeff
  · set l : ℕ := Polynomial.rootMultiplicity β (P.map (Int.castRingHom ℚ)) with hl
    have ha : β.num ≠ 0 := Rat.num_ne_zero.mpr hβ0
    have hb : 0 < β.den := β.den_pos
    set A : Polynomial ℤ :=
      (Polynomial.C (β.den : ℤ) * Polynomial.X - Polynomial.C β.num) ^ l with hA
    have hAprim : A.IsPrimitive := by
      rw [hA]
      exact Commons.Algebra.Polynomial.isPrimitive_pow_C_mul_X_sub_C β.num (β.den : ℤ)
        (Rat.isCoprime_num_den β) l
    -- divisibility over `ℚ`
    have hdiv0 : (Polynomial.X - Polynomial.C β) ^ l ∣ P.map (Int.castRingHom ℚ) := by
      rw [hl]
      exact Polynomial.pow_rootMultiplicity_dvd _ β
    have hmapA : A.map (Int.castRingHom ℚ) =
        (Polynomial.C ((β.den : ℤ) : ℚ) * Polynomial.X - Polynomial.C (β.num : ℚ)) ^ l := by
      rw [hA]
      simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, Int.coe_castRingHom]
    have hβcast : ((β.den : ℚ)) * β = (β.num : ℚ) := by
      have h := Rat.mul_den_eq_num β
      rw [mul_comm]
      exact h
    have hCa : Polynomial.C (β.num : ℚ) =
        Polynomial.C ((β.den : ℤ) : ℚ) * Polynomial.C β := by
      rw [← Polynomial.C_mul]
      congr 1
      have : (((β.den : ℤ) : ℚ)) = ((β.den : ℚ)) := by norm_num
      rw [this, hβcast]
    have hCbX : (Polynomial.C ((β.den : ℤ) : ℚ) * Polynomial.X - Polynomial.C (β.num : ℚ)) =
        Polynomial.C ((β.den : ℤ) : ℚ) * (Polynomial.X - Polynomial.C β) := by
      rw [mul_sub, hCa]
    have hbq_ne : (((β.den : ℤ) : ℚ)) ≠ 0 := by
      have : (0 : ℚ) < ((β.den : ℤ) : ℚ) := by exact_mod_cast hb
      exact ne_of_gt this
    have hunit : IsUnit ((Polynomial.C (((β.den : ℤ) : ℚ))) ^ l) := by
      apply IsUnit.pow
      rw [Polynomial.isUnit_C]
      exact isUnit_iff_ne_zero.mpr hbq_ne
    have hdivA : A.map (Int.castRingHom ℚ) ∣ P.map (Int.castRingHom ℚ) := by
      rw [hmapA, hCbX, mul_pow]
      exact (hunit.mul_left_dvd).mpr hdiv0
    -- Gauss's lemma
    have hAdvd : A ∣ P.primPart :=
      (hAprim.dvd_primPart_iff_dvd hP).mpr
        ((Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast A P hAprim).mpr hdivA)
    obtain ⟨k, hk_le, hk_ge⟩ :=
      coeff_abs_ge_of_dvd_C_mul_X_sub_C β.num β.den hb ha l (Polynomial.primPart_ne_zero P)
        (by rw [← hA]; exact hAdvd)
    -- transfer the bound from `P.primPart` to `P`
    have hcoeff : (max β.num.natAbs β.den) ^ l ≤ (P.coeff k).natAbs := by
      have hPc : P.coeff k = P.content * (P.primPart).coeff k := by
        conv_lhs => rw [Polynomial.eq_C_content_mul_primPart P]
        rw [Polynomial.coeff_C_mul]
      have hcont_nonneg : 0 ≤ P.content :=
        Int.nonneg_of_normalize_eq_self Polynomial.normalize_content
      have hcont_ne : P.content ≠ 0 := fun h => hP (Polynomial.content_eq_zero_iff.mp h)
      rw [hPc, Int.natAbs_mul]
      calc (max β.num.natAbs β.den) ^ l ≤ (P.primPart.coeff k).natAbs := hk_ge
        _ = 1 * (P.primPart.coeff k).natAbs := (one_mul _).symm
        _ ≤ P.content.natAbs * (P.primPart.coeff k).natAbs := by
            apply Nat.mul_le_mul_right
            omega
    have hk_leP : k ≤ P.natDegree := by
      rw [← Polynomial.natDegree_primPart P]
      exact hk_le
    -- height lower bound
    have hheight := mulHeight_coeff_ge k hk_leP
    have htarget : ((max β.num.natAbs β.den : ℕ) : ℝ) ^ l ≤
        Height.mulHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) := by
      calc ((max β.num.natAbs β.den : ℕ) : ℝ) ^ l
          = ((max β.num.natAbs β.den) ^ l : ℕ) := by push_cast; ring
        _ ≤ ((P.coeff k).natAbs : ℝ) := by exact_mod_cast hcoeff
        _ ≤ Height.mulHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) :=
            hheight
    have hxpos : (0 : ℝ) < ((max β.num.natAbs β.den : ℕ) : ℝ) := by
      have : 0 < max β.num.natAbs β.den := lt_of_lt_of_le hb (le_max_right _ _)
      exact_mod_cast this
    calc (l : ℝ) * Height.logHeight₁ β
        = (l : ℝ) * Real.log ((max β.num.natAbs β.den : ℕ) : ℝ) := by
          rw [Rat.logHeight₁_eq_log_max]
      _ = Real.log (((max β.num.natAbs β.den : ℕ) : ℝ) ^ l) := (Real.log_pow _ l).symm
      _ ≤ Real.log (Height.mulHeight
            (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ)))) :=
          Real.log_le_log (by positivity) htarget
      _ = Height.logHeight (fun o : Option ℕ => o.elim (1 : ℚ) (fun m => (P.coeff m : ℚ))) := rfl

end Commons.NumberTheory.Height.MahlerMeasure