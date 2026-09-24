import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.char_large_sieve

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

noncomputable section

/-- Weighted Cauchy–Schwarz for real finset sums: `∑ w F G ≤ √(∑ w F²) √(∑ w G²)`. -/
lemma weighted_cs {ι : Type*} (s : Finset ι) (w F G : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∑ i ∈ s, w i * F i * G i ≤
      Real.sqrt (∑ i ∈ s, w i * F i ^ 2) * Real.sqrt (∑ i ∈ s, w i * G i ^ 2) := by
  have key := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Real.sqrt (w i) * F i) (fun i => Real.sqrt (w i) * G i)
  have e1 : (∑ i ∈ s, w i * F i * G i)
      = ∑ i ∈ s, (Real.sqrt (w i) * F i) * (Real.sqrt (w i) * G i) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [show (Real.sqrt (w i) * F i) * (Real.sqrt (w i) * G i)
        = (Real.sqrt (w i)) ^ 2 * (F i * G i) by ring, Real.sq_sqrt (hw i hi)]
    ring
  have e2 : (∑ i ∈ s, w i * F i ^ 2) = ∑ i ∈ s, (Real.sqrt (w i) * F i) ^ 2 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have e3 : (∑ i ∈ s, w i * G i ^ 2) = ∑ i ∈ s, (Real.sqrt (w i) * G i) ^ 2 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [e1, e2, e3]
  exact key

/-- Reduction of the dyadic totient-weighted sum to the global weighted sum. -/
lemma totient_inv_sum_le {R : ℕ} (hR : 1 ≤ R) (Z : ℕ → ℝ) (hZ : ∀ r, 0 ≤ Z r) (W : ℝ)
    (hCLS : ∑ r ∈ Finset.Icc 1 (2 * R), ((r : ℝ) / (Nat.totient r : ℝ)) * Z r ≤ W) :
    ∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * Z r ≤ (R : ℝ)⁻¹ * W := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hstep : ∀ r ∈ Finset.Icc (R + 1) (2 * R),
      (Nat.totient r : ℝ)⁻¹ * Z r ≤ (R : ℝ)⁻¹ * (((r : ℝ) / (Nat.totient r : ℝ)) * Z r) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hrR : (R : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : R ≤ r)
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
    have hphi_nn : 0 ≤ (Nat.totient r : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hinv : (r : ℝ)⁻¹ ≤ (R : ℝ)⁻¹ := (inv_le_inv₀ hrpos hRpos).mpr hrR
    have hfac_nn : 0 ≤ (r : ℝ) * (Nat.totient r : ℝ)⁻¹ :=
      mul_nonneg (Nat.cast_nonneg _) hphi_nn
    have hphi_eq : (Nat.totient r : ℝ)⁻¹ = (r : ℝ)⁻¹ * ((r : ℝ) * (Nat.totient r : ℝ)⁻¹) := by
      rw [← mul_assoc, inv_mul_cancel₀ hrne, one_mul]
    have hle : (Nat.totient r : ℝ)⁻¹ ≤ (R : ℝ)⁻¹ * ((r : ℝ) * (Nat.totient r : ℝ)⁻¹) :=
      calc (Nat.totient r : ℝ)⁻¹
          = (r : ℝ)⁻¹ * ((r : ℝ) * (Nat.totient r : ℝ)⁻¹) := hphi_eq
        _ ≤ (R : ℝ)⁻¹ * ((r : ℝ) * (Nat.totient r : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_right hinv hfac_nn
    calc (Nat.totient r : ℝ)⁻¹ * Z r
        ≤ ((R : ℝ)⁻¹ * ((r : ℝ) * (Nat.totient r : ℝ)⁻¹)) * Z r :=
          mul_le_mul_of_nonneg_right hle (hZ r)
      _ = (R : ℝ)⁻¹ * (((r : ℝ) / (Nat.totient r : ℝ)) * Z r) := by
          rw [div_eq_mul_inv]; ring
  have hsub : Finset.Icc (R + 1) (2 * R) ⊆ Finset.Icc 1 (2 * R) := by
    intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  calc ∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * Z r
      ≤ ∑ r ∈ Finset.Icc (R + 1) (2 * R),
          (R : ℝ)⁻¹ * (((r : ℝ) / (Nat.totient r : ℝ)) * Z r) := Finset.sum_le_sum hstep
    _ ≤ (R : ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 (2 * R), ((r : ℝ) / (Nat.totient r : ℝ)) * Z r := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r hr _ => ?_)
        exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hZ r))
    _ ≤ (R : ℝ)⁻¹ * W := mul_le_mul_of_nonneg_left hCLS (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem dyadic_bilinear_char_large_sieve (R U V : ℕ) (hR : 1 ≤ R) (a b : ℕ → ℂ) :
    (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ *
        ∑ ψ ∈ @Finset.filter (DirichletCharacter ℂ r) (fun ψ => ψ.IsPrimitive)
            (Classical.decPred (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)) Finset.univ,
          ‖∑ u ∈ Finset.Icc 1 U, a u * ψ (u : ZMod r)‖ *
          ‖∑ v ∈ Finset.Icc 1 V, b v * ψ (v : ZMod r)‖)
      ≤ (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * ∑ u ∈ Finset.Icc 1 U, ‖a u‖ ^ 2) *
          Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * ∑ v ∈ Finset.Icc 1 V, ‖b v‖ ^ 2) := by
  classical
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRinv_nn : 0 ≤ (R : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hQ : 1 ≤ 2 * R := by omega
  set WA : ℝ := ((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * ∑ u ∈ Finset.Icc 1 U, ‖a u‖ ^ 2 with hWA
  set WB : ℝ := ((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * ∑ v ∈ Finset.Icc 1 V, ‖b v‖ ^ 2 with hWB
  set X : ℕ → ℝ := fun r => ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter
        (fun ψ => ψ.IsPrimitive),
        ‖∑ u ∈ Finset.Icc 1 U, a u * ψ (u : ZMod r)‖ ^ 2 with hX
  set Y : ℕ → ℝ := fun r => ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter
        (fun ψ => ψ.IsPrimitive),
        ‖∑ v ∈ Finset.Icc 1 V, b v * ψ (v : ZMod r)‖ ^ 2 with hY
  have hXnn : ∀ r, 0 ≤ X r := by
    intro r; rw [hX]; exact Finset.sum_nonneg (fun i _ => by positivity)
  have hYnn : ∀ r, 0 ≤ Y r := by
    intro r; rw [hY]; exact Finset.sum_nonneg (fun i _ => by positivity)
  have hCLSa : ∑ r ∈ Finset.Icc 1 (2 * R), ((r : ℝ) / (Nat.totient r : ℝ)) * X r ≤ WA := by
    rw [hWA, hX]
    exact char_large_sieve (2 * R) U hQ a
  have hCLSb : ∑ r ∈ Finset.Icc 1 (2 * R), ((r : ℝ) / (Nat.totient r : ℝ)) * Y r ≤ WB := by
    rw [hWB, hY]
    exact char_large_sieve (2 * R) V hQ b
  have hbA : ∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * X r ≤ (R : ℝ)⁻¹ * WA :=
    totient_inv_sum_le hR X hXnn WA hCLSa
  have hbB : ∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * Y r ≤ (R : ℝ)⁻¹ * WB :=
    totient_inv_sum_le hR Y hYnn WB hCLSb
  calc (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ *
        ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ u ∈ Finset.Icc 1 U, a u * ψ (u : ZMod r)‖ *
          ‖∑ v ∈ Finset.Icc 1 V, b v * ψ (v : ZMod r)‖)
      ≤ ∑ r ∈ Finset.Icc (R + 1) (2 * R),
          (Nat.totient r : ℝ)⁻¹ * (Real.sqrt (X r) * Real.sqrt (Y r)) := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
        rw [hX, hY]
        exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * X r)
          * Real.sqrt (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * Y r) := by
        have hwcs := weighted_cs (Finset.Icc (R + 1) (2 * R))
          (fun r => (Nat.totient r : ℝ)⁻¹) (fun r => Real.sqrt (X r)) (fun r => Real.sqrt (Y r))
          (fun r _ => inv_nonneg.mpr (Nat.cast_nonneg _))
        have hsX : (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * X r)
            = ∑ r ∈ Finset.Icc (R + 1) (2 * R),
                (Nat.totient r : ℝ)⁻¹ * (Real.sqrt (X r)) ^ 2 :=
          Finset.sum_congr rfl (fun r _ => by rw [Real.sq_sqrt (hXnn r)])
        have hsY : (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ * Y r)
            = ∑ r ∈ Finset.Icc (R + 1) (2 * R),
                (Nat.totient r : ℝ)⁻¹ * (Real.sqrt (Y r)) ^ 2 :=
          Finset.sum_congr rfl (fun r _ => by rw [Real.sq_sqrt (hYnn r)])
        have h1 : (∑ r ∈ Finset.Icc (R + 1) (2 * R),
              (Nat.totient r : ℝ)⁻¹ * (Real.sqrt (X r) * Real.sqrt (Y r)))
            = ∑ r ∈ Finset.Icc (R + 1) (2 * R),
                ((Nat.totient r : ℝ)⁻¹ * Real.sqrt (X r)) * Real.sqrt (Y r) :=
          Finset.sum_congr rfl (fun r _ => by ring)
        rw [hsX, hsY, h1]
        exact hwcs
    _ ≤ Real.sqrt ((R : ℝ)⁻¹ * WA) * Real.sqrt ((R : ℝ)⁻¹ * WB) :=
        mul_le_mul (Real.sqrt_le_sqrt hbA) (Real.sqrt_le_sqrt hbB)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (R : ℝ)⁻¹ * Real.sqrt WA * Real.sqrt WB := by
        have hsq : Real.sqrt ((R : ℝ)⁻¹) * Real.sqrt ((R : ℝ)⁻¹) = (R : ℝ)⁻¹ := by
          have h := Real.sq_sqrt hRinv_nn
          rwa [pow_two] at h
        rw [Real.sqrt_mul hRinv_nn WA, Real.sqrt_mul hRinv_nn WB]
        rw [show Real.sqrt ((R : ℝ)⁻¹) * Real.sqrt WA * (Real.sqrt ((R : ℝ)⁻¹) * Real.sqrt WB)
            = (Real.sqrt ((R : ℝ)⁻¹) * Real.sqrt ((R : ℝ)⁻¹)) * (Real.sqrt WA * Real.sqrt WB) by ring,
          hsq]
        ring

end

end Commons.NumberTheory.BombieriVinogradov
