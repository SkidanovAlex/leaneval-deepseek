import Mathlib.Analysis.Fourier.AddCircle
import Submission.Commons.Analysis.Fourier.cos_basis_parseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open MeasureTheory intervalIntegral
open scoped Real

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- The `k`-th cosine coefficient `cosCoeff f k` (for `k : ℕ`) is the integral of
`f x * cos (k π (x + 1/2))` over `[-1/2, 1/2]`. -/
lemma cosCoeff_nat_eq {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) :
    cosCoeff f (k : ℤ)
      = ∫ x in (-(1/2))..(1/2), f x * Real.cos ((k : ℝ) * Real.pi * (x + 1/2)) := by
  unfold cosCoeff
  have hsub := intervalIntegral.integral_comp_add_right (a := (-(1/2):ℝ)) (b := 1/2)
        (fun u : ℝ => hExt f u * Real.cos (((k:ℤ) : ℝ) * Real.pi * u)) (1/2)
  rw [show (-(1/2):ℝ) + 1/2 = 0 by norm_num, show (1:ℝ)/2 + 1/2 = 1 by norm_num] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only []
  rw [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)] at hx
  rw [hExt_add_half hx]
  rw [show (((k:ℤ) : ℝ)) = (k:ℝ) by push_cast; ring]

/-- The squared cosine coefficients form an even function on `ℤ`. -/
lemma cosCoeff_sq_even (f : ℝ → ℝ) :
    Function.Even (fun i : ℤ => (cosCoeff f i)^2) := by
  intro i
  show (cosCoeff f (-i))^2 = (cosCoeff f i)^2
  congr 1
  unfold cosCoeff
  apply intervalIntegral.integral_congr
  intro u hu
  simp only []
  rw [show (((-i : ℤ) : ℝ) * Real.pi * u) = -(((i:ℤ) : ℝ) * Real.pi * u) by push_cast; ring,
      Real.cos_neg]

/-- Parseval's identity for the cosine basis on `[-1/2, 1/2]`, in `HasSum` form over `ℤ`. -/
theorem cos_parseval_one_hasSum_int {f : ℝ → ℝ} (hf : Continuous f) :
    HasSum (fun i : ℤ => (cosCoeff f i)^2) (∫ x in (-(1/2))..(1/2), (f x)^2) := by
  have h02 : (0:ℝ) < 2 := by norm_num
  have hL2 : MemLp (fun u => (hExt f u : ℂ)) 2 (volume.restrict (Set.Ioc (0:ℝ) 2)) :=
    memLp_continuous_Ioc (Complex.continuous_ofReal.comp (hExt_continuous hf)) 0 2
  have hbase := hasSum_sq_fourierCoeffOn h02 hL2
  have hterm : (fun i : ℤ => ‖fourierCoeffOn h02 (fun u => (hExt f u : ℂ)) i‖ ^ 2)
      = fun i : ℤ => (cosCoeff f i)^2 := by
    funext i
    rw [fourierCoeffOn_hExt_eq hf i, Complex.sq_norm, Complex.normSq_ofReal]
    ring
  have hval : ((2:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..2, ‖(fun u => (hExt f u : ℂ)) x‖^2
      = ∫ x in (-(1/2))..(1/2), (f x)^2 := by
    rw [show (2:ℝ) - 0 = 2 by norm_num]
    have hb : (∫ x in (0:ℝ)..2, ‖((hExt f x : ℂ))‖^2) = ∫ x in (0:ℝ)..2, (hExt f x)^2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only []
      rw [Complex.sq_norm, Complex.normSq_ofReal]
      ring
    rw [hb]
    rw [smul_eq_mul]
    rw [show (2:ℝ)⁻¹ = 1/2 by norm_num]
    rw [← half_integral_eq hf, integral_sq_eq hf]
  rw [hterm, hval] at hbase
  exact hbase

/-- Folding an even `ℤ`-indexed summable real family to `ℕ`: the `k = 0` term is kept
once and the others are doubled. -/
lemma hasSum_even_int_nat_fold {f : ℤ → ℝ} {L : ℝ}
    (hf : Function.Even f) (h : HasSum f L) :
    HasSum (fun k : ℕ => (if k = 0 then (1:ℝ) else 2) * f (k : ℤ)) L := by
  have hsumZ : Summable f := h.summable
  have hsumN : Summable (fun k : ℕ => f (k : ℤ)) :=
    hsumZ.comp_injective (i := fun k : ℕ => (k : ℤ)) Nat.cast_injective
  have htail : (∑' k : ℕ, f ((k+1 : ℕ) : ℤ)) = (∑' k : ℕ, f (k : ℤ)) - f 0 := by
    have h1 := hsumN.tsum_eq_zero_add
    simp only [Nat.cast_zero] at h1
    linarith [h1]
  have hL : L = f 0 + 2 * ((∑' k : ℕ, f (k : ℤ)) - f 0) := by
    rw [← h.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat hf hsumZ, nsmul_eq_mul,
      tsum_pnat_eq_tsum_succ (f := fun m : ℕ => f (m : ℤ)), htail]
    norm_num
  have hsumA : Summable (fun k : ℕ => (if k = 0 then (1:ℝ) else 2) * f (k : ℤ)) := by
    have hsingle : Summable (fun k : ℕ => if k = 0 then f (0:ℤ) else 0) :=
      (hasSum_ite_eq (0:ℕ) (f (0:ℤ))).summable
    have h2 : Summable (fun k : ℕ => (2:ℝ) * f (k:ℤ)) := Summable.mul_left 2 hsumN
    refine (h2.sub hsingle).congr ?_
    intro k
    by_cases hk : k = 0
    · subst hk; simp only [↓reduceIte, Nat.cast_zero, one_mul]; ring
    · rw [if_neg hk, if_neg hk]; ring
  have htsumA : (∑' k : ℕ, (if k = 0 then (1:ℝ) else 2) * f (k : ℤ)) = L := by
    have h1 := hsumA.tsum_eq_zero_add
    have h2 : (∑' k : ℕ, (if k + 1 = 0 then (1:ℝ) else 2) * f ((k+1 : ℕ) : ℤ))
        = 2 * (∑' k : ℕ, f ((k+1 : ℕ) : ℤ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [if_neg (Nat.succ_ne_zero k)]
    rw [h1, h2]
    simp only [Nat.cast_zero, ↓reduceIte, one_mul]
    rw [htail, hL]
  have hh := hsumA.hasSum
  rwa [htsumA] at hh

/-- Parseval's identity for the cosine basis on `[-1/2, 1/2]`, `ℓ = 1` case. -/
theorem cos_parseval_one_hasSum {f : ℝ → ℝ} (hf : Continuous f) :
    HasSum (fun k : ℕ =>
        (∫ x in (-(1/2))..(1/2), f x * Real.cos ((k:ℝ) * Real.pi * (x + 1/2)))^2
          / (if k = 0 then (1:ℝ) else 1/2))
      (∫ x in (-(1/2))..(1/2), (f x)^2) := by
  have hZ := cos_parseval_one_hasSum_int hf
  have hfold := hasSum_even_int_nat_fold (cosCoeff_sq_even f) hZ
  have hfun : (fun k : ℕ => (if k = 0 then (1:ℝ) else 2) * (cosCoeff f (k:ℤ))^2)
      = fun k : ℕ =>
          (∫ x in (-(1/2))..(1/2), f x * Real.cos ((k:ℝ) * Real.pi * (x + 1/2)))^2
            / (if k = 0 then (1:ℝ) else 1/2) := by
    funext k
    rw [cosCoeff_nat_eq hf k]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]; ring
    · rw [if_neg hk, if_neg hk]; field_simp
  rwa [hfun] at hfold

/-- Parseval's identity for the rescaled cosine basis on `[-ℓ/2, ℓ/2]` (`HasSum` form). -/
theorem cos_parseval_scaled_hasSum {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ → ℝ} (hg : Continuous g) :
    HasSum (fun k : ℕ =>
        (∫ x in (-(ℓ / 2))..(ℓ / 2),
            g x * Real.cos (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2
          / (if k = 0 then ℓ else ℓ / 2))
      (∫ x in (-(ℓ / 2))..(ℓ / 2), (g x) ^ 2) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hf : Continuous (fun t : ℝ => g (ℓ * t)) := hg.comp (by fun_prop)
  have h1 := cos_parseval_one_hasSum (f := fun t : ℝ => g (ℓ * t)) hf
  have h1ℓ := HasSum.mul_left ℓ h1
  have hc : ∀ k : ℕ,
      (∫ x in (-(ℓ/2))..(ℓ/2), g x * Real.cos (((k:ℝ)*Real.pi/ℓ)*(x+ℓ/2)))
        = ℓ * ∫ t in (-(1/2))..(1/2), g (ℓ*t) * Real.cos ((k:ℝ)*Real.pi*(t+1/2)) := by
    intro k
    have key := smul_integral_comp_mul_left
        (fun x : ℝ => g x * Real.cos ((k:ℝ)*Real.pi*(x/ℓ + 1/2))) ℓ
        (a := (-(1/2):ℝ)) (b := (1/2:ℝ))
    rw [show ℓ * (-(1/2)) = -(ℓ/2) by ring, show ℓ * (1/2) = ℓ/2 by ring,
        smul_eq_mul] at key
    have hgi : (∫ x in (-(1/2))..(1/2), g (ℓ*x) * Real.cos ((k:ℝ)*Real.pi*((ℓ*x)/ℓ + 1/2)))
        = ∫ t in (-(1/2))..(1/2), g (ℓ*t) * Real.cos ((k:ℝ)*Real.pi*(t+1/2)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only []
      rw [show (ℓ*t)/ℓ = t by field_simp]
    have hcos : (∫ x in (-(ℓ/2))..(ℓ/2), g x * Real.cos ((k:ℝ)*Real.pi*(x/ℓ + 1/2)))
        = ∫ x in (-(ℓ/2))..(ℓ/2), g x * Real.cos (((k:ℝ)*Real.pi/ℓ)*(x+ℓ/2)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only []
      rw [show ((k:ℝ)*Real.pi/ℓ)*(x+ℓ/2) = (k:ℝ)*Real.pi*(x/ℓ+1/2) by field_simp]
    calc (∫ x in (-(ℓ/2))..(ℓ/2), g x * Real.cos (((k:ℝ)*Real.pi/ℓ)*(x+ℓ/2)))
        = ∫ x in (-(ℓ/2))..(ℓ/2), g x * Real.cos ((k:ℝ)*Real.pi*(x/ℓ + 1/2)) := hcos.symm
      _ = ℓ * ∫ x in (-(1/2))..(1/2), g (ℓ*x) * Real.cos ((k:ℝ)*Real.pi*((ℓ*x)/ℓ + 1/2)) :=
            key.symm
      _ = ℓ * ∫ t in (-(1/2))..(1/2), g (ℓ*t) * Real.cos ((k:ℝ)*Real.pi*(t+1/2)) := by rw [hgi]
  have hV : (∫ x in (-(ℓ/2))..(ℓ/2), (g x)^2)
      = ℓ * ∫ t in (-(1/2))..(1/2), (g (ℓ*t))^2 := by
    have key := smul_integral_comp_mul_left (fun x : ℝ => (g x)^2) ℓ
        (a := (-(1/2):ℝ)) (b := (1/2:ℝ))
    rw [show ℓ * (-(1/2)) = -(ℓ/2) by ring, show ℓ * (1/2) = ℓ/2 by ring,
        smul_eq_mul] at key
    rw [← key]
  have hfun : (fun k : ℕ => ℓ * ((∫ t in (-(1/2))..(1/2),
        g (ℓ*t) * Real.cos ((k:ℝ)*Real.pi*(t+1/2)))^2 / (if k = 0 then (1:ℝ) else 1/2)))
      = fun k : ℕ => (∫ x in (-(ℓ/2))..(ℓ/2),
            g x * Real.cos (((k:ℝ)*Real.pi/ℓ)*(x+ℓ/2)))^2
          / (if k = 0 then ℓ else ℓ/2) := by
    funext k
    have hstep : ∀ D : ℝ, ℓ * (D^2 / (if k = 0 then (1:ℝ) else 1/2))
        = (ℓ * D)^2 / (if k = 0 then ℓ else ℓ/2) := by
      intro D
      by_cases hk : k = 0
      · rw [if_pos hk, if_pos hk]; field_simp
      · rw [if_neg hk, if_neg hk]; field_simp
    rw [hc k]
    exact hstep _
  rw [hfun] at h1ℓ
  rw [← hV] at h1ℓ
  exact h1ℓ

end

end Commons.Analysis.Fourier
