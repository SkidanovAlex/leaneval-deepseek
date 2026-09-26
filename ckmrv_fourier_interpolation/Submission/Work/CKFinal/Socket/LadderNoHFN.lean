import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.Asymptotics.Kaxis_local_tail
import Submission.Work.Asymptotics.T2op_kernelTransform
import Submission.Work.Asymptotics.CuspLadderTS
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.paperLayer_agreement

/-!
# The `T`-ladder of the CKMRV layer, redeployed on the non-clashing import chain

`Work.Asymptotics.lh_paperLayer_vadd_ladder_socket` (the redeployed copy of
`Work.Asymptotics.lh_paperLayer_vadd_ladder`, proved in
`Submission.Work.Asymptotics.PaperLayerLadderTS`) is re-exported here under the *same* name, but
with the whole supporting chain of the `Submission/Work/Asymptotics` copies, rather than the
duplicated `Submission/Work/HFN` copies.  The two copies declare the same names, so a file that
imports `Submission.Work.CKFinal.Socket.Construction` (whose closure contains
`Work.Asymptotics.Pspace` from `Submission/Work/Asymptotics/MiddleRange/Main`) cannot also import
the `HFN` copy of `MiddleRange/Main`; it can, however, import the `Asymptotics` copy.  The bodies
of the two files `FlatTailVaddOneTS` and `PaperLayerLadderTS` are reproduced verbatim below, with
only their `HFN` imports redirected to the corresponding `Asymptotics` modules.
-/

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

namespace Work.Asymptotics

/-! ## Elementary geometry -/

/-- The `𝒟` arc conditions say `|Re u| < (Re u)² + (Im u)²`. -/
private lemma lh_abs_re_lt_normSq_of_mem_DomainD {u : ℍ} (hu : u ∈ DomainD) :
    |u.re| < u.re ^ 2 + u.im ^ 2 := by
  have h1 : (1 / 2 : ℝ) < ‖(u : ℂ) - (1 / 2 : ℂ)‖ := hu.2.2.1
  have h2 : (1 / 2 : ℝ) < ‖(u : ℂ) + (1 / 2 : ℂ)‖ := hu.2.2.2
  have e1 : ‖(u : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (u.re - 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num
    ring
  have e2 : ‖(u : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (u.re + 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num
    ring
  have k1 : (1 / 4 : ℝ) < (u.re - 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [← e1]; nlinarith [norm_nonneg ((u : ℂ) - (1 / 2 : ℂ)), h1]
  have k2 : (1 / 4 : ℝ) < (u.re + 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [← e2]; nlinarith [norm_nonneg ((u : ℂ) + (1 / 2 : ℂ)), h2]
  rw [abs_lt]
  constructor <;> nlinarith [k1, k2]

/-- `‖(u : ℂ) - (3/2 : ℂ)‖ ^ 2 = (Re u - 3/2)^2 + (Im u)^2`. -/
private lemma lh_normSq_sub_threehalf (u : ℍ) :
    ‖(u : ℂ) - (3 / 2 : ℂ)‖ ^ 2 = (u.re - 3 / 2) ^ 2 + u.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- `u - 1 ∈ 𝒟` for `u ∈ 𝒟` with `0 < Re u`. -/
private lemma lh_vadd_neg_one_mem_DomainD_of_pos {u : ℍ} (hu : u ∈ DomainD) (hre : 0 < u.re) :
    ((-1 : ℝ) +ᵥ u) ∈ DomainD := by
  have harc := lh_abs_re_lt_normSq_of_mem_DomainD hu
  obtain ⟨harc1, harc2⟩ := abs_lt.mp harc
  have hcoe : ((((-1 : ℝ) +ᵥ u : ℍ)) : ℂ) = (u : ℂ) - 1 := by
    rw [UpperHalfPlane.coe_vadd]
    simp only [Complex.ofReal_neg, Complex.ofReal_one]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [UpperHalfPlane.vadd_re]; linarith [hu.1]
  · rw [UpperHalfPlane.vadd_re]; linarith [hu.2.1]
  · -- `|(u-1) - 1/2| > 1/2`, i.e. `(Re u - 3/2)^2 + (Im u)^2 > 1/4`
    have hnorm : ‖((((-1 : ℝ) +ᵥ u : ℍ)) : ℂ) - (1 / 2 : ℂ)‖ = ‖(u : ℂ) - (3 / 2 : ℂ)‖ := by
      rw [hcoe]; congr 1; ring
    rw [hnorm]
    have hsq := lh_normSq_sub_threehalf u
    have hkey : (1 / 4 : ℝ) < (u.re - 3 / 2) ^ 2 + u.im ^ 2 := by
      nlinarith [harc2, hu.2.1]
    nlinarith [norm_nonneg ((u : ℂ) - (3 / 2 : ℂ)), hsq, hkey]
  · -- `|(u-1) + 1/2| > 1/2` is exactly the condition `|u - 1/2| > 1/2`
    have hnorm : ‖((((-1 : ℝ) +ᵥ u : ℍ)) : ℂ) + (1 / 2 : ℂ)‖ = ‖(u : ℂ) - (1 / 2 : ℂ)‖ := by
      rw [hcoe]; congr 1; ring
    rw [hnorm]
    exact hu.2.2.1

/-! ## Flatness at `1 +ᵥ u` -/

/-- The pointwise `T`-identity for the kernel on the contour. -/
private lemma lh_Kaxis_vadd (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (u : ℍ)
    (t : ℝ) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
      = 2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
        - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t := by
  have h := congr_fun (Work.Asymptotics.Kaxis_Kfun_T2 ℓ d hd t) ((-1 : ℝ) +ᵥ u)
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h
  rw [show (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = (1 : ℝ) +ᵥ u from by rw [← add_vadd]; norm_num,
    show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = u from by rw [← add_vadd]; norm_num] at h
  linear_combination h

/-- **Flatness of the kernel at `1 +ᵥ u`** for `u ∈ 𝒟` with `Re u > 0`. -/
private theorem lh_flat_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ DomainD) (hre : 0 < u.re) :
    ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t‖ ≤ c * t ^ N := by
  intro N hN
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ DomainD := lh_vadd_neg_one_mem_DomainD_of_pos hu hre
  obtain ⟨c1, hc1, h1⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd
    (K := ({u} : Set ℍ)) isCompact_singleton (by rintro x rfl; exact hu) N hN
  obtain ⟨c2, hc2, h2⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd
    (K := ({((-1 : ℝ) +ᵥ u)} : Set ℍ)) isCompact_singleton
    (by rintro x rfl; exact hu1D) N hN
  refine ⟨2 * c1 + c2, by positivity, fun t ht ht1 => ?_⟩
  have b1 := h1 u t (by simp) ht ht1
  have b2 := h2 ((-1 : ℝ) +ᵥ u) t (by simp) ht ht1
  rw [lh_Kaxis_vadd ℓ d hd u t]
  calc ‖2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
        - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t‖
      ≤ ‖2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t‖
        + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t‖ := norm_sub_le _ _
    _ = 2 * ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t‖
        + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t‖ := by
        rw [norm_mul]; norm_num
    _ ≤ 2 * (c1 * t ^ N) + c2 * t ^ N := by linarith
    _ = (2 * c1 + c2) * t ^ N := by ring

/-! ## The cusp-`i∞` tail at `1 +ᵥ u` -/

/-- **The cusp-`i∞` tail estimate at `1 +ᵥ u`** for `u ∈ 𝒟` with `Re u > 0`. -/
private theorem lh_tail_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ DomainD) (hre : 0 < u.re) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ DomainD := lh_vadd_neg_one_mem_DomainD_of_pos hu hre
  obtain ⟨C1, M1, T1, hC1, hM1, hT1, hb1⟩ := Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd
    (K := ({u} : Set ℍ)) isCompact_singleton (by rintro x rfl; exact hu)
  obtain ⟨C2, M2, T2, hC2, hM2, hT2, hb2⟩ := Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd
    (K := ({((-1 : ℝ) +ᵥ u)} : Set ℍ)) isCompact_singleton (by rintro x rfl; exact hu1D)
  refine ⟨2 * (C1 * Real.exp (Real.pi * T1)) + C2 * Real.exp (Real.pi * T2), max M1 M2, 0,
    by positivity, le_trans hM1 (le_max_left _ _), le_rfl, fun t ht => ?_⟩
  simp only [sub_zero]
  have b1 := hb1 u t (by simp) ht
  have b2 := hb2 ((-1 : ℝ) +ᵥ u) t (by simp) ht
  have hA := Aexp_vadd_ladderTS ℓ d hd u t
  have hval : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t
      = 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
        - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t) := by
    rw [lh_Kaxis_vadd ℓ d hd u t, hA]
    ring
  set A : ℝ := ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
    - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t‖ with hAdef
  set B : ℝ := ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
    - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t‖ with hBdef
  have hA1 : A ≤ C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1))) := by
    rw [hAdef]; exact b1
  have hB1 : B ≤ C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2))) := by
    rw [hBdef]; exact b2
  have hnorm : ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
      - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t)‖
      ≤ 2 * (C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1))))
        + C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2))) := by
    have h1 : ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
        - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t)‖
        ≤ 2 * A + B := by
      calc ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
          - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t)‖
          ≤ ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)‖
            + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t‖ :=
            norm_sub_le _ _
        _ = 2 * A + B := by rw [norm_mul, hAdef, hBdef]; norm_num
    linarith [h1, hA1, hB1]
  rw [hval]
  refine le_trans hnorm ?_
  have hM1' : (1 + t) ^ M1 ≤ (1 + t) ^ max M1 M2 :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hM2' : (1 + t) ^ M2 ≤ (1 + t) ^ max M1 M2 :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have heq1 : Real.exp (-(Real.pi * (t - T1)))
      = Real.exp (Real.pi * T1) * Real.exp (-(Real.pi * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have heq2 : Real.exp (-(Real.pi * (t - T2)))
      = Real.exp (Real.pi * T2) * Real.exp (-(Real.pi * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE1 : C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1)))
      ≤ (C1 * Real.exp (Real.pi * T1)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by
    rw [heq1]
    calc C1 * (1 + t) ^ M1 * (Real.exp (Real.pi * T1) * Real.exp (-(Real.pi * t)))
        = (C1 * Real.exp (Real.pi * T1)) * ((1 + t) ^ M1 * Real.exp (-(Real.pi * t))) := by ring
      _ ≤ (C1 * Real.exp (Real.pi * T1)) * ((1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hM1' (Real.exp_nonneg _)) (by positivity)
      _ = (C1 * Real.exp (Real.pi * T1)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by ring
  have hE2 : C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2)))
      ≤ (C2 * Real.exp (Real.pi * T2)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by
    rw [heq2]
    calc C2 * (1 + t) ^ M2 * (Real.exp (Real.pi * T2) * Real.exp (-(Real.pi * t)))
        = (C2 * Real.exp (Real.pi * T2)) * ((1 + t) ^ M2 * Real.exp (-(Real.pi * t))) := by ring
      _ ≤ (C2 * Real.exp (Real.pi * T2)) * ((1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hM2' (Real.exp_nonneg _)) (by positivity)
      _ = (C2 * Real.exp (Real.pi * T2)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by ring
  calc 2 * (C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1))))
        + C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2)))
      ≤ 2 * ((C1 * Real.exp (Real.pi * T1)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)))
        + (C2 * Real.exp (Real.pi * T2)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by
        linarith
    _ = (2 * (C1 * Real.exp (Real.pi * T1)) + C2 * Real.exp (Real.pi * T2))
          * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by ring


private lemma lh_norm_exp_contour (r t : ℝ) :
    ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [Complex.norm_exp]
  congr 1
  have hr2 : ((r : ℂ) ^ 2).re = r ^ 2 := by
    have h : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow r 2).symm
    rw [h, Complex.ofReal_re]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  rw [hr2]
  ring

/-- The elementary decay comparison used to dominate the cusp-`i∞` tail by an integrable
exponential. -/
private lemma lh_tail_exp_bound {C M T₀ r t : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (ht : 1 ≤ t) :
    C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
      ≤ (C * Real.exp (Real.pi * T₀) * 2 ^ M)
          * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have h1t : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
    calc (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      _ = 2 ^ M * t ^ M := Real.mul_rpow (by norm_num) (by linarith)
  have hX : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) := by
    positivity
  have hCE : (0 : ℝ) ≤ C * Real.exp (Real.pi * T₀) := mul_nonneg hC (Real.exp_nonneg _)
  calc C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
      = (C * Real.exp (Real.pi * T₀))
          * ((1 + t) ^ M
              * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
        rw [show -(Real.pi * (t - T₀)) = Real.pi * T₀ + -(Real.pi * t) by ring, Real.exp_add]
        ring
    _ ≤ (C * Real.exp (Real.pi * T₀))
          * ((2 ^ M * t ^ M)
              * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1t hX) hCE
    _ = (C * Real.exp (Real.pi * T₀) * 2 ^ M)
          * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) := by
        rw [show Real.exp (-((Real.pi * (1 + r ^ 2)) * t))
            = Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) by
          rw [← Real.exp_add]; congr 1; ring]
        ring

/-! ## Integrability of the two integrands, from flatness and from the cusp expansion -/

/-- Integrability on `(0,1]` of the low contour integrand, from a uniform bound on the kernel. -/
private lemma lh_integrableOn_low_of_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ : ℍ} {c : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  have hc : 0 ≤ c := le_trans (norm_nonneg _) (h (1 / 2) (by norm_num) (by norm_num))
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top ?_ c ?_
  · exact ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have hb := h t ht0 ht.2
    rw [norm_mul, lh_norm_exp_contour]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ c * 1 := by
          refine mul_le_mul hb ?_ (Real.exp_nonneg _) hc
          rw [Real.exp_le_one_iff]
          have hpos : 0 ≤ Real.pi * r ^ 2 * t :=
            mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le
          linarith
      _ = c := mul_one c

/-- Integrability on `(0,1]` of the low contour integrand at a point of `𝒟`. -/
private lemma lh_integrableOn_low_of_mem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  obtain ⟨c, -, hb⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd
    (K := {τ}) isCompact_singleton (by rintro x rfl; exact hτ) 0 le_rfl
  exact lh_integrableOn_low_of_bound ℓ d hd
    (fun t ht0 ht1 => by simpa [Real.rpow_zero] using hb τ t (by simp) ht0 ht1) r

/-- Integrability on `(0,1]` of the low contour integrand at the `T`-translate `1 +ᵥ u`. -/
private lemma lh_integrableOn_low_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re)
    (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  obtain ⟨c, -, hb⟩ := lh_flat_vadd_one ℓ d hd u hu hre 0 le_rfl
  exact lh_integrableOn_low_of_bound ℓ d hd
    (fun t ht0 ht1 => by simpa [Real.rpow_zero] using hb t ht0 ht1) r

/-- Integrability on `[1,∞)` of the truncated contour integrand, from a polynomial/exponential
bound on `K - Aexp`. -/
private lemma lh_integrableOn_trunc_of_tail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → ℍ → ℂ) {τ : ℍ} {C M T₀ : ℝ} (hC : 0 ≤ C)
    (hM : 0 ≤ M)
    (h : ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  have hcpos : 0 < Real.pi * (1 + r ^ 2) := by positivity
  have hdomIoi : MeasureTheory.Integrable (fun t : ℝ =>
      (C * Real.exp (Real.pi * T₀) * 2 ^ M)
        * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (Work.Asymptotics.integrableOn_rpow_mul_exp_neg_mul_Ioi M (Real.pi * (1 + r ^ 2))
      hcpos).const_mul _
  have hdom : MeasureTheory.Integrable (fun t : ℝ =>
      (C * Real.exp (Real.pi * T₀) * 2 ^ M)
        * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))))
      (volume.restrict (Set.Ici (1 : ℝ))) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (b := (1 : ℝ))).mpr hdomIoi
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
      (by unfold Work.Asymptotics.Aexp; fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have hb := h t ht1
    rw [norm_mul, lh_norm_exp_contour]
    exact le_trans (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _))
      (lh_tail_exp_bound hC hM ht1)

/-- Integrability on `[1,∞)` of the truncated contour integrand at a point of `𝒟`. -/
private lemma lh_integrableOn_trunc_of_mem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  obtain ⟨C, M, T₀, hC, hM, -, hb⟩ := Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd
    (K := {τ}) isCompact_singleton (by rintro x rfl; exact hτ)
  exact lh_integrableOn_trunc_of_tail ℓ d hd (Work.Asymptotics.Gcusp ℓ d)
    hC.le hM (fun t ht1 => hb τ t (by simp) ht1) r

/-- Integrability on `[1,∞)` of the truncated contour integrand at the `T`-translate `1 +ᵥ u`. -/
private lemma lh_integrableOn_trunc_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re)
    (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  obtain ⟨C, M, T₀, hC, hM, -, hb⟩ := lh_tail_vadd_one ℓ d hd u hu hre
  exact lh_integrableOn_trunc_of_tail ℓ d hd (Work.Asymptotics.Gcusp ℓ d)
    hC.le hM hb r

/-! ## The `T`-ladders of the pieces of the layer -/

/-- The `T`-ladder of `highPart`. -/
private lemma lh_highPart_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (r : ℝ) :
    Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) u r
        - Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) r := by
  simp only [Work.Asymptotics.highPart]
  rw [Gcusp_vadd_ladderTS ℓ d hd 0 0 u, Gcusp_vadd_ladderTS ℓ d hd 0 1 u,
    Gcusp_vadd_ladderTS ℓ d hd 1 0 u, Gcusp_vadd_ladderTS ℓ d hd 1 1 u]
  ring

/-- **The ladder of the `low` piece.** -/
private lemma lh_layerLow_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re) (r : ℝ) :
    Work.Asymptotics.layerLow ℓ d ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.layerLow ℓ d u r
        - Work.Asymptotics.layerLow ℓ d ((-1 : ℝ) +ᵥ u) r := by
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    lh_vadd_neg_one_mem_DomainD_of_pos hu hre
  have hint1 := lh_integrableOn_low_vadd_one ℓ d hd u hu hre r
  have hint0 := lh_integrableOn_low_of_mem ℓ d hd hu r
  have hintm := lh_integrableOn_low_of_mem ℓ d hd hu1D r
  have hpoint : ∀ t : ℝ,
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    linear_combination (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      * lh_Kaxis_vadd ℓ d hd u t
  have hkey : (∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = 2 * (∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        - ∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hpoint t),
      MeasureTheory.integral_sub (hint0.const_mul 2) hintm,
      MeasureTheory.integral_const_mul]
  simp only [Work.Asymptotics.layerLow]
  rw [hkey]
  ring

/-- **The ladder of the `trunc` piece.** -/
private lemma lh_layerTrunc_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re) (r : ℝ) :
    Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d u r
        - Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r := by
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    lh_vadd_neg_one_mem_DomainD_of_pos hu hre
  have hint1 := lh_integrableOn_trunc_vadd_one ℓ d hd u hu hre r
  have hint0 := lh_integrableOn_trunc_of_mem ℓ d hd hu r
  have hintm := lh_integrableOn_trunc_of_mem ℓ d hd hu1D r
  have hpoint : ∀ t : ℝ,
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = 2 * ((Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    linear_combination (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        * lh_Kaxis_vadd ℓ d hd u t
      - (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) * Aexp_vadd_ladderTS ℓ d hd u t
  simp only [Work.Asymptotics.layerTrunc]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun t _ => hpoint t),
    MeasureTheory.integral_sub (hint0.const_mul 2) hintm,
    MeasureTheory.integral_const_mul]
  ring

/-- **The `T`-ladder of `paperLayer` at the translate `1 +ᵥ u`.** -/
theorem lh_paperLayer_vadd_ladder_socket (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re) (r : ℝ) :
    Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u r
        - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r := by
  have hlow := lh_layerLow_vadd_ladder ℓ d hd u hu hre r
  have htrunc := lh_layerTrunc_vadd_ladder ℓ d hd u hu hre r
  have hhigh := lh_highPart_vadd_ladder ℓ d hd u r
  simp only [Work.Asymptotics.paperLayer]
  rw [hlow, htrunc, hhigh]
  ring

/-- **The `T`-ladder of the layer at the translate `1 +ᵥ u`.** -/
private theorem lh_layer_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re) (r : ℝ) :
    Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u r
        - Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r := by
  by_cases hr : r = 0
  · subst hr
    simp [Work.Asymptotics.layer]
  · rw [Work.Asymptotics.layer, if_neg hr, Work.Asymptotics.layer, if_neg hr,
      Work.Asymptotics.layer, if_neg hr]
    exact lh_paperLayer_vadd_ladder_socket ℓ d hd u hu hre r

end Work.Asymptotics
