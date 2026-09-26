/-
# Assembly of the cusp-`i∞` tail estimate on the cusp-`0` tile `E`

This file contains the two algebraic inputs of the assembly of `Work.Asymptotics.ETail` from
the four half-estimates `EtailE_KPlus8`/`EtailE_KMinus8`/`EtailE_KPlus24`/`EtailE_KMinus24`:

* `Aexp_Gcoef'`: `Aexp (Compact.Gcoef d ℓ) τ t = Gfun d ℓ τ (i t)`;
* `Gcusp_eq_Gcoef`: the cusp coefficients `Gcusp ℓ d` of `Submission/Work/Asymptotics/GcuspDefs.lean`
  agree with the equivalent definition `Compact.Gcoef d ℓ`;
* `ETail_of_pieces`: the reduction of `ETail ℓ d` to the two half-estimates, including the
  matching of the thresholds (`N₀ = 2`).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EtailE.Shapes
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.Compact.gfun_eq

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm

namespace Work.Asymptotics

open Work.Asymptotics.EtailE
open Work.Kernels

lemma Aexp_Gcoef' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (t : ℝ)
    (ht : 0 < t) :
    Aexp (Compact.Gcoef d ℓ) τ t = Compact.Gfun d ℓ τ (Work.Kernels.imagAxis t ht) := by
  have hcoe : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  have hE : (Work.Residues.Ept (Work.Kernels.imagAxis t ht)) ^ (-2 : ℤ)
      = Complex.exp (2 * Real.pi * t) := by
    rw [Work.Residues.Ept, hcoe]
    have h1 : Real.pi * Complex.I * ((t : ℂ) * Complex.I)
        = (Real.pi * (t : ℂ)) * (Complex.I * Complex.I) := by ring
    rw [h1, Complex.I_mul_I, _root_.zpow_neg, zpow_ofNat, ← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1
    ring
  rw [Aexp, Compact.Gfun, hcoe, hE]

lemma Gcusp_eq_Gcoef (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Gcusp ℓ d = Compact.Gcoef d ℓ := by
  have hcl : cuspL ℓ = Compact.cuspC ℓ := rfl
  rcases hd with rfl | rfl
  · have hfun : Gcusp ℓ 8 = Gcusp8 ℓ := by rw [Gcusp]; exact if_pos rfl
    rw [hfun]
    funext i j τ
    unfold Gcusp8 Compact.Gcoef
    simp only [if_true, hcl, Work.Kernels.phiVec, Work.Kernels.phiNeg2, Work.Kernels.phi0,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two, Compact.phi1, Compact.phi2t]
    first | split_ifs <;> ring_nf | skip
  · have hfun : Gcusp ℓ 24 = Gcusp24 ℓ := by rw [Gcusp]; exact if_neg (by norm_num)
    rw [hfun]
    funext i j τ
    unfold Gcusp24 Compact.Gcoef
    simp only [if_neg (by norm_num : ¬ (24 = 8)), hcl, Work.Kernels.phiVec, Work.Kernels.phiNeg2,
      Work.Kernels.phi0, Work.Kernels.phi2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
      Fin.val_two, Compact.phi1, Compact.phi2t]
    first | split_ifs <;> ring_nf | skip

/-- Assemble `ETail ℓ d` from the two half-estimates on `E`. -/
lemma ETail_of_pieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hKp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t → (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KPlus d w z - Compact.Gplus d w z‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)))
    (hKm : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t → (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KMinus ℓ d w z - Compact.Gminus d ℓ w z‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t))) :
    ETail ℓ d := by
  obtain ⟨C₁, N₁, M₁, hC₁, hN₁, hM₁, hKp⟩ := hKp
  obtain ⟨C₂, N₂, M₂, hC₂, hN₂, hM₂, hKm⟩ := hKm
  refine ⟨((2:ℕ):ℝ), (C₁ + C₂) / 2 * 2 ^ max M₁ M₂ + 1, max N₁ N₂, max M₁ M₂,
    by norm_num, by positivity, le_max_of_le_left hN₁, le_max_of_le_left hM₁, ?_⟩
  intro w t hw ht
  have hs3 : (3:ℝ) ≤ scale w := three_le_scale w
  have hs1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hs0 : (0:ℝ) ≤ scale w := (E_scale_pos w).le
  have ht9 : (9:ℝ) ≤ t := by
    have h : (scale w) ^ (((2:ℕ)):ℝ) ≤ t := ht
    rw [Real.rpow_natCast] at h
    nlinarith
  have ht0 : 0 < t := by linarith
  have ht1 : (1:ℝ) ≤ t := by linarith
  have hthr : Ethresh w t := by
    unfold Ethresh
    have h1 : (ModularGroup.S • w).im ≤ scale w := E_im_S_le_scale w
    have h3 : (scale w) ^ (((2:ℕ)):ℝ) ≤ t := ht
    rw [Real.rpow_natCast] at h3
    have h4 : 2 * scale w + 1 ≤ (scale w) ^ (2:ℕ) := by nlinarith
    linarith
  set z : ℍ := Work.Kernels.imagAxis t ht0 with hzdef
  have hz : (z : ℂ) = (t : ℂ) * Complex.I := rfl
  have hAp := hKp w z t hw hthr hz
  have hAm := hKm w z t hw hthr hz
  have hKaxis : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t = Work.Kernels.Kfun ℓ d w z := by
    rw [Work.Kernels.Kaxis, dif_pos ht0]
  have hAexp : Aexp (Gcusp ℓ d) w t
      = (Compact.Gplus d w z + Compact.Gminus d ℓ w z) / 2 := by
    rw [Gcusp_eq_Gcoef ℓ d hd, Aexp_Gcoef' ℓ d w t ht0]
    have h := Compact.gfun_eq ℓ d hd w z
    rw [h]
    ring
  have hsplit : Work.Kernels.Kfun ℓ d w z
        - (Compact.Gplus d w z + Compact.Gminus d ℓ w z) / 2
      = ((Work.Kernels.KPlus d w z - Compact.Gplus d w z)
          + (Work.Kernels.KMinus ℓ d w z - Compact.Gminus d ℓ w z)) / 2 := by
    rw [Work.Kernels.Kfun_eq]; ring
  rw [hKaxis, hAexp, hsplit, norm_div, show ‖(2:ℂ)‖ = 2 from by norm_num]
  refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
  have e1 : ‖Work.Kernels.KPlus d w z - Compact.Gplus d w z‖
      ≤ C₁ * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂) * Real.exp (-(Real.pi * t)) := by
    refine le_trans hAp ?_
    have hN' : (scale w) ^ N₁ ≤ (scale w) ^ (max N₁ N₂) := E_rpow_mono w (le_max_left _ _)
    have hM' : (1 + t) ^ M₁ ≤ (1 + t) ^ (max M₁ M₂) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    have h0 : (0:ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
    have hA : C₁ * (scale w) ^ N₁ * (1 + t) ^ M₁ * Real.exp (-(Real.pi * t))
        ≤ C₁ * (scale w) ^ (max N₁ N₂) * (1 + t) ^ M₁ * Real.exp (-(Real.pi * t)) := by
      gcongr
    have hB : C₁ * (scale w) ^ (max N₁ N₂) * (1 + t) ^ M₁ * Real.exp (-(Real.pi * t))
        ≤ C₁ * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂)
            * Real.exp (-(Real.pi * t)) := by
      gcongr
    linarith [hA, hB]
  have e2 : ‖Work.Kernels.KMinus ℓ d w z - Compact.Gminus d ℓ w z‖
      ≤ C₂ * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂) * Real.exp (-(Real.pi * t)) := by
    refine le_trans hAm ?_
    have hN' : (scale w) ^ N₂ ≤ (scale w) ^ (max N₁ N₂) := E_rpow_mono w (le_max_right _ _)
    have hM' : (1 + t) ^ M₂ ≤ (1 + t) ^ (max M₁ M₂) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
    have h0 : (0:ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
    have hA : C₂ * (scale w) ^ N₂ * (1 + t) ^ M₂ * Real.exp (-(Real.pi * t))
        ≤ C₂ * (scale w) ^ (max N₁ N₂) * (1 + t) ^ M₂ * Real.exp (-(Real.pi * t)) := by
      gcongr
    have hB : C₂ * (scale w) ^ (max N₁ N₂) * (1 + t) ^ M₂ * Real.exp (-(Real.pi * t))
        ≤ C₂ * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂)
            * Real.exp (-(Real.pi * t)) := by
      gcongr
    linarith [hA, hB]
  have hsum : (‖Work.Kernels.KPlus d w z - Compact.Gplus d w z‖
      + ‖Work.Kernels.KMinus ℓ d w z - Compact.Gminus d ℓ w z‖) / 2
      ≤ (C₁ + C₂) / 2 * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂)
          * Real.exp (-(Real.pi * t)) := by
    have h3 : (0:ℝ) ≤ (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂)
        * Real.exp (-(Real.pi * t)) := by positivity
    nlinarith [e1, e2, h3]
  refine le_trans hsum ?_
  have h4 : (1 + t) ^ (max M₁ M₂) ≤ 2 ^ (max M₁ M₂) * t ^ (max M₁ M₂) := by
    have h5 : (1 + t : ℝ) ≤ 2 * t := by linarith
    calc (1 + t) ^ (max M₁ M₂) ≤ (2 * t) ^ (max M₁ M₂) :=
          Real.rpow_le_rpow (by linarith) h5 (le_max_of_le_left hM₁)
      _ = 2 ^ (max M₁ M₂) * t ^ (max M₁ M₂) := Real.mul_rpow (by norm_num) ht0.le
  have h6 : (C₁ + C₂) / 2 * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂)
        * Real.exp (-(Real.pi * t))
      ≤ ((C₁ + C₂) / 2 * 2 ^ max M₁ M₂ + 1) * (scale w) ^ (max N₁ N₂) * t ^ (max M₁ M₂)
        * Real.exp (-(Real.pi * t)) := by
    have h7 : (0:ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
    have h8 : (0:ℝ) ≤ (scale w) ^ (max N₁ N₂) := E_rpow_nonneg w _
    have h9 : (0:ℝ) ≤ t ^ (max M₁ M₂) := Real.rpow_nonneg ht0.le _
    have h10 : (C₁ + C₂) / 2 * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂)
        ≤ ((C₁ + C₂) / 2 * 2 ^ max M₁ M₂) * (scale w) ^ (max N₁ N₂) * t ^ (max M₁ M₂) := by
      have h11 : (C₁ + C₂) / 2 * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂)
          ≤ (C₁ + C₂) / 2 * (scale w) ^ (max N₁ N₂)
              * (2 ^ (max M₁ M₂) * t ^ (max M₁ M₂)) := by
        gcongr
      calc (C₁ + C₂) / 2 * (scale w) ^ (max N₁ N₂) * (1 + t) ^ (max M₁ M₂)
          ≤ (C₁ + C₂) / 2 * (scale w) ^ (max N₁ N₂)
              * (2 ^ (max M₁ M₂) * t ^ (max M₁ M₂)) := h11
        _ = ((C₁ + C₂) / 2 * 2 ^ max M₁ M₂) * (scale w) ^ (max N₁ N₂) * t ^ (max M₁ M₂) := by ring
    have h12 : ((C₁ + C₂) / 2 * 2 ^ max M₁ M₂) * (scale w) ^ (max N₁ N₂) * t ^ (max M₁ M₂)
        ≤ ((C₁ + C₂) / 2 * 2 ^ max M₁ M₂ + 1) * (scale w) ^ (max N₁ N₂) * t ^ (max M₁ M₂) := by
      nlinarith [mul_nonneg h8 h9]
    exact le_trans (mul_le_mul_of_nonneg_right h10 h7) (mul_le_mul_of_nonneg_right h12 h7)
  exact h6

end Work.Asymptotics

end
