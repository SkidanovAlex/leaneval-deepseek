import Submission.FUP.DbarBump

open MeasureTheory
open scoped BigOperators ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# Product rules and commutation for the Wirtinger derivatives

This module collects the elementary calculus facts about `partialZ`/`partialZbar` needed for the
Kohn--Morrey (Bochner--Kodaira--Nakano) estimate of the `∂̄`-theory.
-/

namespace Submission.FUP

section Product

/-- The Leibniz rule for `∂_j`. -/
lemma partialZ_mul {f g : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (j : Fin d) :
    partialZ j (fun w => f w * g w) z = f z * partialZ j g z + g z * partialZ j f z := by
  have h : fderiv ℝ (fun w => f w * g w) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fderiv_mul hf hg
  simp only [partialZ, h, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- The Leibniz rule for `∂̄_j`. -/
lemma partialZbar_mul {f g : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (j : Fin d) :
    partialZbar j (fun w => f w * g w) z = f z * partialZbar j g z + g z * partialZbar j f z := by
  have h : fderiv ℝ (fun w => f w * g w) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fderiv_mul hf hg
  simp only [partialZbar, h, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- Additivity of `∂_j` in its argument. -/
lemma partialZ_sub (j : Fin d) {f g : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    partialZ j (fun z => f z - g z) z = partialZ j f z - partialZ j g z := by
  have h : fderiv ℝ (fun z => f z - g z) z = fderiv ℝ f z - fderiv ℝ g z := fderiv_sub hf hg
  simp only [partialZ, h, ContinuousLinearMap.sub_apply]
  ring

/-- Additivity of `∂̄_j` in its argument. -/
lemma partialZbar_sub (j : Fin d) {f g : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    partialZbar j (fun z => f z - g z) z = partialZbar j f z - partialZbar j g z := by
  have h : fderiv ℝ (fun z => f z - g z) z = fderiv ℝ f z - fderiv ℝ g z := fderiv_sub hf hg
  simp only [partialZbar, h, ContinuousLinearMap.sub_apply]
  ring

/-- `∂̄` of a `C³` function is `C¹`. -/
lemma contDiff_partialZ_one {f : ℂᵈ → ℂ} (hf : ContDiff ℝ 2 f) (j : Fin d) :
    ContDiff ℝ 1 (fun z => partialZ j f z) := by
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h1 : ContDiff ℝ 1 (fun z => fderiv ℝ f z (Pi.single j (1 : ℂ))) :=
    hf'.clm_apply contDiff_const
  have h2 : ContDiff ℝ 1 (fun z => fderiv ℝ f z (Pi.single j Complex.I)) :=
    hf'.clm_apply contDiff_const
  have h3 : ContDiff ℝ 1 (fun z => (fderiv ℝ f z (Pi.single j (1 : ℂ))
      - Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2) :=
    (h1.sub (contDiff_const.mul h2)).div_const 2
  convert h3 using 1
  funext z
  rw [partialZ]

/-- `∂̄` of a `C²` function is `C¹`. -/
lemma contDiff_partialZbar_one {f : ℂᵈ → ℂ} (hf : ContDiff ℝ 2 f) (j : Fin d) :
    ContDiff ℝ 1 (fun z => partialZbar j f z) := by
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h1 : ContDiff ℝ 1 (fun z => fderiv ℝ f z (Pi.single j (1 : ℂ))) :=
    hf'.clm_apply contDiff_const
  have h2 : ContDiff ℝ 1 (fun z => fderiv ℝ f z (Pi.single j Complex.I)) :=
    hf'.clm_apply contDiff_const
  have h3 : ContDiff ℝ 1 (fun z => (fderiv ℝ f z (Pi.single j (1 : ℂ))
      + Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2) :=
    (h1.add (contDiff_const.mul h2)).div_const 2
  convert h3 using 1
  funext z
  rw [partialZbar]

/-- `∂_j` of a compactly supported function has compact support. -/
lemma hasCompactSupport_partialZ {f : ℂᵈ → ℂ} (hs : HasCompactSupport f) (j : Fin d) :
    HasCompactSupport (fun z => partialZ j f z) := by
  apply hs.mono'
  intro z hz
  by_contra hzf
  have h0 : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport ℝ hzf
  exact hz (by simp only [partialZ, h0, ContinuousLinearMap.zero_apply, mul_zero, sub_zero,
    zero_div])

/-- `∂̄_j` of a compactly supported function has compact support. -/
lemma hasCompactSupport_partialZbar {f : ℂᵈ → ℂ} (hs : HasCompactSupport f) (j : Fin d) :
    HasCompactSupport (fun z => partialZbar j f z) := by
  apply hs.mono'
  intro z hz
  by_contra hzf
  have h0 : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport ℝ hzf
  exact hz (by simp only [partialZbar, h0, ContinuousLinearMap.zero_apply, mul_zero, add_zero,
    zero_div])

end Product

section Mixed

/-- The derivative of `∂_j h` in the direction `u`, in terms of the mixed second derivatives. -/
lemma fderiv_partialZ_apply {h : ℂᵈ → ℂ} (hh : ContDiff ℝ 2 h) (j : Fin d) (z u : ℂᵈ) :
    fderiv ℝ (fun w => partialZ j h w) z u
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z u
          - Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z u) := by
  have hfd : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have happ : ∀ a : ℂᵈ, DifferentiableAt ℝ (fun w : ℂᵈ => fderiv ℝ h w a) z := by
    intro a
    have h := ((ContinuousLinearMap.apply ℝ ℂ a).differentiableAt).comp z hfd.differentiableAt
    simpa [Function.comp_def] using h
  have hG : DifferentiableAt ℝ (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ))
      - Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) z :=
    (happ (Pi.single j (1:ℂ))).sub ((happ (Pi.single j Complex.I)).const_mul Complex.I)
  have h1 : (fun w : ℂᵈ => partialZ j h w)
      = fun w : ℂᵈ => (1/2 : ℂ) * (fderiv ℝ h w (Pi.single j (1:ℂ))
          - Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) := by
    funext w; rw [partialZ]; ring
  have hsplit : fderiv ℝ (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ))
        - Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) z
      = fderiv ℝ (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ))) z
        - fderiv ℝ (fun w : ℂᵈ => Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) z := by
    rw [show (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ))
          - Complex.I * fderiv ℝ h w (Pi.single j Complex.I))
        = (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ)))
          - (fun w : ℂᵈ => Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) from by
            funext w; rfl]
    exact fderiv_sub (happ _) ((happ _).const_mul Complex.I)
  rw [h1, fderiv_const_mul hG (1/2 : ℂ), hsplit,
    fderiv_const_mul (happ (Pi.single j Complex.I)) Complex.I]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The mixed Wirtinger derivatives commute for a `C²` function: `∂_k ∂̄_j h = ∂̄_j ∂_k h`. -/
lemma partialZ_partialZbar_comm {h : ℂᵈ → ℂ} (hh : ContDiff ℝ 2 h) (j k : Fin d) (z : ℂᵈ) :
    partialZ k (fun w => partialZbar j h w) z
      = partialZbar j (fun w => partialZ k h w) z := by
  have hZ := fderiv_partialZ_apply hh k z
  have hZb := fderiv_partialZbar_apply hh j z
  have hZ1 : fderiv ℝ (fun w => partialZ k h w) z (Pi.single j (1:ℂ))
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j 1)
          - Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z
              (Pi.single j 1)) := hZ _
  have hZ2 : fderiv ℝ (fun w => partialZ k h w) z (Pi.single j Complex.I)
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j Complex.I)
          - Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z
              (Pi.single j Complex.I)) := hZ _
  have hZb1 : fderiv ℝ (fun w => partialZbar j h w) z (Pi.single k (1:ℂ))
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k 1)
          + Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z
              (Pi.single k 1)) := hZb _
  have hZb2 : fderiv ℝ (fun w => partialZbar j h w) z (Pi.single k Complex.I)
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k Complex.I)
          + Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z
              (Pi.single k Complex.I)) := hZb _
  rw [partialZ, partialZbar, hZ1, hZ2, hZb1, hZb2]
  have e1 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j 1)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k 1) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e2 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z (Pi.single j 1)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k Complex.I) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e3 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j Complex.I)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z (Pi.single k 1) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e4 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z (Pi.single j Complex.I)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z (Pi.single k Complex.I) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  rw [e1, e2, e3, e4]
  ring

end Mixed

end Submission.FUP
