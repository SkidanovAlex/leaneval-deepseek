import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Port.Drive.curve_deriv_ne_zero

/-!
# RPB1a: helpers copied out of `Work.RPB.B1.exists_curveIsotopy`

The analytic route to `B1` (`RECTPEG_B1_LEAD.md`, §7 "kept and reused") reuses four auxiliary
lemmas that live in `Submission/Work/RPB/B1/exists_curveIsotopy.lean`.  That file cannot be
imported (its closure contains the open `straighteningFamily_exists` hole), so they are
**copied verbatim** here, in namespace `Work.RPB1a`:

* `omegaC_real_smul` — `ω_ℂ` is quadratic under real scaling (the area normalisation),
* `omegaC_exp_I` — `ω_ℂ(e^{it}, i e^{it}) = 1` (the unit circle has area `π`),
* `contDiff_partialDeriv` — joint smoothness of the parameter derivative of a loop family,
* `curve_deriv_ne_zero_C` — the `t`-derivative of `t ↦ γ(e^{it})` never vanishes for a smooth
  embedding `γ : Circle → ℂ`.

The only external input is `Work.RPB.Port.Drive.circleExp_mfderiv_apply_one_ne_zero`.
-/

set_option autoImplicit false

namespace Work.RPB1a

open scoped Manifold ContDiff Real
open Manifold

noncomputable section

lemma omegaC_real_smul (m : ℝ) (u v : ℂ) :
    Work.RPV.ωC ((m:ℂ)*u) ((m:ℂ)*v) = m^2 * Work.RPV.ωC u v := by
  rw [Work.RPV.ωC, Work.RPV.ωC]
  rw [show (starRingEnd ℂ) ((m:ℂ)*u) = (m:ℂ) * (starRingEnd ℂ) u by rw [map_mul, Complex.conj_ofReal]]
  rw [show (↑m * (starRingEnd ℂ) u) * (↑m * v) = ((m*m:ℝ):ℂ) * ((starRingEnd ℂ) u * v) by
    rw [Complex.ofReal_mul]; ring]
  rw [show (((m*m:ℝ):ℂ) * ((starRingEnd ℂ) u * v)).im = (m*m) * ((starRingEnd ℂ) u * v).im by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring]
  ring

lemma omegaC_exp_I (t : ℝ) :
    Work.RPV.ωC (Complex.exp ((t:ℂ)*Complex.I)) (Complex.exp ((t:ℂ)*Complex.I) * Complex.I) = 1 := by
  rw [Work.RPV.ωC]
  have h : (starRingEnd ℂ) (Complex.exp (↑t * Complex.I)) * (Complex.exp (↑t * Complex.I) * Complex.I)
      = ((Complex.normSq (Complex.exp (↑t * Complex.I)) : ℝ) : ℂ) * Complex.I := by
    rw [← mul_assoc, mul_comm (starRingEnd ℂ (Complex.exp (↑t * Complex.I))) (Complex.exp (↑t * Complex.I)),
      Complex.mul_conj]
  rw [h, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  simp [Complex.mul_im]

theorem contDiff_partialDeriv (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ×ℝ => c z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ×ℝ => deriv (fun s => c z.1 s) z.2) := by
  have h1 : ContDiff ℝ ∞ (fun q : (ℝ×ℝ)×ℝ => c q.1.1 q.2) := by
    have hmap : ContDiff ℝ ∞ (fun q : (ℝ×ℝ)×ℝ => (q.1.1, q.2)) := by fun_prop
    exact hc.comp hmap
  have hf : ContDiff ℝ ∞ (Function.uncurry (fun (p : ℝ×ℝ) (s:ℝ) => c p.1 s)) := h1
  have h := hf.fderiv_apply (𝕜 := ℝ) (n := ∞) (m := ∞)
    (g := fun p : ℝ×ℝ => p.2) (k := fun _ : ℝ×ℝ => (1:ℝ))
    contDiff_snd contDiff_const (by simp)
  simpa [fderiv_apply_one_eq_deriv] using h

theorem curve_deriv_ne_zero_C (γ : Circle → ℂ)
    (hγ : Manifold.IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℂ)) ∞ γ) (t : ℝ) :
    deriv (fun u => γ (Circle.exp u)) t ≠ 0 := by
  have hinj : Function.Injective (mfderiv (𝓡 1) (𝓘(ℝ, ℂ)) γ (Circle.exp t)) :=
    Manifold.IsImmersion.mfderiv_injective hγ.isImmersion (by decide) (Circle.exp t)
  have hexp : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 1) (Circle.exp : ℝ → Circle) t :=
    (contMDiff_circleExp (m := ω)).contMDiffAt.mdifferentiableAt (by decide)
  have hγd : MDifferentiableAt (𝓡 1) (𝓘(ℝ, ℂ)) γ (Circle.exp t) :=
    (hγ.contMDiff (Circle.exp t)).mdifferentiableAt (by decide)
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 1) (I'' := 𝓘(ℝ, ℂ)) t hγd hexp
  have hM : (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (Circle.exp : ℝ → Circle) t) 1 ≠ 0 :=
    Work.RPB.Port.Drive.circleExp_mfderiv_apply_one_ne_zero t
  have hval : (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (fun u => γ (Circle.exp u)) t) 1 ≠ 0 := by
    rw [show (fun u => γ (Circle.exp u)) = γ ∘ (Circle.exp : ℝ → Circle) from rfl, hchain]
    simp only [ContinuousLinearMap.comp_apply]
    intro hA
    exact hM (hinj (by simp [hA]))
  have hderiv : deriv (fun u => γ (Circle.exp u)) t
      = (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (fun u => γ (Circle.exp u)) t) 1 := by
    rw [mfderiv_eq_fderiv]; rfl
  rw [hderiv]; exact hval

end

end Work.RPB1a
