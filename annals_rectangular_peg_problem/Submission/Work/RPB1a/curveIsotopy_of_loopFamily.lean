import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Helpers
import Submission.Work.RPA3.contDiff_param_intervalIntegral
import Submission.Work.RPB.B1.area_pos_of_isotopy_infty

/-!
# N0 of the analytic route: normalisation of a loop family (area `π`, start at the unit circle)

`Work.RPB1a.curveIsotopy_of_loopFamily`: a jointly `C^∞` family `c` of `2π`-periodic embedded
immersed loops, whose time-`0` curve is the counterclockwise unit circle, is (up to a positive
homothety) the time-`1` curve of a `Work.RPV.CurveIsotopy`.

The construction is the normalisation tail of `Work.RPB.B1.polar_isotopy`: with
`A σ = ∫_0^{2π} ω_ℂ(c σ, ∂_t c σ)` the signed-area integral, `A ∘ smoothTransition` is smooth and
positive everywhere (positivity on `[0,1]` is `Work.RPB.B1.area_pos_of_isotopy_infty`), and
`lam τ = √(2π / A (smoothTransition τ))` is a globally smooth positive rescaling with `lam 0 = 1`
(the unit circle has area `2π`) and `lam τ² A (smoothTransition τ) = 2π`, so that
`CI.c τ t = lam τ · c (smoothTransition τ) t` has area `π` for every `τ`.
-/

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

theorem curveIsotopy_of_loopFamily (c : ℝ → ℝ → ℂ) (hc : IsLoopFamily c)
    (h0 : ∀ t : ℝ, c 0 t = Complex.exp (t * I)) :
    ∃ CI : Work.RPV.CurveIsotopy, ∃ lam : ℝ, 0 < lam ∧ ∀ t, CI.c 1 t = (lam : ℂ) * c 1 t := by
  obtain ⟨hcsm, hcper, hcinj, hcimm⟩ := hc
  let A : ℝ → ℝ := fun σ => ∫ t in (0:ℝ)..(2*Real.pi), Work.RPV.ωC (c σ t) (deriv (c σ) t)
  have hA_sm : ContDiff ℝ ∞ A := by
    have hω : ContDiff ℝ ∞ (fun p : ℂ × ℂ => Work.RPV.ωC p.1 p.2) := by
      simp only [Work.RPV.ωC]
      exact Complex.imCLM.contDiff.comp
        ((Complex.conjCLE.contDiff.comp contDiff_fst).mul contDiff_snd)
    have hp : ContDiff ℝ ∞
        (fun z : ℝ × ℝ => (c z.1 z.2, deriv (fun s => c z.1 s) z.2)) :=
      hcsm.prodMk (contDiff_partialDeriv c hcsm)
    have hg : ContDiff ℝ ∞
        (fun z : ℝ × ℝ => Work.RPV.ωC (c z.1 z.2) (deriv (c z.1) z.2)) := hω.comp hp
    have := Work.RPA3.contDiff_param_intervalIntegral (X := ℝ) (F := ℝ) (⊤ : ℕ∞)
      (fun σ t => Work.RPV.ωC (c σ t) (deriv (c σ) t)) hg 0 (2 * Real.pi)
    simpa only [A] using this
  have hA0 : A 0 = 2 * Real.pi := Work.RPB.B1.areaInt_zero c h0
  have hA_pos : ∀ τ, 0 < A (Real.smoothTransition τ) := by
    intro τ
    exact Work.RPB.B1.area_pos_of_isotopy_infty c hcsm hcper hcinj hcimm h0 _
      (Set.mem_Icc.mpr ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
  let lam : ℝ → ℝ := fun τ => Real.sqrt (2 * Real.pi / A (Real.smoothTransition τ))
  have hlam_pos : ∀ τ, 0 < lam τ := by
    intro τ
    simp only [lam]
    exact Real.sqrt_pos.mpr (div_pos (by linarith [Real.pi_pos]) (hA_pos τ))
  have hlam_sm : ContDiff ℝ ∞ lam := by
    simp only [lam]
    apply ContDiff.sqrt
    · exact contDiff_const.div (hA_sm.comp (Real.smoothTransition.contDiff (n := ⊤)))
        (fun τ => ne_of_gt (hA_pos τ))
    · intro τ; exact ne_of_gt (div_pos (by linarith [Real.pi_pos]) (hA_pos τ))
  refine ⟨{
    c := fun τ t => (lam τ : ℂ) * c (Real.smoothTransition τ) t
    smooth := ?_
    per := ?_
    inj := ?_
    imm := ?_
    start := ?_
    area := ?_ }, lam 1, hlam_pos 1, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((lam z.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hlam_sm.comp contDiff_fst)
    have h2 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c (Real.smoothTransition z.1) z.2) :=
      hcsm.comp (((Real.smoothTransition.contDiff (n := ⊤)).comp contDiff_fst).prodMk contDiff_snd)
    exact h1.mul h2
  · intro τ t
    rw [hcper (Real.smoothTransition τ) t]
  · intro τ hτ t t' h
    have hσ : Real.smoothTransition τ ∈ Set.Icc (0:ℝ) 1 :=
      Set.mem_Icc.mpr ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have hlam : (lam τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hlam_pos τ))
    have h2 : c (Real.smoothTransition τ) t = c (Real.smoothTransition τ) t' :=
      mul_left_cancel₀ hlam h
    exact hcinj (Real.smoothTransition τ) hσ t t' h2
  · intro τ hτ t
    have hσ : Real.smoothTransition τ ∈ Set.Icc (0:ℝ) 1 :=
      Set.mem_Icc.mpr ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have hdiff : DifferentiableAt ℝ (c (Real.smoothTransition τ)) t :=
      ((hcsm.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
    rw [deriv_const_mul _ hdiff]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hlam_pos τ))) (hcimm _ hσ t)
  · intro t
    show (lam 0 : ℂ) * c (Real.smoothTransition 0) t = Complex.exp (t * Complex.I)
    have hlam0 : lam 0 = 1 := by
      simp only [lam, Real.smoothTransition.zero, hA0]
      rw [show 2 * Real.pi / (2 * Real.pi) = 1 by field_simp]
      simp
    rw [hlam0, Real.smoothTransition.zero, h0 t]; simp
  · intro τ hτ
    have hσ : Real.smoothTransition τ ∈ Set.Icc (0:ℝ) 1 :=
      Set.mem_Icc.mpr ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have hdiff : ∀ t, DifferentiableAt ℝ (c (Real.smoothTransition τ)) t := fun t =>
      ((hcsm.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
    have hint : ∫ t in (0:ℝ)..(2*Real.pi),
        Work.RPV.ωC ((lam τ : ℂ) * c (Real.smoothTransition τ) t)
          (deriv (fun s => (lam τ : ℂ) * c (Real.smoothTransition τ) s) t)
        = (lam τ)^2 * A (Real.smoothTransition τ) := by
      have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) (2*Real.pi),
          Work.RPV.ωC ((lam τ : ℂ) * c (Real.smoothTransition τ) t)
            (deriv (fun s => (lam τ : ℂ) * c (Real.smoothTransition τ) s) t)
          = (lam τ)^2 * Work.RPV.ωC (c (Real.smoothTransition τ) t)
              (deriv (c (Real.smoothTransition τ)) t) := by
        intro t _
        rw [deriv_const_mul _ (hdiff t)]
        exact omegaC_real_smul (lam τ) _ _
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
    rw [hint]
    have hlam_sq : (lam τ)^2 = 2 * Real.pi / A (Real.smoothTransition τ) := by
      simp only [lam]
      exact Real.sq_sqrt (le_of_lt (div_pos (by linarith [Real.pi_pos]) (hA_pos τ)))
    rw [hlam_sq, div_mul_cancel₀ (2 * Real.pi) (ne_of_gt (hA_pos τ))]
    ring
  · intro t
    show (lam 1 : ℂ) * c (Real.smoothTransition 1) t = (lam 1 : ℂ) * c 1 t
    rw [Real.smoothTransition.one]

end Work.RPB1a
