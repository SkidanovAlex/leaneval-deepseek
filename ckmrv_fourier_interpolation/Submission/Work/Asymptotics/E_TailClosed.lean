import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.exists_bound_iteratedDeriv_tailIntegral_two_regime
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.ae_bound_of_two_regime
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.paperLayer_seminorm
import Submission.Work.Asymptotics.psi1_contDiff_omega
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer
import Submission.Work.Asymptotics.iteratedDeriv_comp_quad_bounded
import Submission.Work.Asymptotics.abs_pow_mul_exp_le
import Submission.Work.Asymptotics.paperLayer_agreement

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open Work.Kernels
open scoped Topology ContDiff

namespace Work.Asymptotics
/-! ## The closed form of the tail `∫_{Ici B} Aexp · e^{-πr²t}` -/

/-- The `λ`-function whose composition with `r ↦ π r²` is the closed form of
`sinSq r · ∫_{Ici B} Aexp G w t · e^{-πr²t} dt`. -/
def tcLambda (G : Fin 2 → Fin 2 → ℍ → ℂ) (B : ℝ) (w : ℍ) (x : ℝ) : ℂ :=
  (x : ℂ) * psiC x * Complex.exp (-((x : ℂ) * (B : ℂ))) * G 0 0 w +
    Complex.I * psiC x * ((x : ℂ) * (B : ℂ) + 1) * Complex.exp (-((x : ℂ) * (B : ℂ))) * G 0 1 w +
    ((x - 2 * Real.pi : ℝ) : ℂ) * psiC (x - 2 * Real.pi)
        * Complex.exp (-(((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ))) * G 1 0 w +
    Complex.I * psiC (x - 2 * Real.pi) * (((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ) + 1)
        * Complex.exp (-(((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ))) * G 1 1 w

/-- The closed form of `sinSq r · ∫_{Ici B} Aexp G w t · e^{-πr²t} dt`, as a function of `r`. -/
def E_TailClosed (G : Fin 2 → Fin 2 → ℍ → ℂ) (B : ℝ) (w : ℍ) (r : ℝ) : ℂ :=
  tcLambda G B w (Real.pi * r ^ 2)

lemma contDiff_psiC' : ContDiff ℝ ω psiC := psi1_contDiff_omega

lemma contDiff_exp_negB (B : ℝ) :
    ContDiff ℝ ω (fun x : ℝ => Complex.exp (-((x : ℂ) * (B : ℂ)))) := by
  refine (Complex.contDiff_exp (𝕜 := ℝ)).comp ?_
  exact ((Complex.ofRealCLM.contDiff.mul contDiff_const)).neg

lemma contDiff_tcLambda (G : Fin 2 → Fin 2 → ℍ → ℂ) (B : ℝ) (w : ℍ) :
    ContDiff ℝ ω (tcLambda G B w) := by
  have hpsi : ContDiff ℝ ω psiC := contDiff_psiC'
  have hid : ContDiff ℝ ω (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hes := contDiff_exp_negB B
  have hsub : ContDiff ℝ ω (fun x : ℝ => x - 2 * Real.pi) := contDiff_id.sub contDiff_const
  have hsubc : ContDiff ℝ ω (fun x : ℝ => ((x - 2 * Real.pi : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsub
  have hexps : ContDiff ℝ ω
      (fun x : ℝ => Complex.exp (-(((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ)))) := by
    refine (Complex.contDiff_exp (𝕜 := ℝ)).comp ?_
    exact ((hsubc.mul contDiff_const)).neg
  have hpss : ContDiff ℝ ω (fun x : ℝ => psiC (x - 2 * Real.pi)) := hpsi.comp hsub
  unfold tcLambda
  have t1 : ContDiff ℝ ω (fun x : ℝ =>
      (x : ℂ) * psiC x * Complex.exp (-((x : ℂ) * (B : ℂ))) * G 0 0 w) :=
    (((hid.mul hpsi).mul hes).mul contDiff_const)
  have t2 : ContDiff ℝ ω (fun x : ℝ =>
      Complex.I * psiC x * ((x : ℂ) * (B : ℂ) + 1) * Complex.exp (-((x : ℂ) * (B : ℂ))) * G 0 1 w) :=
    (((contDiff_const.mul hpsi).mul ((hid.mul contDiff_const).add contDiff_const)).mul hes).mul contDiff_const
  have t3 : ContDiff ℝ ω (fun x : ℝ =>
      ((x - 2 * Real.pi : ℝ) : ℂ) * psiC (x - 2 * Real.pi)
        * Complex.exp (-(((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ))) * G 1 0 w) :=
    (((hsubc.mul hpss).mul hexps).mul contDiff_const)
  have t4 : ContDiff ℝ ω (fun x : ℝ =>
      Complex.I * psiC (x - 2 * Real.pi) * (((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ) + 1)
        * Complex.exp (-(((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ))) * G 1 1 w) :=
    (((contDiff_const.mul hpss).mul ((hsubc.mul contDiff_const).add contDiff_const)).mul hexps).mul contDiff_const
  exact ((t1.add t2).add t3).add t4

lemma contDiff_E_TailClosed (G : Fin 2 → Fin 2 → ℍ → ℂ) (B : ℝ) (w : ℍ) :
    ContDiff ℝ ω (E_TailClosed G B w) := by
  unfold E_TailClosed
  exact (contDiff_tcLambda G B w).comp (by fun_prop)

lemma E_TailClosed_neg (G : Fin 2 → Fin 2 → ℍ → ℂ) (B : ℝ) (w : ℍ) (r : ℝ) :
    E_TailClosed G B w (-r) = E_TailClosed G B w r := by
  unfold E_TailClosed
  rw [show Real.pi * (-r) ^ 2 = Real.pi * r ^ 2 from by ring]

lemma differentiable_E_TailClosed (G : Fin 2 → Fin 2 → ℍ → ℂ) (B : ℝ) (w : ℍ) :
    Differentiable ℝ (E_TailClosed G B w) :=
  (contDiff_E_TailClosed G B w).differentiable (by simp)


/-! ## Shape bounds for the tail closed form -/

lemma E_norm_iteratedDeriv_mul_le (f g : ℝ → ℂ) {m : ℕ} (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g)
    (x : ℝ) :
    ‖iteratedDeriv m (fun y : ℝ => f y * g y) x‖ ≤
      ∑ p ∈ Finset.range (m + 1),
        (m.choose p : ℝ) * ‖iteratedDeriv p f x‖ * ‖iteratedDeriv (m - p) g x‖ := by
  have h := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g) hf hg x
    (hn := le_top (a := (m : ℕ∞ω)))
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  exact h

lemma E_iteratedDeriv_exp_shift (B x₀ : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ))))
      = fun x : ℝ => (-(B : ℂ)) ^ k * Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ))) := by
  induction k with
  | zero => funext x; rw [iteratedDeriv_zero]; simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hd : HasDerivAt (fun x : ℝ => Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ))))
          (-(B : ℂ) * Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))) x := by
        have h1 : HasDerivAt (fun x : ℝ => (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))) (-(B : ℂ)) x := by
          have h2 : HasDerivAt (fun x : ℝ => ((x - x₀ : ℝ) : ℂ) * (B : ℂ)) (B : ℂ) x := by
            have h := (HasDerivAt.ofReal_comp ((hasDerivAt_id x).sub_const x₀)).mul_const (B : ℂ)
            simpa using h
          exact h2.neg
        have hc2 := (Complex.hasDerivAt_exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))).comp x h1
        simpa [Function.comp_def, mul_comm] using hc2
      have hd2 := hd.const_mul ((-(B : ℂ)) ^ k)
      rw [hd2.deriv]
      ring

lemma E_norm_iteratedDeriv_exp_shift (B x₀ : ℝ) (hB0 : 0 ≤ B) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (fun x : ℝ => Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))) x‖
      = B ^ k * Real.exp (-((x - x₀) * B)) := by
  rw [E_iteratedDeriv_exp_shift B x₀ k]
  simp only []
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have h1 : ‖(-(B : ℂ))‖ = B := by
    rw [norm_neg, norm_ofReal_eq_abs, abs_of_nonneg hB0]
  rw [h1]
  have h2 : (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ))).re = -((x - x₀) * B) := by
    simp
  rw [h2]

lemma E_shape_bound (f : ℝ → ℂ) (hfc : ContDiff ℝ ω f)
    (hf : ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, ‖iteratedDeriv m f x‖ ≤ c * (1 + |x|))
    (B x₀ : ℝ) (hB1 : 1 ≤ B) (hB0 : 0 ≤ B) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => f x * Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))) x‖
        ≤ C * (1 + |x|) * Real.exp (-(x - x₀)) := by
  intro m
  choose c hc using hf
  have hgc : ContDiff ℝ ω (fun x : ℝ => Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))) := by
    refine (Complex.contDiff_exp (𝕜 := ℝ)).comp ?_
    exact (((Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)).mul contDiff_const)).neg
  refine ⟨∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) * c p * B ^ (m - p), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun p _ => mul_nonneg (mul_nonneg (by positivity) (hc p).1)
      (pow_nonneg hB0 _))
  · intro x hx
    have hxx0 : 0 ≤ x - x₀ := by linarith
    have hexp_le : Real.exp (-((x - x₀) * B)) ≤ Real.exp (-(x - x₀)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hxx0, hB1]
    have hleib := E_norm_iteratedDeriv_mul_le (m := m) f
      (fun x : ℝ => Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))) hfc hgc x
    refine le_trans hleib ?_
    have hterm : ∀ p ∈ Finset.range (m + 1),
        (m.choose p : ℝ) * ‖iteratedDeriv p f x‖
            * ‖iteratedDeriv (m - p) (fun x : ℝ => Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))) x‖
          ≤ (m.choose p : ℝ) * c p * B ^ (m - p) * ((1 + |x|) * Real.exp (-(x - x₀))) := by
      intro p hp
      rw [E_norm_iteratedDeriv_exp_shift B x₀ hB0 (m - p) x]
      have hcf := (hc p).2 x
      have hBp : (0 : ℝ) ≤ B ^ (m - p) := pow_nonneg hB0 _
      have h2 : Real.exp (-((x - x₀) * B)) ≤ Real.exp (-(x - x₀)) := hexp_le
      have hstep1 : (m.choose p : ℝ) * ‖iteratedDeriv p f x‖
            * (B ^ (m - p) * Real.exp (-((x - x₀) * B)))
          ≤ (m.choose p : ℝ) * (c p * (1 + |x|)) * (B ^ (m - p) * Real.exp (-((x - x₀) * B))) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg hB0 _) (Real.exp_nonneg _))
        exact mul_le_mul_of_nonneg_left hcf (Nat.cast_nonneg _)
      have hstep2 : (m.choose p : ℝ) * (c p * (1 + |x|)) * (B ^ (m - p) * Real.exp (-((x - x₀) * B)))
          ≤ (m.choose p : ℝ) * (c p * (1 + |x|)) * (B ^ (m - p) * Real.exp (-(x - x₀))) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (hc p).1 (by positivity)))
        exact mul_le_mul_of_nonneg_left h2 hBp
      refine le_trans hstep1 (le_trans hstep2 (le_of_eq ?_))
      ring
    calc ∑ p ∈ Finset.range (m + 1),
          (m.choose p : ℝ) * ‖iteratedDeriv p f x‖
            * ‖iteratedDeriv (m - p) (fun x : ℝ => Complex.exp (-(((x - x₀ : ℝ) : ℂ) * (B : ℂ)))) x‖
        ≤ ∑ p ∈ Finset.range (m + 1),
            (m.choose p : ℝ) * c p * B ^ (m - p) * ((1 + |x|) * Real.exp (-(x - x₀))) :=
          Finset.sum_le_sum hterm
      _ = (∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) * c p * B ^ (m - p))
            * ((1 + |x|) * Real.exp (-(x - x₀))) := by
          rw [Finset.sum_mul]
      _ = (∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) * c p * B ^ (m - p))
            * (1 + |x|) * Real.exp (-(x - x₀)) := by ring



lemma E_deriv_ofReal : deriv (fun x : ℝ => (x : ℂ)) = fun _ : ℝ => (1 : ℂ) := by
  funext x
  exact (HasDerivAt.ofReal_comp (hasDerivAt_id x)).deriv

lemma E_iteratedDeriv_ofReal_eq (p : ℕ) :
    iteratedDeriv p (fun x : ℝ => (x : ℂ)) =
      (if p = 0 then (fun x : ℝ => (x : ℂ))
        else if p = 1 then (fun _ : ℝ => (1 : ℂ)) else (fun _ : ℝ => (0 : ℂ))) := by
  induction p with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      rcases k with _ | k
      · have h : (if (0 : ℕ) = 0 then (fun x : ℝ => (x : ℂ))
            else if (0 : ℕ) = 1 then (fun _ : ℝ => (1 : ℂ)) else (fun _ : ℝ => (0 : ℂ)))
            = (fun x : ℝ => (x : ℂ)) := by simp
        rw [h, E_deriv_ofReal]
        simp
      · rcases k with _ | k
        · have h : (if (0 + 1 : ℕ) = 0 then (fun x : ℝ => (x : ℂ))
              else if (0 + 1 : ℕ) = 1 then (fun _ : ℝ => (1 : ℂ)) else (fun _ : ℝ => (0 : ℂ)))
              = (fun _ : ℝ => (1 : ℂ)) := by simp
          rw [h, deriv_const']
          simp
        · have hk : ¬ (k + 1 + 1 = 0) ∧ ¬ (k + 1 + 1 = 1) := by omega
          have h : (if (k + 1 + 1 : ℕ) = 0 then (fun x : ℝ => (x : ℂ))
              else if (k + 1 + 1 : ℕ) = 1 then (fun _ : ℝ => (1 : ℂ)) else (fun _ : ℝ => (0 : ℂ)))
              = (fun _ : ℝ => (0 : ℂ)) := by simp [hk.1, hk.2]
          rw [h, deriv_const']
          simp only [show (k + 1 + 1 + 1 : ℕ) ≠ 0 by omega,
            show (k + 1 + 1 + 1 : ℕ) ≠ 1 by omega, if_false]

lemma E_iteratedDeriv_ofReal_bound (p : ℕ) (x : ℝ) :
    ‖iteratedDeriv p (fun x : ℝ => (x : ℂ)) x‖ ≤ 1 + |x| := by
  rw [E_iteratedDeriv_ofReal_eq p]
  rcases eq_or_ne p 0 with h | h
  · subst h; simp only [if_true]
    rw [norm_ofReal_eq_abs]; linarith [abs_nonneg x]
  · rw [if_neg h]
    rcases eq_or_ne p 1 with h1 | h1
    · subst h1; simp only [if_true]; norm_num
    · rw [if_neg h1]; simp only [Pi.zero_apply, norm_zero]; positivity

lemma E_iteratedDeriv_affine_eq (B : ℝ) (p : ℕ) :
    iteratedDeriv p (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1) =
      (if p = 0 then (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1)
        else if p = 1 then (fun _ : ℝ => (B : ℂ)) else (fun _ : ℝ => (0 : ℂ))) := by
  induction p with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      rcases k with _ | k
      · have h : (if (0 : ℕ) = 0 then (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1)
            else if (0 : ℕ) = 1 then (fun _ : ℝ => (B : ℂ)) else (fun _ : ℝ => (0 : ℂ)))
            = (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1) := by simp
        rw [h]
        funext x
        have hd : HasDerivAt (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1) (B : ℂ) x := by
          have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * (B : ℂ)) ((1:ℂ) * (B:ℂ)) x :=
            (HasDerivAt.ofReal_comp (hasDerivAt_id x)).mul_const (B : ℂ)
          have h2 := h1.add_const (1:ℂ)
          simpa using h2
        rw [hd.deriv]
        simp
      · rcases k with _ | k
        · have h : (if (0 + 1 : ℕ) = 0 then (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1)
              else if (0 + 1 : ℕ) = 1 then (fun _ : ℝ => (B : ℂ)) else (fun _ : ℝ => (0 : ℂ)))
              = (fun _ : ℝ => (B : ℂ)) := by simp
          rw [h, deriv_const']
          simp
        · have hk : ¬ (k + 1 + 1 = 0) ∧ ¬ (k + 1 + 1 = 1) := by omega
          have h : (if (k + 1 + 1 : ℕ) = 0 then (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1)
              else if (k + 1 + 1 : ℕ) = 1 then (fun _ : ℝ => (B : ℂ)) else (fun _ : ℝ => (0 : ℂ)))
              = (fun _ : ℝ => (0 : ℂ)) := by simp [hk.1, hk.2]
          rw [h, deriv_const']
          simp only [show (k + 1 + 1 + 1 : ℕ) ≠ 0 by omega,
            show (k + 1 + 1 + 1 : ℕ) ≠ 1 by omega, if_false]

lemma E_iteratedDeriv_affine_bound (B : ℝ) (hB0 : 0 ≤ B) (p : ℕ) (x : ℝ) :
    ‖iteratedDeriv p (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1) x‖ ≤ (B + 1) * (1 + |x|) := by
  rw [E_iteratedDeriv_affine_eq B p]
  rcases eq_or_ne p 0 with h | h
  · subst h; simp only [if_true]
    calc ‖(x : ℂ) * (B : ℂ) + 1‖ ≤ ‖(x : ℂ) * (B : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = |x| * B + 1 := by
            rw [norm_mul, norm_ofReal_eq_abs, norm_ofReal_eq_abs, abs_of_nonneg hB0, norm_one]
      _ ≤ (B + 1) * (1 + |x|) := by nlinarith [abs_nonneg x, hB0]
  · rw [if_neg h]
    rcases eq_or_ne p 1 with h1 | h1
    · subst h1; simp only [if_true]
      rw [norm_ofReal_eq_abs, abs_of_nonneg hB0]
      nlinarith [abs_nonneg x, hB0]
    · rw [if_neg h1]; simp; positivity

lemma E_iteratedDeriv_comp_sub (g : ℝ → ℂ) (hg : ContDiff ℝ ω g) (c : ℝ) (m : ℕ) :
    iteratedDeriv m (fun x : ℝ => g (x - c)) = fun x : ℝ => iteratedDeriv m g (x - c) := by
  induction m with
  | zero => funext x; rw [iteratedDeriv_zero, iteratedDeriv_zero]
  | succ k ih =>
      funext x
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      have hgdv : HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k+1) g (x - c)) (x - c) := by
        rw [iteratedDeriv_succ]
        exact (hg.differentiable_iteratedDeriv k (by simp) (x - c)).hasDerivAt
      have hp : HasDerivAt (fun y : ℝ => y - c) (1 : ℝ) x := by
        simpa using (hasDerivAt_id x).sub_const c
      have h₂ : HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k+1) g (x - c)) ((fun y : ℝ => y - c) x) :=
        hgdv
      have hcomp := h₂.scomp x hp
      have hderiv : deriv (fun y : ℝ => iteratedDeriv k g (y - c)) x = iteratedDeriv (k+1) g (x - c) := by
        simpa [Function.comp_def] using hcomp.deriv
      rw [hderiv, iteratedDeriv_succ]

def tcF1 : ℝ → ℂ := fun x => (x : ℂ) * psiC x

def tcF2 (B : ℝ) : ℝ → ℂ := fun x => Complex.I * psiC x * (((x : ℂ) * (B : ℂ)) + 1)

def tcF3 : ℝ → ℂ := fun x => ((x - 2 * Real.pi : ℝ) : ℂ) * psiC (x - 2 * Real.pi)

def tcF4 (B : ℝ) : ℝ → ℂ :=
  fun x => Complex.I * psiC (x - 2 * Real.pi) * ((((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ)) + 1)

lemma contDiff_tcF1 : ContDiff ℝ ω tcF1 := by
  unfold tcF1
  exact (Complex.ofRealCLM.contDiff.mul contDiff_psiC')

lemma contDiff_tcF2 (B : ℝ) : ContDiff ℝ ω (tcF2 B) := by
  unfold tcF2
  exact ((contDiff_const.mul contDiff_psiC').mul
    ((Complex.ofRealCLM.contDiff.mul contDiff_const).add contDiff_const))

lemma contDiff_tcF3 : ContDiff ℝ ω tcF3 := by
  unfold tcF3
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (contDiff_psiC'.comp (contDiff_id.sub contDiff_const)))

lemma contDiff_tcF4 (B : ℝ) : ContDiff ℝ ω (tcF4 B) := by
  unfold tcF4
  exact ((contDiff_const.mul (contDiff_psiC'.comp (contDiff_id.sub contDiff_const))).mul
    ((Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)).mul contDiff_const |>.add
      contDiff_const))

lemma E_sum_choose (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
  have hh := add_pow (1 : ℝ) 1 m
  rw [one_add_one_eq_two] at hh
  rw [hh]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [one_pow, one_pow, mul_one, one_mul]

lemma E_tcF1_bound (m : ℕ) (x : ℝ) :
    ‖iteratedDeriv m tcF1 x‖ ≤ 2 ^ (m + 1) * (1 + |x|) := by
  have hleib := E_norm_iteratedDeriv_mul_le (m := m) (fun x : ℝ => (x : ℂ)) psiC
    Complex.ofRealCLM.contDiff contDiff_psiC' x
  have hfun : tcF1 = (fun x : ℝ => (x : ℂ)) * psiC := by
    funext y; unfold tcF1; rw [Pi.mul_apply]
  rw [hfun]
  refine le_trans hleib ?_
  calc ∑ p ∈ Finset.range (m + 1),
        (m.choose p : ℝ) * ‖iteratedDeriv p (fun x : ℝ => (x : ℂ)) x‖
          * ‖iteratedDeriv (m - p) psiC x‖
      ≤ ∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) * (1 + |x|) * 2 := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        refine mul_le_mul (mul_le_mul_of_nonneg_left (E_iteratedDeriv_ofReal_bound p x)
          (by positivity)) (psi1_iteratedDeriv_bound (m - p) x) (by positivity) ?_
        positivity
    _ = 2 ^ (m + 1) * (1 + |x|) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, E_sum_choose, pow_succ]; ring

lemma E_tcF2_bound (B : ℝ) (hB0 : 0 ≤ B) (m : ℕ) (x : ℝ) :
    ‖iteratedDeriv m (tcF2 B) x‖ ≤ 2 ^ (m + 1) * (B + 1) * (1 + |x|) := by
  have hleib := E_norm_iteratedDeriv_mul_le (m := m) (fun x : ℝ => Complex.I * psiC x)
    (fun x : ℝ => (x : ℂ) * (B : ℂ) + 1) (contDiff_const.mul contDiff_psiC')
    ((Complex.ofRealCLM.contDiff.mul contDiff_const).add contDiff_const) x
  have hfun : tcF2 B = (fun x : ℝ => Complex.I * psiC x) * (fun x : ℝ => (x:ℂ)*(B:ℂ)+1) := by
    funext y; unfold tcF2; rw [Pi.mul_apply]
  rw [hfun]
  refine le_trans hleib ?_
  have hps : ∀ p : ℕ, ‖iteratedDeriv p (fun x : ℝ => Complex.I * psiC x) x‖ ≤ 2 := by
    intro p
    rw [iteratedDeriv_const_mul_field (n := p) Complex.I psiC]
    rw [norm_mul]
    have hI : ‖Complex.I‖ = 1 := by simp
    rw [hI, one_mul]
    exact psi1_iteratedDeriv_bound p x
  calc ∑ p ∈ Finset.range (m + 1),
        (m.choose p : ℝ) * ‖iteratedDeriv p (fun x : ℝ => Complex.I * psiC x) x‖
          * ‖iteratedDeriv (m - p) (fun x : ℝ => (x:ℂ)*(B:ℂ)+1) x‖
      ≤ ∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) * 2 * ((B + 1) * (1 + |x|)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hps p) (by positivity))
          (E_iteratedDeriv_affine_bound B hB0 (m - p) x) (by positivity) ?_
        positivity
    _ = 2 ^ (m + 1) * (B + 1) * (1 + |x|) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, E_sum_choose, pow_succ]; ring

lemma E_abs_sub_const_le (x : ℝ) :
    1 + |x - 2 * Real.pi| ≤ (1 + 2 * Real.pi) * (1 + |x|) := by
  have h1 : |x - 2 * Real.pi| ≤ |x| + |2 * Real.pi| := by
    rw [sub_eq_add_neg]
    refine le_trans (abs_add_le x (-(2 * Real.pi))) ?_
    rw [abs_neg]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)] at h1
  nlinarith [abs_nonneg x, Real.pi_pos]

lemma E_tcF3_bound (m : ℕ) (x : ℝ) :
    ‖iteratedDeriv m tcF3 x‖ ≤ 2 ^ (m + 1) * (1 + 2 * Real.pi) * (1 + |x|) := by
  have hsub : tcF3 = fun x : ℝ => tcF1 (x - 2 * Real.pi) := rfl
  rw [hsub, E_iteratedDeriv_comp_sub tcF1 contDiff_tcF1 (2*Real.pi) m]
  have hb := E_tcF1_bound m (x - 2 * Real.pi)
  refine le_trans hb ?_
  have h2 : 1 + |x - 2 * Real.pi| ≤ (1 + 2 * Real.pi) * (1 + |x|) :=
    E_abs_sub_const_le x
  have h3 : (0:ℝ) ≤ 2 ^ (m+1) := by positivity
  calc 2 ^ (m + 1) * (1 + |x - 2 * Real.pi|) ≤ 2 ^ (m+1) * ((1 + 2*Real.pi) * (1 + |x|)) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 2 ^ (m + 1) * (1 + 2 * Real.pi) * (1 + |x|) := by ring

lemma E_tcF4_bound (B : ℝ) (hB0 : 0 ≤ B) (m : ℕ) (x : ℝ) :
    ‖iteratedDeriv m (tcF4 B) x‖ ≤ 2 ^ (m + 1) * (B + 1) * (1 + 2 * Real.pi) * (1 + |x|) := by
  have hsub : tcF4 B = fun x : ℝ => tcF2 B (x - 2 * Real.pi) := rfl
  rw [hsub, E_iteratedDeriv_comp_sub (tcF2 B) (contDiff_tcF2 B) (2*Real.pi) m]
  have hb := E_tcF2_bound B hB0 m (x - 2 * Real.pi)
  refine le_trans hb ?_
  have h2 : 1 + |x - 2 * Real.pi| ≤ (1 + 2 * Real.pi) * (1 + |x|) :=
    E_abs_sub_const_le x
  have h3 : (0:ℝ) ≤ 2 ^ (m+1) * (B + 1) := by positivity
  calc 2 ^ (m + 1) * (B + 1) * (1 + |x - 2 * Real.pi|)
      ≤ 2 ^ (m+1) * (B+1) * ((1 + 2*Real.pi) * (1 + |x|)) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 2 ^ (m + 1) * (B + 1) * (1 + 2 * Real.pi) * (1 + |x|) := by ring


lemma E_one_add_pow_le (y : ℝ) (hy : 0 ≤ y) (M : ℕ) :
    (1 + y) ^ M ≤ 2 ^ M * (1 + y ^ M) := by
  rw [add_pow]
  have hterm : ∀ k ∈ Finset.range (M + 1),
      1 ^ k * y ^ (M - k) * (M.choose k : ℝ) ≤ (1 + y ^ M) * (M.choose k : ℝ) := by
    intro k hk
    have h : y ^ (M - k) ≤ 1 + y ^ M := by
      rcases le_total y 1 with hy1 | hy1
      · have h1 : y ^ (M - k) ≤ 1 := pow_le_one₀ hy hy1
        linarith [pow_nonneg hy M]
      · have h1 : y ^ (M - k) ≤ y ^ M := pow_le_pow_right₀ hy1 (Nat.sub_le M k)
        linarith [pow_nonneg hy M]
    rw [one_pow, one_mul]
    exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
  calc ∑ k ∈ Finset.range (M + 1), 1 ^ k * y ^ (M - k) * (M.choose k : ℝ)
      ≤ ∑ k ∈ Finset.range (M + 1), (1 + y ^ M) * (M.choose k : ℝ) := Finset.sum_le_sum hterm
    _ = (1 + y ^ M) * 2 ^ M := by rw [← Finset.mul_sum, E_sum_choose]
    _ = 2 ^ M * (1 + y ^ M) := by ring

lemma E_gauss_bound (A d : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
    (1 + |x|) ^ A * (1 + Real.pi * x ^ 2) ^ d * Real.exp (-(Real.pi * x ^ 2)) ≤ B := by
  set K : ℝ := ((A + 2 * d : ℝ) / (2 * Real.pi * Real.exp 1)) ^ ((A + 2 * d : ℝ) / 2) with hK
  have hKnn : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  refine ⟨2 ^ (A + 2 * d) * (1 + Real.pi) ^ d * (1 + K), by positivity, fun x => ?_⟩
  have hstep : (1 + Real.pi * x ^ 2) ^ d ≤ (1 + Real.pi) ^ d * (1 + |x|) ^ (2 * d) := by
    have hbase : 1 + Real.pi * x ^ 2 ≤ (1 + Real.pi) * (1 + |x|) ^ 2 := by
      rw [show (1 + |x|) ^ 2 = 1 + 2 * |x| + x ^ 2 by rw [add_sq, sq_abs]; ring]
      nlinarith [Real.pi_pos, abs_nonneg x, sq_nonneg x, mul_nonneg Real.pi_pos.le (abs_nonneg x),
        mul_nonneg Real.pi_pos.le (sq_nonneg x)]
    calc (1 + Real.pi * x ^ 2) ^ d ≤ ((1 + Real.pi) * (1 + |x|) ^ 2) ^ d :=
          pow_le_pow_left₀ (by positivity) hbase d
      _ = (1 + Real.pi) ^ d * (1 + |x|) ^ (2 * d) := by rw [mul_pow, ← pow_mul]
  have h2 : (1 + |x|) ^ (A + 2 * d) * Real.exp (-(Real.pi * x ^ 2))
      ≤ 2 ^ (A + 2 * d) * (1 + K) := by
    have hb := E_one_add_pow_le |x| (abs_nonneg x) (A + 2 * d)
    have hexp1 : Real.exp (-(Real.pi * x ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, sq_nonneg x]
    have hxK : |x| ^ (A + 2 * d) * Real.exp (-(Real.pi * x ^ 2 * 1)) ≤ K := by
      have := abs_pow_mul_exp_le (A + 2 * d) (by norm_num : (0:ℝ) < 1) x
      simpa [hK, mul_one] using this
    rw [mul_one] at hxK
    calc (1 + |x|) ^ (A + 2 * d) * Real.exp (-(Real.pi * x ^ 2))
        ≤ (2 ^ (A + 2 * d) * (1 + |x| ^ (A + 2 * d))) * Real.exp (-(Real.pi * x ^ 2)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = 2 ^ (A + 2 * d) * ((1 + |x| ^ (A + 2 * d)) * Real.exp (-(Real.pi * x ^ 2))) := by ring
      _ = 2 ^ (A + 2 * d) * (Real.exp (-(Real.pi * x ^ 2))
            + |x| ^ (A + 2 * d) * Real.exp (-(Real.pi * x ^ 2))) := by ring
      _ ≤ 2 ^ (A + 2 * d) * (1 + K) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hexp1, hxK]
  calc (1 + |x|) ^ A * (1 + Real.pi * x ^ 2) ^ d * Real.exp (-(Real.pi * x ^ 2))
      ≤ (1 + |x|) ^ A * ((1 + Real.pi) ^ d * (1 + |x|) ^ (2 * d))
          * Real.exp (-(Real.pi * x ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (1 + Real.pi) ^ d * ((1 + |x|) ^ (A + 2 * d) * Real.exp (-(Real.pi * x ^ 2))) := by
        rw [pow_add]; ring
    _ ≤ (1 + Real.pi) ^ d * (2 ^ (A + 2 * d) * (1 + K)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 ^ (A + 2 * d) * (1 + Real.pi) ^ d * (1 + K) := by ring

theorem E_comp_quad_bounded_ge (J : ℝ → ℂ) (x₀ : ℝ) (d : ℕ) (hJ : ContDiff ℝ ⊤ J)
    (hJ' : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
      ‖iteratedDeriv j J x‖ ≤ C * (1 + |x|) ^ d * Real.exp (-x))
    (k l : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, x₀ ≤ Real.pi * r ^ 2 →
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => J (Real.pi * s ^ 2)) r‖ ≤ K := by
  classical
  obtain ⟨n, c, m, j, hmle, hjle, hrepr⟩ := exists_chain_repr J hJ l
  choose Cf hCf using fun i : Fin n => hJ' (j i)
  obtain ⟨Bg, hBgnn, hBg⟩ := E_gauss_bound (k + l) d
  refine ⟨Bg * ∑ i : Fin n, ‖c i‖ * Cf i, ?_, ?_⟩
  · exact mul_nonneg hBgnn (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hCf i).1))
  · intro r hx0
    rw [hrepr r]
    calc |r| ^ k * ‖∑ i : Fin n, c i * (r : ℂ) ^ (m i)
            * iteratedDeriv (j i) J (Real.pi * r ^ 2)‖
        ≤ |r| ^ k * ∑ i : Fin n, ‖c i * (r : ℂ) ^ (m i)
            * iteratedDeriv (j i) J (Real.pi * r ^ 2)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ i : Fin n, |r| ^ k * ‖c i * (r : ℂ) ^ (m i)
            * iteratedDeriv (j i) J (Real.pi * r ^ 2)‖ := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin n, ‖c i‖ * Cf i * Bg := by
          apply Finset.sum_le_sum
          intro i _
          have hZ := (hCf i).2 (Real.pi * r ^ 2) hx0
          have habs : |Real.pi * r ^ 2| = Real.pi * r ^ 2 := abs_of_nonneg (by positivity)
          rw [habs] at hZ
          have hr : ‖(r : ℂ)‖ = |r| := norm_ofReal_eq_abs r
          have hnorm : ‖c i * (r : ℂ) ^ (m i) * iteratedDeriv (j i) J (Real.pi * r ^ 2)‖
              = ‖c i‖ * |r| ^ (m i) * ‖iteratedDeriv (j i) J (Real.pi * r ^ 2)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_pow, hr]
          rw [hnorm]
          have habsr : (0 : ℝ) ≤ |r| := abs_nonneg r
          have hone : (1 : ℝ) ≤ 1 + |r| := by linarith
          have hle1 : |r| ≤ 1 + |r| := by linarith
          have hpow : |r| ^ (k + m i) ≤ (1 + |r|) ^ (k + l) := by
            calc |r| ^ (k + m i) ≤ (1 + |r|) ^ (k + m i) := pow_le_pow_left₀ habsr hle1 _
              _ ≤ (1 + |r|) ^ (k + l) :=
                  pow_le_pow_right₀ hone (by have := hmle i; omega)
          have hpos : (0:ℝ) ≤ ‖c i‖ * |r| ^ (m i) := by positivity
          calc |r| ^ k * (‖c i‖ * |r| ^ (m i) * ‖iteratedDeriv (j i) J (Real.pi * r ^ 2)‖)
              ≤ |r| ^ k * (‖c i‖ * |r| ^ (m i)
                  * (Cf i * (1 + Real.pi * r ^ 2) ^ d
                    * Real.exp (-(Real.pi * r ^ 2)))) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul_of_nonneg_left hZ hpos
            _ = ‖c i‖ * Cf i
                  * (|r| ^ (k + m i) * (1 + Real.pi * r ^ 2) ^ d
                    * Real.exp (-(Real.pi * r ^ 2))) := by
                rw [pow_add]; ring
            _ ≤ ‖c i‖ * Cf i
                  * ((1 + |r|) ^ (k + l) * (1 + Real.pi * r ^ 2) ^ d
                    * Real.exp (-(Real.pi * r ^ 2))) := by
                refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (hCf i).1)
                refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
                exact mul_le_mul_of_nonneg_right hpow (by positivity)
            _ ≤ ‖c i‖ * Cf i * Bg :=
                mul_le_mul_of_nonneg_left (hBg r) (mul_nonneg (norm_nonneg _) (hCf i).1)
      _ = Bg * ∑ i : Fin n, ‖c i‖ * Cf i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring



lemma E_iteratedDeriv_exp_negB (B : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => Complex.exp (-((x : ℂ) * (B : ℂ))))
      = fun x : ℝ => (-(B : ℂ)) ^ k * Complex.exp (-((x : ℂ) * (B : ℂ))) := by
  have h := E_iteratedDeriv_exp_shift B 0 k
  simpa [sub_zero] using h

lemma E_norm_iteratedDeriv_exp_negB (B : ℝ) (hB0 : 0 ≤ B) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (fun x : ℝ => Complex.exp (-((x : ℂ) * (B : ℂ)))) x‖
      = B ^ k * Real.exp (-(x * B)) := by
  rw [E_iteratedDeriv_exp_negB B k]
  simp only []
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have h1 : ‖(-(B : ℂ))‖ = B := by rw [norm_neg, norm_ofReal_eq_abs, abs_of_nonneg hB0]
  rw [h1]
  have h2 : (-((x : ℂ) * (B : ℂ))).re = -(x * B) := by simp
  rw [h2]

theorem E_shape_bound_exp (f : ℝ → ℂ) (hfc : ContDiff ℝ ω f) (cf : ℕ → ℝ)
    (hf : ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m f x‖ ≤ cf m * (1 + |x|))
    (B : ℝ) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B) (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖iteratedDeriv m (fun y : ℝ => f y * Complex.exp (-((y : ℂ) * (B : ℂ)))) x‖
      ≤ (∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) * cf p * B ^ (m - p))
          * (1 + |x|) * Real.exp (-x) := by
  have hgc : ContDiff ℝ ω (fun x : ℝ => Complex.exp (-((x : ℂ) * (B : ℂ)))) :=
    contDiff_exp_negB B
  have hleib := E_norm_iteratedDeriv_mul_le (m := m) f
    (fun x : ℝ => Complex.exp (-((x : ℂ) * (B : ℂ)))) hfc hgc x
  refine le_trans hleib ?_
  have hmain : ∀ p ∈ Finset.range (m + 1),
      (m.choose p : ℝ) * ‖iteratedDeriv p f x‖
          * ‖iteratedDeriv (m - p) (fun x : ℝ => Complex.exp (-((x : ℂ) * (B : ℂ)))) x‖
        ≤ (m.choose p : ℝ) * cf p * B ^ (m - p) * ((1 + |x|) * Real.exp (-x)) := by
    intro p hp
    have hEnorm : ‖iteratedDeriv (m - p) (fun x : ℝ => Complex.exp (-((x : ℂ) * (B : ℂ)))) x‖
        = B ^ (m - p) * Real.exp (-(x * B)) :=
      E_norm_iteratedDeriv_exp_negB B hB0 (m - p) x
    rw [hEnorm]
    have hexp : Real.exp (-(x * B)) ≤ Real.exp (-x) := by
      apply Real.exp_le_exp.mpr; nlinarith [hx, hB1]
    have hBp : (0 : ℝ) ≤ B ^ (m - p) := pow_nonneg hB0 _
    have hcfp : (0 : ℝ) ≤ cf p := le_trans (norm_nonneg _) (by have := hf p 0; simpa using this)
    calc (m.choose p : ℝ) * ‖iteratedDeriv p f x‖ * (B ^ (m - p) * Real.exp (-(x * B)))
        ≤ (m.choose p : ℝ) * (cf p * (1 + |x|)) * (B ^ (m - p) * Real.exp (-(x * B))) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hBp (Real.exp_nonneg _))
          exact mul_le_mul_of_nonneg_left (hf p x) (Nat.cast_nonneg _)
      _ ≤ (m.choose p : ℝ) * (cf p * (1 + |x|)) * (B ^ (m - p) * Real.exp (-x)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hcfp (by positivity)))
          exact mul_le_mul_of_nonneg_left hexp hBp
      _ = (m.choose p : ℝ) * cf p * B ^ (m - p) * ((1 + |x|) * Real.exp (-x)) := by ring
  calc ∑ p ∈ Finset.range (m + 1),
        (m.choose p : ℝ) * ‖iteratedDeriv p f x‖
          * ‖iteratedDeriv (m - p) (fun x : ℝ => Complex.exp (-((x : ℂ) * (B : ℂ)))) x‖
      ≤ ∑ p ∈ Finset.range (m + 1),
          (m.choose p : ℝ) * cf p * B ^ (m - p) * ((1 + |x|) * Real.exp (-x)) :=
        Finset.sum_le_sum hmain
    _ = (∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) * cf p * B ^ (m - p))
          * (1 + |x|) * Real.exp (-x) := by
        rw [← Finset.sum_mul]; ring

def E_sh1 (B : ℝ) : ℝ → ℂ := fun x => tcF1 x * Complex.exp (-((x : ℂ) * (B : ℂ)))
def E_sh2 (B : ℝ) : ℝ → ℂ := fun x => tcF2 B x * Complex.exp (-((x : ℂ) * (B : ℂ)))
def E_sh3 (B : ℝ) : ℝ → ℂ :=
  fun x => tcF3 x * Complex.exp (-(((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ)))
def E_sh4 (B : ℝ) : ℝ → ℂ :=
  fun x => tcF4 B x * Complex.exp (-(((x - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ)))

def E_shC (l : ℕ) (B : ℝ) : ℝ :=
  4 * (B + 1) * (2 + B) ^ l * (1 + 2 * Real.pi) * Real.exp (2 * Real.pi)

lemma E_shC_nonneg (l : ℕ) (B : ℝ) (hB0 : 0 ≤ B) : 0 ≤ E_shC l B := by
  unfold E_shC
  have a : (0:ℝ) ≤ B + 1 := by linarith
  have b : (0:ℝ) ≤ (2 + B) ^ l := pow_nonneg (by linarith) l
  have c : (0:ℝ) ≤ 1 + 2 * Real.pi := by linarith [Real.pi_pos]
  have d : (0:ℝ) ≤ Real.exp (2 * Real.pi) := Real.exp_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) a) b) c) d

lemma E_sum_choose_succ (l : ℕ) (B : ℝ) :
    (∑ p ∈ Finset.range (l + 1), (l.choose p : ℝ) * 2 ^ (p+1) * B ^ (l - p)) = 2 * (2 + B) ^ l := by
  have hp := add_pow (2 : ℝ) B l
  rw [hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp'
  ring

lemma E_sum_choose_succ' (l : ℕ) (B : ℝ) :
    (∑ p ∈ Finset.range (l + 1), (l.choose p : ℝ) * (2 ^ (p+1) * (B+1)) * B ^ (l - p))
      = 2 * (B + 1) * (2 + B) ^ l := by
  have h := E_sum_choose_succ l B
  calc (∑ p ∈ Finset.range (l + 1), (l.choose p : ℝ) * (2 ^ (p+1) * (B+1)) * B ^ (l - p))
      = (B + 1) * (∑ p ∈ Finset.range (l + 1), (l.choose p : ℝ) * 2 ^ (p+1) * B ^ (l - p)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro p hp'; ring
    _ = (B + 1) * (2 * (2 + B) ^ l) := by rw [h]
    _ = 2 * (B + 1) * (2 + B) ^ l := by ring

lemma E_sh1_bound (B : ℝ) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B) (l : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖iteratedDeriv l (E_sh1 B) x‖ ≤ 2 * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x)) := by
  have h := E_shape_bound_exp tcF1 contDiff_tcF1 (fun m => 2 ^ (m+1))
    (fun m y => E_tcF1_bound m y) B hB0 hB1 l x hx
  refine le_trans h ?_
  rw [E_sum_choose_succ l B]
  exact le_of_eq (by ring)

lemma E_sh2_bound (B : ℝ) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B) (l : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖iteratedDeriv l (E_sh2 B) x‖ ≤ 2 * (B + 1) * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x)) := by
  have h := E_shape_bound_exp (tcF2 B) (contDiff_tcF2 B) (fun m => 2 ^ (m+1) * (B+1))
    (fun m y => E_tcF2_bound B hB0 m y) B hB0 hB1 l x hx
  refine le_trans h ?_
  rw [E_sum_choose_succ' l B]
  exact le_of_eq (by ring)

lemma contDiff_E_sh1 (B : ℝ) : ContDiff ℝ ω (E_sh1 B) :=
  contDiff_tcF1.mul (contDiff_exp_negB B)

lemma contDiff_E_sh2 (B : ℝ) : ContDiff ℝ ω (E_sh2 B) :=
  (contDiff_tcF2 B).mul (contDiff_exp_negB B)

lemma E_sh3_eq (B : ℝ) : E_sh3 B = fun x : ℝ => E_sh1 B (x - 2 * Real.pi) := rfl

lemma E_sh4_eq (B : ℝ) : E_sh4 B = fun x : ℝ => E_sh2 B (x - 2 * Real.pi) := rfl

lemma E_sh3_bound (B : ℝ) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B) (l : ℕ) (x : ℝ) (hx : 2*Real.pi ≤ x) :
    ‖iteratedDeriv l (E_sh3 B) x‖ ≤ 2 * (2 + B) ^ l * (Real.exp (2*Real.pi) * (1 + 2*Real.pi))
      * ((1 + |x|) * Real.exp (-x)) := by
  rw [E_sh3_eq, E_iteratedDeriv_comp_sub (E_sh1 B) (contDiff_E_sh1 B) (2*Real.pi) l]
  have hx' : 0 ≤ x - 2 * Real.pi := by linarith
  have h := E_sh1_bound B hB0 hB1 l (x - 2*Real.pi) hx'
  refine le_trans h ?_
  have h1 : 1 + |x - 2 * Real.pi| ≤ (1 + 2 * Real.pi) * (1 + |x|) := E_abs_sub_const_le x
  have h2 : Real.exp (-(x - 2 * Real.pi)) ≤ Real.exp (2 * Real.pi) * Real.exp (-x) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; ring_nf; linarith
  have h3 : (0:ℝ) ≤ 2 * (2 + B) ^ l := by positivity
  calc 2 * (2 + B) ^ l * ((1 + |x - 2 * Real.pi|) * Real.exp (-(x - 2 * Real.pi)))
      ≤ 2 * (2 + B) ^ l * (((1 + 2 * Real.pi) * (1 + |x|))
          * (Real.exp (2 * Real.pi) * Real.exp (-x))) := by
        refine mul_le_mul_of_nonneg_left ?_ h3
        exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by positivity)
    _ = 2 * (2 + B) ^ l * (Real.exp (2*Real.pi) * (1 + 2*Real.pi))
          * ((1 + |x|) * Real.exp (-x)) := by ring

lemma E_sh4_bound (B : ℝ) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B) (l : ℕ) (x : ℝ) (hx : 2*Real.pi ≤ x) :
    ‖iteratedDeriv l (E_sh4 B) x‖ ≤ 2 * (B + 1) * (2 + B) ^ l
      * (Real.exp (2*Real.pi) * (1 + 2*Real.pi)) * ((1 + |x|) * Real.exp (-x)) := by
  rw [E_sh4_eq, E_iteratedDeriv_comp_sub (E_sh2 B) (contDiff_E_sh2 B) (2*Real.pi) l]
  have hx' : 0 ≤ x - 2 * Real.pi := by linarith
  have h := E_sh2_bound B hB0 hB1 l (x - 2*Real.pi) hx'
  refine le_trans h ?_
  have h1 : 1 + |x - 2 * Real.pi| ≤ (1 + 2 * Real.pi) * (1 + |x|) := E_abs_sub_const_le x
  have h2 : Real.exp (-(x - 2 * Real.pi)) ≤ Real.exp (2 * Real.pi) * Real.exp (-x) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; ring_nf; linarith
  have h3 : (0:ℝ) ≤ 2 * (B + 1) * (2 + B) ^ l := by positivity
  calc 2 * (B+1) * (2 + B) ^ l * ((1 + |x - 2 * Real.pi|) * Real.exp (-(x - 2 * Real.pi)))
      ≤ 2 * (B+1) * (2 + B) ^ l * (((1 + 2 * Real.pi) * (1 + |x|))
          * (Real.exp (2 * Real.pi) * Real.exp (-x))) := by
        refine mul_le_mul_of_nonneg_left ?_ h3
        exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by positivity)
    _ = 2 * (B + 1) * (2 + B) ^ l * (Real.exp (2*Real.pi) * (1 + 2*Real.pi))
          * ((1 + |x|) * Real.exp (-x)) := by ring

lemma E_shC_upper (l : ℕ) (B : ℝ) (hB1 : 1 ≤ B) :
    2 * (B + 1) * (2 + B) ^ l * (Real.exp (2*Real.pi) * (1 + 2*Real.pi)) ≤ E_shC l B := by
  have hB0 : (0:ℝ) ≤ B := by linarith
  have h1 : (2 + B) ^ l ≤ (2 * (B + 1)) ^ l :=
    pow_le_pow_left₀ (by linarith) (by linarith) l
  have h2 : (2 * (B + 1)) ^ l = 2 ^ l * (B + 1) ^ l := mul_pow _ _ _
  have h3 : (B + 1) ^ l ≤ (B + 1) ^ (l + 1) := by
    calc (B + 1) ^ l ≤ (B + 1) ^ l * (B + 1) := le_mul_of_one_le_right (by positivity) (by linarith)
      _ = (B + 1) ^ (l + 1) := by rw [pow_succ]
  have a1 : (1:ℝ) ≤ B + 1 := by linarith
  have b1 : (1:ℝ) ≤ 1 + 2*Real.pi := by linarith [Real.pi_pos]
  have c1 : (1:ℝ) ≤ Real.exp (2*Real.pi) := Real.one_le_exp (by positivity)
  have hab : (1:ℝ) ≤ (B + 1) * (1 + 2*Real.pi) := by
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (B + 1) * (1 + 2*Real.pi) := mul_le_mul a1 b1 (by norm_num) (by linarith)
  have hge : (1:ℝ) ≤ (B + 1) * (1 + 2*Real.pi) * Real.exp (2*Real.pi) := by
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ ((B + 1) * (1 + 2*Real.pi)) * Real.exp (2*Real.pi) :=
          mul_le_mul hab c1 (by norm_num) (by linarith)
  have hp : (0:ℝ) ≤ (2 + B)^l := pow_nonneg (by linarith) l
  have h2le : 2 * (2 + B) ^ l ≤ 4 * (2 + B) ^ l * ((B + 1) * (1 + 2*Real.pi) * Real.exp (2*Real.pi)) := by
    have hh : (2 + B)^l * 1 ≤ (2 + B)^l * ((B + 1) * (1 + 2*Real.pi) * Real.exp (2*Real.pi)) :=
      mul_le_mul_of_nonneg_left hge hp
    nlinarith [hh]
  unfold E_shC
  nlinarith [h2le, hp, hge, mul_nonneg hp (le_trans (by norm_num) hge)]

lemma E_tcLambda_shape_ge (G : Fin 2 → Fin 2 → ℍ → ℂ) (B : ℝ) (w : ℍ)
    (hB0 : 0 ≤ B) (hB1 : 1 ≤ B) (l : ℕ) (x : ℝ) (hx : 2*Real.pi ≤ x) :
    ‖iteratedDeriv l (tcLambda G B w) x‖
      ≤ E_shC l B * (‖G 0 0 w‖ + ‖G 0 1 w‖ + ‖G 1 0 w‖ + ‖G 1 1 w‖)
        * (1 + |x|) * Real.exp (-x) := by
  have hF : tcLambda G B w = fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w)
      + (E_sh3 B y * G 1 0 w) + (E_sh4 B y * G 1 1 w) := by
    funext y
    unfold tcLambda E_sh1 E_sh2 E_sh3 E_sh4 tcF1 tcF2 tcF3 tcF4
    ring_nf
  have c3 : ContDiff ℝ ω (E_sh3 B) :=
    contDiff_tcF3.mul (contDiff_exp_negB B |>.comp (contDiff_id.sub contDiff_const))
  have c4 : ContDiff ℝ ω (E_sh4 B) :=
    contDiff_tcF4 B |>.mul (contDiff_exp_negB B |>.comp (contDiff_id.sub contDiff_const))
  have hs1 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh1 B y * G 0 0 w) x :=
    ((contDiff_E_sh1 B).mul contDiff_const).contDiffAt.of_le le_top
  have hs2 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh2 B y * G 0 1 w) x :=
    ((contDiff_E_sh2 B).mul contDiff_const).contDiffAt.of_le le_top
  have hs3 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh3 B y * G 1 0 w) x :=
    (c3.mul contDiff_const).contDiffAt.of_le le_top
  have hs4 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh4 B y * G 1 1 w) x :=
    (c4.mul contDiff_const).contDiffAt.of_le le_top
  rw [hF]
  rw [show (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w)
        + (E_sh3 B y * G 1 0 w) + (E_sh4 B y * G 1 1 w))
      = (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w)
          + (E_sh3 B y * G 1 0 w)) + (fun y : ℝ => (E_sh4 B y * G 1 1 w)) from rfl]
  rw [iteratedDeriv_add ((hs1.add hs2).add hs3) hs4]
  rw [show (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w) + (E_sh3 B y * G 1 0 w))
      = (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w))
        + (fun y : ℝ => (E_sh3 B y * G 1 0 w)) from rfl]
  rw [iteratedDeriv_add (hs1.add hs2) hs3]
  rw [show (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w))
      = (fun y : ℝ => (E_sh1 B y * G 0 0 w)) + (fun y : ℝ => (E_sh2 B y * G 0 1 w)) from rfl]
  rw [iteratedDeriv_add hs1 hs2,
    iteratedDeriv_mul_const_field (n := l) (E_sh1 B) (G 0 0 w),
    iteratedDeriv_mul_const_field (n := l) (E_sh2 B) (G 0 1 w),
    iteratedDeriv_mul_const_field (n := l) (E_sh3 B) (G 1 0 w),
    iteratedDeriv_mul_const_field (n := l) (E_sh4 B) (G 1 1 w)]
  have hx0 : (0:ℝ) ≤ x := by linarith [Real.pi_pos]
  have b1 := E_sh1_bound B hB0 hB1 l x hx0
  have b2 := E_sh2_bound B hB0 hB1 l x hx0
  have b3 := E_sh3_bound B hB0 hB1 l x hx
  have b4 := E_sh4_bound B hB0 hB1 l x hx
  have hC := E_shC_upper l B hB1
  have hR : (0:ℝ) ≤ (1 + |x|) * Real.exp (-x) := by positivity
  have hC2 : 2 * (2 + B) ^ l ≤ E_shC l B := by
    refine le_trans ?_ hC
    have hge : (1:ℝ) ≤ Real.exp (2*Real.pi) * (1 + 2*Real.pi) := by
      have a : (1:ℝ) ≤ Real.exp (2*Real.pi) := Real.one_le_exp (by positivity)
      have b : (1:ℝ) ≤ 1 + 2*Real.pi := by linarith [Real.pi_pos]
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ Real.exp (2*Real.pi) * (1 + 2*Real.pi) := mul_le_mul a b (by norm_num) (by positivity)
    have hB1' : (1:ℝ) ≤ B + 1 := by linarith
    have hp : (0:ℝ) ≤ (2 + B)^l := pow_nonneg (by linarith) l
    have hge2 : (1:ℝ) ≤ (B+1) * (Real.exp (2*Real.pi) * (1 + 2*Real.pi)) := by
      calc (1:ℝ) = (B+1) * 0 + 1 := by ring
        _ ≤ (B+1) * (Real.exp (2*Real.pi) * (1 + 2*Real.pi)) := by
            nlinarith [hge, hB1', mul_nonneg (by linarith : (0:ℝ) ≤ B + 1) (by positivity : (0:ℝ) ≤ Real.exp (2*Real.pi) * (1 + 2*Real.pi))]
    have hh : (2+B)^l * 1 ≤ (2+B)^l * ((B+1) * (Real.exp (2*Real.pi) * (1 + 2*Real.pi))) :=
      mul_le_mul_of_nonneg_left hge2 hp
    calc 2 * (2+B)^l = 2 * ((2+B)^l * 1) := by ring
      _ ≤ 2 * ((2+B)^l * ((B+1) * (Real.exp (2*Real.pi) * (1 + 2*Real.pi)))) :=
          mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = 2 * (B+1) * (2+B)^l * (Real.exp (2*Real.pi) * (1 + 2*Real.pi)) := by ring
  have hC3 : 2 * (2 + B) ^ l * (Real.exp (2*Real.pi) * (1 + 2*Real.pi)) ≤ E_shC l B := by
    refine le_trans ?_ hC
    have h : (2:ℝ) ≤ 2 * (B + 1) := by linarith
    have hp : (0:ℝ) ≤ (2+B)^l * (Real.exp (2*Real.pi) * (1 + 2*Real.pi)) := by positivity
    have hh := mul_le_mul_of_nonneg_right h hp
    nlinarith [hh]
  have hC5 : 2 * (B + 1) * (2 + B) ^ l ≤ E_shC l B := by
    refine le_trans ?_ hC
    have hge : (1:ℝ) ≤ Real.exp (2*Real.pi) * (1 + 2*Real.pi) := by
      have a : (1:ℝ) ≤ Real.exp (2*Real.pi) := Real.one_le_exp (by positivity)
      have b : (1:ℝ) ≤ 1 + 2*Real.pi := by linarith [Real.pi_pos]
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ Real.exp (2*Real.pi) * (1 + 2*Real.pi) := mul_le_mul a b (by norm_num) (by positivity)
    have hp : (0:ℝ) ≤ 2 * (B + 1) * (2 + B)^l := by positivity
    have hh := mul_le_mul_of_nonneg_left hge hp
    rw [mul_one] at hh
    exact hh
  have e1 : ‖iteratedDeriv l (E_sh1 B) x * G 0 0 w‖
      ≤ E_shC l B * ‖G 0 0 w‖ * ((1 + |x|) * Real.exp (-x)) := by
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_right (le_trans b1
      (mul_le_mul_of_nonneg_right hC2 hR)) (norm_nonneg (G 0 0 w))) (le_of_eq ?_)
    ring
  have e2 : ‖iteratedDeriv l (E_sh2 B) x * G 0 1 w‖
      ≤ E_shC l B * ‖G 0 1 w‖ * ((1 + |x|) * Real.exp (-x)) := by
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_right (le_trans b2
      (mul_le_mul_of_nonneg_right hC5 hR)) (norm_nonneg (G 0 1 w))) (le_of_eq ?_)
    ring
  have e3 : ‖iteratedDeriv l (E_sh3 B) x * G 1 0 w‖
      ≤ E_shC l B * ‖G 1 0 w‖ * ((1 + |x|) * Real.exp (-x)) := by
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_right (le_trans b3
      (mul_le_mul_of_nonneg_right hC3 hR)) (norm_nonneg (G 1 0 w))) (le_of_eq ?_)
    ring
  have e4 : ‖iteratedDeriv l (E_sh4 B) x * G 1 1 w‖
      ≤ E_shC l B * ‖G 1 1 w‖ * ((1 + |x|) * Real.exp (-x)) := by
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_right (le_trans b4
      (mul_le_mul_of_nonneg_right hC hR)) (norm_nonneg (G 1 1 w))) (le_of_eq ?_)
    ring
  have htri : ‖iteratedDeriv l (E_sh1 B) x * G 0 0 w
        + iteratedDeriv l (E_sh2 B) x * G 0 1 w
        + iteratedDeriv l (E_sh3 B) x * G 1 0 w
        + iteratedDeriv l (E_sh4 B) x * G 1 1 w‖
      ≤ ‖iteratedDeriv l (E_sh1 B) x * G 0 0 w‖
        + ‖iteratedDeriv l (E_sh2 B) x * G 0 1 w‖
        + ‖iteratedDeriv l (E_sh3 B) x * G 1 0 w‖
        + ‖iteratedDeriv l (E_sh4 B) x * G 1 1 w‖ := by
    have h1 := norm_add_le (iteratedDeriv l (E_sh1 B) x * G 0 0 w
        + iteratedDeriv l (E_sh2 B) x * G 0 1 w + iteratedDeriv l (E_sh3 B) x * G 1 0 w)
      (iteratedDeriv l (E_sh4 B) x * G 1 1 w)
    have h2 := norm_add_le (iteratedDeriv l (E_sh1 B) x * G 0 0 w
        + iteratedDeriv l (E_sh2 B) x * G 0 1 w) (iteratedDeriv l (E_sh3 B) x * G 1 0 w)
    have h3 := norm_add_le (iteratedDeriv l (E_sh1 B) x * G 0 0 w)
      (iteratedDeriv l (E_sh2 B) x * G 0 1 w)
    linarith [h1, h2, h3, norm_nonneg (iteratedDeriv l (E_sh1 B) x * G 0 0 w),
      norm_nonneg (iteratedDeriv l (E_sh2 B) x * G 0 1 w),
      norm_nonneg (iteratedDeriv l (E_sh3 B) x * G 1 0 w),
      norm_nonneg (iteratedDeriv l (E_sh4 B) x * G 1 1 w)]
  calc ‖iteratedDeriv l (E_sh1 B) x * G 0 0 w
        + iteratedDeriv l (E_sh2 B) x * G 0 1 w
        + iteratedDeriv l (E_sh3 B) x * G 1 0 w
        + iteratedDeriv l (E_sh4 B) x * G 1 1 w‖
      ≤ ‖iteratedDeriv l (E_sh1 B) x * G 0 0 w‖
        + ‖iteratedDeriv l (E_sh2 B) x * G 0 1 w‖
        + ‖iteratedDeriv l (E_sh3 B) x * G 1 0 w‖
        + ‖iteratedDeriv l (E_sh4 B) x * G 1 1 w‖ := htri
    _ ≤ E_shC l B * ‖G 0 0 w‖ * ((1 + |x|) * Real.exp (-x))
        + E_shC l B * ‖G 0 1 w‖ * ((1 + |x|) * Real.exp (-x))
        + E_shC l B * ‖G 1 0 w‖ * ((1 + |x|) * Real.exp (-x))
        + E_shC l B * ‖G 1 1 w‖ * ((1 + |x|) * Real.exp (-x)) := by linarith [e1, e2, e3, e4]
    _ = E_shC l B * (‖G 0 0 w‖ + ‖G 0 1 w‖ + ‖G 1 0 w‖ + ‖G 1 1 w‖)
        * (1 + |x|) * Real.exp (-x) := by ring


/-- The chain representation of `s ↦ J(π s²)`, with the constants independent of `J`. -/
lemma E_exists_chain_repr_univ (l : ℕ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (m j : Fin n → ℕ),
      (∀ i, m i ≤ l) ∧ (∀ i, j i ≤ l) ∧
      ∀ (J : ℝ → ℂ), ContDiff ℝ ⊤ J → ∀ x : ℝ,
        iteratedDeriv l (fun s : ℝ => J (Real.pi * s ^ 2)) x
          = ∑ i : Fin n, c i * (x : ℂ) ^ (m i) * iteratedDeriv (j i) J (Real.pi * x ^ 2) := by
  induction l with
  | zero =>
    refine ⟨1, fun _ => 1, fun _ => 0, fun _ => 0, fun i => Nat.zero_le _,
      fun i => Nat.zero_le _, ?_⟩
    intro J hJ x
    rw [iteratedDeriv_zero]
    simp
  | succ l ih =>
    obtain ⟨n, c, m, j, hmle, hjle, hrepr⟩ := ih
    let e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
    let c' : Fin (n + n) → ℂ := fun i =>
      Sum.elim (fun a : Fin n => c a * (m a : ℂ)) (fun b : Fin n => c b * ((2 * Real.pi : ℝ) : ℂ)) (e.symm i)
    let m' : Fin (n + n) → ℕ := fun i =>
      Sum.elim (fun a : Fin n => m a - 1) (fun b : Fin n => m b + 1) (e.symm i)
    let j' : Fin (n + n) → ℕ := fun i =>
      Sum.elim (fun a : Fin n => j a) (fun b : Fin n => j b + 1) (e.symm i)
    refine ⟨n + n, c', m', j', ?_, ?_, ?_⟩
    · intro i
      dsimp only [m']
      cases h : e.symm i with
      | inl a => rw [Sum.elim_inl]; have := hmle a; omega
      | inr b => rw [Sum.elim_inr]; have := hmle b; omega
    · intro i
      dsimp only [j']
      cases h : e.symm i with
      | inl a => rw [Sum.elim_inl]; have := hjle a; omega
      | inr b => rw [Sum.elim_inr]; have := hjle b; omega
    · intro J hJ x
      have hfun : iteratedDeriv (l+1) (fun s : ℝ => J (Real.pi * s ^ 2)) x
          = deriv (fun y : ℝ => ∑ i : Fin n, c i * (y:ℂ)^(m i)
              * iteratedDeriv (j i) J (Real.pi * y^2)) x := by
        rw [iteratedDeriv_succ]
        have hh : iteratedDeriv l (fun s : ℝ => J (Real.pi * s ^ 2))
            = fun y : ℝ => ∑ i : Fin n, c i * (y:ℂ)^(m i)
                * iteratedDeriv (j i) J (Real.pi * y^2) := funext (hrepr J hJ)
        rw [hh]
      rw [hfun]
      have hsum : HasDerivAt (fun y : ℝ => ∑ i : Fin n, c i * (y:ℂ)^(m i)
            * iteratedDeriv (j i) J (Real.pi * y^2))
          (∑ i : Fin n, ((c i * (m i : ℂ)) * (x:ℂ)^(m i - 1) * iteratedDeriv (j i) J (Real.pi * x^2)
            + (c i * ((2 * Real.pi : ℝ) : ℂ)) * (x:ℂ)^(m i + 1)
              * iteratedDeriv (j i + 1) J (Real.pi * x^2))) x := by
        have heqfun : (∑ i : Fin n, (fun y : ℝ => c i * (y:ℂ)^(m i)
              * iteratedDeriv (j i) J (Real.pi * y^2)))
            = (fun y : ℝ => ∑ i : Fin n, c i * (y:ℂ)^(m i)
                * iteratedDeriv (j i) J (Real.pi * y^2)) := by
          funext y; rw [Finset.sum_apply]
        have key := HasDerivAt.sum (u := Finset.univ)
          (fun i (_ : i ∈ Finset.univ) => hasDerivAt_chain_term J hJ (c i) (m i) (j i) x)
        rw [heqfun] at key
        exact key
      rw [hsum.deriv]
      rw [Finset.sum_add_distrib]
      have hR : (∑ i : Fin (n + n), c' i * (x:ℂ)^(m' i)
            * iteratedDeriv (j' i) J (Real.pi * x^2))
          = (∑ a : Fin n, (c a * (m a : ℂ)) * (x:ℂ)^(m a - 1)
              * iteratedDeriv (j a) J (Real.pi * x^2))
            + (∑ b : Fin n, (c b * ((2 * Real.pi : ℝ) : ℂ)) * (x:ℂ)^(m b + 1)
              * iteratedDeriv (j b + 1) J (Real.pi * x^2)) := by
        rw [← Equiv.sum_comp e (fun i => c' i * (x:ℂ)^(m' i)
          * iteratedDeriv (j' i) J (Real.pi * x^2))]
        rw [Fintype.sum_sum_type]
        congr 1
        · refine Finset.sum_congr rfl (fun a _ => ?_)
          simp only [c', m', j', Equiv.symm_apply_apply, Sum.elim_inl]
        · refine Finset.sum_congr rfl (fun b _ => ?_)
          simp only [c', m', j', Equiv.symm_apply_apply, Sum.elim_inr]
      rw [hR]


lemma E_shC_mono (B : ℝ) (hB1 : 1 ≤ B) {l m : ℕ} (h : m ≤ l) : E_shC m B ≤ E_shC l B := by
  unfold E_shC
  have h1 : (2 + B) ^ m ≤ (2 + B) ^ l := pow_le_pow_right₀ (by linarith) h
  have hf : (0:ℝ) ≤ 4 * (B + 1) * (1 + 2*Real.pi) * Real.exp (2*Real.pi) := by positivity
  have hh := mul_le_mul_of_nonneg_left h1 hf
  calc 4 * (B + 1) * (2 + B) ^ m * (1 + 2*Real.pi) * Real.exp (2*Real.pi)
      = 4 * (B + 1) * (1 + 2*Real.pi) * Real.exp (2*Real.pi) * (2 + B)^m := by ring
    _ ≤ 4 * (B + 1) * (1 + 2*Real.pi) * Real.exp (2*Real.pi) * (2 + B)^l := hh
    _ = 4 * (B + 1) * (2 + B) ^ l * (1 + 2*Real.pi) * Real.exp (2*Real.pi) := by ring

lemma E_shC_le (l : ℕ) (B : ℝ) (hB1 : 1 ≤ B) :
    E_shC l B ≤ (8 * 3 ^ l * (1 + 2*Real.pi) * Real.exp (2*Real.pi) + 1) * B ^ (l + 1) := by
  have hB0 : (0:ℝ) ≤ B := by linarith
  have h1 : B + 1 ≤ 2 * B := by linarith
  have h2 : 2 + B ≤ 3 * B := by linarith
  have h3 : (2 + B) ^ l ≤ (3 * B) ^ l := pow_le_pow_left₀ (by linarith) h2 l
  have h4 : (3 * B) ^ l = 3 ^ l * B ^ l := mul_pow _ _ _
  have hpB : (0:ℝ) ≤ B ^ (l+1) := pow_nonneg hB0 _
  have hb : 4 * (B + 1) * (2 + B)^l ≤ 8 * 3^l * B^(l+1) := by
    have h3' : (2 + B)^l ≤ 3^l * B^l := by rw [← h4]; exact h3
    have ha : 4 * (B + 1) ≤ 4 * (2 * B) := by linarith
    have hb0 : (0:ℝ) ≤ (2+B)^l := by positivity
    have hb := mul_le_mul ha h3' hb0 (by positivity)
    calc 4 * (B + 1) * (2 + B)^l = (4 * (B + 1)) * (2 + B)^l := by ring
      _ ≤ (4 * (2 * B)) * (3^l * B^l) := hb
      _ = 8 * 3^l * B^(l+1) := by rw [pow_succ]; ring
  have hb2 : (0:ℝ) ≤ (1 + 2*Real.pi) * Real.exp (2*Real.pi) := by positivity
  have hkey : 4 * (B + 1) * (2 + B) ^ l * (1 + 2*Real.pi) * Real.exp (2*Real.pi)
      ≤ 8 * 3 ^ l * (1 + 2*Real.pi) * Real.exp (2*Real.pi) * B ^ (l+1) := by
    calc 4 * (B + 1) * (2 + B) ^ l * (1 + 2*Real.pi) * Real.exp (2*Real.pi)
        = (4 * (B + 1) * (2 + B) ^ l) * ((1 + 2*Real.pi) * Real.exp (2*Real.pi)) := by ring
      _ ≤ (8 * 3^l * B^(l+1)) * ((1 + 2*Real.pi) * Real.exp (2*Real.pi)) :=
          mul_le_mul_of_nonneg_right hb hb2
      _ = 8 * 3 ^ l * (1 + 2*Real.pi) * Real.exp (2*Real.pi) * B ^ (l + 1) := by ring
  unfold E_shC
  nlinarith [hkey, hpB]

lemma E_tcLambda_shape (G : Fin 2 → Fin 2 → ℍ → ℂ) (B : ℝ) (w : ℍ) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B)
    (l : ℕ) (x : ℝ)
    (hx : (G 1 0 w = 0 ∧ G 1 1 w = 0 ∧ 0 ≤ x) ∨ 2 * Real.pi ≤ x) :
    ‖iteratedDeriv l (tcLambda G B w) x‖
      ≤ E_shC l B * (‖G 0 0 w‖ + ‖G 0 1 w‖ + ‖G 1 0 w‖ + ‖G 1 1 w‖)
        * (1 + |x|) * Real.exp (-x) := by
  rcases hx with ⟨h10, h11, hx0⟩ | hxge
  · rw [h10, h11]
    simp only [norm_zero, add_zero]
    have hF : tcLambda G B w = fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w)
        + (E_sh3 B y * G 1 0 w) + (E_sh4 B y * G 1 1 w) := by
      funext y
      unfold tcLambda E_sh1 E_sh2 E_sh3 E_sh4 tcF1 tcF2 tcF3 tcF4
      ring_nf
    have c3 : ContDiff ℝ ω (E_sh3 B) :=
      contDiff_tcF3.mul (contDiff_exp_negB B |>.comp (contDiff_id.sub contDiff_const))
    have c4 : ContDiff ℝ ω (E_sh4 B) :=
      contDiff_tcF4 B |>.mul (contDiff_exp_negB B |>.comp (contDiff_id.sub contDiff_const))
    have hs1 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh1 B y * G 0 0 w) x :=
      ((contDiff_E_sh1 B).mul contDiff_const).contDiffAt.of_le le_top
    have hs2 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh2 B y * G 0 1 w) x :=
      ((contDiff_E_sh2 B).mul contDiff_const).contDiffAt.of_le le_top
    have hs3 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh3 B y * G 1 0 w) x :=
      (c3.mul contDiff_const).contDiffAt.of_le le_top
    have hs4 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh4 B y * G 1 1 w) x :=
      (c4.mul contDiff_const).contDiffAt.of_le le_top
    rw [hF]
    rw [show (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w)
          + (E_sh3 B y * G 1 0 w) + (E_sh4 B y * G 1 1 w))
        = (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w)
            + (E_sh3 B y * G 1 0 w)) + (fun y : ℝ => (E_sh4 B y * G 1 1 w)) from rfl]
    rw [iteratedDeriv_add ((hs1.add hs2).add hs3) hs4]
    rw [show (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w) + (E_sh3 B y * G 1 0 w))
        = (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w))
          + (fun y : ℝ => (E_sh3 B y * G 1 0 w)) from rfl]
    rw [iteratedDeriv_add (hs1.add hs2) hs3]
    rw [show (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w))
        = (fun y : ℝ => (E_sh1 B y * G 0 0 w)) + (fun y : ℝ => (E_sh2 B y * G 0 1 w)) from rfl]
    rw [iteratedDeriv_add hs1 hs2,
      iteratedDeriv_mul_const_field (n := l) (E_sh1 B) (G 0 0 w),
      iteratedDeriv_mul_const_field (n := l) (E_sh2 B) (G 0 1 w),
      iteratedDeriv_mul_const_field (n := l) (E_sh3 B) (G 1 0 w),
      iteratedDeriv_mul_const_field (n := l) (E_sh4 B) (G 1 1 w)]
    rw [h10, h11]
    simp only [norm_zero, mul_zero, add_zero]
    have b1 := E_sh1_bound B hB0 hB1 l x hx0
    have b2 := E_sh2_bound B hB0 hB1 l x hx0
    have hC := E_shC_upper l B hB1
    have hR : (0:ℝ) ≤ (1 + |x|) * Real.exp (-x) := by positivity
    have hC5 : 2 * (B + 1) * (2 + B) ^ l ≤ E_shC l B := by
      refine le_trans ?_ hC
      have hge : (1:ℝ) ≤ Real.exp (2*Real.pi) * (1 + 2*Real.pi) := by
        have a : (1:ℝ) ≤ Real.exp (2*Real.pi) := Real.one_le_exp (by positivity)
        have b : (1:ℝ) ≤ 1 + 2*Real.pi := by linarith [Real.pi_pos]
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ Real.exp (2*Real.pi) * (1 + 2*Real.pi) := mul_le_mul a b (by norm_num) (by positivity)
      have hp : (0:ℝ) ≤ 2 * (B + 1) * (2 + B)^l := by positivity
      have hh := mul_le_mul_of_nonneg_left hge hp
      rw [mul_one] at hh
      exact hh
    have hC2 : 2 * (2 + B) ^ l ≤ E_shC l B := by
      refine le_trans ?_ hC5
      nlinarith [show (0:ℝ) ≤ (2+B)^l by positivity, hB1]
    have e1 : ‖iteratedDeriv l (E_sh1 B) x * G 0 0 w‖
        ≤ E_shC l B * ‖G 0 0 w‖ * ((1 + |x|) * Real.exp (-x)) := by
      rw [norm_mul]
      refine le_trans (mul_le_mul_of_nonneg_right (le_trans b1
        (mul_le_mul_of_nonneg_right hC2 hR)) (norm_nonneg (G 0 0 w))) (le_of_eq ?_)
      ring
    have e2 : ‖iteratedDeriv l (E_sh2 B) x * G 0 1 w‖
        ≤ E_shC l B * ‖G 0 1 w‖ * ((1 + |x|) * Real.exp (-x)) := by
      rw [norm_mul]
      refine le_trans (mul_le_mul_of_nonneg_right (le_trans b2
        (mul_le_mul_of_nonneg_right hC5 hR)) (norm_nonneg (G 0 1 w))) (le_of_eq ?_)
      ring
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add e1 e2) ?_
    exact le_of_eq (by ring)
  · exact E_tcLambda_shape_ge G B w hB0 hB1 l x hxge


/-! ## The layer `F₂` on the cusp-`0` neighbourhood `E` -/

/-- The threshold of the cusp expansion of `z ↦ K(w,z)` on `E`, from `ERegimes`. -/
def E_Bw (N₀ : ℝ) (w : ℍ) : ℝ := (scale w) ^ N₀

/-- The `trunc` piece of the layer, split at the threshold `(scale w)^{N₀}` instead of at `1`:
the contribution of `∫_1^∞` of the kernel with the non-decaying part `Aexp` subtracted beyond the
threshold.  This is exactly the object estimated by `Work.Asymptotics.E_tail_seminorm`. -/
def E_TailT (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (N₀ : ℝ) (w : ℍ) (r : ℝ) : ℂ :=
  sinSq r * tailIntegral (fun t : ℝ => if t < E_Bw N₀ w then Kaxis (Kfun ℓ d) w t
    else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t) (r ^ 2)

/-- The layer `F₂` (CKMRV (5.2)--(5.3), with the contour split at the threshold
`B = (scale w)^{N₀}` of `Work.Asymptotics.ERegimes`): `low + trunc + closed form of the
non-decaying tail`. -/
def E_Expr (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (N₀ : ℝ) (w : ℍ) (r : ℝ) : ℂ :=
  layerLow ℓ d w r + E_TailT ℓ d N₀ w r + E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w r

/-- The region where the layer is given by the convergent decomposition `E_Expr`: either the
weighted Gaussian makes the integral converge (`2 < r²`), or the kernel has no `e^{2πt}` term at
all (which happens in dimension `8`, where `Gcusp ℓ 8 1 j = 0`). -/
def E_R (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) : Prop :=
  2 < r ^ 2 ∨ (Gcusp ℓ d 1 0 w = 0 ∧ Gcusp ℓ d 1 1 w = 0)

/-- The layer fed to `Work.Asymptotics.E_kernelTransform_seminorm_of_layer`: `E_Expr` on the
convergence region, and `0` outside it.  The value `0` at `r = 0` is forced (the analytic
continuation takes a non-zero value there in dimension `24`, while
`kernelTransform K w 0 = 4 sin²(0)·⋯ = 0`), and the gap at the threshold `r² = 2` is harmless:
the seminorm bound is required for the punctured layer itself. -/
def E_F₂ (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (N₀ : ℝ) (w : ℍ) (r : ℝ) : ℂ := by
  classical
  exact if r ≠ 0 ∧ E_R ℓ d w r then E_Expr ℓ d N₀ w r else 0

lemma E_R_iff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) :
    E_R ℓ d w r ↔ 2 < r ^ 2 ∨ (Gcusp ℓ d 1 0 w = 0 ∧ Gcusp ℓ d 1 1 w = 0) := Iff.rfl

lemma E_F₂_of_R (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (N₀ : ℝ) (w : ℍ) (r : ℝ)
    (h : r ≠ 0 ∧ E_R ℓ d w r) : E_F₂ ℓ d N₀ w r = E_Expr ℓ d N₀ w r := by
  classical
  rw [E_F₂]; exact if_pos h

lemma E_F₂_of_not_R (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (N₀ : ℝ) (w : ℍ) (r : ℝ)
    (h : ¬ (r ≠ 0 ∧ E_R ℓ d w r)) : E_F₂ ℓ d N₀ w r = 0 := by
  classical
  rw [E_F₂]; exact if_neg h

/-- In dimension `8` the kernel has no `e^{2πt}` term, so the region condition `E_R` is
automatic away from `r = 0`. -/
lemma E_R_eight {ℓ : Work.Kernels.LogLambdaData} {w : ℍ} {r : ℝ} :
    E_R ℓ 8 w r := by
  refine Or.inr ⟨?_, ?_⟩ <;> simp [Gcusp, Gcusp8]

lemma E_Gcusp_one_zero {ℓ : Work.Kernels.LogLambdaData} {w : ℍ} (j : Fin 2) :
    Gcusp ℓ 8 1 j w = 0 := by
  simp [Gcusp, Gcusp8]

end Work.Asymptotics
