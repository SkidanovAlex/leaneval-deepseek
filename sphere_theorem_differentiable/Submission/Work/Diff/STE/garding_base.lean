import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CubeSplit
import Submission.Work.Diff.STE.cube_fubini
import Submission.Work.Diff.STE.pd_integral_zero
import Submission.Work.Diff.STE.pd_fourierExp
import Submission.Work.Diff.STE.fourierCoeff_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary helpers for the Gårding estimate on the torus

Small technical lemmas about `Work.Diff.STE.pd`, `pdR`, periodicity and integration over the
cube, used by `Submission/Work/Diff/STE/garding_estimate.lean`.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE

/-- `star` (complex conjugation) commutes with the partial derivative `pd`. -/
lemma ga_pd_star {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) {f : (ι → ℝ) → ℂ} {x : ι → ℝ} (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => star (f y)) x = star (pd i f x) := by
  have hfd : fderiv ℝ (fun y => star (f y)) x
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f x) := by
    have h := (Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
    have h2 : (fun y => star (f y)) = (⇑Complex.conjCLE ∘ f) := by
      funext y
      exact (starRingEnd_apply (f y)).symm.trans (Complex.conjCLE_apply (f y)).symm
    rw [h2]; exact h
  simp only [pd]
  rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, starRingEnd_apply]

/-- `pd` of a real-valued function, viewed as complex valued. -/
lemma ga_pd_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (F : (ι → ℝ) → ℝ) (x : ι → ℝ) (hF : DifferentiableAt ℝ F x) :
    pd i (fun y => (F y : ℂ)) x = (pdR i F x : ℂ) := by
  have hfd : fderiv ℝ (fun y => (F y : ℂ)) x
      = Complex.ofRealCLM.comp (fderiv ℝ F x) := by
    have h := (Complex.ofRealCLM.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
    have h2 : (fun y => (F y : ℂ)) = (⇑Complex.ofRealCLM ∘ F) := rfl
    rw [h2]; exact h
  simp only [pd, pdR]
  rw [hfd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- The partial derivative of a `C^{n+1}` function is `C^n`. -/
lemma ga_contDiff_pd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (n+1) f) (i : ι) :
    ContDiff ℝ n (pd i f) := by
  have h : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (m := n) (le_refl _)
  have h2 : ContDiff ℝ n (fun x => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) := by
    have h3 := (ContinuousLinearMap.apply ℝ ℂ (Pi.single i (1 : ℝ) : ι → ℝ)).contDiff.comp h
    simpa [Function.comp_def, ContinuousLinearMap.apply_apply] using h3
  exact h2

/-- The partial derivative of a periodic function is periodic in every coordinate. -/
lemma ga_periodicIn_pd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) {f : (ι → ℝ) → ℂ} (hper : Periodic1 f) (hf : Differentiable ℝ f) :
    PeriodicIn i (pd j f) := by
  have hfun : f = fun y => f (y + (Pi.single i (1 : ℝ) : ι → ℝ)) := by
    funext y; exact (hper i y).symm
  intro x
  have h1 : HasFDerivAt (fun y : ι → ℝ => y + (Pi.single i (1 : ℝ) : ι → ℝ))
      (ContinuousLinearMap.id ℝ (ι → ℝ)) x := by
    have hid : HasFDerivAt (fun y : ι → ℝ => y) (ContinuousLinearMap.id ℝ (ι → ℝ)) x :=
      hasFDerivAt_id x
    simpa using hid.add_const (Pi.single i (1 : ℝ) : ι → ℝ)
  have h2 : HasFDerivAt (fun y => f (y + (Pi.single i (1 : ℝ) : ι → ℝ)))
      ((fderiv ℝ f (x + (Pi.single i (1 : ℝ) : ι → ℝ))).comp
        (ContinuousLinearMap.id ℝ (ι → ℝ))) x :=
    (hf (x + (Pi.single i (1 : ℝ) : ι → ℝ))).hasFDerivAt.comp x h1
  rw [ContinuousLinearMap.comp_id] at h2
  have h3 : fderiv ℝ (fun y => f (y + (Pi.single i (1 : ℝ) : ι → ℝ))) x
      = fderiv ℝ f (x + (Pi.single i (1 : ℝ) : ι → ℝ)) := h2.fderiv
  have key : fderiv ℝ (fun y => f (y + (Pi.single i (1 : ℝ) : ι → ℝ))) x = fderiv ℝ f x :=
    (congrArg (fun g => fderiv ℝ g x) hfun).symm
  simp only [pd]
  rw [← h3, key]

/-- Conjugation is smooth. -/
lemma ga_contDiff_star {ι : Type*} [Fintype ι] {n : WithTop ℕ∞} {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (fun x => star (f x)) := by
  have h2 : ContDiff ℝ n (fun x => Complex.conjCLE (f x)) :=
    Complex.conjCLE.contDiff.comp hf
  have h3 : (fun x => Complex.conjCLE (f x)) = fun x => star (f x) := by
    funext x; rw [Complex.conjCLE_apply, starRingEnd_apply]
  rwa [h3] at h2

/-- The coercion `ℝ → ℂ` of a smooth function is smooth. -/
lemma ga_contDiff_ofReal {ι : Type*} [Fintype ι] {n : WithTop ℕ∞} {F : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ n F) : ContDiff ℝ n (fun x => (F x : ℂ)) := by
  have h3 := Complex.ofRealCLM.contDiff.comp hF
  simpa [Function.comp_def, Complex.ofRealCLM_apply] using h3

/-- Periodicity of `star ∘ f`. -/
lemma ga_periodicIn_star {ι : Type*} [DecidableEq ι] (i : ι) {f : (ι → ℝ) → ℂ}
    (hper : Periodic1 f) :
    PeriodicIn i (fun x => star (f x)) := by
  intro x
  change star (f (x + Pi.single i 1)) = star (f x)
  rw [hper i x]

/-- Periodicity of a product. -/
lemma ga_periodicIn_mul {ι : Type*} [DecidableEq ι] (i : ι) {f g : (ι → ℝ) → ℂ}
    (hf : PeriodicIn i f) (hg : PeriodicIn i g) :
    PeriodicIn i (fun x => f x * g x) := by
  intro x
  change f (x + Pi.single i 1) * g (x + Pi.single i 1) = f x * g x
  rw [hf x, hg x]

/-- Periodicity of the complex coercion of a real periodic function. -/
lemma ga_periodicIn_ofReal {ι : Type*} [DecidableEq ι] (i : ι) {F : (ι → ℝ) → ℝ}
    (hF : Periodic1 F) :
    PeriodicIn i (fun x => (F x : ℂ)) := by
  intro x
  change ((F (x + Pi.single i 1) : ℝ) : ℂ) = ((F x : ℝ) : ℂ)
  rw [hF i x]

/-- `pdR` of a `C¹` function is continuous. -/
lemma ga_continuous_pdR {ι : Type*} [Fintype ι] [DecidableEq ι] {F : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (i : ι) : Continuous (pdR i F) := by
  have h := hF.continuous_fderiv one_ne_zero
  have h2 : Continuous (fun x : ι → ℝ => (fderiv ℝ F x) (Pi.single i (1 : ℝ))) :=
    h.clm_apply continuous_const
  exact h2

/-- The real part of a Bochner integral is the integral of the real part. -/
lemma ga_re_integral {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℂ)
    (hF : Integrable F (volume.restrict unitCube)) :
    Complex.re (∫ x in unitCube, F x) = ∫ x in unitCube, (F x).re := by
  have h := Complex.reCLM.integral_comp_comm hF
  simpa [Complex.reCLM_apply] using h.symm

/-- Integration by parts on the cube for functions periodic in the coordinate `i`. -/
theorem ga_ibp_pd_unitCube {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f g : (ι → ℝ) → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : PeriodicIn i f) (hgp : PeriodicIn i g) :
    ∫ x in unitCube, f x * pd i g x = - ∫ x in unitCube, pd i f x * g x := by
  have hleib : ∀ x : ι → ℝ, f x * pd i g x
      = pd i (fun y => f y * g y) x - pd i f x * g x := by
    intro x
    rw [pd_mul i (hf.differentiable_one.differentiableAt) (hg.differentiable_one.differentiableAt)]
    ring
  have hfg : ContDiff ℝ 1 (fun y => f y * g y) := hf.mul hg
  have hfgper : PeriodicIn i (fun y => f y * g y) := by
    intro x
    change f (x + Pi.single i 1) * g (x + Pi.single i 1) = f x * g x
    rw [hfp x, hgp x]
  have h1 : Integrable (fun x => pd i (fun y => f y * g y) x) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous (continuous_pd hfg i)
  have h2 : Integrable (fun x => pd i f x * g x) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous ((continuous_pd hf i).mul hg.continuous)
  rw [funext hleib, integral_sub h1 h2, integral_pd_unitCube_zero i hfg hfgper]
  ring

/-- Continuity of the complex coercion of a continuous real function. -/
lemma ga_continuous_ofReal {ι : Type*} {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Continuous (fun x => (F x : ℂ)) :=
  Complex.ofRealCLM.continuous.comp hF

/-- The real part of a finite sum. -/
lemma ga_re_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    Complex.re (∑ i, f i) = ∑ i, Complex.re (f i) := by
  rw [← Complex.reCLM_apply, map_sum Complex.reCLM f Finset.univ]
  simp [Complex.reCLM_apply]

/-- `∑ (-a - b) = -∑ a - ∑ b`. -/
lemma ga_sum_neg_sub {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i, (- a i - b i)) = -(∑ i, a i) - (∑ i, b i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- A continuous real valued function is integrable on the (bounded) unit cube. -/
lemma ga_integrableOn_unitCube_real {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (hF : Continuous F) : Integrable F (volume.restrict unitCube) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

/-- Young's inequality with an arbitrary positive parameter. -/
lemma ga_young {K ε p q : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    K * (p * q) ≤ (K * ε / 2) * p ^ 2 + (K / (2 * ε)) * q ^ 2 := by
  rw [← sub_nonneg]
  have h : (K * ε / 2) * p ^ 2 + (K / (2 * ε)) * q ^ 2 - K * (p * q)
      = (K * (ε * p - q) ^ 2) / (2 * ε) := by
    field_simp
    ring
  rw [h]
  exact div_nonneg (mul_nonneg hK (sq_nonneg _)) (by linarith)

/-- Factorisation of the double sum of `-A * F d - B * G` over a finite type. -/
lemma ga_double_sum_factor {ι : Type*} [Fintype ι] (A B G : ℝ) (F : ι → ℝ) :
    (∑ _c : ι, ∑ d : ι, (-A * F d - B * G))
      = -(A * ((Fintype.card ι : ℝ) * (∑ d, F d)))
        - B * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * G)) := by
  have h1 : ∀ c : ι, (∑ d : ι, (-A * F d - B * G))
      = -A * (∑ d, F d) - B * ((Fintype.card ι : ℝ) * G) := by
    intro c
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Work.Diff.STE
