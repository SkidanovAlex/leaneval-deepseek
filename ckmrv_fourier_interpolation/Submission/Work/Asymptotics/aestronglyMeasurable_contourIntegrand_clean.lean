/-
# Measurability of the CKMRV contour integrand in the contour variable

The parametric-integral theory of `Work.Asymptotics.ParamIntegral` and
`Work.Asymptotics.Holomorphy` requires, for every `z` on the relevant open set, the a.e. strong
measurability of the integrand

  `t ↦ K(z, it) e^{-π r² t}`   on `(0, ∞)`

(this is the hypothesis `hmeas` of `Work.Asymptotics.mdifferentiableAt_kernelTransform`).  This
file discharges it for the CKMRV kernel `K^{(8)}` by exhibiting the integrand as a composition
of explicitly measurable maps.

The two ingredients are:

* `Work.Asymptotics.measurable_Kfun_snd` — `w ↦ K^{(8)}(τ, w)` is measurable on `ℍ`; this is
  proved entrywise from the explicit formula of `Work.Kernels.Kfun` (a finite sum of products of
  the Eisenstein series, `Δ`, the `j`-invariant, the `E₂|₂S` translate, Jacobi's theta functions
  and the logarithm data `𝓛`, `𝓛_S`), all of which are continuous, hence measurable;
* `Work.Asymptotics.measurable_Kaxis_of_measurable` — `t ↦ K(τ, it)` is measurable whenever
  `w ↦ K(τ, w)` is: the point `it` is `Work.Kernels.imagAxis t _`, whose `ℂ`-image `t ↦ t * I`
  is continuous, and `ℍ → ℂ` is a measurable embedding.

Nothing here uses the *cleanliness* of the contour: measurability is unconditional, which is why
this lemma carries no hypotheses beyond the data.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.Basic

noncomputable section

open UpperHalfPlane MeasureTheory Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## Measurability of the classical functions -/

lemma measurable_E2Fun : Measurable E2Fun :=
  ClassicalFacts.E2Fun_mem_InP.1.continuous.measurable

lemma measurable_E4Fun : Measurable E4Fun :=
  ClassicalFacts.E4Fun_mem_InP.1.continuous.measurable

lemma measurable_E6Fun : Measurable E6Fun :=
  ClassicalFacts.E6Fun_mem_InP.1.continuous.measurable

lemma measurable_DeltaFun : Measurable DeltaFun :=
  ClassicalFacts.DeltaFun_mem_InP.1.continuous.measurable

lemma measurable_E8Fun : Measurable E8Fun := by
  unfold E8Fun; exact measurable_E4Fun.pow_const 2

lemma measurable_E10Fun : Measurable E10Fun := by
  unfold E10Fun; exact measurable_E4Fun.mul measurable_E6Fun

lemma measurable_UFun' : Measurable UFun := by
  unfold UFun; exact (ClassicalFacts.theta00Fun_mem_InP.1.continuous.measurable).pow_const 4

lemma measurable_WFun' : Measurable WFun := by
  unfold WFun; exact (ClassicalFacts.theta01Fun_mem_InP.1.continuous.measurable).pow_const 4

lemma measurable_VFun' : Measurable VFun := by
  unfold VFun; exact (ClassicalFacts.theta10Fun_mem_InP.1.continuous.measurable).pow_const 4

/-- `E₂|₂S = E₂ - 6i/(π τ)` is measurable on `ℍ`. -/
lemma measurable_E2S : Measurable E2S := by
  have h : E2S = fun z : ℍ => E2Fun z - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)) := by
    funext z; exact TildeFacts.E2S_eq z
  rw [h]
  refine Measurable.sub measurable_E2Fun ?_
  refine Measurable.div measurable_const ?_
  exact measurable_const.mul UpperHalfPlane.continuous_coe.measurable

/-! ## Measurability of `K^{(8)}(τ, ·)` -/

lemma measurable_fk8 : Measurable (fun w : ℍ => fk 8 w) := by
  simp only [fk]; norm_num; exact measurable_E8Fun

lemma measurable_fk10 : Measurable (fun w : ℍ => fk 10 w) := by
  simp only [fk]; norm_num; exact measurable_E10Fun

lemma measurable_fk6 : Measurable (fun w : ℍ => fk 6 w) := by
  simp only [fk]; norm_num; exact measurable_E6Fun

lemma measurable_fk12 : Measurable (fun w : ℍ => fk 12 w) := by
  simp only [fk]; norm_num; exact measurable_DeltaFun

/-- The entries of the diagonal matrix `Π_{v}(w) = diag(f_{v i}(w))` are measurable. -/
lemma measurable_PiMat_entry (v : Fin 3 → ℤ) (k l : Fin 3)
    (hv : ∀ i, Measurable (fun w : ℍ => fk (v i) w)) :
    Measurable (fun w : ℍ => PiMat v w k l) := by
  by_cases h : k = l
  · rw [show (fun w : ℍ => PiMat v w k l) = fun w => fk (v k) w from by
      funext w; simp only [PiMat, Matrix.diagonal_apply, if_pos h]]
    exact hv k
  · rw [show (fun w : ℍ => PiMat v w k l) = fun w => (0 : ℂ) from by
      funext w; simp only [PiMat, Matrix.diagonal_apply, if_neg h]]
    exact measurable_const

lemma measurable_fk_list_12_10_8 :
    ∀ i : Fin 3, Measurable (fun w : ℍ => fk ((![12, 10, 8] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    first | exact measurable_fk12 | exact measurable_fk10 | exact measurable_fk8

lemma measurable_fk_list_10_8_6 :
    ∀ i : Fin 3, Measurable (fun w : ℍ => fk ((![10, 8, 6] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    first | exact measurable_fk10 | exact measurable_fk8 | exact measurable_fk6

/-- Each entry of `Υ_+^{(8)}(τ, ·)` is measurable. -/
lemma measurable_UpsilonPlus_8_entry (τ : ℍ) (i j : Fin 3) :
    Measurable (fun w : ℍ => UpsilonPlus 8 τ w i j) := by
  have hPi : ∀ k l : Fin 3, Measurable (fun w : ℍ => PiMat ![12, 10, 8] w k l) :=
    fun k l => measurable_PiMat_entry _ k l measurable_fk_list_12_10_8
  fin_cases i <;> fin_cases j <;>
    simp only [UpsilonPlus, reduceIte, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_three, Matrix.cons_val_fin_one,
      Matrix.empty_val'] <;>
    fun_prop (disch := assumption)

/-- Each entry of `Υ_-^{(8)}(τ, ·)` is measurable. -/
lemma measurable_UpsilonMinus_8_entry (τ : ℍ) (i j : Fin 3) :
    Measurable (fun w : ℍ => UpsilonMinus 8 τ w i j) := by
  have hPi : ∀ k l : Fin 3, Measurable (fun w : ℍ => PiMat ![10, 8, 6] w k l) :=
    fun k l => measurable_PiMat_entry _ k l measurable_fk_list_10_8_6
  fin_cases i <;> fin_cases j <;>
    simp only [UpsilonMinus, reduceIte, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_three, Matrix.cons_val_fin_one,
      Matrix.empty_val'] <;>
    fun_prop (disch := assumption)

/-- Each entry of `φ̃(w) = (w², w²(E₂|₂S)(w), w²(E₂|₂S)(w)²)` is measurable. -/
lemma measurable_phitVec (j : Fin 3) : Measurable (fun w : ℍ => phitVec w j) := by
  have h2s : Measurable (fun w : ℍ => E2S w) := measurable_E2S
  fin_cases j <;>
    simp only [phitVec, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    fun_prop (disch := assumption)

/-- Each entry of `ψ̃(w) = (𝓛(w), W(w), U(w)² - V(w)²)` is measurable. -/
lemma measurable_psitVec (ℓ : LogLambdaData) (j : Fin 3) :
    Measurable (fun w : ℍ => psitVec ℓ w j) := by
  have hL : Measurable (fun w : ℍ => ℓ.L w) := ℓ.holo.continuous.measurable
  have hU : Measurable (fun w : ℍ => UFun w) := measurable_UFun'
  have hW : Measurable (fun w : ℍ => WFun w) := measurable_WFun'
  have hV : Measurable (fun w : ℍ => VFun w) := measurable_VFun'
  fin_cases j <;>
    simp only [psitVec, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    fun_prop (disch := assumption)

/-- **`w ↦ K^{(8)}(τ,w)` is measurable on `ℍ`.** -/
lemma measurable_Kfun_snd (ℓ : LogLambdaData) (τ : ℍ) :
    Measurable (fun w : ℍ => Kfun ℓ 8 τ w) := by
  have hUP : ∀ i j : Fin 3, Measurable (fun w : ℍ => UpsilonPlus 8 τ w i j) :=
    fun i j => measurable_UpsilonPlus_8_entry τ i j
  have hUM : ∀ i j : Fin 3, Measurable (fun w : ℍ => UpsilonMinus 8 τ w i j) :=
    fun i j => measurable_UpsilonMinus_8_entry τ i j
  have hphit : ∀ j : Fin 3, Measurable (fun w : ℍ => phitVec w j) := measurable_phitVec
  have hpsit : ∀ j : Fin 3, Measurable (fun w : ℍ => psitVec ℓ w j) := measurable_psitVec ℓ
  unfold Kfun KPlus KMinus
  fun_prop (disch := assumption)

/-! ## Measurability along the contour -/

/-- **`t ↦ K(τ, it)` is measurable on `ℝ`** whenever `w ↦ K(τ,w)` is measurable on `ℍ`. -/
lemma measurable_Kaxis_of_measurable (K : ℍ → ℍ → ℂ) (τ : ℍ) (hK : Measurable (K τ)) :
    Measurable (fun t : ℝ => Kaxis K τ t) := by
  have hcoec : Measurable (fun a : ↥(Set.Ioi (0 : ℝ)) => (a.1 : ℂ) * Complex.I) := by
    have h1 : Measurable (fun a : ↥(Set.Ioi (0 : ℝ)) => (a.1 : ℝ)) := measurable_subtype_coe
    exact (Complex.continuous_ofReal.measurable.comp h1).mul measurable_const
  have himag : Measurable (fun a : ↥(Set.Ioi (0 : ℝ)) => imagAxis a.1 a.2) :=
    (MeasurableEmbedding.measurable_comp_iff UpperHalfPlane.measurableEmbedding_coe).mp hcoec
  have hf : Measurable (fun a : ↥(Set.Ioi (0 : ℝ)) => K τ (imagAxis a.1 a.2)) := hK.comp himag
  exact Measurable.dite hf measurable_const measurableSet_Ioi

theorem aestronglyMeasurable_contourIntegrand_clean (ℓ : Work.Kernels.LogLambdaData) (r : ℝ)
    (z : ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => Work.Asymptotics.contourIntegrand (Work.Kernels.Kfun ℓ 8) r z t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hK : Measurable (fun w : ℍ => Kfun ℓ 8 (UpperHalfPlane.ofComplex z) w) :=
    measurable_Kfun_snd ℓ _
  have h1 : Measurable (fun t : ℝ => contourKernel (Kfun ℓ 8) z t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ 8) (UpperHalfPlane.ofComplex z) hK
  have h2 : Measurable (fun t : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    fun_prop
  have h3 : Measurable (fun t : ℝ => contourIntegrand (Kfun ℓ 8) r z t) := h1.mul h2
  exact h3.stronglyMeasurable.aestronglyMeasurable

end Work.Asymptotics
