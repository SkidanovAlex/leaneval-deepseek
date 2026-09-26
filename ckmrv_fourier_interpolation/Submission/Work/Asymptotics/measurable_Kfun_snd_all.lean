/-
# Measurability of `w ↦ K^{(d)}(τ,w)` in the second variable, for `d ∈ {8,24}`

The parametric-integral theory of the `low` part of the CKMRV layer needs the measurability of
the kernel along the contour, `t ↦ Kaxis (Kfun ℓ d) τ t`.  This reduces
(`Work.Asymptotics.measurable_Kaxis_of_measurable`) to the measurability in the second variable
of `w ↦ Kfun ℓ d τ w`.  The case `d = 8` is
`Work.Asymptotics.measurable_Kfun_snd`; here we add `d = 24` and combine the two.
-/
import Mathlib
import Submission.Work.Asymptotics.aestronglyMeasurable_contourIntegrand_clean

noncomputable section

open UpperHalfPlane MeasureTheory Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## Extra measurability of the classical functions -/

lemma measurable_E14Fun : Measurable E14Fun := by
  rw [show E14Fun = fun w : ℍ => E4Fun w ^ 2 * E6Fun w from rfl]
  exact (measurable_E4Fun.pow_const 2).mul measurable_E6Fun

lemma measurable_jInvariantFun : Measurable jInvariantFun := by
  rw [show jInvariantFun = fun w : ℍ => E4Fun w ^ 3 / DeltaFun w from rfl]
  exact (measurable_E4Fun.pow_const 3).div measurable_DeltaFun

lemma measurable_fk_neg2 : Measurable (fun w : ℍ => fk (-2) w) := by
  have h : (fun w : ℍ => fk (-2) w) = fun w : ℍ => E10Fun w / DeltaFun w := by
    funext w; simp only [fk]; norm_num
  rw [h]; exact measurable_E10Fun.div measurable_DeltaFun

lemma measurable_fk_0 : Measurable (fun w : ℍ => fk 0 w) := by
  have h : (fun w : ℍ => fk 0 w) = fun _ : ℍ => (1 : ℂ) := by
    funext w; simp only [fk]; norm_num
  rw [h]; exact measurable_const

lemma measurable_fk_2 : Measurable (fun w : ℍ => fk 2 w) := by
  have h : (fun w : ℍ => fk 2 w) = fun w : ℍ => E14Fun w / DeltaFun w := by
    funext w; simp only [fk]; norm_num
  rw [h]; exact measurable_E14Fun.div measurable_DeltaFun

lemma measurable_fk_4 : Measurable (fun w : ℍ => fk 4 w) := by
  have h : (fun w : ℍ => fk 4 w) = fun w : ℍ => E4Fun w := by
    funext w; simp only [fk]; norm_num
  rw [h]; exact measurable_E4Fun

lemma measurable_fk_8 : Measurable (fun w : ℍ => fk 8 w) := measurable_fk8

lemma measurable_fk_10 : Measurable (fun w : ℍ => fk 10 w) := measurable_fk10

lemma measurable_fk_12 : Measurable (fun w : ℍ => fk 12 w) := measurable_fk12

lemma measurable_fk_14 : Measurable (fun w : ℍ => fk 14 w) := by
  have h : (fun w : ℍ => fk 14 w) = fun w : ℍ => E14Fun w := by
    funext w; simp only [fk]; norm_num
  rw [h]; exact measurable_E14Fun

lemma meas_list_14_12_10 : ∀ i : Fin 3,
    Measurable (fun w : ℍ => fk ((![14, 12, 10] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    first | exact measurable_fk_14 | exact measurable_fk_12 | exact measurable_fk_10

lemma meas_list_12_10_8 : ∀ i : Fin 3,
    Measurable (fun w : ℍ => fk ((![12, 10, 8] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    first | exact measurable_fk_12 | exact measurable_fk_10 | exact measurable_fk_8

lemma meas_list_4_2_0 : ∀ i : Fin 3,
    Measurable (fun w : ℍ => fk ((![4, 2, 0] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    first | exact measurable_fk_4 | exact measurable_fk_2 | exact measurable_fk_0

lemma meas_list_2_0_neg2 : ∀ i : Fin 3,
    Measurable (fun w : ℍ => fk ((![2, 0, -2] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    first | exact measurable_fk_2 | exact measurable_fk_0 | exact measurable_fk_neg2

/-! ## The `d = 24` coefficient matrices -/

lemma measurable_UpsilonPlus_24_entry (τ : ℍ) (i j : Fin 3) :
    Measurable (fun w : ℍ => UpsilonPlus 24 τ w i j) := by
  have hPi : ∀ k l : Fin 3, Measurable (fun w : ℍ => PiMat ![4, 2, 0] w k l) :=
    fun k l => measurable_PiMat_entry _ k l meas_list_4_2_0
  have hD : Measurable DeltaFun := measurable_DeltaFun
  have hj : Measurable jInvariantFun := measurable_jInvariantFun
  have hfun : (fun w : ℍ => UpsilonPlus 24 τ w i j)
      = fun w : ℍ => (((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun w)⁻¹
          • (PiMat ![14, 12, 10] τ *
            !![6, 0, c1728 * (jInvariantFun τ - jInvariantFun w)⁻¹ - 6;
              -12 * jInvariantFun τ + 5 * c1728,
                -2 * c1728 * (jInvariantFun τ - jInvariantFun w)⁻¹,
                12 * jInvariantFun τ - 7 * c1728;
              c1728 * (jInvariantFun τ - jInvariantFun w)⁻¹ + 6, 0, -6] *
            PiMat ![4, 2, 0] w)) i j := by
    funext w
    simp only [UpsilonPlus, reduceIte]
    norm_num
  rw [hfun]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.sum_univ_three, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.vecHead, Matrix.vecTail] <;>
    fun_prop (disch := assumption)

lemma measurable_UpsilonMinus_24_entry (τ : ℍ) (i j : Fin 3) :
    Measurable (fun w : ℍ => UpsilonMinus 24 τ w i j) := by
  have hPi : ∀ k l : Fin 3, Measurable (fun w : ℍ => PiMat ![2, 0, -2] w k l) :=
    fun k l => measurable_PiMat_entry _ k l meas_list_2_0_neg2
  have hD : Measurable DeltaFun := measurable_DeltaFun
  have hj : Measurable jInvariantFun := measurable_jInvariantFun
  have hfun : (fun w : ℍ => UpsilonMinus 24 τ w i j)
      = fun w : ℍ => (((2 : ℂ) * c1728 * (Real.pi : ℂ) * DeltaFun w
            * (jInvariantFun τ - jInvariantFun w))⁻¹
          • (PiMat ![12, 10, 8] τ *
            !![-2 * c1728, -2 * c1728 * (jInvariantFun τ - jInvariantFun w), 0;
              0, jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun w), -1;
              0, c1728 - 2 * (jInvariantFun τ - jInvariantFun w) - jInvariantFun τ, 1] *
            PiMat ![2, 0, -2] w)) i j := by
    funext w
    simp only [UpsilonMinus, reduceIte]
    norm_num
  rw [hfun]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.sum_univ_three, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.vecHead, Matrix.vecTail] <;>
    fun_prop (disch := assumption)

/-- `KPlus 24 τ ·` is measurable. -/
lemma measurable_KPlus_24_snd (τ : ℍ) :
    Measurable (fun w : ℍ => KPlus 24 τ w) := by
  have hUP : ∀ i j : Fin 3, Measurable (fun w : ℍ => UpsilonPlus 24 τ w i j) :=
    fun i j => measurable_UpsilonPlus_24_entry τ i j
  have hphit : ∀ j : Fin 3, Measurable (fun w : ℍ => phitVec w j) := measurable_phitVec
  unfold KPlus
  fun_prop (disch := assumption)

/-- `KMinus ℓ 24 τ ·` is measurable. -/
lemma measurable_KMinus_24_snd (ℓ : LogLambdaData) (τ : ℍ) :
    Measurable (fun w : ℍ => KMinus ℓ 24 τ w) := by
  have hUM : ∀ i j : Fin 3, Measurable (fun w : ℍ => UpsilonMinus 24 τ w i j) :=
    fun i j => measurable_UpsilonMinus_24_entry τ i j
  have hpsit : ∀ j : Fin 3, Measurable (fun w : ℍ => psitVec ℓ w j) := measurable_psitVec ℓ
  unfold KMinus
  fun_prop (disch := assumption)

/-- **`w ↦ K^{(d)}(τ,w)` is measurable for `d ∈ {8,24}`.** -/
theorem measurable_Kfun_snd_all (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    Measurable (fun w : ℍ => Kfun ℓ d τ w) := by
  rcases hd with rfl | rfl
  · exact measurable_Kfun_snd ℓ τ
  · have h1 := measurable_KPlus_24_snd τ
    have h2 := measurable_KMinus_24_snd ℓ τ
    unfold Kfun
    exact (h1.add h2).div_const 2

end Work.Asymptotics
