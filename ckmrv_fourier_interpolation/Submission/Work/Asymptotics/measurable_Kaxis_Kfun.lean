/-
# Measurability of the contour integrand `t ↦ K^{(d)}(τ, it)` in dimensions 8 and 24

The file `Submission.Work.Asymptotics.aestronglyMeasurable_contourIntegrand_clean` proves that
`w ↦ K^{(8)}(τ,w)` is measurable on `ℍ`, and deduces that `t ↦ K^{(8)}(τ,it)` is measurable on
`ℝ`.  Its proof works entrywise from the explicit formula of `Work.Kernels.Kfun`, using that the
entries of `Υ_±^{(8)}` are built from the (continuous, hence measurable) functions `E₂`, `E₄`,
`E₆`, `Δ`, the `j`-invariant, `E₂|₂S`, Jacobi's theta functions and the logarithm data `𝓛`,
`𝓛_S`.

Here we record the same statement for the second relevant dimension `d = 24`, so that it can be
applied to *both* kernels used in the paper, and conclude the measurability of
`t ↦ K^{(d)}(τ, it)` for `d ∈ {8, 24}`.

The only new ingredients are the entries of `Υ_+^{(24)}` and `Υ_-^{(24)}`
(`Work.Kernels.UpsilonPlus`, `Work.Kernels.UpsilonMinus`), whose `z`-dependence enters through
`Δ(z)`, `j(z)`, `(j(τ) - j(z))^{-1}` and the diagonal matrices `Π_{4,2,0}(z)`, `Π_{2,0,-2}(z)`,
i.e. through the functions `fk 4, fk 2, fk 0, fk (-2)` (which are `E₄`, `E₁₄/Δ`, `1`, `E₁₀/Δ`).
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.aestronglyMeasurable_contourIntegrand_clean

noncomputable section

open UpperHalfPlane MeasureTheory Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## Measurability of the functions entering `Υ_±^{(24)}` -/

lemma measurable_E14Fun_KaxisKfun : Measurable E14Fun := by
  unfold E14Fun
  exact (measurable_E4Fun.pow_const 2).mul measurable_E6Fun

lemma measurable_jInvariantFun_KaxisKfun : Measurable jInvariantFun := by
  unfold jInvariantFun
  exact (measurable_E4Fun.pow_const 3).div measurable_DeltaFun

/-! The `fk`-values appearing on the `z`-side of `Υ_+^{(24)} · Π_{4,2,0}(z)` and
`Υ_-^{(24)} · Π_{2,0,-2}(z)`. -/

lemma measurable_fk14_KaxisKfun : Measurable (fun w : ℍ => fk 14 w) := by
  simp only [fk]; norm_num; exact measurable_E14Fun_KaxisKfun

lemma measurable_fk4_KaxisKfun : Measurable (fun w : ℍ => fk 4 w) := by
  simp only [fk]; norm_num; exact measurable_E4Fun

lemma measurable_fk2_KaxisKfun : Measurable (fun w : ℍ => fk 2 w) := by
  simp only [fk]; norm_num
  exact measurable_E14Fun_KaxisKfun.div measurable_DeltaFun

lemma measurable_fk0_KaxisKfun : Measurable (fun w : ℍ => fk 0 w) := by
  simp only [fk]; norm_num

lemma measurable_fkneg2_KaxisKfun : Measurable (fun w : ℍ => fk (-2) w) := by
  simp only [fk]; norm_num
  exact measurable_E10Fun.div measurable_DeltaFun

lemma measurable_fk_list_4_2_0_KaxisKfun :
    ∀ i : Fin 3, Measurable (fun w : ℍ => fk ((![4, 2, 0] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    first | exact measurable_fk4_KaxisKfun | exact measurable_fk2_KaxisKfun | exact measurable_fk0_KaxisKfun

lemma measurable_fk_list_2_0_neg2_KaxisKfun :
    ∀ i : Fin 3, Measurable (fun w : ℍ => fk ((![2, 0, -2] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    first | exact measurable_fk2_KaxisKfun | exact measurable_fk0_KaxisKfun | exact measurable_fkneg2_KaxisKfun

/-! ## Measurability of the entries of `Υ_±^{(24)}(τ, ·)` -/

/-- Each entry of `Υ_+^{(24)}(τ, ·)` is measurable: the `z`-dependence enters only through
`Δ(z)`, `j(z)`, `(j(τ)-j(z))^{-1}` and the diagonal matrix `Π_{4,2,0}(z)`. -/
lemma measurable_UpsilonPlus_24_entry (τ : ℍ) (i j : Fin 3) :
    Measurable (fun w : ℍ => UpsilonPlus 24 τ w i j) := by
  have hD : Measurable (fun w : ℍ => DeltaFun w) := measurable_DeltaFun
  have hJ : Measurable (fun w : ℍ => jInvariantFun w) := measurable_jInvariantFun_KaxisKfun
  have hM : ∀ l k : Fin 3, Measurable (fun w : ℍ =>
      (!![6, 0, c1728 * (jInvariantFun τ - jInvariantFun w)⁻¹ - 6;
         -12 * jInvariantFun τ + 5 * c1728, -2 * c1728 * (jInvariantFun τ - jInvariantFun w)⁻¹,
           12 * jInvariantFun τ - 7 * c1728;
         c1728 * (jInvariantFun τ - jInvariantFun w)⁻¹ + 6, 0, -6] :
        Matrix (Fin 3) (Fin 3) ℂ) l k) := by
    intro l k
    fin_cases l <;> fin_cases k <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val'] <;>
      fun_prop (disch := assumption)
  have hB : ∀ k j : Fin 3, Measurable (fun w : ℍ => PiMat ![4, 2, 0] w k j) :=
    fun k j => measurable_PiMat_entry _ k j measurable_fk_list_4_2_0_KaxisKfun
  have hA : ∀ i l : Fin 3, Measurable (fun w : ℍ => PiMat ![14, 12, 10] τ i l) :=
    fun i l => measurable_const
  simp only [UpsilonPlus, reduceIte]
  simp only [if_neg (show ¬ ((24:ℕ) = 8) by decide)]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three]
  fun_prop (disch := assumption)

/-- Each entry of `Υ_-^{(24)}(τ, ·)` is measurable. -/
lemma measurable_UpsilonMinus_24_entry (τ : ℍ) (i j : Fin 3) :
    Measurable (fun w : ℍ => UpsilonMinus 24 τ w i j) := by
  have hD : Measurable (fun w : ℍ => DeltaFun w) := measurable_DeltaFun
  have hJ : Measurable (fun w : ℍ => jInvariantFun w) := measurable_jInvariantFun_KaxisKfun
  have hM : ∀ l k : Fin 3, Measurable (fun w : ℍ =>
      (!![-2 * c1728, -2 * c1728 * (jInvariantFun τ - jInvariantFun w), 0;
          0, jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun w), -1;
          0, c1728 - 2 * (jInvariantFun τ - jInvariantFun w) - jInvariantFun τ, 1] :
        Matrix (Fin 3) (Fin 3) ℂ) l k) := by
    intro l k
    fin_cases l <;> fin_cases k <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val'] <;>
      fun_prop (disch := assumption)
  have hB : ∀ k j : Fin 3, Measurable (fun w : ℍ => PiMat ![2, 0, -2] w k j) :=
    fun k j => measurable_PiMat_entry _ k j measurable_fk_list_2_0_neg2_KaxisKfun
  have hA : ∀ i l : Fin 3, Measurable (fun w : ℍ => PiMat ![12, 10, 8] τ i l) :=
    fun i l => measurable_const
  simp only [UpsilonMinus, reduceIte]
  simp only [if_neg (show ¬ ((24:ℕ) = 8) by decide)]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three]
  fun_prop (disch := assumption)

/-! ## Measurability of `w ↦ K^{(24)}(τ,w)` -/

/-- **`w ↦ K^{(24)}(τ,w)` is measurable on `ℍ`.**  Same proof as the `d = 8` case of
`Work.Asymptotics.measurable_Kfun_snd`, with the entries of `Υ_±^{(24)}`. -/
lemma measurable_Kfun_snd_twentyfour (ℓ : LogLambdaData) (τ : ℍ) :
    Measurable (fun w : ℍ => Kfun ℓ 24 τ w) := by
  have hUP : ∀ i j : Fin 3, Measurable (fun w : ℍ => UpsilonPlus 24 τ w i j) :=
    fun i j => measurable_UpsilonPlus_24_entry τ i j
  have hUM : ∀ i j : Fin 3, Measurable (fun w : ℍ => UpsilonMinus 24 τ w i j) :=
    fun i j => measurable_UpsilonMinus_24_entry τ i j
  have hphit : ∀ j : Fin 3, Measurable (fun w : ℍ => phitVec w j) := measurable_phitVec
  have hpsit : ∀ j : Fin 3, Measurable (fun w : ℍ => psitVec ℓ w j) := measurable_psitVec ℓ
  unfold Kfun KPlus KMinus
  fun_prop (disch := assumption)

/-! ## The requested statement -/

lemma measurable_Kaxis_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) := by
  rcases hd with rfl | rfl
  · exact measurable_Kaxis_of_measurable (Kfun ℓ 8) τ (measurable_Kfun_snd ℓ τ)
  · exact measurable_Kaxis_of_measurable (Kfun ℓ 24) τ (measurable_Kfun_snd_twentyfour ℓ τ)

end Work.Asymptotics
