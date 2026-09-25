/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `L²` bound for the adjoint field `czV`

For a compactly supported `C¹` field `φ` the `L²`-norm of the adjoint kernel field
`czV φ z l = ∫ ζ, bmKernel l (ζ - z) * star (czTheta φ ζ)` is controlled by the `L²`-norm of `φ`:

  `∫⁻ z, Σ_l ofReal ‖czV φ z l‖² ≤ ofReal (C²) · ∫⁻ z, Σ_i ofReal ‖φ i z‖²`.

The proof has two ingredients.

* `czV_eq_dCoord_bmPotential`: pointwise, `czV φ z l` is the sum over `i` of the `(1,0)`-derivative
  `∂_i (bmPotential (singleFam l (star ∘ φ_i)))` of the Bochner–Martinelli potential of the
  single-component family `singleFam l (star ∘ φ_i)`.  This is the analytic identity behind the
  duality argument: the adjoint is a sum of `∂`-potentials of the data.
* `czB_L2_bounded`: the already proved `L²` bound for `∂ (bmPotential ·)` on `C¹` compactly
  supported data.  Applied to a single-component family, and combined with Cauchy–Schwarz in the
  `l`-sum, it gives the claim.

-/
import Mathlib
import Submission.Work.NN.Core.czB_C0_defs
import Submission.Work.NN.Core.czB_L2_bounded
import Submission.Work.NN.Core.czB_L2_aux
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord_of_contDiff
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal Topology ContDiff

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-! ## Pointwise identities -/

/-- Cauchy–Schwarz: the squared norm of a sum of `n` vectors is at most `n` times the sum of the
squared norms. -/
lemma norm_sum_sq_le_card_mul {n : ℕ} (f : Fin n → ℂ) :
    ‖∑ i, f i‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
  have h2 : ‖∑ i, f i‖ ^ 2 ≤ (∑ i, ‖f i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (∑ i, ‖f i‖) ^ 2 ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) * ∑ i, ‖f i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_univ, Fintype.card_fin] at h3
  linarith

/-- `(ofReal ‖x‖)² = ofReal (‖x‖²)`. -/
lemma ofReal_norm_sq_eq (x : ℂ) :
    ENNReal.ofReal ‖x‖ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [pow_two, pow_two, ENNReal.ofReal_mul (norm_nonneg x)]

/-- **Pointwise description of the adjoint field.**  For a compactly supported `C¹` field `φ`,
`czV φ z l` is the sum of the `(1,0)`-derivatives of the Bochner–Martinelli potentials of the
single-component families `singleFam l (star ∘ φ_i)`. -/
theorem czV_eq_dCoord_bmPotential {n : ℕ} (hn : 0 < n)
    {φ : Fin n → (Fin n → ℂ) → ℂ} (hφ : ∀ i, ContDiff ℝ 1 (φ i))
    (hφc : ∀ i, HasCompactSupport (φ i)) (z : Fin n → ℂ) (l : Fin n) :
    czV φ z l = ∑ i, Work.CR.Flat.dCoord i
      (Work.CR.Flat.Cauchy.bmPotential (singleFam l (fun w => star (φ i w)))) z := by
  set A : Fin n → (Fin n → ℂ) → ℂ :=
    fun i w => Work.CR.Flat.dCoord i (fun w' => star (φ i w')) w with hA
  have hstr : ∀ i, ContDiff ℝ 1 (fun w => star (φ i w)) := by
    intro i
    have hstar : ContDiff ℝ 1 (fun z : ℂ => star z) := by
      have hh := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff (n := 1)
      rw [show (fun z : ℂ => star z) = ⇑(Complex.conjCLE : ℂ ≃L[ℝ] ℂ) from by
        funext z; rw [Complex.conjCLE_apply]; rfl]
      exact hh
    exact hstar.comp (hφ i)
  have hstrc : ∀ i, HasCompactSupport (fun w => star (φ i w)) := by
    intro i
    simpa [Function.comp_def] using (hφc i).comp_left (g := fun z : ℂ => star z) (by simp)
  have hAcont : ∀ i, Continuous (A i) := fun i => continuous_dCoord_of_contDiff_one (hstr i) i
  have hAcs : ∀ i, HasCompactSupport (A i) := fun i => hasCompactSupport_dCoord (hstrc i) i
  have hstar : ∀ ζ, star (czTheta φ ζ) = ∑ i, A i ζ := by
    intro ζ
    rw [czTheta_apply]
    change starRingEnd ℂ (∑ i, Work.CR.Flat.dbarCoord i (φ i) ζ)
        = ∑ i, Work.CR.Flat.dCoord i (fun w => star (φ i w)) ζ
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (dCoord_star_comp i ((hφ i).differentiable (by norm_num) ζ)).symm
  have h1 : czV φ z l = ∫ ζ, bmKernel l (ζ - z) * (∑ i, A i ζ) := by
    rw [czV_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show bmKernel l (ζ - z) * star (czTheta φ ζ) = bmKernel l (ζ - z) * (∑ i, A i ζ)
    rw [hstar ζ]
  have h2 : ∫ ζ, bmKernel l (ζ - z) * (∑ i, A i ζ)
      = ∫ η, bmKernel l η * (∑ i, A i (z + η)) := by
    rw [← MeasureTheory.integral_sub_right_eq_self
        (fun η => bmKernel l η * (∑ i, A i (z + η))) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show bmKernel l (ζ - z) * (∑ i, A i ζ) = bmKernel l (ζ - z) * (∑ i, A i (z + (ζ - z)))
    rw [show z + (ζ - z) = ζ by abel]
  have h3 : ∫ η, bmKernel l η * (∑ i, A i (z + η))
      = ∑ i, ∫ η, bmKernel l η * A i (z + η) := by
    rw [show (fun η => bmKernel l η * (∑ i, A i (z + η)))
        = fun η => ∑ i, bmKernel l η * A i (z + η) from by
      funext η; rw [Finset.mul_sum]]
    rw [MeasureTheory.integral_finsetSum _
      (fun i _ => integrable_bmKernel_mul_comp hn l (hAcont i) (hAcs i) z)]
  have h4 : ∀ i, ∫ η, bmKernel l η * A i (z + η)
      = Work.CR.Flat.dCoord i
        (Work.CR.Flat.Cauchy.bmPotential (singleFam l (fun w => star (φ i w)))) z := by
    intro i
    rw [bmPotential_dCoord_eq hn (contDiff_singleFam (hstr i))
      (hasCompactSupport_singleFam (hstrc i)) i z]
    rw [Finset.sum_eq_single l]
    · apply integral_congr_ae; refine Filter.Eventually.of_forall fun x => ?_
      simp only [hA, singleFam_self]
    · intro l' _ hl'
      rw [singleFam_of_ne hl']
      simp [Work.CR.Flat.dCoord]
    · intro hl; exact absurd (Finset.mem_univ l) hl
  rw [h1, h2, h3]
  exact Finset.sum_congr rfl fun i _ => h4 i

/-! ## The single-component `L²` bound -/

/-- **The `L²` bound for one component.**  From the `L²` bound for `∂ (bmPotential ·)` on `C¹`
compactly supported data one obtains, for a *single* packet `singleFam l ψ`, the bound for an
arbitrary derivative direction `k`. -/
lemma lintegral_dCoord_bmPotential_singleFam_le {n : ℕ} (_hn : 0 < n) {C : ℝ} (_hC : 0 ≤ C)
    (hczb : ∀ (f g : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ 1 (f j)) →
      (∀ j, ContDiff ℝ 1 (g j)) → (∀ j, HasCompactSupport (f j)) → (∀ j, HasCompactSupport (g j)) →
      (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential f) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential g) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖f j z - g j z‖ ^ 2)
    (l k : Fin n) (ψ : (Fin n → ℂ) → ℂ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
        (‖Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmPotential (singleFam l ψ)) z‖ ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖ψ z‖ ^ 2) := by
  have hf : ∀ j, ContDiff ℝ 1 (singleFam l ψ j) := contDiff_singleFam hψ
  have hfc : ∀ j, HasCompactSupport (singleFam l ψ j) := hasCompactSupport_singleFam hψc
  have hbm0 : Work.CR.Flat.Cauchy.bmPotential (n := n) (fun _ _ => (0:ℂ)) = fun _ => 0 := by
    funext z; simp [Work.CR.Flat.Cauchy.bmPotential]
  have hzero : ∀ i z, Work.CR.Flat.dCoord i
      (Work.CR.Flat.Cauchy.bmPotential (n := n) (fun _ _ => (0:ℂ))) z = 0 := by
    intro i z; rw [hbm0]; simp [Work.CR.Flat.dCoord]
  have hmain := hczb (singleFam l ψ) (fun _ _ => (0:ℂ))
    hf (fun j => contDiff_const) hfc (fun j => HasCompactSupport.zero)
  have hmain' : (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal
        (‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential (singleFam l ψ)) z
          - Work.CR.Flat.dCoord i
            (Work.CR.Flat.Cauchy.bmPotential (n := n) (fun _ _ => (0:ℂ))) z‖ ^ 2))
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal
        (‖singleFam l ψ j z - (fun _ _ => (0:ℂ)) j z‖ ^ 2) := by
    simpa only [ofReal_norm_sq_eq] using hmain
  have hlhs : (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal
        (‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential (singleFam l ψ)) z
          - Work.CR.Flat.dCoord i
            (Work.CR.Flat.Cauchy.bmPotential (n := n) (fun _ _ => (0:ℂ))) z‖ ^ 2))
      = ∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal
        (‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential (singleFam l ψ)) z‖ ^ 2) := by
    refine lintegral_congr fun z => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hzero i z, sub_zero]
  have hrhs : (∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal
        (‖singleFam l ψ j z - (fun _ _ => (0:ℂ)) j z‖ ^ 2))
      = ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖ψ z‖ ^ 2) := by
    refine lintegral_congr fun z => ?_
    rw [Finset.sum_eq_single l]
    · simp
    · intro j _ hj; rw [singleFam_of_ne hj]; simp
    · intro h; exact absurd (Finset.mem_univ l) h
  rw [hlhs, hrhs] at hmain'
  calc ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
        (‖Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmPotential (singleFam l ψ)) z‖ ^ 2)
      ≤ ∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal
        (‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential (singleFam l ψ)) z‖ ^ 2) :=
        lintegral_mono fun z => Finset.single_le_sum
          (f := fun i => ENNReal.ofReal
            (‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential (singleFam l ψ)) z‖ ^ 2))
          (fun i _ => bot_le) (Finset.mem_univ k)
    _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖ψ z‖ ^ 2) := hmain'

/-! ## The main `L²` bound -/

theorem czV_L2_bound {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Fin n → (Fin n → ℂ) → ℂ),
      (∀ i, ContDiff ℝ 1 (φ i)) → (∀ i, HasCompactSupport (φ i)) →
      (∫⁻ z : Fin n → ℂ, ∑ l : Fin n, ENNReal.ofReal (‖Work.NN.Core.czV φ z l‖ ^ 2))
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2) := by
  obtain ⟨C, hC, hczb⟩ := czB_L2_bounded hn
  refine ⟨(n:ℝ) * C, by positivity, ?_⟩
  intro φ hφ hφc
  set A : Fin n → Fin n → (Fin n → ℂ) → ℂ :=
    fun l i => Work.CR.Flat.dCoord i
      (Work.CR.Flat.Cauchy.bmPotential (singleFam l (fun w => star (φ i w)))) with hA
  have hstr : ∀ i, ContDiff ℝ 1 (fun w => star (φ i w)) := by
    intro i
    have hstar : ContDiff ℝ 1 (fun z : ℂ => star z) := by
      have hh := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff (n := 1)
      rw [show (fun z : ℂ => star z) = ⇑(Complex.conjCLE : ℂ ≃L[ℝ] ℂ) from by
        funext z; rw [Complex.conjCLE_apply]; rfl]
      exact hh
    exact hstar.comp (hφ i)
  have hstrc : ∀ i, HasCompactSupport (fun w => star (φ i w)) := by
    intro i
    simpa [Function.comp_def] using (hφc i).comp_left (g := fun z : ℂ => star z) (by simp)
  have hcont : ∀ l i, Continuous (A l i) := by
    intro l i
    have hbm : ContDiff ℝ 1
        (Work.CR.Flat.Cauchy.bmPotential (singleFam l (fun w => star (φ i w)))) :=
      Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn
        (contDiff_singleFam (hstr i)) (hasCompactSupport_singleFam (hstrc i))
    exact continuous_dCoord_of_contDiff_one hbm i
  have hmeas : ∀ l i, Measurable (fun z => ENNReal.ofReal (‖A l i z‖ ^ 2)) :=
    fun l i => ENNReal.measurable_ofReal.comp (((hcont l i).norm.pow 2).measurable)
  have hmeasφ : ∀ i, Measurable (fun z => ENNReal.ofReal (‖φ i z‖ ^ 2)) :=
    fun i => ENNReal.measurable_ofReal.comp (((hφ i).continuous.norm.pow 2).measurable)
  have hAbound : ∀ l i, ∫⁻ z, ENNReal.ofReal (‖A l i z‖ ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z, ENNReal.ofReal (‖φ i z‖ ^ 2) := by
    intro l i
    have h := lintegral_dCoord_bmPotential_singleFam_le hn hC hczb l i
      (fun w => star (φ i w)) (hstr i) (hstrc i)
    simpa [hA, norm_star] using h
  have hpoint : ∀ z, ∑ l, ‖czV φ z l‖ ^ 2 ≤ (n:ℝ) * ∑ l, ∑ i, ‖A l i z‖ ^ 2 := by
    intro z
    have hl : ∀ l, ‖czV φ z l‖ ^ 2 ≤ (n:ℝ) * ∑ i, ‖A l i z‖ ^ 2 := by
      intro l
      have h := norm_sum_sq_le_card_mul (fun i => A l i z)
      rw [← czV_eq_dCoord_bmPotential hn hφ hφc z l] at h
      simpa [hA] using h
    calc ∑ l, ‖czV φ z l‖ ^ 2 ≤ ∑ l, (n:ℝ) * ∑ i, ‖A l i z‖ ^ 2 :=
          Finset.sum_le_sum fun l _ => hl l
      _ = (n:ℝ) * ∑ l, ∑ i, ‖A l i z‖ ^ 2 := by rw [Finset.mul_sum]
  have stepA : ∫⁻ z, ∑ l, ENNReal.ofReal (‖czV φ z l‖ ^ 2)
      ≤ ∫⁻ z, ENNReal.ofReal ((n:ℝ) * ∑ l, ∑ i, ‖A l i z‖ ^ 2) := by
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)]
    exact ENNReal.ofReal_le_ofReal (hpoint z)
  have stepB : ∫⁻ z, ENNReal.ofReal ((n:ℝ) * ∑ l, ∑ i, ‖A l i z‖ ^ 2)
      = ∫⁻ z, (n:ENNReal) * ENNReal.ofReal (∑ l, ∑ i, ‖A l i z‖ ^ 2) := by
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  have stepC : ∫⁻ z, (n:ENNReal) * ENNReal.ofReal (∑ l, ∑ i, ‖A l i z‖ ^ 2)
      = (n:ENNReal) * ∫⁻ z, ENNReal.ofReal (∑ l, ∑ i, ‖A l i z‖ ^ 2) :=
    lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)
  have stepD : ∫⁻ z, ENNReal.ofReal (∑ l, ∑ i, ‖A l i z‖ ^ 2)
      = ∫⁻ z, ∑ l, ∑ i, ENNReal.ofReal (‖A l i z‖ ^ 2) := by
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => Finset.sum_nonneg fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  have stepE : ∫⁻ z, ∑ l, ∑ i, ENNReal.ofReal (‖A l i z‖ ^ 2)
      = ∑ l, ∑ i, ∫⁻ z, ENNReal.ofReal (‖A l i z‖ ^ 2) := by
    rw [MeasureTheory.lintegral_finsetSum (s := Finset.univ)
      (f := fun l z => ∑ i, ENNReal.ofReal (‖A l i z‖ ^ 2))
      (fun l _ => Finset.measurable_sum _ fun i _ => hmeas l i)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MeasureTheory.lintegral_finsetSum (s := Finset.univ)
      (f := fun i z => ENNReal.ofReal (‖A l i z‖ ^ 2)) (fun i _ => hmeas l i)]
  have hsumI : ∑ i : Fin n, ∫⁻ z, ENNReal.ofReal (‖φ i z‖ ^ 2)
      = ∫⁻ z, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2) :=
    (MeasureTheory.lintegral_finsetSum (s := Finset.univ)
      (f := fun i z => ENNReal.ofReal (‖φ i z‖ ^ 2)) (fun i _ => hmeasφ i)).symm
  have stepF : ∑ l : Fin n, ∑ i : Fin n, ∫⁻ z, ENNReal.ofReal (‖A l i z‖ ^ 2)
      ≤ ∑ l : Fin n, ∑ i : Fin n,
          ENNReal.ofReal (C ^ 2) * ∫⁻ z, ENNReal.ofReal (‖φ i z‖ ^ 2) :=
    Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun i _ => hAbound l i
  have stepG : ∑ l : Fin n, ∑ i : Fin n,
        ENNReal.ofReal (C ^ 2) * ∫⁻ z, ENNReal.ofReal (‖φ i z‖ ^ 2)
      = (n:ENNReal) * (ENNReal.ofReal (C ^ 2) * ∫⁻ z, ∑ i : Fin n,
          ENNReal.ofReal (‖φ i z‖ ^ 2)) := by
    have h : ∀ l : Fin n, (∑ i : Fin n, ENNReal.ofReal (C ^ 2) * ∫⁻ z,
          ENNReal.ofReal (‖φ i z‖ ^ 2))
        = ENNReal.ofReal (C ^ 2) * ∑ i : Fin n, ∫⁻ z, ENNReal.ofReal (‖φ i z‖ ^ 2) := by
      intro l; rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun l _ => h l), hsumI]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have stepH : (n:ENNReal) * ((n:ENNReal) * (ENNReal.ofReal (C ^ 2)
        * ∫⁻ z, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2)))
      = ENNReal.ofReal (((n:ℝ) * C) ^ 2) * ∫⁻ z, ∑ i : Fin n,
          ENNReal.ofReal (‖φ i z‖ ^ 2) := by
    have h1 : (n:ENNReal) * (n:ENNReal) = ENNReal.ofReal ((n:ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1; ring
    have h2 : ENNReal.ofReal ((n:ℝ) ^ 2) * ENNReal.ofReal (C ^ 2)
        = ENNReal.ofReal (((n:ℝ) * C) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    calc (n:ENNReal) * ((n:ENNReal) * (ENNReal.ofReal (C ^ 2)
          * ∫⁻ z, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2)))
        = ((n:ENNReal) * (n:ENNReal)) * (ENNReal.ofReal (C ^ 2)
            * ∫⁻ z, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2)) := by ring
      _ = (ENNReal.ofReal ((n:ℝ) ^ 2) * ENNReal.ofReal (C ^ 2))
            * ∫⁻ z, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2) := by rw [h1, mul_assoc]
      _ = ENNReal.ofReal (((n:ℝ) * C) ^ 2)
            * ∫⁻ z, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2) := by rw [h2]
  calc ∫⁻ z, ∑ l, ENNReal.ofReal (‖czV φ z l‖ ^ 2)
      ≤ ∫⁻ z, ENNReal.ofReal ((n:ℝ) * ∑ l, ∑ i, ‖A l i z‖ ^ 2) := stepA
    _ = ∫⁻ z, (n:ENNReal) * ENNReal.ofReal (∑ l, ∑ i, ‖A l i z‖ ^ 2) := stepB
    _ = (n:ENNReal) * ∫⁻ z, ENNReal.ofReal (∑ l, ∑ i, ‖A l i z‖ ^ 2) := stepC
    _ = (n:ENNReal) * ∫⁻ z, ∑ l, ∑ i, ENNReal.ofReal (‖A l i z‖ ^ 2) := by rw [stepD]
    _ = (n:ENNReal) * ∑ l, ∑ i, ∫⁻ z, ENNReal.ofReal (‖A l i z‖ ^ 2) := by rw [stepE]
    _ ≤ (n:ENNReal) * ∑ l, ∑ i,
          ENNReal.ofReal (C ^ 2) * ∫⁻ z, ENNReal.ofReal (‖φ i z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left stepF bot_le
    _ = (n:ENNReal) * ((n:ENNReal) * (ENNReal.ofReal (C ^ 2)
          * ∫⁻ z, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2))) := by rw [stepG]
    _ = ENNReal.ofReal (((n:ℝ) * C) ^ 2) * ∫⁻ z, ∑ i : Fin n,
          ENNReal.ofReal (‖φ i z‖ ^ 2) := stepH

end Work.NN.Core
