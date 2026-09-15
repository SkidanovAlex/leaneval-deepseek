import Mathlib
import Submission.Commons.Analysis.Fourier.convolution_sq_le_hsNorm
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral

open MeasureTheory FourierTransform
open scoped FourierTransform ENNReal RealInnerProductSpace

namespace Commons.Analysis.Fourier

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure 𝔼)

/-! ### Auxiliary lemmas -/

/-- The pointwise convolution is insensitive to almost-everywhere changes of its first argument. -/
lemma convFun_congr_ae {u v φ : 𝔼 → ℂ} (h : u =ᵐ[volume] v) :
    convFun u φ = convFun v φ := by
  funext x
  simp only [convFun]
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

/-- `eLpNorm` of a pointwise product against a uniformly bounded function. -/
lemma eLpNorm_mul_le_of_bound {v m : 𝔼 → ℂ} {M : ℝ}
    (hM : ∀ ξ, ‖m ξ‖ ≤ M) :
    eLpNorm (fun ξ => v ξ * m ξ) 2 (volume : Measure 𝔼)
      ≤ ENNReal.ofReal M * eLpNorm v 2 (volume : Measure 𝔼) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall (fun ξ => ?_)) 2
  rw [norm_mul]
  calc ‖v ξ‖ * ‖m ξ‖ ≤ ‖v ξ‖ * M := mul_le_mul_of_nonneg_left (hM ξ) (norm_nonneg _)
    _ = M * ‖v ξ‖ := mul_comm _ _

/-- The `L²` element with representative `ξ ↦ 𝓕 g ξ * 𝓕 φ ξ`. -/
noncomputable def fourierMulLp (φ : 𝔼 → ℂ)
    (hφtop : MemLp (fun ξ : 𝔼 => 𝓕 φ ξ) ⊤ (volume : Measure 𝔼))
    (g : L2) : L2 :=
  (hφtop.mul (Lp.memLp (𝓕 g : L2))).toLp
    (fun ξ => ((𝓕 g : L2) : 𝔼 → ℂ) ξ * 𝓕 φ ξ)

/-- The `L²` element given by the pointwise convolution with `φ`. -/
noncomputable def convLp (φ : 𝔼 → ℂ) (hφI : Integrable φ (volume : Measure 𝔼))
    (g : L2) : L2 :=
  (memLp_convFun_two (Lp.memLp g) hφI).toLp (convFun (g : 𝔼 → ℂ) φ)

lemma norm_convLp_sub_le (φ : 𝔼 → ℂ) (hφI : Integrable φ (volume : Measure 𝔼)) (g g' : L2) :
    ‖convLp φ hφI g - convLp φ hφI g'‖
      ≤ (eLpNorm φ 1 (volume : Measure 𝔼)).toReal * ‖g - g'‖ := by
  have h1 : convLp φ hφI g - convLp φ hφI g'
      = ((memLp_convFun_two (Lp.memLp g) hφI).sub
          (memLp_convFun_two (Lp.memLp g') hφI)).toLp
          (fun x => convFun (g : 𝔼 → ℂ) φ x - convFun (g' : 𝔼 → ℂ) φ x) := rfl
  rw [h1, MeasureTheory.Lp.norm_toLp]
  have h3 : eLpNorm (fun x => convFun (g : 𝔼 → ℂ) φ x - convFun (g' : 𝔼 → ℂ) φ x) 2
        (volume : Measure 𝔼)
      ≤ eLpNorm ((g : 𝔼 → ℂ) - (g' : 𝔼 → ℂ)) 2 (volume : Measure 𝔼)
          * eLpNorm φ 1 (volume : Measure 𝔼) :=
    eLpNorm_convFun_sub_le (Lp.memLp g) (Lp.memLp g') hφI
  have h4 : eLpNorm ((g : 𝔼 → ℂ) - (g' : 𝔼 → ℂ)) 2 (volume : Measure 𝔼)
      = eLpNorm ((g - g' : L2) : 𝔼 → ℂ) 2 (volume : Measure 𝔼) :=
    (eLpNorm_congr_ae (Lp.coeFn_sub g g')).symm
  have hφfin : eLpNorm φ 1 (volume : Measure 𝔼) ≠ ⊤ :=
    (memLp_one_iff_integrable.mpr hφI).eLpNorm_lt_top.ne
  have hfin : eLpNorm ((g : 𝔼 → ℂ) - (g' : 𝔼 → ℂ)) 2 (volume : Measure 𝔼)
      * eLpNorm φ 1 (volume : Measure 𝔼) ≠ ⊤ := by
    rw [h4]
    exact ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) hφfin
  calc (eLpNorm (fun x => convFun (g : 𝔼 → ℂ) φ x - convFun (g' : 𝔼 → ℂ) φ x) 2
        (volume : Measure 𝔼)).toReal
      ≤ (eLpNorm ((g : 𝔼 → ℂ) - (g' : 𝔼 → ℂ)) 2 (volume : Measure 𝔼)
          * eLpNorm φ 1 (volume : Measure 𝔼)).toReal := ENNReal.toReal_mono hfin h3
    _ = (eLpNorm ((g : 𝔼 → ℂ) - (g' : 𝔼 → ℂ)) 2 (volume : Measure 𝔼)).toReal
          * (eLpNorm φ 1 (volume : Measure 𝔼)).toReal := ENNReal.toReal_mul
    _ = (eLpNorm ((g - g' : L2) : 𝔼 → ℂ) 2 (volume : Measure 𝔼)).toReal
          * (eLpNorm φ 1 (volume : Measure 𝔼)).toReal := by rw [h4]
    _ = ‖g - g'‖ * (eLpNorm φ 1 (volume : Measure 𝔼)).toReal := by
        rw [MeasureTheory.Lp.norm_def]
    _ = (eLpNorm φ 1 (volume : Measure 𝔼)).toReal * ‖g - g'‖ := mul_comm _ _

lemma norm_fourierMulLp_sub_le (φ : 𝔼 → ℂ)
    (hφtop : MemLp (fun ξ : 𝔼 => 𝓕 φ ξ) ⊤ (volume : Measure 𝔼))
    {M : ℝ} (hMnn : 0 ≤ M) (hM : ∀ ξ, ‖𝓕 φ ξ‖ ≤ M) (g g' : L2) :
    ‖fourierMulLp φ hφtop g - fourierMulLp φ hφtop g'‖ ≤ M * ‖g - g'‖ := by
  have h1 : fourierMulLp φ hφtop g - fourierMulLp φ hφtop g'
      = ((hφtop.mul (Lp.memLp (𝓕 g : L2))).sub
          (hφtop.mul (Lp.memLp (𝓕 g' : L2)))).toLp
          (fun ξ => ((𝓕 g : L2) : 𝔼 → ℂ) ξ * 𝓕 φ ξ
            - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ * 𝓕 φ ξ) := rfl
  rw [h1, MeasureTheory.Lp.norm_toLp]
  have h2 : (fun ξ => ((𝓕 g : L2) : 𝔼 → ℂ) ξ * 𝓕 φ ξ
        - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ * 𝓕 φ ξ)
      = fun ξ => (((𝓕 g : L2) : 𝔼 → ℂ) ξ - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ) * 𝓕 φ ξ := by
    funext ξ; ring
  rw [h2]
  have h3 : eLpNorm (fun ξ => (((𝓕 g : L2) : 𝔼 → ℂ) ξ - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ)
        * 𝓕 φ ξ) 2 (volume : Measure 𝔼)
      ≤ ENNReal.ofReal M * eLpNorm
          (fun ξ => ((𝓕 g : L2) : 𝔼 → ℂ) ξ - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ) 2
          (volume : Measure 𝔼) :=
    eLpNorm_mul_le_of_bound hM
  have h4 : eLpNorm (fun ξ : 𝔼 => ((𝓕 g : L2) : 𝔼 → ℂ) ξ - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ) 2
        (volume : Measure 𝔼)
      = eLpNorm ((𝓕 g - 𝓕 g' : L2) : 𝔼 → ℂ) 2 (volume : Measure 𝔼) :=
    eLpNorm_congr_ae (Lp.coeFn_sub (𝓕 g) (𝓕 g')).symm
  have hfin : ENNReal.ofReal M * eLpNorm
        (fun ξ => ((𝓕 g : L2) : 𝔼 → ℂ) ξ - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ) 2
        (volume : Measure 𝔼) ≠ ⊤ := by
    rw [h4]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)
  calc (eLpNorm (fun ξ => (((𝓕 g : L2) : 𝔼 → ℂ) ξ - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ)
        * 𝓕 φ ξ) 2 (volume : Measure 𝔼)).toReal
      ≤ (ENNReal.ofReal M * eLpNorm
          (fun ξ => ((𝓕 g : L2) : 𝔼 → ℂ) ξ - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ) 2
          (volume : Measure 𝔼)).toReal := ENNReal.toReal_mono hfin h3
    _ = M * (eLpNorm
          (fun ξ => ((𝓕 g : L2) : 𝔼 → ℂ) ξ - ((𝓕 g' : L2) : 𝔼 → ℂ) ξ) 2
          (volume : Measure 𝔼)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMnn]
    _ = M * ‖𝓕 g - 𝓕 g'‖ := by rw [h4, MeasureTheory.Lp.norm_def]
    _ = M * ‖g - g'‖ := by
        rw [← fourier_sub_lp g g', MeasureTheory.Lp.norm_fourier_eq]

/-- The identity holds for Schwartz functions. -/
theorem fourier_convLp_toLp_schwartz (φ : 𝔼 → ℂ) (hφI : Integrable φ (volume : Measure 𝔼))
    (hφtop : MemLp (fun ξ : 𝔼 => 𝓕 φ ξ) ⊤ (volume : Measure 𝔼))
    (θ : SchwartzMap 𝔼 ℂ) :
    𝓕 (convLp φ hφI (θ.toLp 2 (volume : Measure 𝔼))) =
      fourierMulLp φ hφtop (θ.toLp 2 (volume : Measure 𝔼)) := by
  have hθ1 : MemLp (θ : 𝔼 → ℂ) 1 (volume : Measure 𝔼) := θ.memLp 1 volume
  have hθ2 : MemLp (θ : 𝔼 → ℂ) 2 (volume : Measure 𝔼) := θ.memLp 2 volume
  have hθint : Integrable (θ : 𝔼 → ℂ) := memLp_one_iff_integrable.mp hθ1
  have hconv : convLp φ hφI (θ.toLp 2 (volume : Measure 𝔼))
      = (memLp_convFun_two hθ2 hφI).toLp (convFun (θ : 𝔼 → ℂ) φ) := by
    rw [convLp]
    refine MemLp.toLp_congr _ _ ?_
    have h1 : (↑↑(θ.toLp 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) =ᵐ[volume] (θ : 𝔼 → ℂ) :=
      MemLp.coeFn_toLp hθ2
    exact Filter.EventuallyEq.of_eq (convFun_congr_ae h1)
  rw [hconv]
  refine Lp.ext ?_
  have hA : ((𝓕 ((memLp_convFun_two hθ2 hφI).toLp (convFun (θ:𝔼→ℂ) φ)) : L2) : 𝔼 → ℂ)
      =ᵐ[volume] fun ξ => 𝓕 (convFun (θ:𝔼→ℂ) φ) ξ :=
    fourier_toLp_ae_eq_fourier_of_memLp (memLp_convFun_one hθ1 hφI) (memLp_convFun_two hθ2 hφI)
  have hC : ((fourierMulLp φ hφtop (θ.toLp 2 (volume : Measure 𝔼)) : L2) : 𝔼 → ℂ)
      =ᵐ[volume] fun ξ => ((𝓕 (θ.toLp 2 (volume : Measure 𝔼)) : L2) : 𝔼 → ℂ) ξ * 𝓕 φ ξ := by
    rw [fourierMulLp]
    exact MemLp.coeFn_toLp _
  have hAθ : ((𝓕 (θ.toLp 2 (volume : Measure 𝔼)) : L2) : 𝔼 → ℂ) =ᵐ[volume] (fun ξ => 𝓕 θ ξ) := by
    rw [show (𝓕 (θ.toLp 2 (volume : Measure 𝔼)) : L2) = ((𝓕 θ).toLp 2 (volume : Measure 𝔼))
      from SchwartzMap.toLp_fourier_eq θ]
    exact MemLp.coeFn_toLp _
  filter_upwards [hA, hC, hAθ] with ξ h1 h2 h3
  rw [h1, h2, h3, fourier_convFun hφI hθint ξ, SchwartzMap.fourier_coe, mul_comm]

/-- The main statement, with `d` kept as a section variable. -/
theorem fourier_convFun_ae_aux {f φ : 𝔼 → ℂ} {A : ℝ}
    (hf : MemLp f 2 (volume : Measure 𝔼))
    (hφI : Integrable φ (volume : Measure 𝔼))
    (hφ2 : MemLp φ 2 (volume : Measure 𝔼))
    (hAb : ∀ ξ : 𝔼, ‖𝓕 φ ξ‖ ≤ A) :
    (fun ξ : 𝔼 =>
        ((𝓕
          ((memLp_convFun_two hf hφI).toLp
            (convFun f φ)) : L2) :
                𝔼 → ℂ) ξ)
      =ᵐ[volume]
      (fun ξ => ((𝓕 (hf.toLp f) : L2) : 𝔼 → ℂ) ξ *
        𝓕 φ ξ) := by
  have hcont : Continuous (fun ξ : 𝔼 => 𝓕 φ ξ) :=
    VectorFourier.fourierIntegral_continuous (E := ℂ) (V := 𝔼) (W := 𝔼)
      (e := Real.fourierChar) (μ := (volume : Measure 𝔼)) (L := innerₗ 𝔼)
      Real.continuous_fourierChar continuous_inner hφI
  have hφtop : MemLp (fun ξ : 𝔼 => 𝓕 φ ξ) ⊤ (volume : Measure 𝔼) :=
    memLp_top_of_bound hcont.aestronglyMeasurable A (Filter.Eventually.of_forall hAb)
  have hMnn : (0:ℝ) ≤ max A 0 := le_max_right _ _
  have hM : ∀ ξ : 𝔼, ‖𝓕 φ ξ‖ ≤ max A 0 := fun ξ => (hAb ξ).trans (le_max_left _ _)
  let Kc : NNReal := ⟨(eLpNorm φ 1 (volume : Measure 𝔼)).toReal, ENNReal.toReal_nonneg⟩
  have hKc : (Kc : ℝ) = (eLpNorm φ 1 (volume : Measure 𝔼)).toReal := rfl
  have hCLip : LipschitzWith Kc (convLp φ hφI) := by
    refine LipschitzWith.of_dist_le_mul (fun g g' => ?_)
    rw [dist_eq_norm, dist_eq_norm, hKc]
    exact norm_convLp_sub_le φ hφI g g'
  let KM : NNReal := ⟨max A 0, hMnn⟩
  have hKM : (KM : ℝ) = max A 0 := rfl
  have hTLip : LipschitzWith KM (fourierMulLp φ hφtop) := by
    refine LipschitzWith.of_dist_le_mul (fun g g' => ?_)
    rw [dist_eq_norm, dist_eq_norm, hKM]
    exact norm_fourierMulLp_sub_le φ hφtop hMnn hM g g'
  have hΦcont : Continuous (fun g : L2 => 𝓕 (convLp φ hφI g)) :=
    continuous_fourier.comp hCLip.continuous
  have hTcont : Continuous (fourierMulLp φ hφtop) := hTLip.continuous
  have hclosed : IsClosed {g : L2 | 𝓕 (convLp φ hφI g) = fourierMulLp φ hφtop g} :=
    isClosed_eq hΦcont hTcont
  have hDense : DenseRange (fun θ : SchwartzMap 𝔼 ℂ => (θ.toLp 2 (volume : Measure 𝔼) : L2)) :=
    SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top
  have hsub : Set.range (fun θ : SchwartzMap 𝔼 ℂ => (θ.toLp 2 (volume : Measure 𝔼) : L2))
      ⊆ {g : L2 | 𝓕 (convLp φ hφI g) = fourierMulLp φ hφtop g} := by
    rintro _ ⟨θ, rfl⟩
    exact fourier_convLp_toLp_schwartz φ hφI hφtop θ
  have hall : ∀ g : L2, 𝓕 (convLp φ hφI g) = fourierMulLp φ hφtop g := by
    intro g
    have hc : closure (Set.range (fun θ : SchwartzMap 𝔼 ℂ => (θ.toLp 2 (volume : Measure 𝔼) : L2)))
        ⊆ {g : L2 | 𝓕 (convLp φ hφI g) = fourierMulLp φ hφtop g} :=
      (hclosed.closure_subset_iff).mpr hsub
    refine hc ?_
    rw [hDense.closure_range]
    exact Set.mem_univ g
  have hconv : convLp φ hφI (hf.toLp f) = (memLp_convFun_two hf hφI).toLp (convFun f φ) := by
    rw [convLp]
    refine MemLp.toLp_congr _ _ ?_
    exact Filter.EventuallyEq.of_eq (convFun_congr_ae (MemLp.coeFn_toLp hf))
  have key : (𝓕 ((memLp_convFun_two hf hφI).toLp (convFun f φ)) : L2)
      = fourierMulLp φ hφtop (hf.toLp f) := by
    rw [← hconv]
    exact hall (hf.toLp f)
  rw [key, fourierMulLp]
  exact MemLp.coeFn_toLp _

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform
open scoped FourierTransform ENNReal

theorem fourier_convFun_ae (d : ℕ) {f φ : EuclideanSpace ℝ (Fin d) → ℂ} {A : ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hφI : MeasureTheory.Integrable φ (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hφ2 : MeasureTheory.MemLp φ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hAb : ∀ ξ : EuclideanSpace ℝ (Fin d), ‖FourierTransform.fourier φ ξ‖ ≤ A) :
    (fun ξ : EuclideanSpace ℝ (Fin d) =>
        ((FourierTransform.fourier
          ((Commons.Analysis.Fourier.memLp_convFun_two hf hφI).toLp
            (Commons.Analysis.Fourier.convFun f φ)) : MeasureTheory.Lp ℂ 2
              (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
                EuclideanSpace ℝ (Fin d) → ℂ) ξ)
      =ᵐ[MeasureTheory.volume]
      (fun ξ => ((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) ξ *
        FourierTransform.fourier φ ξ) :=
  fourier_convFun_ae_aux (d := d) hf hφI hφ2 hAb

end Commons.Analysis.Fourier
