import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_theta_real_defs
import Submission.Work.BourgainPlan.Maximal.mst_theta_weighted_defs
import Submission.Work.BourgainPlan.Maximal.iwmult_const
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.iwMult_mul
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers
import Submission.Work.BourgainPlan.Maximal.translateAverage_integrable
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation_integrable
import Submission.Work.BourgainPlan.Maximal.multForm_comp_neg_bound

/-!
# The circle form of MST's `(C2)` from the real-variable form

The real-variable input `MSTThetaRealMult P r A` bounds the signed sum of the *polynomial averaging
operators* `h ↦ ∫₀¹ h (x − P (2^k t)) dt` on `L^{2r}(ℝ)`; the circle input `MSTThetaRawMult P r B`
bounds the multiplier whose symbol is `Θ_ε = Σ_{j<M} ε_j (Φ_{2^{(j+1)2^i}} − Φ_{2^{j2^i}})`, read
on the circle through the canonical lift `iwRep`.  The passage between the two is the content of
this file:

* the fundamental-domain lift of `Θ_ε ∘ iwRep` is the indicator of `(-1/2, 1/2)` times
  `Θ_ε ∘ neg` (off the single point `1/2`);
* the *inverse* Fourier transform of `1_{(-1/2,1/2)} · (Θ_ε ∘ neg) · 𝓕g` is `−S(Π g)`, where
  `Π` is the interval (Dirichlet) projection `𝓕⁻ (1_{(-1/2,1/2)} · 𝓕 ·)` and `S` is the signed sum of
  translate-averages of `MSTThetaRealMult`;
* `Π` is `L^{2r}`-bounded (`interval_projection_memLp`) and `S` is `L^{2r}`-bounded by `A`
  (`MSTThetaRealMult`), so the product is bounded by `C·A`.

The conjugate symbol needed by `MSTThetaRawMult` is `Θ_ε` with conjugate signs, reflected.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal FourierTransform Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-! ## The two real-variable objects -/

/-- The signed sum of translate-averages whose `L^{2r}`-bound is the hypothesis `MSTThetaRealMult`:
`S_ε g(x) = Σ_{j<M} ε_j (∫₀¹ g (x − P (2^{j2^i} t)) dt − ∫₀¹ g (x − P (2^{(j+1)2^i} t)) dt)`. -/
def mstS (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∑ j ∈ Finset.range M, ε j *
    ((∫ t in (0:ℝ)..1, g (x - (toRealPoly P).eval ((((2:ℝ) ^ (j * 2 ^ i)) * t))))
      - (∫ t in (0:ℝ)..1, g (x - (toRealPoly P).eval ((((2:ℝ) ^ ((j+1) * 2 ^ i)) * t)))))

/-- The symbol `1_{(-1/2,1/2)} · (Θ_ε ∘ neg)`, i.e. the fundamental-domain lift of `Θ_ε ∘ iwRep`
(up to the endpoint `1/2`). -/
def mstSym (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) : ℝ → ℂ :=
  fun x => if x ∈ Set.Ioo (-(1/2 : ℝ)) (1/2) then mstThetaEps P i M ε (-x) else 0

/-- The interval (Dirichlet) projection symbol `1_{(-1/2,1/2)}`. -/
def mstInd : ℝ → ℂ := fun ξ => if ξ ∈ Set.Ioo (-(1/2 : ℝ)) (1/2) then (1 : ℂ) else 0

/-! ## Elementary symmetries of the profile and of `Θ_ε` -/

/-- The conjugate of the profile is the profile at the opposite frequency. -/
lemma star_polyProfile_eq (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    starRingEnd ℂ (polyProfile P N β) = polyProfile P N (-β) := by
  rw [star_polyProfile, show (-β) = (-1) * β by ring, polyProfile_eq_polyE]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show (-1 : ℝ) * β * (toRealPoly P).eval ((N : ℝ) * s)
      = -(β * (toRealPoly P).eval ((N : ℝ) * s)) by ring]

/-- **Conjugation of `Θ_ε`** is `Θ` with conjugate signs, reflected. -/
lemma star_mstThetaEps (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) (θ : ℝ) :
    starRingEnd ℂ (mstThetaEps P i M ε θ)
      = mstThetaEps P i M (fun j => starRingEnd ℂ (ε j)) (-θ) := by
  rw [mstThetaEps_apply, mstThetaEps_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_sub, star_polyProfile_eq, star_polyProfile_eq]

/-! ## The fundamental-domain lifts -/

/-- The only point where the fundamental-domain indicator `Ioc (-1/2) (1/2]` differs from the open
interval `Ioo (-1/2) (1/2)`. -/
lemma mem_Ioc_iff_mem_Ioo_or_eq (x : ℝ) :
    x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2) ↔ x ∈ Set.Ioo (-(1/2 : ℝ)) (1/2) ∨ x = 1/2 := by
  rw [Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr h
  · rintro (⟨h1, h2⟩ | rfl)
    · exact ⟨h1, h2.le⟩
    · exact ⟨by norm_num, le_rfl⟩

/-- **The lift of `Θ_ε ∘ iwRep`.**  Off the single point `1/2` it is `mstSym`. -/
theorem circleLift_mstThetaEps_comp_iwRep (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) :
    Work.BourgainPlan.Thm52.circleLift (fun ξ : Circ => mstThetaEps P i M ε (iwRep ξ))
      =ᵐ[(volume : Measure ℝ)] mstSym P i M ε := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1/2 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hae] with x hx
  by_cases hmem : x ∈ Set.Ioo (-(1/2 : ℝ)) (1/2)
  · have hIoc : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2) := Set.Ioo_subset_Ioc_self hmem
    rw [mstSym, if_pos hmem, Work.BourgainPlan.Thm52.circleLift_of_mem hIoc]
    have hcoe : (-(x : Circ)) = ((-x : ℝ) : Circ) := (AddCircle.coe_neg (1 : ℝ) (x := x)).symm
    rw [hcoe, iwRep_coe_of_mem (show (-x) ∈ Set.Ioc (-(1/2 : ℝ)) (1/2) from by
          rw [Set.mem_Ioo] at hmem
          exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩)]
  · have hIoc : x ∉ Set.Ioc (-(1/2 : ℝ)) (1/2) := fun h =>
      hmem ((mem_Ioc_iff_mem_Ioo_or_eq x).mp h |>.resolve_right hx)
    rw [mstSym, if_neg hmem, Work.BourgainPlan.Thm52.circleLift_of_notMem hIoc]

/-- **The lift of the conjugate symbol.**  Off the single point `1/2` its reflection is `mstSym`
for the conjugate signs. -/
theorem circleLift_star_mstThetaEps_comp_iwRep (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) :
    Work.BourgainPlan.Thm52.circleLift
        (fun ξ : Circ => starRingEnd ℂ (mstThetaEps P i M ε (iwRep ξ)))
      =ᵐ[(volume : Measure ℝ)]
        fun x => mstSym P i M (fun j => starRingEnd ℂ (ε j)) (-x) := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1/2 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hae] with x hx
  by_cases hmem : x ∈ Set.Ioo (-(1/2 : ℝ)) (1/2)
  · have hIoc : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2) := Set.Ioo_subset_Ioc_self hmem
    rw [Work.BourgainPlan.Thm52.circleLift_of_mem hIoc]
    have hcoe : (-(x : Circ)) = ((-x : ℝ) : Circ) := (AddCircle.coe_neg (1 : ℝ) (x := x)).symm
    rw [hcoe, star_mstThetaEps, iwRep_coe_of_mem (show (-x) ∈ Set.Ioc (-(1/2 : ℝ)) (1/2) from by
          rw [Set.mem_Ioo] at hmem
          exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩)]
    have hmem' : (-x) ∈ Set.Ioo (-(1/2 : ℝ)) (1/2) := by
      rw [Set.mem_Ioo] at hmem; exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
    rw [mstSym, if_pos hmem', neg_neg]
  · have hIoc : x ∉ Set.Ioc (-(1/2 : ℝ)) (1/2) := fun h =>
      hmem ((mem_Ioc_iff_mem_Ioo_or_eq x).mp h |>.resolve_right hx)
    rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hIoc]
    have hnotmem : (-x) ∉ Set.Ioo (-(1/2 : ℝ)) (1/2) := by
      intro h
      rw [Set.mem_Ioo] at h
      exact hmem ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [mstSym, if_neg hnotmem]


/-! ## Linearity of the inverse Fourier transform on `L¹` functions -/

/-- Multiplying an `L¹` function by a unimodular character preserves integrability. -/
lemma integrable_polyE_mul {f : ℝ → ℂ} (hf : MeasureTheory.Integrable f) (x : ℝ) :
    MeasureTheory.Integrable (fun ξ : ℝ => polyE (ξ * x) * f ξ) := by
  refine MeasureTheory.Integrable.mono' hf.norm ?_ ?_
  · exact ((continuous_polyE.comp (continuous_id.mul continuous_const)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  · filter_upwards with ξ
    rw [norm_mul, norm_polyE, one_mul]

lemma fourierInv_add_of_integrable {f h : ℝ → ℂ} (hf : MeasureTheory.Integrable f)
    (hh : MeasureTheory.Integrable h) :
    FourierTransformInv.fourierInv (f + h)
      = FourierTransformInv.fourierInv f + FourierTransformInv.fourierInv h := by
  funext x
  simp only [Pi.add_apply]
  rw [fourierInv_eq_polyE_integral, fourierInv_eq_polyE_integral, fourierInv_eq_polyE_integral]
  rw [show (fun ξ : ℝ => polyE (ξ * x) * (f + h) ξ)
      = fun ξ : ℝ => polyE (ξ * x) * f ξ + polyE (ξ * x) * h ξ by
        funext ξ; simp [mul_add]]
  rw [MeasureTheory.integral_add (integrable_polyE_mul hf x) (integrable_polyE_mul hh x)]

lemma fourierInv_sub_of_integrable {f h : ℝ → ℂ} (hf : MeasureTheory.Integrable f)
    (hh : MeasureTheory.Integrable h) :
    FourierTransformInv.fourierInv (f - h)
      = FourierTransformInv.fourierInv f - FourierTransformInv.fourierInv h := by
  funext x
  simp only [Pi.sub_apply]
  rw [fourierInv_eq_polyE_integral, fourierInv_eq_polyE_integral, fourierInv_eq_polyE_integral]
  rw [show (fun ξ : ℝ => polyE (ξ * x) * (f - h) ξ)
      = fun ξ : ℝ => polyE (ξ * x) * f ξ - polyE (ξ * x) * h ξ by
        funext ξ; simp [mul_sub]]
  rw [MeasureTheory.integral_sub (integrable_polyE_mul hf x) (integrable_polyE_mul hh x)]

lemma fourierInv_const_mul_of_integrable (c : ℂ) (f : ℝ → ℂ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => c * f ξ)
      = fun x => c * FourierTransformInv.fourierInv f x := by
  funext x
  rw [fourierInv_eq_polyE_integral, fourierInv_eq_polyE_integral]
  rw [show (fun ξ : ℝ => polyE (ξ * x) * (c * f ξ))
      = fun ξ : ℝ => c * (polyE (ξ * x) * f ξ) by
        funext ξ; ring]
  rw [MeasureTheory.integral_const_mul]

lemma fourierInv_sum_of_integrable {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ s, MeasureTheory.Integrable (F i)) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => ∑ i ∈ s, F i ξ)
      = fun x => ∑ i ∈ s, FourierTransformInv.fourierInv (F i) x := by
  funext x
  rw [fourierInv_eq_polyE_integral]
  rw [show (fun ξ : ℝ => polyE (ξ * x) * ∑ i ∈ s, F i ξ)
      = fun ξ : ℝ => ∑ i ∈ s, polyE (ξ * x) * F i ξ by
        funext ξ; rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum s (fun i hi => integrable_polyE_mul (hF i hi) x)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fourierInv_eq_polyE_integral]

/-! ## The interval projection -/

/-- The interval (Dirichlet) projection `Π g = 𝓕⁻ (1_{(-1/2,1/2)} · 𝓕 g)`, i.e. `multForm mstInd g`. -/
def mstProj (g : ℝ → ℂ) : ℝ → ℂ :=
  FourierTransformInv.fourierInv (fun ξ : ℝ => mstInd ξ * FourierTransform.fourier g ξ)

lemma mstProj_eq_multForm (g : ℝ → ℂ) : mstProj g = multForm mstInd g := rfl

lemma mstInd_eq (ξ : ℝ) : mstInd ξ = if ξ ∈ Set.Ioo (-(1/2 : ℝ)) (1/2) then (1 : ℂ) else 0 := rfl

/-! ## The symbol identity -/

/-- The symbol identity: `mstSym · 𝓕g` is the signed sum of the products `1_{(-1/2,1/2)} 𝓕g` against
the conjugated profiles. -/
lemma mstSym_mul_fourier (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) (g : ℝ → ℂ) :
    (fun ξ : ℝ => mstSym P i M ε ξ * FourierTransform.fourier g ξ)
      = fun ξ : ℝ => ∑ j ∈ Finset.range M, ε j *
          ((mstInd ξ * FourierTransform.fourier g ξ) * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
            - (mstInd ξ * FourierTransform.fourier g ξ) * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ)) := by
  funext ξ
  by_cases hξ : ξ ∈ Set.Ioo (-(1/2 : ℝ)) (1/2)
  · rw [mstSym, if_pos hξ, mstInd, if_pos hξ, one_mul]
    rw [mstThetaEps_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_polyProfile_eq, star_polyProfile_eq]
    ring
  · rw [mstSym, if_neg hξ, mstInd, if_neg hξ, zero_mul]
    simp

/-! ## The core identity -/

/-- **The multiplier form of `mstSym` is minus the signed sum of translate-averages of the interval
projection.**  Writing `u = 1_{(-1/2,1/2)} · 𝓕g` (so that `mstProj g = 𝓕⁻ u`), the conjugate profile
turns the interval projection into the averaging operator:

`𝓕⁻ ((mstSym · 𝓕g)) x = − Σ_{j<M} ε_j (∫₀¹ Πg (x − P (2^{j2^i} t)) dt − ∫₀¹ Πg (x − P (2^{(j+1)2^i} t)) dt)`. -/
theorem multForm_mstSym_eq (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) {g : ℝ → ℂ}
    (hg : MeasureTheory.Integrable g) :
    multForm (mstSym P i M ε) g = fun x => - mstS P i M ε (mstProj g) x := by
  have hIint : MeasureTheory.Integrable mstInd := by
    have h : mstInd = (Set.Ioo (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℂ)) := by
      funext ξ; rw [mstInd, Set.indicator_apply]
    rw [h]
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr ?_
    refine MeasureTheory.integrableOn_const ?_ (by simp)
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hfour_meas : AEStronglyMeasurable (FourierTransform.fourier g) volume :=
    (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier
      (memLp_one_iff_integrable.mpr hg)).aestronglyMeasurable
  have hfour_bdd : ∀ᵐ ξ ∂volume, ‖FourierTransform.fourier g ξ‖ ≤ ∫ y : ℝ, ‖g y‖ :=
    Filter.Eventually.of_forall fun ξ => Commons.Analysis.CalderonZygmund.norm_fourier_le g ξ
  set u : ℝ → ℂ := fun ξ => mstInd ξ * FourierTransform.fourier g ξ with hu
  have hu_int : MeasureTheory.Integrable u := by
    have h := hIint.bdd_mul hfour_meas hfour_bdd
    rw [hu]
    exact h.congr (Filter.Eventually.of_forall fun ξ => mul_comm _ _)
  have hU : ∀ N : ℕ, MeasureTheory.Integrable
      (fun ξ : ℝ => u ξ * starRingEnd ℂ (polyProfile P N ξ)) := by
    intro N
    refine MeasureTheory.Integrable.mono' hu_int.norm
      (hu_int.aestronglyMeasurable.mul
        (Complex.continuous_conj.comp (continuous_polyProfile P N)).aestronglyMeasurable) ?_
    filter_upwards with ξ
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_polyProfile_le_one P N ξ)
  have hmain : multForm (mstSym P i M ε) g
      = FourierTransformInv.fourierInv (fun ξ : ℝ => ∑ j ∈ Finset.range M, ε j *
          (u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
            - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ))) := by
    unfold multForm
    rw [mstSym_mul_fourier]
  rw [hmain]
  have hstep1 : FourierTransformInv.fourierInv (fun ξ : ℝ => ∑ j ∈ Finset.range M, ε j *
        (u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
          - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ)))
      = fun x => ∑ j ∈ Finset.range M, FourierTransformInv.fourierInv
          (fun ξ : ℝ => ε j * (u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
            - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ))) x :=
    fourierInv_sum_of_integrable (Finset.range M)
      (fun j ξ => ε j * (u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
            - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ)))
      (fun j _ => ((hU _).sub (hU _)).const_mul _)
  rw [hstep1]
  have hstep2 : (fun x => ∑ j ∈ Finset.range M, FourierTransformInv.fourierInv
          (fun ξ : ℝ => ε j * (u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
            - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ))) x)
      = fun x => ∑ j ∈ Finset.range M, ε j *
          ((∫ t in (0:ℝ)..1, mstProj g (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t)))
            - (∫ t in (0:ℝ)..1, mstProj g (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)))) := by
    funext x
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : FourierTransformInv.fourierInv
          (fun ξ : ℝ => u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ))
        = fun y => ∫ t in (0:ℝ)..1,
            mstProj g (y - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t)) := by
      funext y
      rw [polyProfile_fourier_dilation_integrable P (2 ^ ((j+1) * 2 ^ i)) (G := u) hu_int y]
      refine intervalIntegral.integral_congr fun z _ => ?_
      simp only [Nat.cast_pow, Nat.cast_ofNat, hu, mstProj]
    have h2 : FourierTransformInv.fourierInv
          (fun ξ : ℝ => u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ))
        = fun y => ∫ t in (0:ℝ)..1,
            mstProj g (y - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)) := by
      funext y
      rw [polyProfile_fourier_dilation_integrable P (2 ^ (j * 2 ^ i)) (G := u) hu_int y]
      refine intervalIntegral.integral_congr fun z _ => ?_
      simp only [Nat.cast_pow, Nat.cast_ofNat, hu, mstProj]
    have hin : FourierTransformInv.fourierInv
          (fun ξ : ℝ => u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
            - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ))
        = fun y => (∫ t in (0:ℝ)..1,
              mstProj g (y - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t)))
            - (∫ t in (0:ℝ)..1,
              mstProj g (y - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t))) := by
      have hsub : FourierTransformInv.fourierInv
            (fun ξ : ℝ => u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
              - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ))
          = FourierTransformInv.fourierInv
              (fun ξ : ℝ => u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ))
            - FourierTransformInv.fourierInv
              (fun ξ : ℝ => u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ)) :=
        fourierInv_sub_of_integrable (hU _) (hU _)
      rw [hsub, h1, h2]
      funext y
      rw [Pi.sub_apply]
    have hmul : FourierTransformInv.fourierInv
          (fun ξ : ℝ => ε j * (u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
            - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ)))
        = fun x => ε j * (FourierTransformInv.fourierInv
            (fun ξ : ℝ => u ξ * starRingEnd ℂ (polyProfile P (2 ^ ((j+1) * 2 ^ i)) ξ)
              - u ξ * starRingEnd ℂ (polyProfile P (2 ^ (j * 2 ^ i)) ξ)) x) :=
      fourierInv_const_mul_of_integrable (ε j) _
    rw [hmul, hin]
  rw [hstep2]
  funext x
  rw [mstS, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_neg, neg_sub]
/-! ## Continuity, boundedness and integrability of `mstSym` -/

lemma continuous_mstThetaEps' (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) :
    Continuous (mstThetaEps P i M ε) := by
  rw [show mstThetaEps P i M ε = fun θ => ∑ j ∈ Finset.range M, ε j *
      (polyProfile P (2 ^ ((j+1) * 2 ^ i)) θ - polyProfile P (2 ^ (j * 2 ^ i)) θ) from rfl]
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (((continuous_polyProfile P _).sub (continuous_polyProfile P _)))

lemma norm_mstThetaEps_le' (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ)
    (hε : ∀ j : ℕ, ‖ε j‖ ≤ 1) (θ : ℝ) : ‖mstThetaEps P i M ε θ‖ ≤ 2 * (M : ℝ) := by
  rw [mstThetaEps_apply]
  calc ‖∑ j ∈ Finset.range M, ε j * (polyProfile P (2 ^ ((j+1) * 2 ^ i)) θ
          - polyProfile P (2 ^ (j * 2 ^ i)) θ)‖
      ≤ ∑ j ∈ Finset.range M, ‖ε j * (polyProfile P (2 ^ ((j+1) * 2 ^ i)) θ
          - polyProfile P (2 ^ (j * 2 ^ i)) θ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range M, (1 * 2) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        refine mul_le_mul (hε j) ?_ (norm_nonneg _) (by norm_num)
        have h1 := norm_polyProfile_le_one P (2 ^ ((j+1) * 2 ^ i)) θ
        have h2 := norm_polyProfile_le_one P (2 ^ (j * 2 ^ i)) θ
        linarith [norm_sub_le (polyProfile P (2 ^ ((j+1) * 2 ^ i)) θ)
          (polyProfile P (2 ^ (j * 2 ^ i)) θ)]
    _ = 2 * (M : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

lemma norm_mstSym_le (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ)
    (hε : ∀ j : ℕ, ‖ε j‖ ≤ 1) (x : ℝ) : ‖mstSym P i M ε x‖ ≤ 2 * (M : ℝ) := by
  rw [mstSym]
  by_cases hx : x ∈ Set.Ioo (-(1/2 : ℝ)) (1/2)
  · rw [if_pos hx]
    exact norm_mstThetaEps_le' P i M ε hε (-x)
  · rw [if_neg hx, norm_zero]
    positivity

lemma aestronglyMeasurable_mstSym (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) :
    AEStronglyMeasurable (mstSym P i M ε) volume := by
  have hcont : Continuous (fun x : ℝ => mstThetaEps P i M ε (-x)) :=
    (continuous_mstThetaEps' P i M ε).comp continuous_neg
  have h : mstSym P i M ε
      = (Set.Ioo (-(1/2 : ℝ)) (1/2)).indicator (fun x : ℝ => mstThetaEps P i M ε (-x)) := by
    funext x; rw [mstSym, Set.indicator_apply]
  rw [h]
  exact hcont.aestronglyMeasurable.indicator measurableSet_Ioo

lemma integrable_mstSym (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ)
    (hε : ∀ j : ℕ, ‖ε j‖ ≤ 1) : MeasureTheory.Integrable (mstSym P i M ε) := by
  have hInt : MeasureTheory.Integrable
      ((Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (2 * (M:ℝ)))) (volume : Measure ℝ) := by
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
    refine MeasureTheory.integrableOn_const ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top
  refine hInt.mono' (aestronglyMeasurable_mstSym P i M ε) ?_
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (-(1/2 : ℝ)) (1/2)
  · rw [Set.indicator_of_mem hx]
    exact norm_mstSym_le P i M ε hε x
  · rw [Set.indicator_of_notMem hx, mstSym,
      if_neg (fun h => hx ⟨le_of_lt h.1, h.2.le⟩), norm_zero]

/-! ## Integrability of the operator `mstS` on `L¹` -/

lemma integrable_translateAverage (P : Polynomial ℤ) (c : ℝ) {w : ℝ → ℂ}
    (hw : MeasureTheory.Integrable w) :
    MeasureTheory.Integrable
      (fun x : ℝ => ∫ t in (0:ℝ)..1, w (x - (toRealPoly P).eval (c * t))) := by
  have hφ : Measurable (fun t : ℝ => (toRealPoly P).eval (c * t)) :=
    ((Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)).measurable
  exact (translateAverage_integrable hφ hw).1

lemma integrable_mstS (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) {w : ℝ → ℂ}
    (hw : MeasureTheory.Integrable w) : MeasureTheory.Integrable (mstS P i M ε w) := by
  show MeasureTheory.Integrable (fun x : ℝ => ∑ j ∈ Finset.range M, ε j *
      ((∫ t in (0:ℝ)..1, w (x - (toRealPoly P).eval ((((2:ℝ) ^ (j * 2 ^ i)) * t))))
        - (∫ t in (0:ℝ)..1, w (x - (toRealPoly P).eval ((((2:ℝ) ^ ((j+1) * 2 ^ i)) * t))))))
  refine MeasureTheory.integrable_finsetSum _ fun j _ => ?_
  refine Integrable.const_mul (Integrable.sub ?_ ?_) _
  · exact integrable_translateAverage P _ hw
  · exact integrable_translateAverage P _ hw

/-! ## Pointwise convergence of the truncations under `mstS` -/

set_option maxHeartbeats 1000000 in
lemma tendsto_mstS_truncLp (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) {w : ℝ → ℂ} (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => mstS P i M ε (truncLp w n) x) Filter.atTop
      (𝓝 (mstS P i M ε w x)) := by
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ∀ y ∈ Set.Icc (0:ℝ) ((2:ℝ) ^ (M * 2 ^ i)),
      |(toRealPoly P).eval y| ≤ Cb := by
    obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((Polynomial.continuous (toRealPoly P)).continuousOn)
    exact ⟨Cb, fun y hy => hCb y hy⟩
  have hmem : ∀ k : ℕ, k ≤ M → ∀ t ∈ Set.Icc (0:ℝ) 1,
      x - (toRealPoly P).eval (((2:ℝ) ^ (k * 2 ^ i)) * t)
        ∈ Set.Icc (-(|x| + Cb)) (|x| + Cb) := by
    intro k hk t ht
    have hcle : (2:ℝ) ^ (k * 2 ^ i) ≤ (2:ℝ) ^ (M * 2 ^ i) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ hk)
    have hc0 : (0:ℝ) ≤ (2:ℝ) ^ (k * 2 ^ i) := by positivity
    have hy : (2:ℝ) ^ (k * 2 ^ i) * t ∈ Set.Icc (0:ℝ) ((2:ℝ) ^ (M * 2 ^ i)) :=
      ⟨mul_nonneg hc0 ht.1, by nlinarith [hcle, ht.1, ht.2, hc0]⟩
    have hb := hCb _ hy
    rw [abs_le] at hb
    rw [Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le x, hb.1], by linarith [le_abs_self x, hb.2]⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      mstS P i M ε (truncLp w n) x = mstS P i M ε w x := by
    filter_upwards [Filter.eventually_ge_atTop ⌈|x| + Cb⌉₊] with n hn
    have hn' : |x| + Cb ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have hsub : ∀ k : ℕ, k ≤ M → ∀ t ∈ Set.Icc (0:ℝ) 1,
        truncLp w n (x - (toRealPoly P).eval (((2:ℝ) ^ (k * 2 ^ i)) * t))
          = w (x - (toRealPoly P).eval (((2:ℝ) ^ (k * 2 ^ i)) * t)) := by
      intro k hk t ht
      refine truncLp_of_mem ?_
      have h := hmem k hk t ht
      rw [Set.mem_Icc] at h ⊢
      exact ⟨by linarith [h.1, hn'], by linarith [h.2, hn']⟩
    change (∑ j ∈ Finset.range M, ε j *
        ((∫ t in (0:ℝ)..1, truncLp w n (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)))
          - (∫ t in (0:ℝ)..1,
              truncLp w n (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t)))))
      = (∑ j ∈ Finset.range M, ε j *
        ((∫ t in (0:ℝ)..1, w (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)))
          - (∫ t in (0:ℝ)..1, w (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t)))))
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : (∫ t in (0:ℝ)..1, truncLp w n (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)))
        = (∫ t in (0:ℝ)..1, w (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t))) := by
      refine intervalIntegral.integral_congr fun (t : ℝ) ht => ?_
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact hsub j (le_of_lt (Finset.mem_range.mp hj)) t ht
    have h2 : (∫ t in (0:ℝ)..1,
          truncLp w n (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t)))
        = (∫ t in (0:ℝ)..1,
            w (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t))) := by
      refine intervalIntegral.integral_congr fun (t : ℝ) ht => ?_
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact hsub (j+1) (Nat.succ_le_of_lt (Finset.mem_range.mp hj)) t ht
    rw [h1, h2]
  exact Filter.Tendsto.congr' (hev.mono fun n hn => hn.symm) tendsto_const_nhds

/-! ## The interval projection as a multiplier -/

lemma integrable_mstInd_fourier {g : ℝ → ℂ} (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable (fun ξ : ℝ => mstInd ξ * FourierTransform.fourier g ξ) := by
  have hIint : MeasureTheory.Integrable mstInd := by
    have h : mstInd = (Set.Ioo (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℂ)) := by
      funext ξ; rw [mstInd, Set.indicator_apply]
    rw [h]
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr ?_
    refine MeasureTheory.integrableOn_const ?_ (by simp)
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hfour_meas : AEStronglyMeasurable (FourierTransform.fourier g) volume :=
    (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier
      (memLp_one_iff_integrable.mpr hg)).aestronglyMeasurable
  have hfour_bdd : ∀ᵐ ξ ∂volume, ‖FourierTransform.fourier g ξ‖ ≤ ∫ y : ℝ, ‖g y‖ :=
    Filter.Eventually.of_forall fun ξ => Commons.Analysis.CalderonZygmund.norm_fourier_le g ξ
  exact (hIint.bdd_mul hfour_meas hfour_bdd).congr
    (Filter.Eventually.of_forall fun ξ => mul_comm _ _)

lemma aestronglyMeasurable_mstProj {g : ℝ → ℂ} (hg : MeasureTheory.Integrable g) :
    AEStronglyMeasurable (mstProj g) volume :=
  (Commons.Analysis.Fourier.continuous_fourierInv_of_integrable _
    (integrable_mstInd_fourier hg)).aestronglyMeasurable

lemma norm_mstProj_le {g : ℝ → ℂ} (x : ℝ) :
    ‖mstProj g x‖ ≤ ∫ y : ℝ, ‖mstInd y * FourierTransform.fourier g y‖ :=
  norm_fourierInv_le _ x

/-! ## The core bound -/

theorem mstSym_multForm_bound (P : Polynomial ℤ) (r : ℕ) (hr : 2 ≤ r) {A C : ℝ}
    (hA : 0 < A) (hC : 0 < C)
    (hCbound : ∀ (f : ℝ → ℂ), MeasureTheory.Integrable f →
      MeasureTheory.MemLp f (ENNReal.ofReal (2 * (r:ℝ))) →
      ∫⁻ x : ℝ, ‖mstProj f x‖ₑ ^ (2*(r:ℝ))
        ≤ ENNReal.ofReal (C ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2*(r:ℝ)))
    (hreal : ∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j, ‖ε j‖ ≤ 1) → ∀ h : ℝ → ℂ,
      MeasureTheory.Integrable h →
      ∫⁻ x : ℝ, ‖mstS P i M ε h x‖ₑ ^ (2*(r:ℝ))
        ≤ ENNReal.ofReal (A ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2*(r:ℝ))) :
    ∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j, ‖ε j‖ ≤ 1) → ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
      ∫⁻ x : ℝ, ‖multForm (mstSym P i M ε) g x‖ₑ ^ (2*(r:ℝ))
        ≤ ENNReal.ofReal ((C*A) ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2*(r:ℝ)) := by
  intro i M ε hε
  have hq : (0:ℝ) ≤ 2*(r:ℝ) := by positivity
  have hCA : (0:ℝ) < C * A := mul_pos hC hA
  refine multForm_bound_of_l2 hq hCA.le (aestronglyMeasurable_mstSym P i M ε)
    (integrable_mstSym P i M ε hε) ?_
  intro g hg hg2
  by_cases hfin : (∫⁻ x : ℝ, ‖g x‖ₑ ^ (2*(r:ℝ))) = ⊤
  · rw [hfin, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hCA _)))]
    exact le_top
  · have hfin' : (∫⁻ x : ℝ, ‖g x‖ₑ ^ (2*(r:ℝ))) < ⊤ := lt_top_iff_ne_top.mpr hfin
    have hgq : MeasureTheory.MemLp g (ENNReal.ofReal (2*(r:ℝ))) volume := by
      rw [MeasureTheory.memLp_iff, MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (p := ENNReal.ofReal (2*(r:ℝ))) (by positivity) ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
        ENNReal.toReal_ofReal hq]
      exact hfin'
    have hproj := hCbound g hg hgq
    have hSbound : ∫⁻ x : ℝ, ‖mstS P i M ε (mstProj g) x‖ₑ ^ (2*(r:ℝ))
        ≤ ENNReal.ofReal (A ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖mstProj g x‖ₑ ^ (2*(r:ℝ)) := by
      have hpt : ∀ x : ℝ, Filter.Tendsto
          (fun n : ℕ => ‖mstS P i M ε (truncLp (mstProj g) n) x‖ₑ ^ (2*(r:ℝ)))
          Filter.atTop (𝓝 (‖mstS P i M ε (mstProj g) x‖ₑ ^ (2*(r:ℝ)))) := by
        intro x
        exact ((ENNReal.continuous_rpow_const).tendsto _).comp
          ((continuous_enorm.tendsto _).comp (tendsto_mstS_truncLp P i M ε x))
      have hmeas : ∀ n : ℕ, AEMeasurable (fun x : ℝ =>
          ‖mstS P i M ε (truncLp (mstProj g) n) x‖ₑ ^ (2*(r:ℝ))) volume := by
        intro n
        have hint : MeasureTheory.Integrable (truncLp (mstProj g) n) :=
          integrable_truncLp (aestronglyMeasurable_mstProj hg)
            (fun x => norm_mstProj_le x) n
        exact (((integrable_mstS P i M ε hint).aestronglyMeasurable).aemeasurable).enorm.pow_const _
      calc ∫⁻ x : ℝ, ‖mstS P i M ε (mstProj g) x‖ₑ ^ (2*(r:ℝ))
          = ∫⁻ x : ℝ, liminf (fun n : ℕ =>
              ‖mstS P i M ε (truncLp (mstProj g) n) x‖ₑ ^ (2*(r:ℝ))) Filter.atTop := by
            refine lintegral_congr_ae ?_
            filter_upwards with x
            exact (hpt x).liminf_eq.symm
        _ ≤ liminf (fun n : ℕ => ∫⁻ x : ℝ,
              ‖mstS P i M ε (truncLp (mstProj g) n) x‖ₑ ^ (2*(r:ℝ))) Filter.atTop :=
            lintegral_liminf_le' hmeas
        _ ≤ ENNReal.ofReal (A ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖mstProj g x‖ₑ ^ (2*(r:ℝ)) := by
            refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall fun _ => by simp⟩ ?_
            intro b hb
            obtain ⟨n, hn⟩ := hb.exists
            refine hn.trans ?_
            refine (hreal i M ε hε (truncLp (mstProj g) n)
              (integrable_truncLp (aestronglyMeasurable_mstProj hg)
                (fun x => norm_mstProj_le x) n)).trans ?_
            refine mul_le_mul' le_rfl ?_
            refine lintegral_mono fun x => ?_
            refine ENNReal.rpow_le_rpow ?_ hq
            rw [← ofReal_norm, ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (norm_truncLp_le (mstProj g) n x)
    have hid := multForm_mstSym_eq (P := P) (i := i) (M := M) (ε := ε) hg
    calc ∫⁻ x : ℝ, ‖multForm (mstSym P i M ε) g x‖ₑ ^ (2*(r:ℝ))
        = ∫⁻ x : ℝ, ‖mstS P i M ε (mstProj g) x‖ₑ ^ (2*(r:ℝ)) := by
          refine lintegral_congr fun x => ?_
          simp only [hid, enorm_neg]
      _ ≤ ENNReal.ofReal (A ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖mstProj g x‖ₑ ^ (2*(r:ℝ)) :=
          hSbound
      _ ≤ ENNReal.ofReal (A ^ (2*(r:ℝ))) *
            (ENNReal.ofReal (C ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2*(r:ℝ))) :=
          mul_le_mul' le_rfl hproj
      _ = ENNReal.ofReal ((C*A) ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2*(r:ℝ)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _),
            ← Real.mul_rpow hA.le hC.le, mul_comm A C]

/-! ## The theorem -/

theorem mstThetaRawMult_of_real {P : Polynomial ℤ} {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hreal : Work.BourgainPlan.Maximal.MSTThetaRealMult P r A) :
    ∃ B : ℝ, 0 < B ∧ Work.BourgainPlan.Maximal.MSTThetaRawMult P r B := by
  have hr2 : (1:ℝ) < 2 * (r:ℝ) := by
    have h2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith
  obtain ⟨C, hCpos, hC⟩ := interval_projection_memLp (2 * (r:ℝ)) hr2
  refine ⟨C * A, mul_pos hCpos hA, ?_⟩
  have hCbound : ∀ (f : ℝ → ℂ), MeasureTheory.Integrable f →
      MeasureTheory.MemLp f (ENNReal.ofReal (2*(r:ℝ))) →
      ∫⁻ x : ℝ, ‖mstProj f x‖ₑ ^ (2*(r:ℝ))
        ≤ ENNReal.ofReal (C ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2*(r:ℝ)) := by
    intro f hf hfq
    have h := hC (-(1/2)) (1/2) (by norm_num) f hf hfq
    simpa only [mstProj, mstInd, ENNReal.rpow_eq_pow] using h
  have hreal' : ∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j, ‖ε j‖ ≤ 1) → ∀ h : ℝ → ℂ,
      MeasureTheory.Integrable h →
      ∫⁻ x : ℝ, ‖mstS P i M ε h x‖ₑ ^ (2*(r:ℝ))
        ≤ ENNReal.ofReal (A ^ (2*(r:ℝ))) * ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2*(r:ℝ)) :=
    fun i M ε hε h hh => hreal i M ε hε h hh
  have hbound := mstSym_multForm_bound P r hr hA hCpos hCbound hreal'
  intro i M ε hε
  constructor
  · rw [iwMult_iff_multForm]
    intro g hg
    have hsym := hbound i M ε hε g hg
    have hae := circleLift_mstThetaEps_comp_iwRep P i M ε
    have hident : multForm
        (Work.BourgainPlan.Thm52.circleLift (fun ξ : Circ => mstThetaEps P i M ε (iwRep ξ))) g
        = multForm (mstSym P i M ε) g := by
      unfold multForm
      refine fourierInv_congr_ae ?_
      filter_upwards [hae] with ξ hξ
      rw [hξ]
    rwa [hident]
  · rw [iwMult_iff_multForm]
    intro g hg
    have hε' : ∀ j : ℕ, ‖starRingEnd ℂ (ε j)‖ ≤ 1 := fun j => by
      rw [Complex.norm_conj]; exact hε j
    have hsym := multForm_comp_neg_bound (q := 2*(r:ℝ))
      (m := mstSym P i M (fun j => starRingEnd ℂ (ε j))) (A := C*A)
      (hbound i M (fun j => starRingEnd ℂ (ε j)) hε') g hg
    have hae := circleLift_star_mstThetaEps_comp_iwRep P i M ε
    have hident : multForm
        (Work.BourgainPlan.Thm52.circleLift
          (fun ξ : Circ => starRingEnd ℂ (mstThetaEps P i M ε (iwRep ξ)))) g
        = multForm (fun x => mstSym P i M (fun j => starRingEnd ℂ (ε j)) (-x)) g := by
      unfold multForm
      refine fourierInv_congr_ae ?_
      filter_upwards [hae] with ξ hξ
      rw [hξ]
    have hgoal : multForm
        (Work.BourgainPlan.Thm52.circleLift
          (fun ξ : Circ => star (mstThetaEps P i M ε (iwRep ξ)))) g
        = multForm (fun x => mstSym P i M (fun j => starRingEnd ℂ (ε j)) (-x)) g := by
      rw [show (fun ξ : Circ => star (mstThetaEps P i M ε (iwRep ξ)))
          = (fun ξ : Circ => starRingEnd ℂ (mstThetaEps P i M ε (iwRep ξ))) from by
        funext ξ; rw [← starRingEnd_apply]]
      exact hident
    rw [hgoal]
    exact hsym

end

end Work.BourgainPlan.Maximal
