import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Fourier.dyadic_boundary_tiling_separated_bounded
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped FourierTransform ENNReal RealInnerProductSpace Topology

noncomputable section

namespace BoundaryLayer

/-! ## General `L²` multiplier machinery (real line) -/

/-- The pointwise product of an `L²` class with an essentially bounded function. -/
def mulLp (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (hm.mul (Lp.memLp g)).toLp (m * (g : ℝ → ℂ))

lemma mulLp_coe (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (mulLp m hm g : ℝ → ℂ) =ᵐ[volume] m * (g : ℝ → ℂ) :=
  MemLp.coeFn_toLp _

lemma enorm_eq_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  simp [enorm_eq_nnnorm]

lemma enorm_mulLp (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mulLp m hm g‖ₑ = (∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(g) ξ‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) := by
  rw [mulLp, MeasureTheory.Lp.enorm_toLp]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))]
  congr 1
  apply lintegral_congr
  intro ξ
  rw [Pi.mul_apply, enorm_mul]
  have h2 : (2:ℝ≥0∞).toReal = 2 := by simp
  rw [h2, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]

/-- The multiplier operator with symbol `m`: `f ↦ 𝓕⁻ (m · 𝓕 f)`. -/
def multiplier (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  𝓕⁻ (mulLp m hm (𝓕 f))

lemma enorm_fourierInv (Y : Lp ℂ 2 (volume : Measure ℝ)) : ‖𝓕⁻ Y‖ₑ = ‖Y‖ₑ := by
  have h : ‖𝓕⁻ Y‖ = ‖Y‖ := by
    have := MeasureTheory.Lp.norm_fourier_eq (𝓕⁻ Y)
    rw [FourierInvPair.fourier_fourierInv_eq] at this
    exact this.symm
  rw [MeasureTheory.Lp.enorm_def, MeasureTheory.Lp.enorm_def]
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def] at h
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp h with h' | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact h'
  · exact absurd h2 (MeasureTheory.Lp.eLpNorm_ne_top Y)
  · exact absurd h1 (MeasureTheory.Lp.eLpNorm_ne_top _)

lemma enorm_fourier (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖𝓕 f‖ₑ = ‖f‖ₑ := by
  have h : ‖𝓕 f‖ = ‖f‖ := MeasureTheory.Lp.norm_fourier_eq f
  rw [MeasureTheory.Lp.enorm_def, MeasureTheory.Lp.enorm_def]
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def] at h
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp h with h' | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact h'
  · exact absurd h2 (MeasureTheory.Lp.eLpNorm_ne_top f)
  · exact absurd h1 (MeasureTheory.Lp.eLpNorm_ne_top _)

lemma enorm_multiplier_sq (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖multiplier m hm f‖ₑ ^ (2:ℝ)
      = ∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
  rw [multiplier, enorm_fourierInv, enorm_mulLp, ← ENNReal.rpow_mul]
  norm_num

lemma lp_enorm_sq_eq_lintegral (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖g‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖(g : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
  rw [MeasureTheory.Lp.enorm_def,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (Lp.aestronglyMeasurable g)]
  have h2 : (2:ℝ≥0∞).toReal = 2 := by simp
  rw [h2, show (1:ℝ)/(2:ℝ) = 1/2 by norm_num, ← ENNReal.rpow_mul]
  norm_num

lemma sq_iSup_le_tsum {ι : Type*} [Countable ι] (u : ι → ℝ≥0∞) :
    (⨆ i, u i) ^ (2:ℝ) ≤ ∑' i, (u i) ^ (2:ℝ) := by
  set S : ℝ≥0∞ := ∑' i, (u i) ^ (2:ℝ) with hS
  have h1 : ∀ i, u i ≤ S ^ (1/2 : ℝ) := by
    intro i
    have hi : (u i) ^ (2:ℝ) ≤ S := by rw [hS]; exact ENNReal.le_tsum (f := fun i => (u i) ^ (2:ℝ)) i
    have h2 : ((u i) ^ (2:ℝ)) ^ (1/2:ℝ) ≤ S ^ (1/2:ℝ) := ENNReal.rpow_le_rpow hi (by norm_num)
    rwa [← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one] at h2
  calc (⨆ i, u i) ^ (2:ℝ) ≤ (S ^ (1/2:ℝ)) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow (iSup_le h1) (by norm_num)
    _ = S := by rw [← ENNReal.rpow_mul, show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- **`L²` square-function bound for a countable family of multipliers whose squared moduli
are pointwise summable.** -/
theorem l2_multiplier_square_function {ι : Type*} [Countable ι]
    (m : ι → ℝ → ℂ) (hm : ∀ i, MemLp (m i) ⊤ (volume : Measure ℝ))
    (f : Lp ℂ 2 (volume : Measure ℝ)) (A : ℝ)
    (hA : ∀ ξ, (∑' i, ‖m i ξ‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal (A^2)) :
    ∫⁻ x, (⨆ i, ‖(multiplier (m i) (hm i) f) x‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal (A^2) * ‖f‖ₑ ^ (2:ℝ) := by
  have hmeas : ∀ i, AEMeasurable (fun x => ‖(multiplier (m i) (hm i) f) x‖ₑ ^ (2:ℝ)) volume :=
    fun i => (MeasureTheory.Lp.aestronglyMeasurable (multiplier (m i) (hm i) f)).enorm.pow_const (2:ℝ)
  calc ∫⁻ x, (⨆ i, ‖(multiplier (m i) (hm i) f) x‖ₑ) ^ (2:ℝ)
      ≤ ∫⁻ x, ∑' i, ‖(multiplier (m i) (hm i) f) x‖ₑ ^ (2:ℝ) := by
        apply lintegral_mono; intro x
        exact sq_iSup_le_tsum (fun i => ‖(multiplier (m i) (hm i) f) x‖ₑ)
    _ = ∑' i, ∫⁻ x, ‖(multiplier (m i) (hm i) f) x‖ₑ ^ (2:ℝ) :=
        lintegral_tsum hmeas
    _ = ∑' i, ‖multiplier (m i) (hm i) f‖ₑ ^ (2:ℝ) := by
        apply tsum_congr; intro i
        rw [lp_enorm_sq_eq_lintegral]
    _ = ∑' i, ∫⁻ ξ, ‖m i ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
        apply tsum_congr; intro i
        rw [enorm_multiplier_sq]
    _ = ∫⁻ ξ, ∑' i, ‖m i ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) :=
        (lintegral_tsum (f := fun (i : ι) (ξ : ℝ) =>
            ‖m i ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ))
          (fun i => ((hm i).aestronglyMeasurable.enorm.pow_const (2:ℝ)).mul
            ((MeasureTheory.Lp.aestronglyMeasurable (𝓕 f)).enorm.pow_const (2:ℝ)))).symm
    _ = ∫⁻ ξ, (∑' i, ‖m i ξ‖ₑ ^ (2:ℝ)) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro ξ
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (A^2) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
        apply lintegral_mono; intro ξ
        exact mul_le_mul' (hA ξ) le_rfl
    _ = ENNReal.ofReal (A^2) * ∫⁻ ξ, ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A^2) * ‖𝓕 f‖ₑ ^ (2:ℝ) := by rw [lp_enorm_sq_eq_lintegral]
    _ = ENNReal.ofReal (A^2) * ‖f‖ₑ ^ (2:ℝ) := by rw [enorm_fourier]

/-! ## Plancherel for the pointwise inverse Fourier integral -/

lemma mpNeg : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) (volume : Measure ℝ) :=
  ⟨measurable_neg, Measure.map_neg_eq_self volume⟩

/-- **Plancherel for the pointwise inverse Fourier integral of an `L¹ ∩ L²` function.** -/
theorem lintegral_pwInv {h : ℝ → ℂ} (h1 : MemLp h 1 (volume : Measure ℝ))
    (h2 : MemLp h 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖𝓕⁻ h x‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) := by
  have hF : ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (fun ξ => 𝓕 h ξ) :=
    Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp h1 h2
  have hcomp : (fun x : ℝ => (𝓕 h) (-x))
      =ᵐ[volume]
        (fun x => ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (-x)) := by
    filter_upwards [(hF.comp_tendsto mpNeg.quasiMeasurePreserving.tendsto_ae).symm] with x hx
    simpa only [Function.comp_apply] using hx
  have hpw : ∀ x : ℝ, 𝓕⁻ h x = (𝓕 h) (-x) := fun x => Real.fourierInv_eq_fourier_neg h x
  have hHcoe : ((Lp.compMeasurePreserving (f := fun x : ℝ => -x) mpNeg
        (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume]
        fun x => ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (-x) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (f := fun x : ℝ => -x)
      (𝓕 (h2.toLp h)) mpNeg] with x hx
    simpa only [Function.comp_apply] using hx
  have hHG : ‖(Lp.compMeasurePreserving (f := fun x : ℝ => -x) mpNeg
        (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ))‖ₑ
      = ‖(𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))‖ₑ := by
    have := Lp.norm_compMeasurePreserving (f := fun x : ℝ => -x)
      (𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) mpNeg
    rw [← ofReal_norm, ← ofReal_norm, this]
  calc ∫⁻ x, ‖𝓕⁻ h x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖(𝓕 h) (-x)‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro x; rw [hpw x]
    _ = ∫⁻ x, ‖((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (-x)‖ₑ ^ (2:ℝ) :=
        lintegral_congr_ae (hcomp.mono fun x hx => by simp only [hx])
    _ = ∫⁻ x, ‖((Lp.compMeasurePreserving (f := fun x : ℝ => -x) mpNeg
            (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ ^ (2:ℝ) :=
        (lintegral_congr_ae (hHcoe.mono fun x hx => by simp only [hx])).symm
    _ = ‖(Lp.compMeasurePreserving (f := fun x : ℝ => -x) mpNeg
            (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ))‖ₑ ^ (2:ℝ) :=
        (lp_enorm_sq_eq_lintegral _).symm
    _ = ‖(𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))‖ₑ ^ (2:ℝ) := by rw [hHG]
    _ = ‖h2.toLp h‖ₑ ^ (2:ℝ) := by rw [enorm_fourier]
    _ = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) := by
        rw [lp_enorm_sq_eq_lintegral (h2.toLp h)]
        exact lintegral_congr_ae ((MemLp.coeFn_toLp h2).mono fun x hx => by simp only [hx])

section Setup
variable {K : ℕ}

def hj (j : ℕ) : ℝ := (2:ℝ) ^ (-(j:ℝ) - 1)

lemma hj_pos (j : ℕ) : 0 < hj j := Real.rpow_pos_of_pos (by norm_num) _

lemma hj_nonneg (j : ℕ) : 0 ≤ hj j := le_of_lt (hj_pos j)

lemma hj_le (j : ℕ) : hj j ≤ 1 / 2 := by
  have h2 : -(j : ℝ) - 1 ≤ -(1 : ℝ) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  calc hj j ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    _ = 1 / 2 := by rw [show (-(1 : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]; norm_num

lemma hj_half (j : ℕ) : hj (j+1) = hj j / 2 := by
  unfold hj
  have he : -(((j + 1 : ℕ) : ℝ)) - 1 = (-(j : ℝ) - 1) + (-(1 : ℝ)) := by push_cast; ring
  rw [he, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show (-(1 : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]; ring
lemma hj_mono {j j' : ℕ} (h : j ≤ j') : hj j' ≤ hj j := by
  unfold hj
  have h2 : -(j' : ℝ) - 1 ≤ -(j : ℝ) - 1 := by
    have : (j : ℝ) ≤ (j' : ℝ) := by exact_mod_cast h
    linarith
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h2

def Fexp (t θ : ℝ) : ℂ := Complex.exp (-(Complex.I * (t : ℂ) * (θ : ℂ)))

lemma measurable_Fexp (t : ℝ) : Measurable (Fexp t) := by
  unfold Fexp; fun_prop

lemma norm_ofReal (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

lemma norm_Fexp (t θ : ℝ) : ‖Fexp t θ‖ = 1 := by
  unfold Fexp
  rw [Complex.norm_exp]
  have : (-(Complex.I * (t : ℂ) * (θ : ℂ))).re = 0 := by simp
  rw [this, Real.exp_zero]

def FexpInv (t θ : ℝ) : ℂ := Complex.exp ((2 * Real.pi * inner ℝ θ t : ℝ) * Complex.I)

lemma Fexp_neg (t ξ : ℝ) : Fexp t (-(2 * Real.pi) * ξ) = FexpInv t ξ := by
  unfold Fexp FexpInv
  congr 1
  rw [Real.inner_apply]
  push_cast
  ring

def symb (lam : Fin K → ℝ) (φ : ℝ → ℝ) (j : ℕ) : ℝ → ℂ := fun θ =>
  ∑ k : Fin K, (Set.Ioc (lam k - hj j) (lam k + hj j)).indicator
     (fun θ => ((1 - φ ((θ - lam k) / hj j)) : ℂ)) θ

def bst (lam : Fin K → ℝ) (φ : ℝ → ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  ∑ k : Fin K, ∫ θ in (lam k - hj j)..(lam k + hj j),
      ((1 - φ ((θ - lam k) / hj j)) : ℂ) * Fexp t θ

def kern (lam : Fin K → ℝ) (φ : ℝ → ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  ∫ θ, symb lam φ j θ * Fexp t θ

def symF (lam : Fin K → ℝ) (φ : ℝ → ℝ) (j : ℕ) : ℝ → ℂ :=
  fun ξ => symb lam φ j (-(2 * Real.pi) * ξ)


end Setup

section Bracket
variable {K : ℕ} (lam : Fin K → ℝ)

lemma measurable_symb_summand {φ : ℝ → ℝ} (hφ : Measurable φ) (k : Fin K) (j : ℕ) :
    Measurable (fun θ => ((1 - φ ((θ - lam k) / hj j)) : ℂ)) := by
  unfold hj
  fun_prop

/-- The bracket is the Fourier transform of the symbol. -/
lemma bst_eq_kern {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (j : ℕ) (t : ℝ) : bst lam φ j t = kern lam φ j t := by
  unfold bst kern symb
  have hstep : ∀ k : Fin K,
      (∫ θ in (lam k - hj j)..(lam k + hj j),
          ((1 - φ ((θ - lam k) / hj j)) : ℂ) * Fexp t θ)
        = ∫ θ, (Set.Ioc (lam k - hj j) (lam k + hj j)).indicator
            (fun θ => ((1 - φ ((θ - lam k) / hj j)) : ℂ)) θ * Fexp t θ := by
    intro k
    rw [intervalIntegral.integral_of_le (by linarith [hj_nonneg j])]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with θ
    by_cases h : θ ∈ Set.Ioc (lam k - hj j) (lam k + hj j)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  rw [← MeasureTheory.integral_finsetSum]
  · congr 1 with θ
    rw [Finset.sum_mul]
  · intro k _
    have hg : Integrable ((Set.Ioc (lam k - hj j) (lam k + hj j)).indicator (fun _ : ℝ => (1:ℝ)))
        volume := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by simp)
    refine Integrable.mono' hg ?_ ?_
    · exact (((measurable_symb_summand lam hφ k j).indicator measurableSet_Ioc).mul
        (measurable_Fexp t)).aestronglyMeasurable
    · filter_upwards with θ
      by_cases h : θ ∈ Set.Ioc (lam k - hj j) (lam k + hj j)
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, norm_mul, norm_Fexp, mul_one]
        rw [show ((1 - φ ((θ - lam k)/hj j)) : ℂ) =
            (((1 - φ ((θ - lam k)/hj j)) : ℝ) : ℂ) from by norm_num]
        rw [norm_ofReal, abs_le]
        have hy := hbd ((θ - lam k)/hj j)
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
        simp


/-- The Fourier transform of the symbol is the inverse Fourier transform of the frequency symbol. -/
lemma kern_eq_invFT (lam : Fin K → ℝ) (φ : ℝ → ℝ) (j : ℕ) (t : ℝ) :
    kern lam φ j t = 2 * Real.pi * (𝓕⁻ (symF lam φ j) t) := by
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
      (g := fun θ => symb lam φ j θ * Fexp t θ) (-(2 * Real.pi))
  have hg : (fun x : ℝ => (fun θ => symb lam φ j θ * Fexp t θ) (-(2 * Real.pi) * x))
      = fun x : ℝ => symF lam φ j x * FexpInv t x := by
    funext x; simp only [symF, Fexp_neg]
  rw [hg] at hsub
  have hcoef : |(-(2 * Real.pi))⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [inv_neg, abs_neg, abs_of_pos (by positivity)]
  rw [hcoef] at hsub
  have hfw : 𝓕⁻ (symF lam φ j) t = ∫ x, symF lam φ j x * FexpInv t x := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with x
    rw [smul_eq_mul, mul_comm]
    rfl
  have hA : 𝓕⁻ (symF lam φ j) t = (2 * Real.pi)⁻¹ • kern lam φ j t := by
    rw [hfw, hsub]
    rfl
  rw [hA, Complex.real_smul]
  have hpos : (0:ℝ) < 2 * Real.pi := by positivity
  have h2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hpos
  have hcast : ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ h2, one_mul]

end Bracket


section Tiling
variable {K : ℕ} (lam : Fin K → ℝ)

/-- Finite version of the dyadic boundary-layer tiling bound. -/
lemma tiling_finite (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (φ : ℝ → ℝ) (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (θ : ℝ) :
    ∀ F : Finset ℕ, ∑ j ∈ F,
        |(if ∃ k : Fin K, |θ - lam k| ≤ hj j then (1 : ℝ) else 0)
          - ∑ k : Fin K, φ ((θ - lam k) / hj j)| ^ 2 ≤ 1 := by
  classical
  intro F
  set I : ℕ → ℝ := fun j => if ∃ k : Fin K, |θ - lam k| ≤ hj j then (1 : ℝ) else 0 with hI
  set S : ℕ → ℝ := fun j => ∑ k : Fin K, φ ((θ - lam k) / hj j) with hS
  set T : ℕ → ℝ := fun j => |I j - S j| ^ 2 with hT
  have hzero : ∀ (j : ℕ) (k0 : Fin K), |θ - lam k0| ≤ hj j →
      ∀ k : Fin K, k ≠ k0 → φ ((θ - lam k) / hj j) = 0 := by
    intro j k0 hk0 k hk
    by_contra hne
    have hlt1 : |(θ - lam k) / hj j| < 1 := by
      by_contra hcon
      simp only [not_lt] at hcon
      exact hne (h0 _ hcon)
    rw [abs_div, abs_of_pos (hj_pos j)] at hlt1
    have hlt2 : |θ - lam k| < hj j := (div_lt_one (hj_pos j)).mp hlt1
    have htri : |lam k - lam k0| ≤ |θ - lam k| + |θ - lam k0| := by
      calc |lam k - lam k0| = |(lam k - θ) + (θ - lam k0)| := by congr 1; ring
        _ ≤ |lam k - θ| + |θ - lam k0| := abs_add_le _ _
        _ = |θ - lam k| + |θ - lam k0| := by rw [abs_sub_comm]
    have hlt3 : |lam k - lam k0| < 1 := by have := hj_le j; linarith
    have hge := hsep k k0 hk
    linarith
  have hsum_single : ∀ (j : ℕ) (k0 : Fin K), |θ - lam k0| ≤ hj j →
      S j = φ ((θ - lam k0) / hj j) := by
    intro j k0 hk0
    exact Finset.sum_eq_single k0 (fun k _ hk => hzero j k0 hk0 k hk)
      (fun hmem => absurd (Finset.mem_univ k0) hmem)
  have hsum_zero : ∀ j : ℕ, (¬ ∃ k : Fin K, |θ - lam k| ≤ hj j) → S j = 0 := by
    intro j hex
    show (∑ k : Fin K, φ ((θ - lam k) / hj j)) = 0
    apply Finset.sum_eq_zero
    intro k _
    apply h0
    have hk : hj j < |θ - lam k| := by
      by_contra hc
      simp only [not_lt] at hc
      exact hex ⟨k, hc⟩
    rw [abs_div, abs_of_pos (hj_pos j), one_le_div (hj_pos j)]
    exact le_of_lt hk
  have hterm : ∀ j : ℕ, T j ≤ 1 := by
    intro j
    simp only [hT]
    by_cases hex : ∃ k : Fin K, |θ - lam k| ≤ hj j
    · obtain ⟨k0, hk0⟩ := hex
      have hI1 : I j = 1 := by simp only [hI]; exact if_pos ⟨k0, hk0⟩
      have hS1 := hsum_single j k0 hk0
      have hS0 : 0 ≤ S j := by rw [hS1]; exact (hbdd _).1
      have hSle : S j ≤ 1 := by rw [hS1]; exact (hbdd _).2
      have habs : |I j - S j| ≤ 1 := by
        rw [hI1, abs_le]; constructor <;> linarith
      exact pow_le_one₀ (abs_nonneg _) habs
    · have hI0 : I j = 0 := by simp only [hI]; exact if_neg hex
      have hS0 := hsum_zero j hex
      rw [hI0, hS0]; norm_num
  have hwit : ∀ j : ℕ, T j ≠ 0 →
      ∃ k : Fin K, hj j / 2 < |θ - lam k| ∧ |θ - lam k| ≤ hj j := by
    intro j hTj
    have hIS : I j ≠ S j := by
      intro hc
      exact hTj (by simp only [hT]; rw [hc]; simp)
    by_cases hex : ∃ k : Fin K, |θ - lam k| ≤ hj j
    · obtain ⟨k0, hk0⟩ := hex
      refine ⟨k0, ?_, hk0⟩
      have hI1 : I j = 1 := by simp only [hI]; exact if_pos ⟨k0, hk0⟩
      have hS1 := hsum_single j k0 hk0
      have hne1 : φ ((θ - lam k0) / hj j) ≠ 1 := by
        intro hc; exact hIS (by rw [hI1, hS1, hc])
      have hb1 : ¬ (|(θ - lam k0) / hj j| ≤ 1 / 2) := fun hc => hne1 (h1 _ hc)
      simp only [not_le] at hb1
      rw [abs_div, abs_of_pos (hj_pos j)] at hb1
      rw [lt_div_iff₀ (hj_pos j)] at hb1
      linarith
    · exfalso
      exact hIS (by simp only [hI]; rw [if_neg hex, hsum_zero j hex])
  have huniq : ∀ j j' : ℕ, T j ≠ 0 → T j' ≠ 0 → j = j' := by
    intro j j' hj' hj''
    by_contra hne
    obtain ⟨k, hk1, hk2⟩ := hwit j hj'
    obtain ⟨k', hk1', hk2'⟩ := hwit j' hj''
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hjj : j + 1 ≤ j' := hlt
      have hhalf_le : hj j' ≤ hj j / 2 := le_trans (hj_mono hjj) (le_of_eq (hj_half j))
      rcases eq_or_ne k k' with hkk | hkk
      · have hd : |θ - lam k| = |θ - lam k'| := by rw [hkk]
        linarith
      · have htri : |lam k - lam k'| ≤ |θ - lam k| + |θ - lam k'| := by
          calc |lam k - lam k'| = |(lam k - θ) + (θ - lam k')| := by congr 1; ring
            _ ≤ |lam k - θ| + |θ - lam k'| := abs_add_le _ _
            _ = |θ - lam k| + |θ - lam k'| := by rw [abs_sub_comm]
        have hlt3 : |lam k - lam k'| < 1 := by have := hj_le j; linarith
        have hge := hsep k k' hkk
        linarith
    · have hjj : j' + 1 ≤ j := hlt
      have hhalf_le : hj j ≤ hj j' / 2 := le_trans (hj_mono hjj) (le_of_eq (hj_half j'))
      rcases eq_or_ne k k' with hkk | hkk
      · have hd : |θ - lam k| = |θ - lam k'| := by rw [hkk]
        linarith
      · have htri : |lam k - lam k'| ≤ |θ - lam k| + |θ - lam k'| := by
          calc |lam k - lam k'| = |(lam k - θ) + (θ - lam k')| := by congr 1; ring
            _ ≤ |lam k - θ| + |θ - lam k'| := abs_add_le _ _
            _ = |θ - lam k| + |θ - lam k'| := by rw [abs_sub_comm]
        have hlt3 : |lam k - lam k'| < 1 := by have := hj_le j'; linarith
        have hge := hsep k k' hkk
        linarith
  by_cases hnon : ∃ j ∈ F, T j ≠ 0
  · obtain ⟨j0, hj0mem, hj0⟩ := hnon
    have hsingle : ∀ b ∈ F, b ≠ j0 → T b = 0 := by
      intro b hb hbne
      by_contra hb'
      exact hbne (huniq b j0 hb' hj0)
    rw [Finset.sum_eq_single j0 hsingle (fun h => absurd hj0mem h)]
    exact hterm j0
  · push_neg at hnon
    rw [Finset.sum_eq_zero hnon]
    norm_num

/-- The symbol agrees with the indicator-minus-plateau sum away from the endpoints. -/
lemma symb_eq (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (φ : ℝ → ℝ) (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (j : ℕ) (θ : ℝ)
    (hZ : ∀ k : Fin K, |θ - lam k| ≠ hj j) :
    symb lam φ j θ
      = (((if ∃ k : Fin K, |θ - lam k| ≤ hj j then (1:ℝ) else 0)
          - ∑ k : Fin K, φ ((θ - lam k)/hj j) : ℝ) : ℂ) := by
  classical
  have hmem : ∀ k : Fin K, θ ∈ Set.Ioc (lam k - hj j) (lam k + hj j) ↔ |θ - lam k| ≤ hj j := by
    intro k
    rw [Set.mem_Ioc, abs_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by linarith⟩
      rcases lt_or_eq_of_le h1 with h | h
      · linarith
      · exact absurd (show |θ - lam k| = hj j from by
          rw [← h, abs_neg, abs_of_pos (hj_pos j)]) (hZ k)
  have huniq : ∀ k l : Fin K, |θ - lam k| ≤ hj j → |θ - lam l| ≤ hj j → k = l := by
    intro k l hk hl
    by_contra hne
    have htri : |lam k - lam l| ≤ |θ - lam k| + |θ - lam l| := by
      calc |lam k - lam l| = |(lam k - θ) + (θ - lam l)| := by congr 1; ring
        _ ≤ |lam k - θ| + |θ - lam l| := abs_add_le _ _
        _ = |θ - lam k| + |θ - lam l| := by rw [abs_sub_comm]
    have hge := hsep k l hne
    have h2h := hj_le j
    have hk' : |θ - lam k| = hj j := by linarith
    exact hZ k hk'
  have hind : ∀ k : Fin K, (Set.Ioc (lam k - hj j) (lam k + hj j)).indicator
      (fun θ => ((1 - φ ((θ - lam k)/hj j)) : ℂ)) θ
      = if |θ - lam k| ≤ hj j then ((1 - φ ((θ - lam k)/hj j)) : ℂ) else 0 := by
    intro k
    rw [Set.indicator]
    by_cases h : θ ∈ Set.Ioc (lam k - hj j) (lam k + hj j)
    · rw [if_pos h, if_pos ((hmem k).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((hmem k).mpr hc))]
  have hzero : ∀ l : Fin K, ¬ (|θ - lam l| ≤ hj j) → φ ((θ - lam l)/hj j) = 0 := by
    intro l hl
    apply h0
    rw [abs_div, abs_of_pos (hj_pos j), one_le_div (hj_pos j)]
    exact le_of_lt (not_le.mp hl)
  unfold symb
  rw [Finset.sum_congr rfl (fun k _ => hind k)]
  by_cases hex : ∃ k : Fin K, |θ - lam k| ≤ hj j
  · obtain ⟨k0, hk0⟩ := hex
    have hL : (∑ k : Fin K, if |θ - lam k| ≤ hj j then ((1 - φ ((θ - lam k)/hj j)) : ℂ) else 0)
        = ((1 - φ ((θ - lam k0)/hj j)) : ℂ) := by
      have key : (∑ k : Fin K, if |θ - lam k| ≤ hj j then ((1 - φ ((θ - lam k)/hj j)) : ℂ) else 0)
          = (if |θ - lam k0| ≤ hj j then ((1 - φ ((θ - lam k0)/hj j)) : ℂ) else 0) :=
        Finset.sum_eq_single (s := Finset.univ)
          (f := fun k : Fin K => if |θ - lam k| ≤ hj j then ((1 - φ ((θ - lam k)/hj j)) : ℂ) else 0)
          k0 (fun b _ hb => by simp only [if_neg (fun hc => hb (huniq b k0 hc hk0))])
          (fun h => absurd (Finset.mem_univ k0) h)
      rw [key, if_pos hk0]
    have hR : (∑ k : Fin K, φ ((θ - lam k)/hj j)) = φ ((θ - lam k0)/hj j) :=
      Finset.sum_eq_single (s := Finset.univ) (f := fun k : Fin K => φ ((θ - lam k)/hj j))
        k0 (fun b _ hb => hzero b (fun hc => hb (huniq b k0 hc hk0)))
        (fun h => absurd (Finset.mem_univ k0) h)
    rw [hL, hR, if_pos ⟨k0, hk0⟩]
    norm_num
  · have hL : (∑ k : Fin K, if |θ - lam k| ≤ hj j then ((1 - φ ((θ - lam k)/hj j)) : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      simp only [if_neg (fun hc => hex ⟨b, hc⟩)]
    have hR : (∑ k : Fin K, φ ((θ - lam k)/hj j)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _; exact hzero b (fun hc => hex ⟨b, hc⟩)
    rw [hL, hR, if_neg hex]
    norm_num


lemma symb_enorm_sq_ofReal (x : ℝ) :
    ‖(((x : ℝ)) : ℂ)‖ₑ ^ (2:ℝ) = ENNReal.ofReal (|x|^2) := by
  rw [enorm_eq_ofReal_norm, norm_ofReal, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
    ENNReal.rpow_natCast]
  exact (ENNReal.ofReal_pow (abs_nonneg x) 2).symm

lemma countable_endpoints (lam : Fin K → ℝ) :
    (⋃ k : Fin K, ⋃ j : ℕ, ({(lam k + hj j), (lam k - hj j)} : Set ℝ)).Countable := by
  apply Set.countable_iUnion
  intro k
  apply Set.countable_iUnion
  intro j
  exact Set.Finite.countable (Set.finite_singleton _ |>.insert _)

/-- The pointwise dyadic tiling bound for the boundary-layer symbol, a.e. in frequency. -/
lemma ae_symb_tsum_le (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (φ : ℝ → ℝ) (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∀ᵐ θ ∂(volume : Measure ℝ),
      ∑' j : ℕ, ‖symb lam φ j θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal 4 := by
  set Z : Set ℝ := ⋃ k : Fin K, ⋃ j : ℕ, ({(lam k + hj j), (lam k - hj j)} : Set ℝ) with hZdef
  have hZnull : (volume : Measure ℝ) Z = 0 :=
    Set.Countable.measure_zero (countable_endpoints lam) volume
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ Z := by
    rw [ae_iff]
    convert hZnull using 2
    ext θ
    simp only [Set.mem_ofPred_eq, not_not]
  filter_upwards [hae] with θ hθ
  have hθk : ∀ (k : Fin K) (j : ℕ), |θ - lam k| ≠ hj j := by
    intro k j h
    apply hθ
    rw [hZdef]
    have h' : θ - lam k = hj j ∨ θ - lam k = -(hj j) := (abs_eq (le_of_lt (hj_pos j))).mp h
    refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h' with h' | h'
    · left; linarith
    · right; linarith
  have hsymb : ∀ j : ℕ, symb lam φ j θ
      = (((if ∃ k : Fin K, |θ - lam k| ≤ hj j then (1:ℝ) else 0)
          - ∑ k : Fin K, φ ((θ - lam k)/hj j) : ℝ) : ℂ) :=
    fun j => symb_eq lam hsep φ h0 j θ (fun k => hθk k j)
  calc ∑' j : ℕ, ‖symb lam φ j θ‖ₑ ^ (2:ℝ)
      = ∑' j : ℕ, ENNReal.ofReal
          ((|(if ∃ k : Fin K, |θ - lam k| ≤ hj j then (1:ℝ) else 0)
            - ∑ k : Fin K, φ ((θ - lam k)/hj j)|)^2) := by
        apply tsum_congr; intro j
        rw [hsymb j, symb_enorm_sq_ofReal]
    _ = ⨆ F : Finset ℕ, ∑ j ∈ F, ENNReal.ofReal
          ((|(if ∃ k : Fin K, |θ - lam k| ≤ hj j then (1:ℝ) else 0)
            - ∑ k : Fin K, φ ((θ - lam k)/hj j)|)^2) := ENNReal.tsum_eq_iSup_sum
    _ ≤ ENNReal.ofReal 4 := by
        apply iSup_le
        intro F
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        calc (∑ j ∈ F, |(if ∃ k : Fin K, |θ - lam k| ≤ hj j then (1:ℝ) else 0)
              - ∑ k : Fin K, φ ((θ - lam k)/hj j)|^2) ≤ 1 :=
              tiling_finite lam hsep φ h1 h0 hbdd θ F
          _ ≤ 4 := by norm_num

end Tiling


section Symbol
variable {K : ℕ} (lam : Fin K → ℝ)

/-- A crude bound for the frequencies. -/
def freqBound (lam : Fin K → ℝ) : ℝ := ∑ k : Fin K, |lam k| + 1

lemma freqBound_nonneg (lam : Fin K → ℝ) : 0 ≤ freqBound lam := by
  have : (0:ℝ) ≤ ∑ k : Fin K, |lam k| :=
    Finset.sum_nonneg (s := Finset.univ) (f := fun k : Fin K => |lam k|)
      (fun i _ => abs_nonneg (lam i))
  simp only [freqBound]; linarith

lemma abs_lam_add_one_le_freqBound (lam : Fin K → ℝ) (k : Fin K) : |lam k| + 1 ≤ freqBound lam := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin K => |lam k|)
    (fun i _ => abs_nonneg (lam i)) (a := k) (Finset.mem_univ k)
  simp only [freqBound]; linarith

lemma measurable_symb {φ : ℝ → ℝ} (hφ : Measurable φ) (j : ℕ) : Measurable (symb lam φ j) := by
  unfold symb
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact (measurable_symb_summand lam hφ k j).indicator measurableSet_Ioc

lemma norm_symb_le {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (j : ℕ) (θ : ℝ) :
    ‖symb lam φ j θ‖ ≤ (K : ℝ) := by
  unfold symb
  calc ‖∑ k : Fin K, (Set.Ioc (lam k - hj j) (lam k + hj j)).indicator
        (fun θ => ((1 - φ ((θ - lam k) / hj j)) : ℂ)) θ‖
      ≤ ∑ k : Fin K, ‖(Set.Ioc (lam k - hj j) (lam k + hj j)).indicator
        (fun θ => ((1 - φ ((θ - lam k) / hj j)) : ℂ)) θ‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin K, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [Set.indicator]
        by_cases h : θ ∈ Set.Ioc (lam k - hj j) (lam k + hj j)
        · rw [if_pos h]
          rw [show ((1 - φ ((θ - lam k)/hj j)) : ℂ) =
              (((1 - φ ((θ - lam k)/hj j)) : ℝ) : ℂ) from by norm_num, norm_ofReal, abs_le]
          have hy := hbd ((θ - lam k)/hj j)
          exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
        · rw [if_neg h]; simp
    _ = (K : ℝ) := by simp

lemma symb_support_subset (φ : ℝ → ℝ) (j : ℕ) :
    Function.support (symb lam φ j) ⊆ Set.Icc (-(freqBound lam)) (freqBound lam) := by
  intro θ hθ
  simp only [Function.mem_support] at hθ
  by_contra hcon
  apply hθ
  unfold symb
  apply Finset.sum_eq_zero
  intro k _
  rw [Set.indicator_of_notMem]
  intro hmem
  apply hcon
  rw [Set.mem_Icc]
  rw [Set.mem_Ioc] at hmem
  have hk := abs_lam_add_one_le_freqBound lam k
  exact ⟨by linarith [hmem.1, hj_le j, neg_abs_le (lam k)],
         by linarith [hmem.2, hj_le j, le_abs_self (lam k)]⟩

lemma hasCompactSupport_symb (φ : ℝ → ℝ) (j : ℕ) : HasCompactSupport (symb lam φ j) :=
  IsCompact.of_isClosed_subset (isCompact_Icc (a := -(freqBound lam)) (b := freqBound lam))
    isClosed_closure (closure_minimal (symb_support_subset lam φ j)
      (isClosed_Icc (a := -(freqBound lam)) (b := freqBound lam)))

lemma memLp_symb {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (j : ℕ) (p : ℝ≥0∞) :
    MemLp (symb lam φ j) p volume :=
  (hasCompactSupport_symb lam φ j).memLp_of_bound (measurable_symb lam hφ j).aestronglyMeasurable
    (K : ℝ) (Filter.Eventually.of_forall (norm_symb_le lam hbd j))

lemma measurable_symF {φ : ℝ → ℝ} (hφ : Measurable φ) (j : ℕ) : Measurable (symF lam φ j) := by
  unfold symF
  exact (measurable_symb lam hφ j).comp (by fun_prop)

lemma norm_symF_le {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (j : ℕ) (ξ : ℝ) :
    ‖symF lam φ j ξ‖ ≤ (K : ℝ) := norm_symb_le lam hbd j _

lemma symF_support_subset (φ : ℝ → ℝ) (j : ℕ) :
    Function.support (symF lam φ j) ⊆
      Set.Icc (-(freqBound lam / (2 * Real.pi))) (freqBound lam / (2 * Real.pi)) := by
  intro ξ hξ
  rw [Function.mem_support] at hξ
  have h : symb lam φ j (-(2 * Real.pi) * ξ) ≠ 0 := by
    intro hc; exact hξ (by simp only [symF]; exact hc)
  have hI := symb_support_subset lam φ j (by rwa [Function.mem_support])
  rw [Set.mem_Icc] at hI ⊢
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  refine ⟨?_, ?_⟩
  · rw [← neg_div, div_le_iff₀ hp]; linarith [hI.2]
  · rw [le_div_iff₀ hp]; linarith [hI.1]

lemma hasCompactSupport_symF (φ : ℝ → ℝ) (j : ℕ) : HasCompactSupport (symF lam φ j) :=
  IsCompact.of_isClosed_subset
    (isCompact_Icc (a := -(freqBound lam / (2 * Real.pi))) (b := freqBound lam / (2 * Real.pi)))
    isClosed_closure (closure_minimal (symF_support_subset lam φ j)
      (isClosed_Icc (a := -(freqBound lam / (2 * Real.pi))) (b := freqBound lam / (2 * Real.pi))))

lemma memLp_symF {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (j : ℕ) (p : ℝ≥0∞) :
    MemLp (symF lam φ j) p volume :=
  (hasCompactSupport_symF lam φ j).memLp_of_bound (measurable_symF lam hφ j).aestronglyMeasurable
    (K : ℝ) (Filter.Eventually.of_forall (norm_symF_le lam hbd j))

end Symbol


section Fubini

lemma inner_integral_eq (f : ℝ → ℂ) (hfi : Integrable f) (x θ : ℝ) :
    (∫ y, f y * Fexp (x - y) θ) = Fexp x θ * 𝓕 f (-(θ/(2*Real.pi))) := by
  have hsplit : ∀ y : ℝ, Fexp (x-y) θ
      = Fexp x θ * Complex.exp (Complex.I * (y : ℂ) * (θ : ℂ)) := by
    intro y
    unfold Fexp
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc ∫ y, f y * Fexp (x - y) θ
      = ∫ y, f y * (Fexp x θ * Complex.exp (Complex.I * (y : ℂ) * (θ : ℂ))) := by
        apply integral_congr_ae; filter_upwards with y; rw [hsplit y]
    _ = Fexp x θ * ∫ y, f y * Complex.exp (Complex.I * (y : ℂ) * (θ : ℂ)) := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae; filter_upwards with y; ring
    _ = Fexp x θ * 𝓕 f (-(θ/(2*Real.pi))) := by
        congr 1
        rw [Real.fourier_eq']
        apply integral_congr_ae; filter_upwards with v
        rw [smul_eq_mul, Real.inner_apply, mul_comm (f v)]
        congr 1
        have hv : -2 * Real.pi * (v * (-(θ/(2*Real.pi)))) = v * θ := by field_simp
        rw [hv]
        push_cast
        ring_nf

lemma integrable_fubini_kernel (Mj : ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ)
    (hM1 : MemLp Mj 1 volume) (hf1 : MemLp f 1 volume) :
    Integrable (fun p : ℝ × ℝ => f p.1 * (Mj p.2 * Fexp (x - p.1) p.2)) (volume.prod volume) := by
  have hg : Integrable (fun p : ℝ × ℝ => ‖f p.1‖ * ‖Mj p.2‖) (volume.prod volume) :=
    (memLp_one_iff_integrable.mp hf1).norm.mul_prod (memLp_one_iff_integrable.mp hM1).norm
  refine hg.mono' ?_ ?_
  · have hcont : Continuous (fun p : ℝ × ℝ => Fexp (x - p.1) p.2) := by
      unfold Fexp; fun_prop
    exact (hf1.aestronglyMeasurable.comp_fst).mul
      ((hM1.aestronglyMeasurable.comp_snd).mul hcont.aestronglyMeasurable)
  · filter_upwards with p
    rw [norm_mul, norm_mul, norm_Fexp, mul_one]

lemma fubini_kernel_eq (Mj : ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ)
    (hM1 : MemLp Mj 1 volume) (hf1 : MemLp f 1 volume) :
    (∫ y, f y * (∫ θ, Mj θ * Fexp (x - y) θ))
      = ∫ θ, Mj θ * (∫ y, f y * Fexp (x - y) θ) := by
  have hint := integrable_fubini_kernel Mj f x hM1 hf1
  calc ∫ y, f y * (∫ θ, Mj θ * Fexp (x - y) θ)
      = ∫ y, ∫ θ, f y * (Mj θ * Fexp (x - y) θ) := by
        apply integral_congr_ae; filter_upwards with y
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ θ, ∫ y, f y * (Mj θ * Fexp (x - y) θ) := integral_integral_swap hint
    _ = ∫ θ, Mj θ * (∫ y, f y * Fexp (x - y) θ) := by
        apply integral_congr_ae; filter_upwards with θ
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae; filter_upwards with y; ring

lemma kern_fubini (Mj : ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ)
    (hM1 : MemLp Mj 1 volume) (hf1 : MemLp f 1 volume) :
    (∫ y, f y * (∫ θ, Mj θ * Fexp (x - y) θ))
      = 2 * Real.pi * 𝓕⁻ (fun ξ => Mj (-(2*Real.pi) * ξ) * 𝓕 f ξ) x := by
  rw [fubini_kernel_eq Mj f x hM1 hf1]
  have hfi := memLp_one_iff_integrable.mp hf1
  have hstep : ∀ θ : ℝ, (∫ y, f y * Fexp (x-y) θ) = Fexp x θ * 𝓕 f (-(θ/(2*Real.pi))) :=
    fun θ => inner_integral_eq f hfi x θ
  have hG : (∫ θ, Mj θ * (Fexp x θ * 𝓕 f (-(θ/(2*Real.pi)))))
      = 2 * Real.pi * ∫ ξ, Mj (-(2*Real.pi)*ξ) * 𝓕 f ξ * FexpInv x ξ := by
    have hg : ∀ ξ : ℝ, (fun θ => Mj θ * (Fexp x θ * 𝓕 f (-(θ/(2*Real.pi))))) (-(2*Real.pi)*ξ)
        = Mj (-(2*Real.pi)*ξ) * 𝓕 f ξ * FexpInv x ξ := by
      intro ξ
      show Mj (-(2*Real.pi)*ξ) * (Fexp x (-(2*Real.pi)*ξ)
            * 𝓕 f (-((-(2*Real.pi)*ξ)/(2*Real.pi)))) = Mj (-(2*Real.pi)*ξ) * 𝓕 f ξ * FexpInv x ξ
      rw [show (-((-(2*Real.pi)*ξ)/(2*Real.pi))) = ξ from by field_simp, Fexp_neg]
      ring
    have hcv := Measure.integral_comp_mul_left
      (g := fun θ => Mj θ * (Fexp x θ * 𝓕 f (-(θ/(2*Real.pi))))) (-(2*Real.pi))
    simp only [hg] at hcv
    have hcoef : |(-(2*Real.pi))⁻¹| = (2*Real.pi)⁻¹ := by
      rw [inv_neg, abs_neg, abs_of_pos (by positivity)]
    rw [hcoef] at hcv
    have hpos : (0:ℝ) < 2 * Real.pi := by positivity
    have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpos
    have hH : (∫ ξ, Mj (-(2*Real.pi)*ξ) * 𝓕 f ξ * FexpInv x ξ)
        = (2 * Real.pi)⁻¹ • ∫ θ, Mj θ * (Fexp x θ * 𝓕 f (-(θ/(2*Real.pi)))) := hcv
    rw [hH, Complex.real_smul]
    rw [show ((2:ℂ) * (Real.pi:ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast hne), one_mul]
  calc ∫ θ, Mj θ * (∫ y, f y * Fexp (x - y) θ)
      = ∫ θ, Mj θ * (Fexp x θ * 𝓕 f (-(θ/(2*Real.pi)))) := by
        apply integral_congr_ae; filter_upwards with θ; rw [hstep θ]
    _ = 2 * Real.pi * ∫ ξ, Mj (-(2*Real.pi)*ξ) * 𝓕 f ξ * FexpInv x ξ := hG
    _ = 2 * Real.pi * 𝓕⁻ (fun ξ => Mj (-(2*Real.pi) * ξ) * 𝓕 f ξ) x := by
        congr 1
        rw [Real.fourierInv_eq']
        apply integral_congr_ae; filter_upwards with ξ
        simp only [smul_eq_mul, FexpInv, Real.inner_apply]
        ring

end Fubini


section Bound
variable {K : ℕ} (lam : Fin K → ℝ)

lemma mpSub (x : ℝ) : MeasurePreserving (fun y : ℝ => x - y) volume volume :=
  (measurePreserving_add_left volume x).comp mpNeg

lemma memLp_fourier {f : ℝ → ℂ} (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume :=
  (Lp.memLp (𝓕 (hf2.toLp f))).ae_eq (fourier_toLp_ae_eq_fourier_of_memLp hf1 hf2)

lemma enorm_const_mul_sq (c : ℝ) (z : ℂ) :
    ‖(c : ℂ) * z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (c^2) * ‖z‖ₑ ^ (2:ℝ) := by
  rw [enorm_mul, enorm_eq_ofReal_norm, norm_ofReal]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]
  rw [ENNReal.rpow_natCast]
  rw [← ENNReal.ofReal_pow (abs_nonneg c) 2]
  congr 1
  rw [sq_abs]

lemma fourierInv_symF {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (j : ℕ) :
    ∀ t : ℝ, bst lam φ j t = ((2*Real.pi : ℝ) : ℂ) * 𝓕⁻ (symF lam φ j) t := fun t => by
  rw [bst_eq_kern lam hφ hbd j t, kern_eq_invFT lam φ j t]
  push_cast; ring

lemma lintegral_bst_sq {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (j : ℕ) :
    ∫⁻ y, ‖bst lam φ j y‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal ((2*Real.pi)^2) * ∫⁻ ξ, ‖symF lam φ j ξ‖ₑ ^ (2:ℝ) := by
  have h := fourierInv_symF lam hφ hbd j
  calc ∫⁻ y, ‖bst lam φ j y‖ₑ ^ (2:ℝ)
      = ∫⁻ y, ‖((2*Real.pi : ℝ) : ℂ) * 𝓕⁻ (symF lam φ j) y‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro y; rw [h y]
    _ = ∫⁻ y, ENNReal.ofReal ((2*Real.pi)^2) * ‖𝓕⁻ (symF lam φ j) y‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro y; rw [enorm_const_mul_sq]
    _ = ENNReal.ofReal ((2*Real.pi)^2) * ∫⁻ y, ‖𝓕⁻ (symF lam φ j) y‖ₑ ^ (2:ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((2*Real.pi)^2) * ∫⁻ ξ, ‖symF lam φ j ξ‖ₑ ^ (2:ℝ) := by
        rw [lintegral_pwInv (memLp_symF lam hφ hbd j 1) (memLp_symF lam hφ hbd j 2)]

lemma measurable_fourier {g : ℝ → ℂ} (hg : MemLp g 1 volume) : Measurable (𝓕 g) :=
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
    (memLp_one_iff_integrable.mp hg)).measurable

lemma measurable_fourierInv {g : ℝ → ℂ} (hg : MemLp g 1 volume) :
    Measurable (fun t => 𝓕⁻ g t) := by
  have hc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
      (memLp_one_iff_integrable.mp hg)
  have : (fun t : ℝ => 𝓕⁻ g t) = fun t => 𝓕 g (-t) :=
    funext (fun t => Real.fourierInv_eq_fourier_neg g t)
  rw [this]
  exact (hc.comp continuous_neg).measurable

lemma measurable_bst {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (j : ℕ) :
    Measurable (bst lam φ j) := by
  have h := fourierInv_symF lam hφ hbd j
  rw [show bst lam φ j = fun t => ((2*Real.pi : ℝ) : ℂ) * 𝓕⁻ (symF lam φ j) t from funext h]
  exact (measurable_const.mul
    (measurable_fourierInv (memLp_symF lam hφ hbd j 1)))

lemma lintegral_bst_shift {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (j : ℕ) (x : ℝ) :
    ∫⁻ y, ‖bst lam φ j (x - y)‖ₑ ^ (2:ℝ) = ∫⁻ y, ‖bst lam φ j y‖ₑ ^ (2:ℝ) :=
  (mpSub x).lintegral_comp ((measurable_bst lam hφ hbd j).enorm.pow_const (2:ℝ))

lemma memLp_fourier_symF {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (j : ℕ) {f : ℝ → ℂ} (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    MemLp (fun ξ => symF lam φ j ξ * 𝓕 f ξ) 1 volume ∧
      MemLp (fun ξ => symF lam φ j ξ * 𝓕 f ξ) 2 volume := by
  have hF : MemLp (𝓕 f) 2 volume := memLp_fourier hf1 hf2
  refine ⟨?_, ?_⟩
  · exact MemLp.mul (p := 2) (q := 2) (r := 1) (memLp_symF lam hφ hbd j 2) hF
  · exact MemLp.mul (p := ⊤) (q := 2) (r := 2) (memLp_symF lam hφ hbd j ⊤) hF

lemma ae_symF_tsum_le (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (φ : ℝ → ℝ) (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∀ᵐ ξ ∂(volume : Measure ℝ),
      ∑' j : ℕ, ‖symF lam φ j ξ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal 4 := by
  have h := ae_symb_tsum_le lam hsep φ h1 h0 hbd
  have hqmp : Measure.QuasiMeasurePreserving (fun ξ : ℝ => -(2*Real.pi)*ξ) volume volume := by
    have hh : (-(2*Real.pi)) ≠ 0 := by rw [neg_ne_zero]; positivity
    have hsm := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hh
    simpa [smul_eq_mul] using hsm
  filter_upwards [hqmp.ae h] with ξ hξ
  simpa only [symF] using hξ

lemma hH_gen {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 volume) (j : ℕ) (x : ℝ) :
    (∫ y, f y * bst lam φ j (x - y))
      = ((2*Real.pi : ℝ) : ℂ) * 𝓕⁻ (fun ξ => symF lam φ j ξ * 𝓕 f ξ) x := by
  have hbst : (∫ y, f y * bst lam φ j (x - y))
      = ∫ y, f y * (∫ θ, symb lam φ j θ * Fexp (x - y) θ) := by
    apply integral_congr_ae; filter_upwards with y
    rw [bst_eq_kern lam hφ hbd j (x - y)]; rfl
  rw [hbst, kern_fubini (symb lam φ j) f x (memLp_symb lam hφ hbd j 1) hf1]
  have hf_eq : (fun ξ => symb lam φ j (-(2*Real.pi)*ξ) * 𝓕 f ξ)
      = fun ξ => symF lam φ j ξ * 𝓕 f ξ := by ext ξ; rfl
  rw [hf_eq]
  norm_num

lemma lintegral_enorm_sq_lt_top {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    ∫⁻ y, ‖g y‖ₑ ^ (2:ℝ) < ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hg.eLpNorm_lt_top
  simpa using h

lemma memLp_bst {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (j : ℕ) :
    MemLp (bst lam φ j) 2 volume := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (measurable_bst lam hφ hbd j).aestronglyMeasurable,
    show ((2:ℝ≥0∞)).toReal = 2 by norm_num, lintegral_bst_sq lam hφ hbd j]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lintegral_enorm_sq_lt_top (memLp_symF lam hφ hbd j 2))

lemma memLp_bst_shift {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (j : ℕ) (x : ℝ) : MemLp (fun y : ℝ => bst lam φ j (x - y)) 2 volume :=
  (memLp_bst lam hφ hbd j).comp_measurePreserving (mpSub x)

lemma integrable_bound_bst {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (j : ℕ) (x : ℝ) :
    Integrable (fun y : ℝ => ‖f y‖ * ‖bst lam φ j (x - y)‖) volume := by
  refine ⟨(hf.aestronglyMeasurable.norm).mul
      ((memLp_bst_shift lam hφ hbd j x).aestronglyMeasurable.norm), ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ y, ENNReal.ofReal ‖‖f y‖ * ‖bst lam φ j (x - y)‖‖
      = ∫⁻ y, ‖f y‖ₑ * ‖bst lam φ j (x - y)‖ₑ := by
        apply lintegral_congr; intro y
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
          ENNReal.ofReal_mul (norm_nonneg _),
          ← enorm_eq_ofReal_norm, ← enorm_eq_ofReal_norm]
    _ ≤ (∫⁻ y, ‖f y‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ)) *
          (∫⁻ y, ‖bst lam φ j (x - y)‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
          (hf.aestronglyMeasurable.enorm)
          ((memLp_bst_shift lam hφ hbd j x).aestronglyMeasurable.enorm)
    _ < ⊤ := by
        apply ENNReal.mul_lt_top
        · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            (lintegral_enorm_sq_lt_top hf).ne
        · rw [lintegral_bst_shift lam hφ hbd j x, lintegral_bst_sq lam hφ hbd j]
          exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (lintegral_enorm_sq_lt_top (memLp_symF lam hφ hbd j 2))).ne

lemma l2_bound_L1L2 {φ : ℝ → ℝ} (hφ : Measurable φ) (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (f : ℝ → ℂ) (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ)
      ≤ ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) := by
  have hH : ∀ (j : ℕ) (x : ℝ), (∫ y, f y * bst lam φ j (x - y))
      = ((2*Real.pi : ℝ) : ℂ) * 𝓕⁻ (fun ξ => symF lam φ j ξ * 𝓕 f ξ) x :=
    fun j x => hH_gen lam hφ hbd hf1 j x
  have hper : ∀ j : ℕ, ∫⁻ x, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal ((2*Real.pi)^2) * ∫⁻ ξ, ‖symF lam φ j ξ * 𝓕 f ξ‖ₑ ^ (2:ℝ) := by
    intro j
    have hcongr : (fun x => ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ))
        = fun x => ‖((2*Real.pi : ℝ) : ℂ) * 𝓕⁻ (fun ξ => symF lam φ j ξ * 𝓕 f ξ) x‖ₑ ^ (2:ℝ) := by
      funext x; rw [hH j x]
    rw [hcongr]
    have hstep : ∫⁻ x, ‖((2*Real.pi : ℝ) : ℂ) * 𝓕⁻ (fun ξ => symF lam φ j ξ * 𝓕 f ξ) x‖ₑ ^ (2:ℝ)
        = ∫⁻ x, ENNReal.ofReal ((2*Real.pi)^2) * ‖𝓕⁻ (fun ξ => symF lam φ j ξ * 𝓕 f ξ) x‖ₑ ^ (2:ℝ) := by
      apply lintegral_congr; intro x; rw [enorm_const_mul_sq]
    rw [hstep, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_pwInv (memLp_fourier_symF lam hφ hbd j hf1 hf2).1
        (memLp_fourier_symF lam hφ hbd j hf1 hf2).2]
  have hmeas : ∀ j : ℕ, AEMeasurable (fun x : ℝ => ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)) volume := by
    intro j
    have hc : (fun x : ℝ => ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ))
        = fun x : ℝ => ENNReal.ofReal ((2*Real.pi)^2) *
            ‖𝓕⁻ (fun ξ => symF lam φ j ξ * 𝓕 f ξ) x‖ₑ ^ (2:ℝ) := by
      funext x
      rw [hH j x, enorm_const_mul_sq]
    rw [hc]
    exact (measurable_const.mul ((measurable_fourierInv
      (memLp_fourier_symF lam hφ hbd j hf1 hf2).1).enorm.pow_const _)).aemeasurable
  have hsum : ∫⁻ x, ∑' j : ℕ, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)
      = ∑' j : ℕ, ∫⁻ x, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ) :=
    lintegral_tsum hmeas
  have hsum2 : ∑' j : ℕ, ∫⁻ ξ, ‖symF lam φ j ξ * 𝓕 f ξ‖ₑ ^ (2:ℝ)
      = ∫⁻ ξ, ∑' j : ℕ, ‖symF lam φ j ξ * 𝓕 f ξ‖ₑ ^ (2:ℝ) := by
    refine (lintegral_tsum ?_).symm
    intro j
    exact (((measurable_symF lam hφ j).mul
      (measurable_fourier hf1)).enorm.pow_const _).aemeasurable
  have hpoint : ∀ ξ : ℝ, ∑' j : ℕ, ‖symF lam φ j ξ * 𝓕 f ξ‖ₑ ^ (2:ℝ)
      = (∑' j : ℕ, ‖symF lam φ j ξ‖ₑ ^ (2:ℝ)) * ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
    intro ξ
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr; intro j
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  have hplanch : ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ) = ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) := by
    have hae : ((𝓕 (hf2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 f :=
      fourier_toLp_ae_eq_fourier_of_memLp hf1 hf2
    calc ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ)
        = ∫⁻ ξ, ‖((𝓕 (hf2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ) :=
          lintegral_congr_ae (hae.mono (fun ξ hξ => by simp only [← hξ]))
      _ = ‖(𝓕 (hf2.toLp f) : Lp ℂ 2 volume)‖ₑ ^ (2:ℝ) := (lp_enorm_sq_eq_lintegral _).symm
      _ = ‖hf2.toLp f‖ₑ ^ (2:ℝ) := by rw [enorm_fourier]
      _ = ∫⁻ x, ‖(hf2.toLp f : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := lp_enorm_sq_eq_lintegral _
      _ = ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) := by
          apply lintegral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hf2] with x hx
          rw [hx, enorm_eq_ofReal_norm]
  calc ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ)
      = ∫⁻ x, ∑' j : ℕ, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro x
        apply tsum_congr; intro j
        rw [enorm_eq_ofReal_norm]
    _ = ∑' j : ℕ, ∫⁻ x, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ) := hsum
    _ = ENNReal.ofReal ((2*Real.pi)^2) *
          ∑' j : ℕ, ∫⁻ ξ, ‖symF lam φ j ξ * 𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        rw [tsum_congr (fun j => hper j), ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal ((2*Real.pi)^2) *
          ∫⁻ ξ, ∑' j : ℕ, ‖symF lam φ j ξ * 𝓕 f ξ‖ₑ ^ (2:ℝ) := by rw [hsum2]
    _ = ENNReal.ofReal ((2*Real.pi)^2) *
          ∫⁻ ξ, (∑' j : ℕ, ‖symF lam φ j ξ‖ₑ ^ (2:ℝ)) * ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        congr 1
        apply lintegral_congr; intro ξ; rw [hpoint]
    _ ≤ ENNReal.ofReal ((2*Real.pi)^2) *
          ∫⁻ ξ, ENNReal.ofReal 4 * ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        exact mul_le_mul_right (by
          apply lintegral_mono_ae
          filter_upwards [ae_symF_tsum_le lam hsep φ h1 h0 hbd] with ξ hξ
          exact mul_le_mul_left hξ _) _
    _ = ENNReal.ofReal ((2*Real.pi)^2) *
          (ENNReal.ofReal 4 * ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ)) := by
        congr 1
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((2*Real.pi)^2) * ENNReal.ofReal 4 *
          ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by ring
    _ = ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        congr 1
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2*Real.pi)^2)]
        congr 1
        ring
    _ = ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) := by
        rw [hplanch]

end Bound


section General
variable {K : ℕ} (lam : Fin K → ℝ)

lemma indicator_Icc_memLp (n : ℕ) (p : ℝ≥0∞) :
    MemLp (fun y : ℝ => (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℂ)) y) p volume := by
  refine HasCompactSupport.memLp_of_bound ?_ ?_ 1 (Filter.Eventually.of_forall (fun y => ?_))
  · refine IsCompact.of_isClosed_subset (isCompact_Icc (a := -(n:ℝ)) (b := (n:ℝ))) isClosed_closure
      (closure_minimal ?_ (isClosed_Icc (a := -(n:ℝ)) (b := (n:ℝ))))
    intro y hy
    simp only [Function.mem_support] at hy
    by_contra hc
    exact hy (by rw [Set.indicator_apply, if_neg hc])
  · exact (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
  · rw [Set.indicator_apply]
    by_cases h : y ∈ Set.Icc (-(n:ℝ)) (n:ℝ)
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp

lemma l2_bound_general {φ : ℝ → ℝ} (hφ : Measurable φ) (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ)
      ≤ ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) := by
  set G : ℕ → ℝ → ℂ := fun n y => (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator f y with hGdef
  have hGeq : ∀ n y, G n y = (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℂ)) y * f y := by
    intro n y
    rw [hGdef]
    simp only [Set.indicator_apply, Pi.mul_apply]
    by_cases h : y ∈ Set.Icc (-(n:ℝ)) (n:ℝ) <;> simp [h]
  have hGmem : ∀ n, MemLp (G n) 1 volume ∧ MemLp (G n) 2 volume := by
    intro n
    constructor
    · refine (MemLp.mul (p := 2) (q := 2) (r := 1) (indicator_Icc_memLp n 2) hf).ae_eq ?_
      filter_upwards with y; exact (hGeq n y).symm
    · refine (MemLp.mul (p := ⊤) (q := 2) (r := 2) (indicator_Icc_memLp n ⊤) hf).ae_eq ?_
      filter_upwards with y; exact (hGeq n y).symm
  have hGle : ∀ n y, ‖G n y‖ ≤ ‖f y‖ := by
    intro n y
    rw [hGdef]
    simp only [Set.indicator_apply]
    by_cases h : y ∈ Set.Icc (-(n:ℝ)) (n:ℝ) <;> simp [h]
  have hGtend : ∀ y : ℝ, Tendsto (fun n => G n y) atTop (𝓝 (f y)) := by
    intro y
    have hev : ∀ᶠ n : ℕ in atTop, y ∈ Set.Icc (-(n:ℝ)) (n:ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈|y|⌉₊] with n hn
      have hc : ((⌈|y|⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [Set.mem_Icc]
      exact abs_le.mp (le_trans (Nat.le_ceil |y|) hc)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with n hn
    rw [hGdef]; simp only [Set.indicator_of_mem hn]
  have hconv : ∀ (j : ℕ) (x : ℝ), Tendsto (fun n => ∫ y, G n y * bst lam φ j (x - y)) atTop
      (𝓝 (∫ y, f y * bst lam φ j (x - y))) := by
    intro j x
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖f y‖ * ‖bst lam φ j (x - y)‖) (fun n => ?_)
      (integrable_bound_bst lam hφ hbd hf j x) (fun n => ?_) ?_
    · exact ((hGmem n).2.aestronglyMeasurable.mul
        (memLp_bst_shift lam hφ hbd j x).aestronglyMeasurable)
    · filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hGle n y) (norm_nonneg _)
    · filter_upwards with y
      exact (hGtend y).mul_const _
  have hFatou : ∀ N : ℕ, ∫⁻ x, ∑ j ∈ Finset.range N, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) := by
    intro N
    have hlim : ∀ᵐ x ∂(volume : Measure ℝ), Filter.Tendsto
        (fun n => ∑ j ∈ Finset.range N, ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)) atTop
        (𝓝 (∑ j ∈ Finset.range N, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ))) := by
      filter_upwards with x
      exact tendsto_finsetSum _ (fun j _ =>
        ((ENNReal.continuous_rpow_const (y := 2)).tendsto _).comp ((hconv j x).enorm))
    have hmeas : ∀ n : ℕ, Measurable (fun x : ℝ =>
        ∑ j ∈ Finset.range N, ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)) := by
      intro n
      refine Finset.measurable_sum _ (fun j _ => ?_)
      have hc : (fun x : ℝ => ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ))
          = fun x : ℝ => ENNReal.ofReal ((2*Real.pi)^2) *
              ‖𝓕⁻ (fun ξ => symF lam φ j ξ * 𝓕 (G n) ξ) x‖ₑ ^ (2:ℝ) := by
        funext x
        rw [hH_gen lam hφ hbd (hGmem n).1 j x, enorm_const_mul_sq]
      rw [hc]
      exact measurable_const.mul ((measurable_fourierInv
        (memLp_fourier_symF lam hφ hbd j (hGmem n).1 (hGmem n).2).1).enorm.pow_const _)
    have hbnd : ∀ n, ∫⁻ x, ∑ j ∈ Finset.range N, ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)
        ≤ ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) := by
      intro n
      have hen : (∫⁻ x, ∑ j ∈ Finset.range N, ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ))
          = ∫⁻ x, ∑ j ∈ Finset.range N,
              ENNReal.ofReal ‖∫ y, G n y * bst lam φ j (x - y)‖ ^ (2:ℝ) := by
        apply lintegral_congr; intro x
        apply Finset.sum_congr rfl; intro j _
        rw [enorm_eq_ofReal_norm]
      refine le_trans (le_of_eq hen) ?_
      refine le_trans ?_ (le_trans (l2_bound_L1L2 lam hφ h1 h0 hbd hsep (G n) (hGmem n).1 (hGmem n).2) ?_)
      · apply lintegral_mono; intro x
        exact ENNReal.sum_le_tsum _
      · apply mul_le_mul_right
        apply lintegral_mono
        intro x
        have hgf : ENNReal.ofReal ‖G n x‖ ^ (2:ℝ) = ENNReal.ofReal (‖G n x‖ ^ 2) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ENNReal.ofReal_pow (norm_nonneg _)]
        have hff : ENNReal.ofReal ‖f x‖ ^ (2:ℝ) = ENNReal.ofReal (‖f x‖ ^ 2) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ENNReal.ofReal_pow (norm_nonneg _)]
        dsimp only
        rw [hgf, hff]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hGle n x) 2)
    calc ∫⁻ x, ∑ j ∈ Finset.range N, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)
        = ∫⁻ x, Filter.liminf (fun n => ∑ j ∈ Finset.range N,
            ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)) atTop := by
          apply lintegral_congr_ae
          filter_upwards [hlim] with x hx
          exact hx.liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ∑ j ∈ Finset.range N,
            ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)) atTop :=
          lintegral_liminf_le hmeas
      _ ≤ ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) := by
          refine liminf_le_of_le ⟨0, Filter.Eventually.of_forall (fun i => bot_le)⟩ (fun b hb => ?_)
          obtain ⟨n, hn⟩ := hb.exists
          exact le_trans hn (hbnd n)
  have hSm : ∀ N : ℕ, Measurable (fun x : ℝ =>
      ∑ j ∈ Finset.range N, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)) := by
    intro N
    have hlim : Tendsto (fun n : ℕ => fun x : ℝ =>
        ∑ j ∈ Finset.range N, ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)) atTop
        (𝓝 (fun x : ℝ => ∑ j ∈ Finset.range N, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ))) := by
      rw [tendsto_pi_nhds]
      intro x
      exact tendsto_finsetSum _ (fun j _ =>
        ((ENNReal.continuous_rpow_const (y := 2)).tendsto _).comp ((hconv j x).enorm))
    refine measurable_of_tendsto_metrizable (fun n => ?_) hlim
    refine Finset.measurable_sum _ (fun j _ => ?_)
    have hc : (fun x : ℝ => ‖(∫ y, G n y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ))
        = fun x : ℝ => ENNReal.ofReal ((2*Real.pi)^2) *
            ‖𝓕⁻ (fun ξ => symF lam φ j ξ * 𝓕 (G n) ξ) x‖ₑ ^ (2:ℝ) := by
      funext x
      rw [hH_gen lam hφ hbd (hGmem n).1 j x, enorm_const_mul_sq]
    rw [hc]
    exact measurable_const.mul ((measurable_fourierInv
      (memLp_fourier_symF lam hφ hbd j (hGmem n).1 (hGmem n).2).1).enorm.pow_const _)
  have htsum : ∀ x : ℝ, ∑' j : ℕ, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)
      = ⨆ N : ℕ, ∑ j ∈ Finset.range N, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ) := by
    intro x
    rw [ENNReal.tsum_eq_iSup_sum]
    apply le_antisymm
    · refine iSup_le (fun s => ?_)
      exact le_iSup_of_le (s.sup id + 1) (Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)))
        (fun i _ _ => bot_le))
    · refine iSup_le (fun N => ?_)
      exact le_iSup (fun s : Finset ℕ => ∑ j ∈ s, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ))
        (Finset.range N)
  have hsup : ∫⁻ x, ∑' j : ℕ, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ)
      = ⨆ N : ℕ, ∫⁻ x, ∑ j ∈ Finset.range N, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ) := by
    rw [lintegral_congr htsum]
    rw [lintegral_iSup (fun N => hSm N) (fun N N' hNN' x =>
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hNN'))
        (fun i _ _ => bot_le))]
  calc ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ)
      = ∫⁻ x, ∑' j : ℕ, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro x
        apply tsum_congr; intro j
        rw [enorm_eq_ofReal_norm]
    _ = ⨆ N : ℕ, ∫⁻ x, ∑ j ∈ Finset.range N, ‖(∫ y, f y * bst lam φ j (x - y))‖ₑ ^ (2:ℝ) := hsup
    _ ≤ ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) :=
        iSup_le (fun N => hFatou N)

end General

section Main
variable {K : ℕ} (lam : Fin K → ℝ)

lemma ae_eq_comp_affine {φ φ' : ℝ → ℝ} (h : φ =ᵐ[volume] φ') (a b : ℝ) (hb : b ≠ 0) :
    (fun θ => φ ((θ - a)/b)) =ᵐ[volume] (fun θ => φ' ((θ - a)/b)) := by
  have h1 : Measure.QuasiMeasurePreserving (fun θ : ℝ => θ - a) volume volume := by
    have := (measurePreserving_add_right volume (-a)).quasiMeasurePreserving
    simpa [sub_eq_add_neg] using this
  have h2 : Measure.QuasiMeasurePreserving (fun x : ℝ => x / b) volume volume := by
    have := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (show b⁻¹ ≠ 0 by simpa using hb)
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using this
  exact (h2.comp h1).ae_eq h

lemma aesm_of_comp_affine {φ : ℝ → ℂ} (a b : ℝ) (hb : b ≠ 0)
    (h : AEStronglyMeasurable (fun θ => φ ((θ - a)/b)) volume) :
    AEStronglyMeasurable φ volume := by
  obtain ⟨g, hgm, hgae⟩ := h
  have h3 : Measure.QuasiMeasurePreserving (fun θ : ℝ => θ - a) volume volume := by
    have := (measurePreserving_add_right volume (-a)).quasiMeasurePreserving
    simpa [sub_eq_add_neg] using this
  have h4 : Measure.QuasiMeasurePreserving (fun x : ℝ => x / b) volume volume := by
    have := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (show b⁻¹ ≠ 0 by simpa using hb)
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using this
  have h5 : Measure.QuasiMeasurePreserving (fun x : ℝ => b * x + a) volume volume := by
    have h6 : Measure.QuasiMeasurePreserving (fun x : ℝ => a + x) volume volume :=
      (measurePreserving_add_left volume a).quasiMeasurePreserving
    have h7 : Measure.QuasiMeasurePreserving (fun x : ℝ => b * x) volume volume := by
      have := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hb
      simpa [smul_eq_mul] using this
    have h8 := h6.comp h7
    simpa only [Function.comp_def, add_comm] using h8
  have hcomp := h5.ae_eq hgae
  have hfun : ∀ x : ℝ, ((fun θ : ℝ => φ ((θ - a)/b)) ∘ (fun x : ℝ => b * x + a)) x = φ x := by
    intro x
    simp only [Function.comp_apply]
    rw [show (b * x + a - a)/b = x from by rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hb]]
  refine ⟨g ∘ (fun x : ℝ => b * x + a), hgm.comp_measurable (by fun_prop), ?_⟩
  filter_upwards [hcomp] with x hx
  rw [hfun x] at hx
  exact hx

end Main

lemma bst_congr_ae {K : ℕ} (lam : Fin K → ℝ) {φ φ' : ℝ → ℝ} (h : φ =ᵐ[volume] φ')
    (j : ℕ) (t : ℝ) :
    bst lam φ j t = bst lam φ' j t := by
  apply Finset.sum_congr rfl
  intro k _
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_eq_comp_affine h (lam k) (hj j) (ne_of_gt (hj_pos j))] with θ hθ
  intro _
  rw [hθ]

/-- If the boundary-layer integral is interval integrable then `φ` is a.e. strongly measurable. -/
lemma aesm_of_intervalIntegrable {φ : ℝ → ℝ} (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {c b : ℝ} (hb : 0 < b) (t : ℝ)
    (h : IntervalIntegrable (fun θ => ((1 - φ ((θ - c)/b)) : ℂ) * Fexp t θ)
      volume (c - b) (c + b)) :
    AEStronglyMeasurable φ volume := by
  classical
  set s : Set ℝ := Set.uIoc (c - b) (c + b) with hs
  have hsmeasset : MeasurableSet s := by rw [hs]; exact measurableSet_uIoc
  have hsc : s = {θ : ℝ | (θ - c)/b ∈ Set.Ioc (-1) 1} := by
    ext θ
    rw [hs, Set.mem_uIoc, Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by rw [lt_div_iff₀ hb]; linarith, by rw [div_le_iff₀ hb]; linarith⟩
      · exact ⟨by rw [lt_div_iff₀ hb]; linarith, by rw [div_le_iff₀ hb]; linarith⟩
    · rintro ⟨h1, h2⟩
      have h1' : c - b < θ := by rw [lt_div_iff₀ hb] at h1; linarith
      have h2' : θ ≤ c + b := by rw [div_le_iff₀ hb] at h2; linarith
      exact Or.inl ⟨h1', h2'⟩
  have hs_eq : s = Set.Ioc (c - b) (c + b) := by
    rw [hs, Set.uIoc_of_le (by linarith)]
  have haesm : AEStronglyMeasurable
      (fun θ => ((1 - φ ((θ - c)/b)) : ℂ) * Fexp t θ) (volume.restrict s) := by
    rw [hs_eq]; exact h.1.1
  have hconj : AEStronglyMeasurable (fun θ => (starRingEnd ℂ (Fexp t θ))) (volume.restrict s) :=
    (Complex.continuous_conj.comp
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable.restrict
  have hH : AEStronglyMeasurable (fun θ => ((1 - φ ((θ - c)/b)) : ℂ)) (volume.restrict s) := by
    refine (haesm.mul hconj).congr ?_
    filter_upwards with θ
    simp only [Pi.mul_apply]
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_Fexp]
    norm_num
  have hind : AEStronglyMeasurable (s.indicator (fun θ => ((1 - φ ((θ - c)/b)) : ℂ))) volume := by
    obtain ⟨G, hGm, hGeq⟩ := hH
    refine ⟨s.indicator G, hGm.indicator hsmeasset, ?_⟩
    have h2 : (volume.restrict s) {a : ℝ | ((1 - φ ((a - c)/b)) : ℂ) ≠ G a} = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hGeq; exact hGeq
    rw [Filter.EventuallyEq, ae_iff]
    have hsub : {a : ℝ | ¬ s.indicator (fun θ => ((1 - φ ((θ - c)/b)) : ℂ)) a = s.indicator G a} ⊆
        {a : ℝ | a ∈ s ∧ ((1 - φ ((a - c)/b)) : ℂ) ≠ G a} := by
      intro a ha
      by_cases hc : a ∈ s
      · refine ⟨hc, fun hcon => ha ?_⟩
        rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc]
        exact hcon
      · exact absurd (by rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc]) ha
    have h2' : volume (s ∩ {a : ℝ | ((1 - φ ((a - c)/b)) : ℂ) ≠ G a}) = 0 := by
      have hB : ∀ᵐ a ∂(volume : Measure ℝ),
          a ∈ s → a ∉ {a : ℝ | ((1 - φ ((a - c)/b)) : ℂ) ≠ G a} := by
        rw [← ae_restrict_iff' hsmeasset, ae_iff]
        convert h2 using 2
        ext a
        simp only [Set.mem_setOf_eq, not_not]
      have hae : ∀ᵐ a ∂(volume : Measure ℝ),
          ¬ (a ∈ s ∧ a ∈ {a : ℝ | ((1 - φ ((a - c)/b)) : ℂ) ≠ G a}) := by
        filter_upwards [hB] with a ha
        rintro ⟨hs, hb⟩
        exact ha hs hb
      have hfin := ae_iff.mp hae
      convert hfin using 2
      ext a
      simp [Set.mem_inter_iff]
    exact measure_mono_null hsub h2'
  have hcomp : AEStronglyMeasurable
      (fun x : ℝ => ((1 - φ x) : ℂ) * (Set.Ioc (-1) 1).indicator (fun _ => (1:ℂ)) x) volume := by
    refine aesm_of_comp_affine (φ := fun x : ℝ =>
        ((1 - φ x) : ℂ) * (Set.Ioc (-1) 1).indicator (fun _ => (1:ℂ)) x)
      (a := c) (b := b) (ne_of_gt hb) ?_
    refine hind.congr ?_
    filter_upwards with θ
    by_cases hθ : (θ - c)/b ∈ Set.Ioc (-1) 1
    · rw [Set.indicator_of_mem (show θ ∈ s from by rw [hsc]; exact hθ), Set.indicator_of_mem hθ]
      ring
    · rw [Set.indicator_of_notMem (show θ ∉ s from by rw [hsc]; exact hθ), Set.indicator_of_notMem hθ]
      ring
  have hφc : AEStronglyMeasurable (fun x : ℝ => (φ x : ℂ)) volume := by
    have hfun : (fun x : ℝ => (φ x : ℂ)) = fun x : ℝ =>
        (Set.Ioc (-1) 1).indicator (fun _ => (1:ℂ)) x -
          ((1 - φ x : ℂ) * (Set.Ioc (-1) 1).indicator (fun _ => (1:ℂ)) x) := by
      funext x
      rw [Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioc (-1) 1
      · rw [if_pos hx]; ring
      · rw [if_neg hx, mul_zero, sub_zero]
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with hx | hx
        · have hx0 : x ≤ 0 := by linarith
          rw [h0 x (by rw [abs_of_nonpos hx0]; linarith), Complex.ofReal_zero]
        · have hx0 : 0 < x := by linarith
          rw [h0 x (by rw [abs_of_pos hx0]; linarith), Complex.ofReal_zero]
    rw [hfun]
    exact (measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable.sub hcomp
  exact Complex.continuous_re.comp_aestronglyMeasurable hφc

/-- If `φ` is not a.e. strongly measurable then every boundary-layer symbol vanishes. -/
lemma bst_eq_zero_of_not_aesm {K : ℕ} (lam : Fin K → ℝ) {φ : ℝ → ℝ}
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (hφ : ¬ AEStronglyMeasurable φ volume) (j : ℕ) (t : ℝ) : bst lam φ j t = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  rw [intervalIntegral.integral_undef]
  intro hint
  exact hφ (aesm_of_intervalIntegrable h0 (hj_pos j) t hint)


end BoundaryLayer

open BoundaryLayer

/-- **Boundary-layer `L²` square-function bound.** -/
theorem boundary_layer_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (φ : ℝ → ℝ), (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ∑' j : ℕ,
            ENNReal.ofReal ‖∫ y : ℝ, f y *
            (∑ k : Fin K,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ ^ (2:ℝ))
          ≤ ENNReal.ofReal (C^2) * MeasureTheory.lintegral MeasureTheory.volume
              (fun x : ℝ => ENNReal.ofReal ‖f x‖ ^ (2:ℝ)) := by
  refine ⟨4 * Real.pi, by positivity, ?_⟩
  intro K lam hsep φ h1 h0 hbdd f hf
  change (∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ))
      ≤ ENNReal.ofReal ((4*Real.pi)^2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ)
  by_cases hφ : AEStronglyMeasurable φ volume
  · rcases hφ with ⟨φ₀, hφ₀s, hφ₀⟩
    have hφ₀m : Measurable φ₀ := hφ₀s.measurable
    let gp : ℝ → ℝ := fun x =>
      if |x| ≤ 1/2 then 1 else if 1 ≤ |x| then 0 else max 0 (min 1 (φ₀ x))
    have hgpm : Measurable gp := by
      refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const ?_)
      · exact measurableSet_le measurable_abs measurable_const
      · exact measurableSet_le measurable_const measurable_abs
      · simpa only [max_comm] using ((measurable_const.min hφ₀m).max measurable_const)
    have hgp1 : ∀ x : ℝ, |x| ≤ 1/2 → gp x = 1 := by
      intro x hx
      simp only [gp]
      rw [if_pos hx]
    have hgp0 : ∀ x : ℝ, 1 ≤ |x| → gp x = 0 := by
      intro x hx
      simp only [gp]
      rw [if_neg (by linarith : ¬ |x| ≤ 1/2), if_pos hx]
    have hgpbdd : ∀ x : ℝ, 0 ≤ gp x ∧ gp x ≤ 1 := by
      intro x
      simp only [gp]
      split_ifs with hc1 hc2
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨le_refl 0, by norm_num⟩
      · exact ⟨le_trans (le_max_left 0 _) le_rfl,
          max_le (by norm_num) (min_le_left _ _)⟩
    have hgpae : gp =ᵐ[volume] φ := by
      filter_upwards [hφ₀] with x hx
      simp only [gp]
      by_cases hc1 : |x| ≤ 1/2
      · rw [if_pos hc1, h1 x hc1]
      · rw [if_neg hc1]
        by_cases hc2 : 1 ≤ |x|
        · rw [if_pos hc2, h0 x hc2]
        · rw [if_neg hc2, ← hx, min_eq_right (hbdd x).2, max_eq_right (hbdd x).1]
    have hLHS : (∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ))
        = ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam gp j (x - y)‖ ^ (2:ℝ) := by
      apply lintegral_congr; intro x
      apply tsum_congr; intro j
      have hy : (∫ y, f y * bst lam φ j (x - y)) = ∫ y, f y * bst lam gp j (x - y) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [bst_congr_ae lam hgpae.symm j (x - y)]
      rw [hy]
    rw [hLHS]
    exact l2_bound_general lam hgpm hgp1 hgp0 hgpbdd hsep f hf
  · have hbst0 : ∀ (j : ℕ) (t : ℝ), bst lam φ j t = 0 :=
      fun j t => bst_eq_zero_of_not_aesm lam h0 hφ j t
    have hzero : (∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ)) = 0 := by
      have hpt : ∀ x : ℝ,
          (∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ)) = 0 := by
        intro x
        have h0j : (fun j : ℕ => ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ))
            = fun _ => (0 : ℝ≥0∞) := by
          funext j
          have hint : (∫ y, f y * bst lam φ j (x - y)) = 0 := by
            have hfun : (fun y : ℝ => f y * bst lam φ j (x - y)) = fun _ => (0:ℂ) :=
              funext (fun y => by rw [hbst0 j (x - y), mul_zero])
            rw [hfun]
            exact integral_zero _ _
          rw [hint, norm_zero, ENNReal.ofReal_zero,
            ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
        rw [h0j]
        simp only [tsum_zero]
      calc ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y, f y * bst lam φ j (x - y)‖ ^ (2:ℝ)
          = ∫⁻ x, (0 : ℝ≥0∞) := lintegral_congr (fun x => hpt x)
        _ = 0 := lintegral_zero
    rw [hzero]
    exact bot_le

end