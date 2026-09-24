import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.gSum_fourier
import Submission.Work.GM.Affine.affineSum_sq_le_gSum_sq
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.region_III_bound
import Submission.Work.GM.Affine.region_III_bound_ext
import Submission.Work.GM.Affine.gSum_cauchy_gen
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.regionII_core

/-!
# `Work.GM.Affine.ghat_fine_core2` (GM §9, the fine case, corrected form)

Target: GM's Lemma 9.2 with the "narrow-function" fallback `Mbig⁴ ∫f²`:

`∫ u, (gSum K M₁ M₂ M₃ f u)² ≤ C' T^δ (Mbig⁶ (∫f)² + Mbig² √(∫f²) √(∫Gfun²) + Mbig⁴ ∫f²)`

for all `0 < M₁,M₂ ≤ Mbig`, `0 < M₃ ≤ C₃ Mbig` and `Mbig ≤ T⁴`.

## Structure

* `∫ u, gSum² = ∫ ξ, ‖ĝ ξ‖²` (`gSum_fourier`);
* split `∫_ℝ` at `a = T^η M₁/M₃` (`η = min δ 1/2`) and at `T⁶`:
  `region_I_bound` bounds `|ξ| ≤ a` by `C T^η Mbig⁶ (∫f)²`;
  `regionII_core` (delegated) bounds `a < |ξ| ≤ T⁶` by the three-term expression;
  `region_III_bound_ext` bounds the tails `|ξ| > T⁶`;
* the cases `Mbig < 1` (elementary, via `gSum_cauchy_gen`) and `M₃ < 1` (reduction to
  `M₃ = 1` with parameter `K+3`: replacing `M₃` by `1` only enlarges the `m₃`-range while
  the old `ψ₁`-weights are `≤ 1`) are handled separately.

The single analytic input is `Submission/Work/GM/Affine/regionII_core.lean`; see
`NOTES_ghat_fine_core2.md` for its analysis.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary facts about the ranges -/

lemma R1_eq_empty_of_lt_half {M₁ : ℝ} (h0 : 0 ≤ M₁) (h : M₁ < 1 / 2) : R1 M₁ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [R1, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨h1, h2⟩, h3⟩ := hm
  have hfloor0 : ⌊2 * M₁⌋ = (0 : ℤ) := by
    refine le_antisymm ?_ (Int.floor_nonneg.mpr (by linarith))
    have hlt : ⌊2 * M₁⌋ < (1 : ℤ) := by
      apply Int.floor_lt.mpr
      push_cast
      linarith
    omega
  rw [hfloor0] at h1 h2
  simp only [neg_zero] at h1
  have hm0 : m = 0 := by omega
  rw [hm0] at h3
  simp only [Int.cast_zero, abs_zero] at h3
  linarith

lemma R2_eq_empty_of_lt_half {M₂ : ℝ} (h : M₂ < 1 / 2) : R2 M₂ = ∅ := by
  rw [R2]
  have h2M : 2 * M₂ < (1 : ℝ) := by linarith
  have hlt : ⌊2 * M₂⌋ < (1 : ℤ) := Int.floor_lt.mpr (by exact_mod_cast h2M)
  have hIcc : Finset.Icc (1 : ℤ) ⌊2 * M₂⌋ = ∅ := by
    rw [Finset.Icc_eq_empty_iff]
    omega
  rw [hIcc]
  simp

lemma gSum_eq_zero_of_R1_empty {K M₁ M₂ M₃ : ℝ} (h : R1 M₁ = ∅) (f : ℝ → ℝ) (u : ℝ) :
    gSum K M₁ M₂ M₃ f u = 0 := by
  rw [gSum, h]
  simp

lemma gSum_eq_zero_of_R2_empty {K M₁ M₂ M₃ : ℝ} (h : R2 M₂ = ∅) (f : ℝ → ℝ) (u : ℝ) :
    gSum K M₁ M₂ M₃ f u = 0 := by
  rw [gSum]
  refine Finset.sum_eq_zero (fun m₁ _ => ?_)
  rw [h]
  simp

/-- The support of a function with `SuppHyp C₀` is contained in a fixed compact interval. -/
lemma hasCompactSupport_of_SuppHyp_gfc2 {C₀ : ℝ} {f : ℝ → ℝ} (h : SuppHyp C₀ f) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / C₀) C₀) isCompact_Icc
    (fun x hx => h x (Function.mem_support.mp hx))

/-! ## Continuity and the integral splitting -/

lemma continuous_ghat_sq {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (fun ξ : ℝ => ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) := by
  have hexp := (gSum_fourier hK hM₁ hM₂ hM₃ hf hcs).2
  rw [funext (fun ξ => hexp ξ)]
  have hcont : Continuous (fun ξ : ℝ =>
      ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂,
        ((((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)) *
          ∑ m₃ ∈ R3ext K M₃, ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) *
            efun (ξ * (m₃ : ℝ) / (m₁ : ℝ)))) := by
    refine continuous_finsetSum _ (fun m₁ _ => continuous_finsetSum _ (fun m₂ _ => ?_))
    refine Continuous.mul (Continuous.mul continuous_const
      ((continuous_fhat hf hcs).comp (by fun_prop))) ?_
    refine continuous_finsetSum _ (fun m₃ _ => ?_)
    exact Continuous.mul continuous_const (by unfold efun; fun_prop)
  exact (hcont.norm).pow 2

lemma integral_le_Icc_add_tails {h : ℝ → ℝ} (hcont : Continuous h) (hh : ∀ x, 0 ≤ h x)
    {c : ℝ} (_hc : 0 ≤ c) :
    (∫ x, h x) ≤ (∫ x in Set.Icc (-c) c, h x) + (∫ x in Set.Ioi c, h x)
      + (∫ x in Set.Iio (-c), h x) := by
  have hcompl : (Set.Icc (-c) c)ᶜ = Set.Ioi c ∪ Set.Iio (-c) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Ioi, Set.mem_Iio,
      not_and_or, not_le]
    tauto
  have hdisj : Disjoint (Set.Ioi c) (Set.Iio (-c)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ioi] at hx1
    simp only [Set.mem_Iio] at hx2
    linarith
  have hsplit : (∫⁻ x, ENNReal.ofReal (h x))
      = (∫⁻ x in Set.Icc (-c) c, ENNReal.ofReal (h x))
        + (∫⁻ x in Set.Ioi c, ENNReal.ofReal (h x))
        + (∫⁻ x in Set.Iio (-c), ENNReal.ofReal (h x)) := by
    have e1 := MeasureTheory.lintegral_add_compl (μ := volume)
      (f := fun x => ENNReal.ofReal (h x)) (A := Set.Icc (-c) c) measurableSet_Icc
    have e2 : (∫⁻ x in (Set.Icc (-c) c)ᶜ, ENNReal.ofReal (h x))
        = (∫⁻ x in Set.Ioi c, ENNReal.ofReal (h x))
          + (∫⁻ x in Set.Iio (-c), ENNReal.ofReal (h x)) := by
      rw [hcompl]
      exact MeasureTheory.lintegral_union measurableSet_Iio hdisj
    rw [e2] at e1
    rw [← add_assoc] at e1
    exact e1.symm
  have hsingle : ∀ s : Set ℝ, (∫ x in s, h x)
      = (∫⁻ x in s, ENNReal.ofReal (h x)).toReal := by
    intro s
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict s)
      (Filter.Eventually.of_forall hh) hcont.aestronglyMeasurable
  have e2 : (∫ x, h x) = (∫⁻ x, ENNReal.ofReal (h x)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh)
      hcont.aestronglyMeasurable
  rw [e2, hsplit, hsingle (Set.Icc (-c) c), hsingle (Set.Ioi c), hsingle (Set.Iio (-c))]
  calc ((∫⁻ x in Set.Icc (-c) c, ENNReal.ofReal (h x))
          + (∫⁻ x in Set.Ioi c, ENNReal.ofReal (h x))
          + (∫⁻ x in Set.Iio (-c), ENNReal.ofReal (h x))).toReal
      ≤ ((∫⁻ x in Set.Icc (-c) c, ENNReal.ofReal (h x))
          + (∫⁻ x in Set.Ioi c, ENNReal.ofReal (h x))).toReal
        + (∫⁻ x in Set.Iio (-c), ENNReal.ofReal (h x)).toReal := ENNReal.toReal_add_le
    _ ≤ ((∫⁻ x in Set.Icc (-c) c, ENNReal.ofReal (h x)).toReal
          + (∫⁻ x in Set.Ioi c, ENNReal.ofReal (h x)).toReal)
        + (∫⁻ x in Set.Iio (-c), ENNReal.ofReal (h x)).toReal := by
        linarith [ENNReal.toReal_add_le
          (a := ∫⁻ x in Set.Icc (-c) c, ENNReal.ofReal (h x))
          (b := ∫⁻ x in Set.Ioi c, ENNReal.ofReal (h x))]
    _ = (∫⁻ x in Set.Icc (-c) c, ENNReal.ofReal (h x)).toReal
        + (∫⁻ x in Set.Ioi c, ENNReal.ofReal (h x)).toReal
        + (∫⁻ x in Set.Iio (-c), ENNReal.ofReal (h x)).toReal := by ring

lemma integral_Icc_split {h : ℝ → ℝ} (hcont : Continuous h) {a b : ℝ} (hab : a ≤ b) :
    (∫ ξ in Set.Icc (-b) b, h ξ)
      = (∫ ξ in Set.Icc (-a) a, h ξ) + (∫ ξ in (Set.Icc (-b) b) \ (Set.Icc (-a) a), h ξ) := by
  have hsub : Set.Icc (-a) a ⊆ Set.Icc (-b) b := by
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hunion : Set.Icc (-a) a ∪ ((Set.Icc (-b) b) \ (Set.Icc (-a) a)) = Set.Icc (-b) b := by
    rw [Set.union_sdiff_self, Set.union_eq_self_of_subset_left hsub]
  have hd : Disjoint (Set.Icc (-a) a) ((Set.Icc (-b) b) \ (Set.Icc (-a) a)) :=
    Set.disjoint_sdiff_right
  have hrest : MeasurableSet ((Set.Icc (-b) b) \ (Set.Icc (-a) a)) :=
    measurableSet_Icc.diff measurableSet_Icc
  have hInt1 : IntegrableOn h (Set.Icc (-a) a) := hcont.integrableOn_Icc
  have hInt2 : IntegrableOn h ((Set.Icc (-b) b) \ (Set.Icc (-a) a)) :=
    IntegrableOn.mono_set_ae (hcont.integrableOn_Icc (a := -b) (b := b))
      (Filter.Eventually.of_forall (fun x hx => hx.1))
  conv_lhs => rw [← hunion]
  exact setIntegral_union hd hrest hInt1 hInt2

/-! ## The reduction `M₃ ≤ 1 ⟹ gSum K M₁ M₂ M₃ f ≤ gSum (K+3) M₁ M₂ 1 f` -/

lemma R3ext_subset_Kp3_one {K M₃ : ℝ} (hK : 0 < K) (hM₃ : 0 < M₃) (hM₃1 : M₃ ≤ 1) :
    R3ext K M₃ ⊆ R3ext (K + 3) 1 := by
  intro m hm
  simp only [R3ext, Finset.mem_Icc] at hm ⊢
  have hkey : ⌈(K + 3 + 1) * 1⌉ = ⌈K + 4⌉ := by ring_nf
  rw [hkey]
  have hb : ⌈(K + 1) * M₃⌉ ≤ ⌈K + 4⌉ := Int.ceil_mono (by nlinarith)
  constructor
  · omega
  · exact le_trans hm.2 hb

lemma psi1_eq_one_of_mem_R3ext_le_one {K M₃ : ℝ} (hK : 0 < K) (hM₃ : 0 < M₃) (hM₃1 : M₃ ≤ 1)
    {m : ℤ} (hm : m ∈ R3ext K M₃) : psi1 (K + 3) (m : ℝ) = 1 := by
  apply psi1_eq_one
  simp only [R3ext, Finset.mem_Icc] at hm
  have habs : ((|m| : ℤ) : ℝ) ≤ K + 3 := by
    have h1 : |m| ≤ ⌈(K + 1) * M₃⌉ := abs_le.mpr ⟨hm.1, hm.2⟩
    have h2 : ((⌈(K + 1) * M₃⌉ : ℤ) : ℝ) ≤ K + 2 := by
      have h3 : ⌈(K + 1) * M₃⌉ ≤ ⌈K + 1⌉ := Int.ceil_mono (by nlinarith)
      have h4 : ((⌈K + 1⌉ : ℤ) : ℝ) ≤ K + 2 := by
        have h := Int.ceil_lt_add_one (K + 1); push_cast at h ⊢; linarith
      have h5 : ((⌈(K + 1) * M₃⌉ : ℤ) : ℝ) ≤ ((⌈K + 1⌉ : ℤ) : ℝ) := by exact_mod_cast h3
      linarith
    have h6 : ((|m| : ℤ) : ℝ) ≤ ((⌈(K + 1) * M₃⌉ : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  rw [Int.cast_abs] at habs
  exact habs

lemma gSum_le_gSum_Kp3_one {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₃ : 0 < M₃) (hM₃1 : M₃ ≤ 1)
    {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (u : ℝ) :
    gSum K M₁ M₂ M₃ f u ≤ gSum (K + 3) M₁ M₂ 1 f u := by
  rw [gSum, gSum]
  refine Finset.sum_le_sum (fun m₁ _ => Finset.sum_le_sum (fun m₂ _ => ?_))
  calc ∑ m₃ ∈ R3ext K M₃, psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / (m₂ : ℝ))
      ≤ ∑ m₃ ∈ R3ext K M₃,
          psi1 (K + 3) ((m₃ : ℝ) / 1) * f (((m₁ : ℝ) * u + m₃) / (m₂ : ℝ)) := by
        refine Finset.sum_le_sum (fun m₃ hm₃ => ?_)
        have h1 : psi1 (K + 3) ((m₃ : ℝ) / 1) = 1 := by
          rw [div_one]
          exact psi1_eq_one_of_mem_R3ext_le_one hK hM₃ hM₃1 hm₃
        rw [h1]
        simpa using mul_le_mul_of_nonneg_right (psi1_le_one K _) (hf _)
    _ ≤ ∑ m₃ ∈ R3ext (K + 3) 1,
          psi1 (K + 3) ((m₃ : ℝ) / 1) * f (((m₁ : ℝ) * u + m₃) / (m₂ : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (R3ext_subset_Kp3_one hK hM₃ hM₃1)
          (fun m₃ _ _ => mul_nonneg (psi1_nonneg _ _) (hf _))

/-! ## The main case `1 ≤ Mbig`, `1 ≤ M₃` -/

/-- Elementary arithmetic for the small-`Mbig` case. -/
private lemma small_arith {c₀ Tδ X Y Z C' : ℝ} (hc₀ : 0 ≤ c₀) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hZ : 0 ≤ Z) (hTδ : 1 ≤ Tδ) (hC' : c₀ ≤ C') :
    c₀ * Z ≤ C' * Tδ * (X + Y + Z) := by
  have hZle : Z ≤ X + Y + Z := by linarith
  have h2 : Z ≤ Tδ * (X + Y + Z) := by nlinarith [hTδ, hX, hY, hZle]
  calc c₀ * Z ≤ C' * Z := mul_le_mul_of_nonneg_right hC' hZ
    _ ≤ C' * (Tδ * (X + Y + Z)) := mul_le_mul_of_nonneg_left h2 (le_trans hc₀ hC')
    _ = C' * Tδ * (X + Y + Z) := by ring

private theorem core_ge_one {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
        ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 ≤
          C' * T ^ δ *
            (Mbig ^ 6 * (∫ u, f u) ^ 2 +
              Mbig ^ 2 * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
                (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
              Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
  obtain ⟨CI, hCIpos, hI⟩ := region_I_bound K
  obtain ⟨CII, hCIIpos, hII⟩ :=
    regionII_core (C₀ := C₀) (K := K) (T₀ := T₀) (C₃ := C₃) hC₀ hK hT₀ hC₃ c δ hδ
  obtain ⟨CIII, hCIIIpos, hIII⟩ :=
    region_III_bound_ext (C₀ := C₀) (K := K) (T₀ := T₀) (C₃ := C₃) hC₀ hK hT₀ hC₃ c δ hδ
  refine ⟨CI * C₃ ^ 6 + CII + CIII + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hSupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃ hMbig1 hMbT hM₃1 hM₃C
    hM₁ hM₁M hM₂ hM₂M
  have hTpos : 0 < T := lt_of_lt_of_le (by linarith : (0:ℝ) < T₀) hT
  have hT1 : (1:ℝ) ≤ T := le_trans hT₀ hT
  have hTδnn : (0:ℝ) ≤ T ^ δ := Real.rpow_nonneg hTpos.le δ
  have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp_gfc2 hSupp
  have hUnn : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hfnn
  have hVnn : (0:ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hJnn : (0:ℝ) ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃1
  -- the exponent η and the split point a
  have hηnn : (0:ℝ) ≤ min δ 1 / 2 := by
    have : (0:ℝ) < min δ 1 := lt_min hδ zero_lt_one
    linarith
  have hη1 : min δ 1 / 2 ≤ 1 := by
    have := min_le_right δ 1; linarith
  have hηδ : min δ 1 / 2 ≤ δ := by
    have := min_le_left δ 1; linarith
  have hTη_le : T ^ (min δ 1 / 2) ≤ T ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hT1 hηδ
  set a : ℝ := T ^ (min δ 1 / 2) * M₁ / M₃ with hadef
  have hann : 0 ≤ a := by rw [hadef]; positivity
  have haT : a ≤ T ^ 6 := by
    rw [hadef]
    have h1 : T ^ (min δ 1 / 2) ≤ T := by
      have h := Real.rpow_le_rpow_of_exponent_le hT1 hη1
      rwa [Real.rpow_one] at h
    have h2 : M₁ / M₃ ≤ Mbig := by rw [div_le_iff₀ hM₃pos]; nlinarith
    calc T ^ (min δ 1 / 2) * M₁ / M₃
        = T ^ (min δ 1 / 2) * (M₁ / M₃) := by ring
      _ ≤ T * Mbig := mul_le_mul h1 h2 (by positivity) hTpos.le
      _ ≤ T * T ^ 4 := mul_le_mul_of_nonneg_left hMbT hTpos.le
      _ = T ^ 5 := by ring
      _ ≤ T ^ 6 := pow_le_pow_right₀ hT1 (by norm_num)
  -- continuity
  have hcont : Continuous (fun ξ : ℝ => ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) :=
    continuous_ghat_sq hK hM₁ hM₂ hM₃pos hf hcs
  -- the three region bounds
  have hIapp : (∫ ξ in Set.Icc (-a) a, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ CI * C₃ ^ 6 * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2) := by
    have hb := hI (max Mbig M₃) M₁ M₂ M₃ T (min δ 1 / 2) hM₁
      (le_trans hM₁M (le_max_left _ _)) hM₂ (le_trans hM₂M (le_max_left _ _)) hM₃1
      (le_max_right _ _) hT1 hηnn f hf hcs hfnn
    have hmax : (max Mbig M₃) ^ 6 ≤ C₃ ^ 6 * Mbig ^ 6 := by
      have h1 : max Mbig M₃ ≤ C₃ * Mbig := by
        refine max_le ?_ hM₃C
        nlinarith [hC₃, hMbig1]
      calc (max Mbig M₃) ^ 6 ≤ (C₃ * Mbig) ^ 6 := pow_le_pow_left₀ (by positivity) h1 6
        _ = C₃ ^ 6 * Mbig ^ 6 := by ring
    have hcoef : (0:ℝ) ≤ CI * C₃ ^ 6 :=
      mul_nonneg hCIpos.le (pow_nonneg (by linarith : (0:ℝ) ≤ C₃) 6)
    have hstep : CI * C₃ ^ 6 * T ^ (min δ 1 / 2) * (Mbig ^ 6 * (∫ u, f u) ^ 2)
        ≤ CI * C₃ ^ 6 * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2) := by
      have hXnn : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 := by positivity
      have hcoef : (0:ℝ) ≤ CI * C₃ ^ 6 :=
        mul_nonneg hCIpos.le (pow_nonneg (by linarith : (0:ℝ) ≤ C₃) 6)
      calc CI * C₃ ^ 6 * T ^ (min δ 1 / 2) * (Mbig ^ 6 * (∫ u, f u) ^ 2)
          = (CI * C₃ ^ 6) * (T ^ (min δ 1 / 2) * (Mbig ^ 6 * (∫ u, f u) ^ 2)) := by ring
        _ ≤ (CI * C₃ ^ 6) * (T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hTη_le hXnn) hcoef
        _ = CI * C₃ ^ 6 * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2) := by ring
    calc (∫ ξ in Set.Icc (-a) a, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        = (∫ ξ in Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃))
              (T ^ (min δ 1 / 2) * M₁ / M₃), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) := by rw [hadef]
      _ ≤ CI * T ^ (min δ 1 / 2) * (max Mbig M₃) ^ 6 * (∫ u, f u) ^ 2 := hb
      _ ≤ CI * T ^ (min δ 1 / 2) * (C₃ ^ 6 * Mbig ^ 6) * (∫ u, f u) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hmax (by positivity)
      _ = CI * C₃ ^ 6 * T ^ (min δ 1 / 2) * (Mbig ^ 6 * (∫ u, f u) ^ 2) := by ring
      _ ≤ CI * C₃ ^ 6 * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2) := hstep

  have hIIapp := hII T hT f hf hfnn hSupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMbig1 hMbT hM₃1 hM₃C hM₁ hM₁M hM₂ hM₂M
  have hIIIapp := hIII T hT f hf hfnn hSupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hM₁ hM₁M hM₂ hM₂M hM₃pos hM₃C hMbT
  -- Plancherel and the splitting
  have hplan : ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 = ∫ ξ, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2 :=
    (gSum_fourier hK hM₁ hM₂ hM₃pos hf hcs).1
  have hsplit1 := integral_le_Icc_add_tails hcont (fun ξ => sq_nonneg _) (c := T ^ 6)
    (by positivity)
  have hsplit2 := integral_Icc_split hcont (a := a) (b := T ^ 6) haT
  rw [hsplit2] at hsplit1
  -- abbreviations for the three right-hand terms
  set X : ℝ := Mbig ^ 6 * (∫ u, f u) ^ 2 with hX
  set Y : ℝ := Mbig ^ 2 * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
    (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) with hY
  set Z : ℝ := Mbig ^ 4 * ∫ u, (f u) ^ 2 with hZ
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hYnn : 0 ≤ Y := by
    rw [hY]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hVnn _))
      (Real.rpow_nonneg hJnn _)
  have hZnn : 0 ≤ Z := by rw [hZ]; positivity
  have hXYZnn : 0 ≤ X + Y + Z := by linarith
  -- the middle region bound in terms of X, Y, Z
  have hII' : (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
        \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
        ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) ≤ CII * T ^ δ * (X + Y + Z) := by
    rw [hX, hY, hZ]
    exact hIIapp
  have hI' : (∫ ξ in Set.Icc (-a) a, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ CI * C₃ ^ 6 * T ^ δ * X := by
    have hXeq : X = Mbig ^ 6 * (∫ u, f u) ^ 2 := hX
    rw [hXeq]
    exact hIapp
  have hIII' : (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      + (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ CIII * T ^ δ * X := by
    rw [hX]
    refine hIIIapp.trans (le_of_eq ?_)
    ring
  -- conclusion
  have hfinal : (∫ ξ, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ (CI * C₃ ^ 6 + CII + CIII) * T ^ δ * (X + Y + Z) := by
    have h1 := hsplit1
    have h2 : (∫ ξ in Set.Icc (-a) a, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        + (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        + ((∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
          + (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2))
        ≤ CI * C₃ ^ 6 * T ^ δ * X + CII * T ^ δ * (X + Y + Z) + CIII * T ^ δ * X := by
      linarith [hI', hII', hIII']
    have h3 : CI * C₃ ^ 6 * T ^ δ * X + CII * T ^ δ * (X + Y + Z) + CIII * T ^ δ * X
        ≤ (CI * C₃ ^ 6 + CII + CIII) * T ^ δ * (X + Y + Z) := by
      have h4 : CI * C₃ ^ 6 * T ^ δ * X + CIII * T ^ δ * X
          ≤ (CI * C₃ ^ 6 + CIII) * T ^ δ * (X + Y + Z) := by
        have : CI * C₃ ^ 6 * T ^ δ * X + CIII * T ^ δ * X
            = (CI * C₃ ^ 6 + CIII) * T ^ δ * X := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (by linarith [hYnn, hZnn]) (by positivity)
      linarith [h4]
    linarith [h1, h2, h3]
  rw [hplan]
  refine hfinal.trans ?_
  have hle : (CI * C₃ ^ 6 + CII + CIII) * T ^ δ * (X + Y + Z)
      ≤ (CI * C₃ ^ 6 + CII + CIII + 1) * T ^ δ * (X + Y + Z) := by
    have h0 : (0:ℝ) ≤ T ^ δ * (X + Y + Z) := mul_nonneg hTδnn hXYZnn
    have h1 : CI * C₃ ^ 6 + CII + CIII ≤ CI * C₃ ^ 6 + CII + CIII + 1 := by linarith
    calc (CI * C₃ ^ 6 + CII + CIII) * T ^ δ * (X + Y + Z)
        = (CI * C₃ ^ 6 + CII + CIII) * (T ^ δ * (X + Y + Z)) := by ring
      _ ≤ (CI * C₃ ^ 6 + CII + CIII + 1) * (T ^ δ * (X + Y + Z)) :=
          mul_le_mul_of_nonneg_right h1 h0
      _ = (CI * C₃ ^ 6 + CII + CIII + 1) * T ^ δ * (X + Y + Z) := by ring
  exact hle


/-! ## The target -/

theorem ghat_fine_core2 {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ C₃ * Mbig → Mbig ≤ T ^ 4 →
        ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 ≤
          C' * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 +
            Mbig ^ 2 * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
              (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
            Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
  obtain ⟨C₁, hC₁pos, h₁⟩ := core_ge_one (K := K) hC₀ hK hT₀ hC₃ c δ hδ
  obtain ⟨C₂, hC₂pos, h₂⟩ := core_ge_one (K := K + 3) hC₀ (by linarith) hT₀ hC₃ c δ hδ
  obtain ⟨CC, hCCpos, hCC⟩ := gSum_cauchy_gen
  refine ⟨max (max C₁ C₂) (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)) + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hSupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃C hMbT
  have hTpos : 0 < T := lt_of_lt_of_le (by linarith : (0:ℝ) < T₀) hT
  have hT1 : (1:ℝ) ≤ T := le_trans hT₀ hT
  have hTδ1 : (1:ℝ) ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hTδnn : (0:ℝ) ≤ T ^ δ := Real.rpow_nonneg hTpos.le δ
  have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp_gfc2 hSupp
  have hUnn : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hfnn
  have hVnn : (0:ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hJnn : (0:ℝ) ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hRHSnn : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 +
      Mbig ^ 2 * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
        (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
      Mbig ^ 4 * ∫ u, (f u) ^ 2 := by
    have h1 : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ Mbig ^ 2 * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
        (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) := by
      exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hVnn _))
        (Real.rpow_nonneg hJnn _)
    have h3 : (0:ℝ) ≤ Mbig ^ 4 * ∫ u, (f u) ^ 2 := by positivity
    linarith
  by_cases hbig : 1 ≤ Mbig
  · by_cases h3 : 1 ≤ M₃
    · -- main case
      have hmain := h₁ T hT f hf hfnn hSupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
        hbig hMbT h3 hM₃C hM₁ hM₁M hM₂ hM₂M
      refine hmain.trans ?_
      have hle : C₁ ≤ max (max C₁ C₂) (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)) + 1 := by
        have := le_max_left (max C₁ C₂) (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1))
        have := le_max_left C₁ C₂
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hTδnn) hRHSnn
    · -- `M₃ < 1`: reduce to `M₃ = 1` with parameter `K+3`
      push_neg at h3
      have hM₃pos : 0 < M₃ := hM₃
      have hnn : ∀ u, 0 ≤ gSum K M₁ M₂ M₃ f u := fun u => gSum_nonneg hfnn u
      have hmajc : Continuous (fun u : ℝ => gSum (K + 3) M₁ M₂ 1 f u) :=
        continuous_gSum_real' (K + 3) M₁ M₂ 1 hf
      have hmajcs : HasCompactSupport (fun u : ℝ => gSum (K + 3) M₁ M₂ 1 f u) :=
        hasCompactSupport_gSum_real' (K + 3) M₁ M₂ 1 hM₁ hcs
      have hmajcs2 : HasCompactSupport (fun u : ℝ => (gSum (K + 3) M₁ M₂ 1 f u) ^ 2) := by
        have h := hmajcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
        simpa [Function.comp_def] using h
      have hInt : Integrable (fun u : ℝ => (gSum (K + 3) M₁ M₂ 1 f u) ^ 2) :=
        (hmajc.pow 2).integrable_of_hasCompactSupport hmajcs2
      have hg : (∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2)
          ≤ ∫ u, (gSum (K + 3) M₁ M₂ 1 f u) ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) hInt
          (Filter.Eventually.of_forall fun u =>
            pow_le_pow_left₀ (hnn u) (gSum_le_gSum_Kp3_one hK hM₃pos h3.le hfnn u) 2)
      have h3' : (1:ℝ) ≤ 1 := le_rfl
      have hC : (1:ℝ) ≤ C₃ * Mbig := by nlinarith [hC₃, hbig]
      have hmain := h₂ T hT f hf hfnn hSupp Λ hΛ hdec hcompat Mbig M₁ M₂ 1
        hbig hMbT h3' hC hM₁ hM₁M hM₂ hM₂M
      refine hg.trans ?_
      refine hmain.trans ?_
      have hle : C₂ ≤ max (max C₁ C₂) (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)) + 1 := by
        have := le_max_left (max C₁ C₂) (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1))
        have := le_max_right C₁ C₂
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hTδnn) hRHSnn
  · -- `Mbig < 1`
    push_neg at hbig
    have hMbpos : 0 < Mbig := lt_of_lt_of_le hM₁ hM₁M
    by_cases hhalf : Mbig < 1 / 2
    · have hR1 : R1 M₁ = ∅ :=
        R1_eq_empty_of_lt_half (le_of_lt hM₁) (by linarith [hM₁M, hhalf])
      have hzero : ∀ u, gSum K M₁ M₂ M₃ f u = 0 := fun u => gSum_eq_zero_of_R1_empty hR1 f u
      have hz : (∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2) = 0 := by simp [hzero]
      rw [hz]
      exact mul_nonneg (mul_nonneg (by positivity) hTδnn) hRHSnn
    · push_neg at hhalf
      -- the crude Cauchy–Schwarz bound (valid for every `Mbig`)
      have hcc := hCC K (max Mbig M₃) M₁ M₂ M₃ hK.le (lt_of_lt_of_le hMbpos (le_max_left _ _))
        hM₁ (le_trans hM₁M (le_max_left _ _)) hM₂ (le_trans hM₂M (le_max_left _ _))
        hM₃ (le_max_right _ _) f hf hcs hfnn
      have hMb6 : (max Mbig M₃) ^ 6 ≤ C₃ ^ 6 := by
        have hle : max Mbig M₃ ≤ C₃ * Mbig := by
          refine max_le ?_ hM₃C
          nlinarith [hC₃, hMbpos]
        calc (max Mbig M₃) ^ 6 ≤ (C₃ * Mbig) ^ 6 := pow_le_pow_left₀ (by positivity) hle 6
          _ ≤ (C₃ * 1) ^ 6 := by
              apply pow_le_pow_left₀ (by positivity)
              nlinarith [hMbpos, hbig]
          _ = C₃ ^ 6 := by ring
      have hMb4 : (1:ℝ) ≤ 16 * Mbig ^ 4 := by
        nlinarith [hhalf, sq_nonneg (Mbig ^ 2 - 1 / 4), sq_nonneg (Mbig - 1 / 2)]
      have hstep : ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2
          ≤ (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)) * (Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
        refine hcc.trans ?_
        have h6 : (max Mbig M₃) ^ 6 + 1 ≤ C₃ ^ 6 + 1 := by linarith [hMb6]
        calc CC * (K + 1) ^ 2 * ((max Mbig M₃) ^ 6 + 1) * ∫ u, (f u) ^ 2
            = (CC * (K + 1) ^ 2) * (((max Mbig M₃) ^ 6 + 1) * ∫ u, (f u) ^ 2) := by ring
          _ ≤ (CC * (K + 1) ^ 2) * ((C₃ ^ 6 + 1) * ∫ u, (f u) ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6 hVnn) (by positivity)
          _ = CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1) * ∫ u, (f u) ^ 2 := by ring
          _ = (CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)) * ∫ u, (f u) ^ 2 := by ring
          _ ≤ (CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)) * ((16 * Mbig ^ 4) * ∫ u, (f u) ^ 2) := by
              have hcoefnn : (0:ℝ) ≤ CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1) :=
                mul_nonneg (mul_nonneg hCCpos.le (sq_nonneg _))
                  (by
                    have h : (0:ℝ) < C₃ := by linarith
                    positivity)
              have hV' : ∫ u, (f u) ^ 2 ≤ (16 * Mbig ^ 4) * ∫ u, (f u) ^ 2 := by
                nlinarith [hVnn, hMb4]
              exact mul_le_mul_of_nonneg_left hV' hcoefnn
          _ ≤ (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)) * (Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
              have hA : (0:ℝ) ≤ Mbig ^ 4 * ∫ u, (f u) ^ 2 := by positivity
              have hcoef : (0:ℝ) ≤ CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1) :=
                mul_nonneg (mul_nonneg hCCpos.le (sq_nonneg _))
                  (by
                    have h : (0:ℝ) < C₃ := by linarith
                    positivity)
              nlinarith [hA, hcoef, hCCpos.le, hC₃, hMb4, hVnn]
      refine hstep.trans ?_
      have hXnn : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 := by positivity
      have hYnn : (0:ℝ) ≤ Mbig ^ 2 * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
          (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) :=
        mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hVnn _))
          (Real.rpow_nonneg hJnn _)
      have hZnn2 : (0:ℝ) ≤ Mbig ^ 4 * ∫ u, (f u) ^ 2 := by positivity
      have hC'le : 32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)
          ≤ max (max C₁ C₂) (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1)) + 1 := by
        linarith [le_max_right (max C₁ C₂)
          (32 * CC * (K + 1) ^ 2 * (C₃ ^ 6 + 1))]
      refine small_arith ?_ hXnn hYnn hZnn2 hTδ1 hC'le
      exact mul_nonneg (mul_nonneg (by linarith [hCCpos] : (0:ℝ) ≤ 32 * CC) (sq_nonneg _))
        (by
                    have h : (0:ℝ) < C₃ := by linarith
                    positivity)

end

end Work.GM.Affine
