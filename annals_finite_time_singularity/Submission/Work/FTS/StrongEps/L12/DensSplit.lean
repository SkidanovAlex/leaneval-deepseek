import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two elementary helpers -/

/-- The `D_z^0`-summand of the `ℋ^k`-integrand is exactly the square of the weighted datum
`Gaz`, for `k = 0` (at higher order it is only bounded by the integrand). -/
private lemma HkIntegrand_zero_eq_Gaz_sq (α : ℝ) (h : ℝ → ℝ → ℝ) (s θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 h s θ = (Work.FTS.GalBasis.cc.Gaz h s θ) ^ 2 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.DzIter_zero, Work.FTS.GalBasis.cc.Gaz,
    Work.FTS.GalBasis.cc.Sw]

/-- Splitting the integral over `Iθ` at a measurable set `M ⊆ Iθ`, for an integrable datum. -/
private lemma setIntegral_Iθ_split {f : ℝ → ℝ} {M : Set ℝ}
    (hM : MeasurableSet M) (hMI : M ⊆ Work.Spaces.Iθ)
    (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, f θ ∂volume
      = (∫ θ in M, f θ ∂volume) + (∫ θ in Work.Spaces.Iθ \ M, f θ ∂volume) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hunion : M ∪ (Work.Spaces.Iθ \ M) = Work.Spaces.Iθ := by
    ext θ
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact hMI h
      · exact h
    · intro hθ
      by_cases h : θ ∈ M
      · exact Or.inl h
      · exact Or.inr ⟨hθ, h⟩
  have h := MeasureTheory.setIntegral_union (f := f) (s := M) (t := Work.Spaces.Iθ \ M)
    disjoint_sdiff_self_right (hIθ.diff hM) (hf.mono_set hMI) (hf.mono_set Set.sdiff_subset)
  rw [hunion] at h
  exact h

/-- namespace `Work.FTS.StrongEps.L12`, declaration name `DensSplit`.
Angular split bound for the `L₁₂`-density.  Notation: `K θ = 3 sin θ cos²θ` (`Work.Spaces.K`),
`Sw θ = sin(2θ)^{η/2}` (`Work.FTS.GalBasis.cc.Sw`), `Wlam s = s/(1+s)²`
(`Work.FTS.GalBasis.cc.Wlam`), `Gaz h s θ = h s θ · (w s / Sw θ)` (`Work.FTS.GalBasis.cc.Gaz`, with
`w s = (1+s)²/s²`), and `Work.Spaces.HkIntegrand α 0 h s θ = (Gaz h s θ)²`.  Since
`Work.Construction.L12dens h s = Wlam s · ∫_θ K θ · Sw θ · Gaz h s θ` for `s > 0`
(`Work.FTS.GalBasis.cc.L12dens_eq_weighted`), splitting the angular integral at the middle
interval `M = Icc ε (π/2-ε)` — bounding the `M`-piece by `S · ∫_θ K Sw` (using the hypothesis
`|Gaz| ≤ S` on `M` and `K Sw ≥ 0` on `Iθ`) and the two end-pieces by Cauchy–Schwarz in `θ` against
`√(∫_{Iθ∖M}(K Sw)²) · √(∫_θ (Gaz)²) = √(∫_{Iθ∖M}(K Sw)²) · √(∫_θ HkIntegrand α 0 h s θ)` — gives the
stated bound.  The model is `Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le` (the same argument
without the split), whose three-step route (domination `|Gaz| ≤ √(HkIntegrand)`; `|∫ uv| ≤ ∫|uv|`;
honest Cauchy–Schwarz for the two *measurable* factors `|K Sw|` and `√(HkIntegrand)`, the latter
being measurable because `hint` says it is integrable) is to be reused on the two pieces.  No
measurability of `h`/`Gaz` is assumed.  The degenerate cases are harmless: if the density integrand
`θ ↦ K θ Sw θ Gaz h s θ` is not integrable on `Iθ`, then `L12dens h s = 0` (junk value of the
Bochner integral) and the right-hand side is `≥ 0`; otherwise `M` and `Iθ ∖ M` are measurable
disjoint, `M ⊆ Iθ` (because `0 < ε` and `ε < π/2`), and the integral splits. -/
theorem DensSplit {α s ε S : ℝ} {h : ℝ → ℝ → ℝ}
    (hs : 0 < s) (hε : 0 < ε) (hε' : ε < π / 2)
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 h s θ) Work.Spaces.Iθ)
    (hSnn : 0 ≤ S)
    (hS : ∀ θ ∈ Set.Icc ε (π / 2 - ε), |Work.FTS.GalBasis.cc.Gaz h s θ| ≤ S) :
    |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.Wlam s *
        (S * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ)
          + Real.sqrt (∫ θ in Work.Spaces.Iθ \ Set.Icc ε (π / 2 - ε),
              (Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ)) := by
  have hεle : ε < π / 2 := hε'
  rw [Work.FTS.GalBasis.cc.L12dens_eq_weighted h hs, abs_mul,
    abs_of_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)]
  set M : Set ℝ := Set.Icc ε (π / 2 - ε) with hM
  set f : ℝ → ℝ := fun θ => Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ
    * Work.FTS.GalBasis.cc.Gaz h s θ with hf
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ with hu
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 0 h s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hMmeas : MeasurableSet M := measurableSet_Icc
  have hMI : M ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    rw [hM] at hθ
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ ⊢
    exact ⟨le_trans (le_of_lt hε) hθ.1, by linarith [hεle, hθ.2]⟩
  have hcont_K : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hcont_u : Continuous u := by
    rw [hu]; exact hcont_K.mul Work.FTS.GalBasis.cc.continuous_sw
  -- the datum is dominated by the square root of the `ℋ⁰`-integrand
  have hHk : ∀ θ : ℝ, Work.Spaces.HkIntegrand α 0 h s θ
      = (Work.FTS.GalBasis.cc.Gaz h s θ) ^ 2 := fun θ => HkIntegrand_zero_eq_Gaz_sq α h s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := fun θ => by rw [hw]; exact Real.sqrt_nonneg _
  have hw_sq : ∀ θ : ℝ, w θ ^ 2 = Work.Spaces.HkIntegrand α 0 h s θ := fun θ => by
    rw [hw]; exact Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 0 h s θ)
  have hGaz_le_w : ∀ θ : ℝ, |Work.FTS.GalBasis.cc.Gaz h s θ| ≤ w θ := by
    intro θ
    have h : w θ = |Work.FTS.GalBasis.cc.Gaz h s θ| := by
      simp only [hw, hHk θ, Real.sqrt_sq_eq_abs]
    exact le_of_eq h.symm
  -- integrability of the two factors
  have hu2_int_Iθ : MeasureTheory.IntegrableOn (fun θ => u θ ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have habsu2_int_Iθ : MeasureTheory.IntegrableOn (fun θ => |u θ| ^ 2) Work.Spaces.Iθ :=
    (hcont_u.abs.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hu_int_Iθ : MeasureTheory.IntegrableOn u Work.Spaces.Iθ :=
    hcont_u.continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int_Iθ : MeasureTheory.IntegrableOn (fun θ => w θ ^ 2) Work.Spaces.Iθ :=
    hint.congr_fun (fun θ _ => (hw_sq θ).symm) hIθ
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hMemLp_u : MeasureTheory.MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr habsu2_int_Iθ
  have hMemLp_w : MeasureTheory.MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      hw_aesm).mpr hw2_int_Iθ
  -- the middle piece: bound by `S · ∫ K Sw`
  have hpiece1 : |∫ θ in M, f θ| ≤ S * ∫ θ in Work.Spaces.Iθ, u θ := by
    have h1 : |∫ θ in M, f θ| ≤ ∫ θ in M, |f θ| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict M) (f := f))
    have h2 : ∫ θ in M, |f θ| ≤ ∫ θ in M, |u θ| * S := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => abs_nonneg _) ?_ ?_
      · exact ((hcont_u.abs.mul continuous_const).continuousOn.integrableOn_compact
          isCompact_Icc).mono_set hMI
      · filter_upwards [MeasureTheory.self_mem_ae_restrict hMmeas] with θ hθ
        have hθ' : θ ∈ Set.Icc ε (π / 2 - ε) := by simpa only [hM] using hθ
        calc |f θ| = |u θ| * |Work.FTS.GalBasis.cc.Gaz h s θ| := by simp only [hf, hu, abs_mul]
          _ ≤ |u θ| * S := mul_le_mul_of_nonneg_left (hS θ hθ') (abs_nonneg _)
    have h3 : ∫ θ in M, |u θ| * S = S * ∫ θ in M, |u θ| := by
      rw [MeasureTheory.integral_mul_const]
      ring
    have h4 : ∫ θ in M, |u θ| = ∫ θ in M, u θ := by
      refine MeasureTheory.setIntegral_congr_fun hMmeas ?_
      intro θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := hMI hθ
      have hnn : 0 ≤ Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ :=
        mul_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθI)
          (Work.FTS.GalBasis.cc.Sw_nonneg_of_mem_Iθ hθI)
      simp only [hu]
      exact abs_of_nonneg hnn
    have h5 : ∫ θ in M, u θ ≤ ∫ θ in Work.Spaces.Iθ, u θ := by
      have hsplit := setIntegral_Iθ_split (f := u) hMmeas hMI hu_int_Iθ
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ \ M, u θ := by
        refine MeasureTheory.setIntegral_nonneg (hIθ.diff hMmeas) ?_
        intro θ hθ
        have hθI : θ ∈ Work.Spaces.Iθ := hθ.1
        simp only [hu]
        exact mul_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθI)
          (Work.FTS.GalBasis.cc.Sw_nonneg_of_mem_Iθ hθI)
      linarith
    calc |∫ θ in M, f θ| ≤ ∫ θ in M, |f θ| := h1
      _ ≤ ∫ θ in M, |u θ| * S := h2
      _ = S * ∫ θ in M, |u θ| := h3
      _ = S * ∫ θ in M, u θ := by rw [h4]
      _ ≤ S * ∫ θ in Work.Spaces.Iθ, u θ := mul_le_mul_of_nonneg_left h5 hSnn
  -- the two end pieces: Cauchy–Schwarz in `θ`
  have hpiece2 : |∫ θ in Work.Spaces.Iθ \ M, f θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, u θ ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
    have h1 : |∫ θ in Work.Spaces.Iθ \ M, f θ| ≤ ∫ θ in Work.Spaces.Iθ \ M, |f θ| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (Work.Spaces.Iθ \ M)) (f := f))
    have huw_int_Iθ : MeasureTheory.IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
      have hmaj : MeasureTheory.IntegrableOn
          (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
        (hu2_int_Iθ.add hw2_int_Iθ).div_const 2
      refine hmaj.mono' (hcont_u.abs.aestronglyMeasurable.mul hw_aesm) ?_
      filter_upwards with θ
      have ha : 0 ≤ |u θ| := abs_nonneg _
      have hb : 0 ≤ w θ := hw_nn θ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb, abs_of_nonneg ha]
      have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
      rw [sq_abs (u θ)] at key
      exact key
    have h2 : ∫ θ in Work.Spaces.Iθ \ M, |f θ| ≤ ∫ θ in Work.Spaces.Iθ \ M, |u θ| * w θ := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => abs_nonneg _)
        (huw_int_Iθ.mono_set Set.sdiff_subset) ?_
      filter_upwards with θ
      calc |f θ| = |u θ| * |Work.FTS.GalBasis.cc.Gaz h s θ| := by simp only [hf, hu, abs_mul]
        _ ≤ |u θ| * w θ := mul_le_mul_of_nonneg_left (hGaz_le_w θ) (abs_nonneg _)
    have hle : volume.restrict (Work.Spaces.Iθ \ M) ≤ volume.restrict Work.Spaces.Iθ :=
      MeasureTheory.Measure.restrict_mono Set.sdiff_subset le_rfl
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := fun θ => |u θ|) (v := w) (s := Work.Spaces.Iθ \ M)
      (hMemLp_u.mono_measure hle) (hMemLp_w.mono_measure hle)
    have h3 : ∫ θ in Work.Spaces.Iθ \ M, |u θ| * w θ
        = |∫ θ in Work.Spaces.Iθ \ M, |u θ| * w θ| := by
      rw [abs_of_nonneg]
      exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
    have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, |u θ| ^ 2)
        = Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, u θ ^ 2) := by
      congr 1
      exact MeasureTheory.setIntegral_congr_fun (hIθ.diff hMmeas) (fun θ _ => sq_abs (u θ))
    have h5 : Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, w θ ^ 2)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
      refine Real.sqrt_le_sqrt ?_
      calc ∫ θ in Work.Spaces.Iθ \ M, w θ ^ 2
          ≤ ∫ θ in Work.Spaces.Iθ, w θ ^ 2 :=
            MeasureTheory.setIntegral_mono_set hw2_int_Iθ
              (Filter.Eventually.of_forall fun θ => sq_nonneg _)
              (Filter.Eventually.of_forall fun θ hθ => hθ.1)
        _ = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ :=
            MeasureTheory.setIntegral_congr_fun hIθ (fun θ _ => hw_sq θ)
    calc |∫ θ in Work.Spaces.Iθ \ M, f θ|
        ≤ ∫ θ in Work.Spaces.Iθ \ M, |f θ| := h1
      _ ≤ ∫ θ in Work.Spaces.Iθ \ M, |u θ| * w θ := h2
      _ = |∫ θ in Work.Spaces.Iθ \ M, |u θ| * w θ| := h3
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, |u θ| ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, w θ ^ 2) := hcs
      _ = Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, u θ ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, w θ ^ 2) := by rw [h4]
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, u θ ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) :=
          mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)
  by_cases hInt : MeasureTheory.Integrable
      (fun θ => Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ
        * Work.FTS.GalBasis.cc.Gaz h s θ) (volume.restrict Work.Spaces.Iθ)
  · -- the angular integrand is integrable: split and use the two piece bounds
    have hf_int : MeasureTheory.IntegrableOn f Work.Spaces.Iθ := by
      show MeasureTheory.Integrable f (volume.restrict Work.Spaces.Iθ)
      simpa only [hf] using hInt
    have hmain : |∫ θ in Work.Spaces.Iθ, f θ|
        ≤ S * (∫ θ in Work.Spaces.Iθ, u θ)
          + Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, u θ ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
      have hsplit := setIntegral_Iθ_split (f := f) hMmeas hMI hf_int
      calc |∫ θ in Work.Spaces.Iθ, f θ|
          = |(∫ θ in M, f θ) + (∫ θ in Work.Spaces.Iθ \ M, f θ)| := by rw [hsplit]
        _ ≤ |∫ θ in M, f θ| + |∫ θ in Work.Spaces.Iθ \ M, f θ| := abs_add_le _ _
        _ ≤ S * (∫ θ in Work.Spaces.Iθ, u θ)
              + Real.sqrt (∫ θ in Work.Spaces.Iθ \ M, u θ ^ 2)
                * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) :=
            add_le_add hpiece1 hpiece2
    refine mul_le_mul_of_nonneg_left ?_ (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)
    simpa only [hu] using hmain
  · -- otherwise the angular integral is the junk value `0` and the bound is trivial
    have hzero : ∫ θ in Work.Spaces.Iθ, f θ = 0 := by
      simp only [hf]
      exact MeasureTheory.integral_undef hInt
    rw [hzero, abs_zero, mul_zero]
    refine mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le) ?_
    refine add_nonneg (mul_nonneg hSnn ?_)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    refine MeasureTheory.setIntegral_nonneg hIθ ?_
    intro θ hθ
    simpa only [hu] using mul_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ)
      (Work.FTS.GalBasis.cc.Sw_nonneg_of_mem_Iθ hθ)

end Work.FTS.StrongEps.L12
