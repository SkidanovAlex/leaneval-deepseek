import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.StrongEps.LocUnif.D5.exists_strictMono_tendsto_ae_of_lintegral_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter Set

namespace Work.FTS.StrongEps.LocUnif.D5

set_option maxHeartbeats 1600000

/-- The `L¹`-norm (as a lower integral) of the `θ`-slice of `W k - w` over `[a,b]`. -/
private noncomputable def SliceLInt (a b : ℝ) (W : ℕ → ℝ → ℝ → ℝ) (w : ℝ → ℝ → ℝ)
    (k : ℕ) (θ : ℝ) : ENNReal :=
  ∫⁻ z in Set.Icc a b, ENNReal.ofReal |W k z θ - w z θ|

/-- The uncurried difference of the `k`-th approximant and the limit is a.e. measurable for
the product of the two restricted measures. -/
private lemma aemeasurable_uncurried_sub {a b c d : ℝ} {W : ℕ → ℝ → ℝ → ℝ}
    {w : ℝ → ℝ → ℝ}
    (hWm : ∀ k : ℕ, AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hwm : AEMeasurable (fun p : ℝ × ℝ => w p.1 p.2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) (k : ℕ) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2|)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) := by
  rw [Measure.prod_restrict]
  exact ((((hWm k).sub hwm).abs).ennreal_ofReal)

/-- A.e. in `θ`, the `z`-slices of an a.e. measurable function on the box are a.e. measurable
for the restricted measure in `z`. -/
private lemma slice_measurable_ae {a b c d : ℝ} {W : ℕ → ℝ → ℝ → ℝ} {w : ℝ → ℝ → ℝ}
    (hWm : ∀ k : ℕ, AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hwm : AEMeasurable (fun p : ℝ × ℝ => w p.1 p.2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)),
      (∀ k : ℕ, AEMeasurable (fun z : ℝ => W k z θ)
        (volume.restrict (Set.Icc a b))) ∧
      AEMeasurable (fun z : ℝ => w z θ) (volume.restrict (Set.Icc a b)) := by
  have hbox : ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d)))
      = volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := Measure.prod_restrict _ _
  have key : ∀ (X : ℝ × ℝ → ℝ),
      AEMeasurable X (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) →
      ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)),
        AEMeasurable (fun z : ℝ => X (z, θ)) (volume.restrict (Set.Icc a b)) := by
    intro X hX
    obtain ⟨G, hG, hGeq⟩ := hX
    rw [← hbox] at hGeq
    have hswap := (Measure.measurePreserving_swap
      (μ := volume.restrict (Set.Icc c d))
      (ν := volume.restrict (Set.Icc a b))).quasiMeasurePreserving.ae hGeq
    have h2 := Measure.ae_ae_of_ae_prod hswap
    filter_upwards [h2] with θ hθ
    have hGm : Measurable (fun z : ℝ => G (z, θ)) :=
      hG.comp (measurable_prodMk_right (y := θ))
    refine hGm.aemeasurable.congr ?_
    filter_upwards [hθ] with z hz
    simpa using hz.symm
  refine Eventually.and ?_ ?_
  · rw [ae_all_iff]
    intro k
    exact key (fun p : ℝ × ℝ => W k p.1 p.2) (hWm k)
  · exact key (fun p : ℝ × ℝ => w p.1 p.2) hwm

/-- The norm of an interval integral is bounded by the lower integral of the modulus over the
corresponding `Ioc`-interval. -/
private lemma norm_intervalIntegral_le_toReal {z z₀ : ℝ} {h : ℝ → ℝ} :
    ‖∫ u in z..z₀, h u‖
      ≤ (∫⁻ u in Set.Ioc (min z z₀) (max z z₀), ENNReal.ofReal |h u|).toReal := by
  rcases le_total z z₀ with hle | hle
  · rw [intervalIntegral.integral_of_le hle, min_eq_left hle, max_eq_right hle]
    refine (MeasureTheory.norm_integral_le_lintegral_norm _).trans ?_
    rw [show (∫⁻ u in Set.Ioc z z₀, ENNReal.ofReal ‖h u‖)
        = (∫⁻ u in Set.Ioc z z₀, ENNReal.ofReal |h u|) from
      lintegral_congr fun u => by rw [Real.norm_eq_abs]]
  · rw [intervalIntegral.integral_symm z₀ z, norm_neg, intervalIntegral.integral_of_le hle,
      min_eq_right hle, max_eq_left hle]
    refine (MeasureTheory.norm_integral_le_lintegral_norm _).trans ?_
    rw [show (∫⁻ u in Set.Ioc z₀ z, ENNReal.ofReal ‖h u‖)
        = (∫⁻ u in Set.Ioc z₀ z, ENNReal.ofReal |h u|) from
      lintegral_congr fun u => by rw [Real.norm_eq_abs]]

/-- `L¹`-convergence of a sequence of functions on `[a,b]` to `g` implies the convergence of the
interval integrals against any subinterval. -/
private lemma interval_tendsto_aux {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmf : ∀ k, AEMeasurable (f k) (volume.restrict (Set.Icc a b)))
    (hmg : AEMeasurable g (volume.restrict (Set.Icc a b)))
    (hP : Tendsto (fun k => ∫⁻ z in Set.Icc a b, ENNReal.ofReal |f k z - g z|)
      atTop (nhds 0)) :
    ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
      Tendsto (fun k => ∫ u in z..z₀, f k u) atTop (nhds (∫ u in z..z₀, g u)) := by
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hP 1 zero_lt_one
  have key : ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
      ∀ᶠ k in atTop,
        ‖(∫ u in z..z₀, f k u) - (∫ u in z..z₀, g u)‖
          ≤ (∫⁻ u in Set.Icc a b, ENNReal.ofReal |f k u - g u|).toReal := by
    intro z hz z₀ hz₀
    filter_upwards [eventually_atTop.mpr ⟨N, hN⟩] with k hk
    have hfin : (∫⁻ u in Set.Icc a b, ENNReal.ofReal |f k u - g u|) < ⊤ :=
      lt_of_le_of_lt hk ENNReal.one_lt_top
    have hsub : Set.Ioc (min z z₀) (max z z₀) ⊆ Set.Icc a b := fun u hu =>
      ⟨le_trans (le_min hz.1 hz₀.1) hu.1.le, le_trans hu.2 (max_le hz.2 hz₀.2)⟩
    have hdiff : IntervalIntegrable (fun u => f k u - g u) volume z z₀ := by
      rw [intervalIntegrable_iff]
      refine ⟨?_, ?_⟩
      · exact (((hmf k).mono_set hsub).aestronglyMeasurable).sub
          ((hmg.mono_set hsub).aestronglyMeasurable)
      · change ∫⁻ u, ‖f k u - g u‖ₑ ∂(volume.restrict (Set.uIoc z z₀)) < ⊤
        have h1 : ∫⁻ u, ‖f k u - g u‖ₑ ∂(volume.restrict (Set.uIoc z z₀))
            = ∫⁻ u in Set.Ioc (min z z₀) (max z z₀), ENNReal.ofReal |f k u - g u| := by
          rw [show Set.uIoc z z₀ = Set.Ioc (min z z₀) (max z z₀) from rfl]
          exact lintegral_congr fun u => Real.enorm_eq_ofReal_abs _
        rw [h1]
        exact lt_of_le_of_lt (lintegral_mono_set hsub) hfin
    by_cases h1 : IntervalIntegrable (f k) volume z z₀
    · by_cases h2 : IntervalIntegrable g volume z z₀
      · rw [← intervalIntegral.integral_sub h1 h2]
        refine (norm_intervalIntegral_le_toReal (z := z) (z₀ := z₀)).trans ?_
        refine ENNReal.toReal_mono hfin.ne (lintegral_mono_set ?_)
        intro u hu
        exact ⟨le_trans (le_min hz.1 hz₀.1) hu.1.le, le_trans hu.2 (max_le hz.2 hz₀.2)⟩
      · exact absurd ((h1.sub hdiff).congr (fun u _ => by ring)) h2
    · by_cases h2 : IntervalIntegrable g volume z z₀
      · exact absurd ((hdiff.add h2).congr (fun u _ => by ring)) h1
      · rw [intervalIntegral.integral_undef h1, intervalIntegral.integral_undef h2,
          sub_zero, norm_zero]
        exact ENNReal.toReal_nonneg
  intro z hz z₀ hz₀
  have hbound := key z hz z₀ hz₀
  have hlim : Tendsto (fun k => (∫⁻ u in Set.Icc a b, ENNReal.ofReal |f k u - g u|).toReal)
      atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (show (0 : ENNReal) ≠ ⊤ by simp)).comp hP
    have h0 : (0 : ENNReal).toReal = 0 := by simp
    rw [h0] at h
    exact h
  have hsqueeze : Tendsto
      (fun k => ‖(∫ u in z..z₀, f k u) - (∫ u in z..z₀, g u)‖) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) hbound hlim
  have h0 : Tendsto (fun k => (∫ u in z..z₀, f k u) - (∫ u in z..z₀, g u))
      atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hsqueeze
  have h1 := h0.add_const (∫ u in z..z₀, g u)
  simpa only [sub_add_cancel, zero_add] using h1

theorem slice_interval_tendsto_of_L1 {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {W : ℕ → ℝ → ℝ → ℝ} {w : ℝ → ℝ → ℝ}
    (hWm : ∀ k : ℕ, AEMeasurable
      (fun p : ℝ × ℝ => W k p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hwm : AEMeasurable
      (fun p : ℝ × ℝ => w p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hL1 : Filter.Tendsto (fun k => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2|) Filter.atTop (nhds 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)),
        ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
          Filter.Tendsto (fun k => ∫ u in z..z₀, W (ψ k) u θ) Filter.atTop
            (nhds (∫ u in z..z₀, w u θ)) := by
  -- Measurability of the `θ`-slices of the lower integrals
  have hLmeas : ∀ k, AEMeasurable (SliceLInt a b W w k)
      (volume.restrict (Set.Icc c d)) := by
    intro k
    exact (aemeasurable_uncurried_sub hWm hwm k).lintegral_prod_left
  -- Tonelli: the iterated lower integral is the lower integral over the box
  have key : ∀ k, ∫⁻ θ, SliceLInt a b W w k θ ∂(volume.restrict (Set.Icc c d))
      = ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2| := by
    intro k
    have hf : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2|)
        ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
      have h' := aemeasurable_uncurried_sub hWm hwm k
      rw [Measure.prod_restrict] at h'
      exact h'
    have h := MeasureTheory.setLIntegral_prod_symm
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := Set.Icc a b) (t := Set.Icc c d)
      (f := fun p : ℝ × ℝ => ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2|) hf
    exact h.symm
  have hLtot : Filter.Tendsto
      (fun k => ∫⁻ θ, SliceLInt a b W w k θ ∂(volume.restrict (Set.Icc c d)))
      Filter.atTop (nhds 0) :=
    hL1.congr' (Eventually.of_forall fun k => (key k).symm)
  -- extract the a.e.-convergent subsequence
  obtain ⟨ψ, hψ, hψae⟩ := exists_strictMono_tendsto_ae_of_lintegral_tendsto hLmeas hLtot
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hψae, slice_measurable_ae hWm hwm] with θ hθ hslice
  refine interval_tendsto_aux hab (fun k => hslice.1 (ψ k)) hslice.2 ?_
  exact hθ

end Work.FTS.StrongEps.LocUnif.D5
