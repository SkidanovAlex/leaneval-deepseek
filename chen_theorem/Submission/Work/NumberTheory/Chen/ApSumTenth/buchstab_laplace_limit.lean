import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Work.NumberTheory.Chen.ApSumTenth

attribute [local instance] Classical.propDecidable

/-! ## Definitions -/

/-- The ratio `s ↦ A s / s`. -/
def bF (A : ℝ → ℝ) : ℝ → ℝ := fun s => A s / s

/-- The primitive `b ↦ ∫_1^b A v / v dv`. -/
def bPrim (A : ℝ → ℝ) : ℝ → ℝ := fun b => ∫ v in (1 : ℝ)..b, bF A v

/-- The Laplace transform `l ↦ ∫_1^∞ e^{-l s} A s / s ds`. -/
def bPhi (A : ℝ → ℝ) : ℝ → ℝ :=
  fun l => ∫ s in Set.Ioi (1 : ℝ), Real.exp (-(l * s)) * bF A s

/-- `∫_1^∞ e^{-q} / q dq`. -/
def bBeta : ℝ := ∫ q in Set.Ioi (1 : ℝ), Real.exp (-q) / q

/-- `∫_1^l e^{-q} / q dq`. -/
def bG (l : ℝ) : ℝ := ∫ q in (1 : ℝ)..l, Real.exp (-q) / q

/-- `exp (∫_1^∞ e^{-q}/q dq - ∫_1^l e^{-q}/q dq)`. -/
def bP (l : ℝ) : ℝ := Real.exp (bBeta - bG l)

/-! ## §1  Elementary bounds -/

theorem bF_bound {A : ℝ → ℝ} {C : ℝ}
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s)) :
    ∀ s : ℝ, 1 ≤ s → |bF A s| ≤ 2 * |C| := by
  intro s hs
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hAs : |A s| ≤ |C| * (1 + s) :=
    (hbd s hs).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
  rw [bF, abs_div, abs_of_pos hs0]
  calc |A s| / s ≤ |C| * (1 + s) / s := div_le_div_of_nonneg_right hAs hs0.le
    _ = |C| * ((1 + s) / s) := by ring
    _ ≤ |C| * 2 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        rw [add_div, div_self (ne_of_gt hs0)]
        have h1s : (1 : ℝ) / s ≤ 1 := by
          have h := one_div_le_one_div_of_le (show (0:ℝ) < 1 by norm_num) hs
          simpa using h
        linarith
    _ = 2 * |C| := by ring

theorem integrableOn_exp_neg_mul (c : ℝ) (hc : 0 < c) (a : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-(c * s))) (Set.Ioi a) := by
  have h := integrableOn_exp_mul_Ioi (a := -c) (by linarith) a
  simpa [neg_mul] using h

theorem bF_intervalIntegrable {A : ℝ → ℝ}
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b) :
    ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (bF A) volume a b := by
  intro a b ha hb
  have hmem : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact ne_of_gt (lt_of_lt_of_le ha h1)
    · exact ne_of_gt (lt_of_lt_of_le hb h1)
  have hg : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a b) := continuousOn_id.inv₀ hmem
  have h := (hint a b).mul_continuousOn (g := fun x : ℝ => x⁻¹) hg
  exact h.congr (fun x _ => by rw [bF, div_eq_mul_inv])

theorem bF_continuousOn {A : ℝ → ℝ} (hA : ContinuousOn A (Set.Ioi (1 : ℝ))) :
    ContinuousOn (bF A) (Set.Ioi (1 : ℝ)) := by
  have h : ContinuousOn (fun s : ℝ => A s / s) (Set.Ioi (1 : ℝ)) :=
    hA.div continuousOn_id (fun x hx => by
      rw [Set.mem_Ioi] at hx
      exact ne_of_gt (lt_trans one_pos hx))
  exact h.congr (fun x _ => rfl)

/-! ## §2  Continuity of `A` on `(1,∞)` -/

theorem bPrim_continuousOn {A : ℝ → ℝ} {C : ℝ}
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b)
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s)) :
    ContinuousOn (bPrim A) (Set.Ici (1 : ℝ)) := by
  have hintF := bF_intervalIntegrable hint
  have hbound := bF_bound hbd
  have key : ∀ b ∈ Set.Ici (1 : ℝ), ∀ b' ∈ Set.Ici (1 : ℝ),
      |bPrim A b - bPrim A b'| ≤ (2 * |C|) * |b - b'| := by
    intro b hb b' hb'
    have hb1 : (1 : ℝ) ≤ b := hb
    have hb1' : (1 : ℝ) ≤ b' := hb'
    have hI1b : IntervalIntegrable (bF A) volume (1 : ℝ) b := hintF 1 b one_pos (by linarith)
    have hI1b' : IntervalIntegrable (bF A) volume (1 : ℝ) b' := hintF 1 b' one_pos (by linarith)
    have hspl : bPrim A b - bPrim A b' = ∫ x in b'..b, bF A x := by
      have h1 : bPrim A b = ∫ x in (1 : ℝ)..b, bF A x := rfl
      have h2 : bPrim A b' = ∫ x in (1 : ℝ)..b', bF A x := rfl
      rw [h1, h2, intervalIntegral.integral_interval_sub_left hI1b hI1b']
    rw [hspl]
    have hnc := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := b') (b := b) (C := 2 * |C|) (f := bF A) (fun x hx => by
        rw [Real.norm_eq_abs]
        apply hbound
        have hsub : x ∈ Set.uIcc b' b := Set.uIoc_subset_uIcc hx
        rw [Set.mem_uIcc] at hsub
        rcases hsub with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact le_trans hb1' h1
        · exact le_trans hb1 h1)
    simpa [Real.norm_eq_abs] using hnc
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  by_cases hC0 : C = 0
  · refine ⟨1, one_pos, fun a ha _ => ?_⟩
    have hk : bPrim A a - bPrim A b = 0 := by
      have hk' := key a ha b hb
      simpa [hC0] using hk'
    rw [Real.dist_eq, hk, abs_zero]; exact hε
  · have hpos : 0 < 2 * |C| := by
      have : 0 < |C| := abs_pos.mpr hC0
      linarith
    refine ⟨ε / (2 * |C|), div_pos hε hpos, fun a ha hdist => ?_⟩
    have hk := key a ha b hb
    rw [Real.dist_eq] at hdist ⊢
    calc |bPrim A a - bPrim A b| ≤ (2 * |C|) * |a - b| := hk
      _ < (2 * |C|) * (ε / (2 * |C|)) := mul_lt_mul_of_pos_left hdist hpos
      _ = ε := by field_simp

theorem bA_eq_prim {A : ℝ → ℝ} {c₀ : ℝ}
    (hinit : ∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀)
    (hrec : ∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v) :
    ∀ s ∈ Set.Ioi (1 : ℝ), A s = c₀ + bPrim A (max (s - 1) 1) := by
  intro s hs
  have hs1 : (1 : ℝ) < s := hs
  by_cases h2 : s ≤ 2
  · have hmem : s ∈ Set.Icc (1 : ℝ) 2 := ⟨le_of_lt hs1, h2⟩
    have hmax : max (s - 1) 1 = 1 := max_eq_right (by linarith)
    rw [hinit s hmem, hmax, bPrim, intervalIntegral.integral_same, add_zero]
  · have hge : (2 : ℝ) ≤ s := le_of_lt (lt_of_not_ge h2)
    have hmax : max (s - 1) 1 = s - 1 := max_eq_left (by linarith)
    rw [hrec s hge, hmax]
    simp only [bPrim, bF]

theorem bA_continuousOn {A : ℝ → ℝ} {c₀ C : ℝ}
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b)
    (hinit : ∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀)
    (hrec : ∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v)
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s)) :
    ContinuousOn A (Set.Ioi (1 : ℝ)) := by
  have hprim := bPrim_continuousOn hint hbd
  have hφ : ContinuousOn (fun s : ℝ => max (s - 1) 1) (Set.Ioi (1 : ℝ)) :=
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => max (s - 1) 1) (Set.Ioi (1 : ℝ)) (Set.Ici (1 : ℝ)) :=
    fun s _ => show (1:ℝ) ≤ max (s - 1) 1 from le_max_right _ _
  have hcomp : ContinuousOn (fun s : ℝ => bPrim A (max (s - 1) 1)) (Set.Ioi (1 : ℝ)) :=
    hprim.comp hφ hmaps
  have h2 : ContinuousOn (fun s : ℝ => c₀ + bPrim A (max (s - 1) 1)) (Set.Ioi (1 : ℝ)) :=
    continuousOn_const.add hcomp
  exact h2.congr (fun s hs => bA_eq_prim hinit hrec s hs)

/-! ## §3  Differentiability of `A` -/

theorem bA_hasDerivAt {A : ℝ → ℝ} {c₀ C : ℝ}
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b)
    (hinit : ∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀)
    (hrec : ∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v)
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s)) :
    ∀ t : ℝ, 2 < t → HasDerivAt A (bF A (t - 1)) t := by
  intro t ht
  have hAcont := bA_continuousOn hint hinit hrec hbd
  have hfcont : ContinuousOn (bF A) (Set.Ioi (1 : ℝ)) := bF_continuousOn hAcont
  have ht1 : t - 1 ∈ Set.Ioi (1 : ℝ) := by rw [Set.mem_Ioi]; linarith
  have hintF : IntervalIntegrable (bF A) volume (1 : ℝ) (t - 1) :=
    bF_intervalIntegrable hint 1 (t - 1) one_pos (by linarith)
  have hCat : ContinuousAt (bF A) (t - 1) :=
    hfcont.continuousAt (isOpen_Ioi.mem_nhds ht1)
  have hSMAF : StronglyMeasurableAtFilter (bF A) (nhds (t - 1)) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun x hx => hfcont.continuousAt (isOpen_Ioi.mem_nhds hx)) (t - 1) ht1
  have hderiv_prim : HasDerivAt (fun u => ∫ x in (1 : ℝ)..u, bF A x) (bF A (t - 1)) (t - 1) :=
    intervalIntegral.integral_hasDerivAt_right hintF hSMAF hCat
  have hchain : HasDerivAt (fun s : ℝ => bPrim A (s - 1)) (bF A (t - 1)) t := by
    have hc := HasDerivAt.comp t hderiv_prim ((hasDerivAt_id t).sub_const 1)
    have hfun : ((fun u => ∫ x in (1 : ℝ)..u, bF A x) ∘ fun x : ℝ => id x - 1)
        = fun s : ℝ => bPrim A (s - 1) := by
      funext s; simp [bPrim, Function.comp]
    rw [hfun, mul_one] at hc
    exact hc
  have heq : A =ᶠ[nhds t] (fun s : ℝ => c₀ + bPrim A (s - 1)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs2 : (2 : ℝ) < s := hs
    have hsI : s ∈ Set.Ioi (1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
    have hmax : max (s - 1) 1 = s - 1 := max_eq_left (by linarith)
    rw [bA_eq_prim hinit hrec s hsI, hmax]
  exact (hchain.const_add c₀).congr_of_eventuallyEq heq

/-! ## §4  Differentiability of the Laplace transform -/

theorem self_mul_exp_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    s * Real.exp (-(c * s)) ≤ (2 / c) * Real.exp (-(c / 2 * s)) := by
  have h1 : c * s ≤ 2 * Real.exp (c * s / 2) := by
    have h2 : c * s ≤ Real.exp (c * s / 2) := by
      have h := Real.two_mul_le_exp (x := c * s / 2); linarith
    linarith [Real.exp_pos (c * s / 2)]
  have hEc : Real.exp (c * s / 2) * Real.exp (-(c * s)) = Real.exp (-(c / 2 * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hs1 : (c * s) * Real.exp (-(c * s)) / c = s * Real.exp (-(c * s)) := by
    rw [div_eq_iff (ne_of_gt hc)]; ring
  calc s * Real.exp (-(c * s))
      = (c * s) * Real.exp (-(c * s)) / c := hs1.symm
    _ ≤ (2 * Real.exp (c * s / 2)) * Real.exp (-(c * s)) / c :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
          (le_of_lt hc)
    _ = 2 * (Real.exp (c * s / 2) * Real.exp (-(c * s))) / c := by ring
    _ = 2 * Real.exp (-(c / 2 * s)) / c := by rw [hEc]
    _ = (2 / c) * Real.exp (-(c / 2 * s)) := by ring

theorem bPhi_hasDerivAt {A : ℝ → ℝ} {c₀ C : ℝ}
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b)
    (hinit : ∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀)
    (hrec : ∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v)
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s))
    {l : ℝ} (hl : 0 < l) :
    HasDerivAt (bPhi A) (- ∫ s in Set.Ioi (1 : ℝ), Real.exp (-(l * s)) * A s) l := by
  have hAcont := bA_continuousOn hint hinit hrec hbd
  have hfcont : ContinuousOn (bF A) (Set.Ioi (1 : ℝ)) := bF_continuousOn hAcont
  have hfmeas : AEStronglyMeasurable (bF A) (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hfcont.aestronglyMeasurable measurableSet_Ioi
  have hbound := bF_bound hbd
  have hFmeas : ∀ᶠ x in 𝓝 l, AEStronglyMeasurable (fun s => Real.exp (-(x * s)) * bF A s)
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    Eventually.of_forall fun x =>
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable).mul
        hfmeas
  have hFint : Integrable (fun s => Real.exp (-(l * s)) * bF A s)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hg : Integrable (fun s : ℝ => (2 * |C|) * Real.exp (-(l * s)))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (integrableOn_exp_neg_mul l hl 1).const_mul (2 * |C|)
    refine Integrable.mono' hg ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable).mul
        hfmeas
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [Set.mem_Ioi] at hs
      have hbf := hbound s (le_of_lt hs)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [Real.exp_pos (-(l * s)), abs_nonneg (bF A s), hbf]
  have hF'meas : AEStronglyMeasurable (fun s => (Real.exp (-(l * s)) * (-s)) * bF A s)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have h1 : Continuous (fun s : ℝ => Real.exp (-(l * s)) * (-s)) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul continuous_id.neg
    exact h1.aestronglyMeasurable.mul hfmeas
  have hbd' : ∀ᵐ a ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ∀ x ∈ Set.Ioi (l / 2),
        ‖(Real.exp (-(x * a)) * (-a)) * bF A a‖
          ≤ (2 * |C|) * (2 / (l / 2)) * Real.exp (-(l / 2 / 2 * a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [Set.mem_Ioi] at ha
    have ha0 : 0 < a := lt_trans one_pos ha
    intro x hx
    rw [Set.mem_Ioi] at hx
    have hbf := hbound a (le_of_lt ha)
    have hexp : Real.exp (-(x * a)) ≤ Real.exp (-(l / 2 * a)) := by
      apply Real.exp_le_exp.mpr
      have : l / 2 * a < x * a := by nlinarith [hx, ha0]
      linarith
    have hle := self_mul_exp_le (c := l / 2) (s := a) (by linarith) ha0
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos ha0]
    have hstep : Real.exp (-(x * a)) * a ≤ Real.exp (-(l / 2 * a)) * a :=
      mul_le_mul_of_nonneg_right hexp (le_of_lt ha0)
    calc Real.exp (-(x * a)) * a * |bF A a|
        ≤ Real.exp (-(l / 2 * a)) * a * (2 * |C|) :=
          mul_le_mul hstep hbf (abs_nonneg _)
            (mul_nonneg (Real.exp_pos _).le (le_of_lt ha0))
      _ = (2 * |C|) * (a * Real.exp (-(l / 2 * a))) := by ring
      _ ≤ (2 * |C|) * ((2 / (l / 2)) * Real.exp (-(l / 2 / 2 * a))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (2 * |C|) * (2 / (l / 2)) * Real.exp (-(l / 2 / 2 * a)) := by ring
  have hbound_int : Integrable (fun s : ℝ => (2 * |C|) * (2 / (l / 2)) * Real.exp (-(l / 2 / 2 * s)))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (integrableOn_exp_neg_mul (l / 2 / 2) (by linarith) 1).const_mul ((2 * |C|) * (2 / (l / 2)))
  have hdiff : ∀ᵐ a ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ∀ x ∈ Set.Ioi (l / 2),
        HasDerivAt (fun x => Real.exp (-(x * a)) * bF A a)
          ((Real.exp (-(x * a)) * (-a)) * bF A a) x := by
    refine Eventually.of_forall fun a x _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => -(y * a)) (-a) x := by
      have h := ((hasDerivAt_id x).mul_const a).neg
      have hf : (- fun y : ℝ => id y * a) = fun y : ℝ => -(y * a) := by
        funext y; simp
      rw [hf] at h
      simpa using h
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(y * a))) (Real.exp (-(x * a)) * (-a)) x :=
      h1.exp
    simpa using h2.mul_const (bF A a)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (1 : ℝ))) (𝕜 := ℝ) (E := ℝ)
    (F := fun x s => Real.exp (-(x * s)) * bF A s)
    (F' := fun x s => (Real.exp (-(x * s)) * (-s)) * bF A s)
    (x₀ := l) (s := Set.Ioi (l / 2))
    (bound := fun s => (2 * |C|) * (2 / (l / 2)) * Real.exp (-(l / 2 / 2 * s)))
    (Ioi_mem_nhds (by linarith)) hFmeas hFint hF'meas hbd' hbound_int hdiff
  obtain ⟨_, hderiv⟩ := key
  have hb : (fun n => ∫ a, Real.exp (-(n * a)) * bF A a ∂(volume.restrict (Set.Ioi (1 : ℝ))))
      = bPhi A := by
    funext n; rfl
  rw [hb] at hderiv
  have hval : (∫ a, (Real.exp (-(l * a)) * (-a)) * bF A a
        ∂(volume.restrict (Set.Ioi (1 : ℝ))))
      = - ∫ s in Set.Ioi (1 : ℝ), Real.exp (-(l * s)) * A s := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [Set.mem_Ioi] at ha
    have ha0 : a ≠ 0 := ne_of_gt (lt_trans one_pos ha)
    simp only [bF]
    field_simp
  rw [hval] at hderiv
  exact hderiv

/-! ## §5  The integral identity `∫_1^∞ e^{-λs} A s ds = (e^{-λ}/λ)(c₀ + Φ λ)` -/

theorem integrableOn_mul_exp_neg_mul (c : ℝ) (hc : 0 < c) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-(c * s))) (Set.Ioi a) := by
  have hg : IntegrableOn (fun s : ℝ => (2 / c) * Real.exp (-(c / 2 * s))) (Set.Ioi a) :=
    (integrableOn_exp_neg_mul (c / 2) (by linarith) a).const_mul (2 / c)
  refine Integrable.mono' hg ?_ ?_
  · exact (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Set.mem_Ioi] at hs
    have hs0 : 0 < s := lt_of_le_of_lt ha hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0.le, abs_of_pos (Real.exp_pos _)]
    exact self_mul_exp_le hc hs0

theorem integrableOn_one_add_mul_exp_neg_mul (c : ℝ) (hc : 0 < c) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun s : ℝ => (1 + s) * Real.exp (-(c * s))) (Set.Ioi a) := by
  have h := (integrableOn_exp_neg_mul c hc a).add (integrableOn_mul_exp_neg_mul c hc ha)
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]; ring

theorem integral_exp_neg_mul_interval (c : ℝ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Real.exp (-(c * x)) = (Real.exp (-(c * a)) - Real.exp (-(c * b))) / c := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -(Real.exp (-(c * y))) / c) (Real.exp (-(c * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
      have h := ((hasDerivAt_id x).mul_const c).neg
      have hf : (- fun y : ℝ => id y * c) = fun y : ℝ => -(c * y) := by
        funext y; simp [mul_comm]
      rw [hf] at h
      simpa using h
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(c * y)))
        (Real.exp (-(c * x)) * (-c)) x := h1.exp
    have h3 : HasDerivAt (fun y : ℝ => -(Real.exp (-(c * y))) / c)
        (-(Real.exp (-(c * x)) * (-c)) / c) x := h2.neg.div_const c
    have hval : -(Real.exp (-(c * x)) * (-c)) / c = Real.exp (-(c * x)) := by
      rw [show -(Real.exp (-(c * x)) * (-c)) = Real.exp (-(c * x)) * c by ring,
          mul_div_cancel_right₀ _ hc]
    rw [hval] at h3
    exact h3
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp (-(c * x))) volume a b :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  field_simp
  ring

theorem bPsi_eq {A : ℝ → ℝ} {c₀ C : ℝ}
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b)
    (hinit : ∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀)
    (hrec : ∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v)
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s))
    {l : ℝ} (hl : 0 < l) :
    ∫ s in Set.Ioi (1 : ℝ), Real.exp (-(l * s)) * A s
      = (Real.exp (-l) / l) * (c₀ + bPhi A l) := by
  have hAcont := bA_continuousOn hint hinit hrec hbd
  have hfcont : ContinuousOn (bF A) (Set.Ioi (1 : ℝ)) := bF_continuousOn hAcont
  have hc2 : Continuous (fun x : ℝ => -Real.exp (-(l * x)) / l) := by
    have h3 : Continuous (fun x : ℝ => Real.exp (-(l * x))) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
    exact h3.neg.div_const l
  have hI1 : IntegrableOn (fun x : ℝ => A x * Real.exp (-(l * x))) (Set.Ioi (1 : ℝ)) := by
    have hg : IntegrableOn (fun x : ℝ => |C| * ((1 + x) * Real.exp (-(l * x)))) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_one_add_mul_exp_neg_mul l hl (by norm_num : (0:ℝ) ≤ 1)).const_mul |C|
    refine Integrable.mono' hg ?_ ?_
    · exact ((hAcont.aestronglyMeasurable measurableSet_Ioi).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Set.mem_Ioi] at hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hA' : |A x| ≤ |C| * (1 + x) :=
        (hbd x (le_of_lt hx)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
      calc |A x| * Real.exp (-(l * x)) ≤ (|C| * (1 + x)) * Real.exp (-(l * x)) :=
            mul_le_mul_of_nonneg_right hA' (Real.exp_pos _).le
        _ = |C| * ((1 + x) * Real.exp (-(l * x))) := by ring
  -- integrability of `A · v'` and `u' · v` on `Ioi 2`
  have hIuv' : IntegrableOn (fun x : ℝ => A x * Real.exp (-(l * x))) (Set.Ioi (2 : ℝ)) :=
    hI1.mono_set (Set.Ioi_subset_Ioi (by norm_num : (1:ℝ) ≤ 2))
  have hIu'v : IntegrableOn (fun x : ℝ => bF A (x - 1) * (-Real.exp (-(l * x)) / l))
      (Set.Ioi (2 : ℝ)) := by
    have hg : IntegrableOn (fun x : ℝ => (2 * |C| / l) * Real.exp (-(l * x))) (Set.Ioi (2 : ℝ)) :=
      (integrableOn_exp_neg_mul l hl 2).const_mul (2 * |C| / l)
    refine Integrable.mono' hg ?_ ?_
    · have hmaps : Set.MapsTo (fun x : ℝ => x - 1) (Set.Ioi (2:ℝ)) (Set.Ioi (1:ℝ)) := by
        intro x hx; rw [Set.mem_Ioi] at hx ⊢; linarith
      have hcomp : ContinuousOn (fun x : ℝ => bF A (x - 1)) (Set.Ioi (2:ℝ)) :=
        hfcont.comp (continuousOn_id.sub continuousOn_const) hmaps
      exact (hcomp.aestronglyMeasurable measurableSet_Ioi).mul
        (hc2.continuousOn.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Set.mem_Ioi] at hx
      have hbf : |bF A (x - 1)| ≤ 2 * |C| := bF_bound hbd (x - 1) (by linarith)
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos hl]
      calc |bF A (x - 1)| * (Real.exp (-(l * x)) / l)
          ≤ (2 * |C|) * (Real.exp (-(l * x)) / l) := by
            apply mul_le_mul_of_nonneg_right hbf (by positivity)
        _ = (2 * |C| / l) * Real.exp (-(l * x)) := by ring
  -- the derivative of `v`
  have hv : ∀ x ∈ Set.Ioi (2:ℝ),
      HasDerivAt (fun x : ℝ => -Real.exp (-(l * x)) / l) (Real.exp (-(l * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(l * y)) (-l) x := by
      have h := ((hasDerivAt_id x).mul_const l).neg
      have hf : (- fun y : ℝ => id y * l) = fun y : ℝ => -(l * y) := by
        funext y; simp [mul_comm]
      rw [hf] at h
      simpa using h
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(l * y)))
        (Real.exp (-(l * x)) * (-l)) x := h1.exp
    have h3 : HasDerivAt (fun y : ℝ => -(Real.exp (-(l * y))) / l)
        (-(Real.exp (-(l * x)) * (-l)) / l) x := h2.neg.div_const l
    have hval : -(Real.exp (-(l * x)) * (-l)) / l = Real.exp (-(l * x)) := by
      rw [show -(Real.exp (-(l * x)) * (-l)) = Real.exp (-(l * x)) * l by ring,
          mul_div_cancel_right₀ _ (ne_of_gt hl)]
    rw [hval] at h3
    exact h3
  have hu : ∀ x ∈ Set.Ioi (2:ℝ), HasDerivAt A (bF A (x - 1)) x :=
    fun x hx => bA_hasDerivAt hint hinit hrec hbd x hx
  -- the two limits
  have hzero : Tendsto (A * fun x : ℝ => -Real.exp (-(l * x)) / l)
      (nhdsWithin 2 (Set.Ioi 2)) (nhds (c₀ * (-Real.exp (-(l * 2)) / l))) := by
    have hA2 : A 2 = c₀ := hinit 2 ⟨by norm_num, le_refl 2⟩
    have h1 : Tendsto A (nhdsWithin 2 (Set.Ioi 2)) (nhds c₀) := by
      rw [← hA2]
      exact (hAcont.continuousAt (isOpen_Ioi.mem_nhds (by norm_num : (2:ℝ) ∈ Set.Ioi 1))).tendsto.mono_left inf_le_left
    have h2 : Tendsto (fun x : ℝ => -Real.exp (-(l * x)) / l) (nhdsWithin 2 (Set.Ioi 2))
        (nhds (-Real.exp (-(l * 2)) / l)) :=
      hc2.continuousAt.tendsto.mono_left inf_le_left
    exact h1.mul h2
  have hinfty : Tendsto (A * fun x : ℝ => -Real.exp (-(l * x)) / l) atTop (nhds 0) := by
    have hexp3 : Tendsto (fun x : ℝ => (1 + x) * Real.exp (-(l * x))) atTop (nhds 0) := by
      have hexp1 : Tendsto (fun x : ℝ => Real.exp (-(l * x))) atTop (nhds 0) := by
        simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 l hl
      have hexp2 : Tendsto (fun x : ℝ => x * Real.exp (-(l * x))) atTop (nhds 0) := by
        simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 l hl
      have h := hexp1.add hexp2
      simpa [add_mul, one_mul] using h
    have hupper : Tendsto (fun x : ℝ => (|C| / l) * ((1 + x) * Real.exp (-(l * x)))) atTop (nhds 0) := by
      have h := hexp3.const_mul (|C| / l)
      simpa using h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards with x; positivity
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos hl]
      have hA' : |A x| ≤ |C| * (1 + x) :=
        (hbd x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
      calc |A x| * (Real.exp (-(l * x)) / l)
          ≤ (|C| * (1 + x)) * (Real.exp (-(l * x)) / l) :=
            mul_le_mul_of_nonneg_right hA' (by positivity)
        _ = (|C| / l) * ((1 + x) * Real.exp (-(l * x))) := by ring
  -- integration by parts
  have hIBV := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (2:ℝ)) (u := A) (v := fun x : ℝ => -Real.exp (-(l * x)) / l)
    (u' := fun x : ℝ => bF A (x - 1)) (v' := fun x : ℝ => Real.exp (-(l * x)))
    (a' := c₀ * (-Real.exp (-(l * 2)) / l)) (b' := 0)
    hu hv hIuv' hIu'v hzero hinfty
  -- the translation
  have hmp : MeasurePreserving (fun x : ℝ => x + (-1)) volume volume :=
    measurePreserving_add_right volume (-1)
  have hme : MeasurableEmbedding (fun x : ℝ => x + (-1)) :=
    (Homeomorph.addRight (-1)).measurableEmbedding
  have himg : (fun x : ℝ => x + (-1)) '' Set.Ioi (2:ℝ) = Set.Ioi (1:ℝ) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_Ioi] at hx ⊢; linarith
    · intro hy
      rw [Set.mem_Ioi] at hy
      exact ⟨y + 1, by rw [Set.mem_Ioi]; linarith, by ring⟩
  have htr : ∫ x in Set.Ioi (2:ℝ), Real.exp (-(l * x)) * bF A (x - 1)
      = Real.exp (-l) * bPhi A l := by
    have h1 : ∫ x in Set.Ioi (2:ℝ), Real.exp (-(l * x)) * bF A (x - 1)
        = ∫ y in Set.Ioi (1:ℝ), Real.exp (-(l * (y + 1))) * bF A y := by
      have h := hmp.setIntegral_image_emb hme
        (fun y : ℝ => Real.exp (-(l * (y + 1))) * bF A y) (Set.Ioi 2)
      rw [himg] at h
      rw [h]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      simp only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
    rw [h1]
    have h2 : ∫ y in Set.Ioi (1:ℝ), Real.exp (-(l * (y + 1))) * bF A y
        = ∫ y in Set.Ioi (1:ℝ), Real.exp (-l) * (Real.exp (-(l * y)) * bF A y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [show -(l * (y + 1)) = -(l * y) + (-l) by ring, Real.exp_add]; ring
    rw [h2, MeasureTheory.integral_const_mul]
    rfl
  have hIu'v_val : ∫ x in Set.Ioi (2:ℝ), bF A (x - 1) * (-Real.exp (-(l * x)) / l)
      = -(Real.exp (-l) / l) * bPhi A l := by
    have h1 : ∫ x in Set.Ioi (2:ℝ), bF A (x - 1) * (-Real.exp (-(l * x)) / l)
        = ∫ x in Set.Ioi (2:ℝ), (-(1 / l)) * (Real.exp (-(l * x)) * bF A (x - 1)) := by
      apply integral_congr_ae
      filter_upwards with x; ring
    rw [h1, MeasureTheory.integral_const_mul, htr]
    ring
  have hH2 : ∫ x in Set.Ioi (2:ℝ), A x * Real.exp (-(l * x))
      = c₀ * Real.exp (-(2 * l)) / l + (Real.exp (-l) / l) * bPhi A l := by
    rw [hIBV, hIu'v_val]
    ring_nf
  have hH1 : ∫ x in (1:ℝ)..2, A x * Real.exp (-(l * x))
      = c₀ * ((Real.exp (-l) - Real.exp (-(2 * l))) / l) := by
    have hcongr : Set.EqOn (fun x : ℝ => A x * Real.exp (-(l * x)))
        (fun x : ℝ => c₀ * Real.exp (-(l * x))) (Set.uIcc (1:ℝ) 2) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
      rw [Set.mem_Icc] at hx
      show A x * Real.exp (-(l * x)) = c₀ * Real.exp (-(l * x))
      rw [hinit x ⟨hx.1, hx.2⟩]
    rw [intervalIntegral.integral_congr hcongr]
    rw [show (fun x : ℝ => c₀ * Real.exp (-(l * x))) = fun x => Real.exp (-(l * x)) * c₀ from
      funext (fun x => by ring), intervalIntegral.integral_mul_const c₀]
    rw [integral_exp_neg_mul_interval l (ne_of_gt hl) 1 2]
    ring_nf
  have hsplit : ∫ x in Set.Ioi (1:ℝ), A x * Real.exp (-(l * x))
      = (∫ x in (1:ℝ)..2, A x * Real.exp (-(l * x)))
        + ∫ x in Set.Ioi (2:ℝ), A x * Real.exp (-(l * x)) := by
    linarith [intervalIntegral.integral_Ioi_sub_Ioi hI1 (by norm_num : (1:ℝ) ≤ 2)]
  have hmain : ∫ x in Set.Ioi (1:ℝ), A x * Real.exp (-(l * x))
      = (Real.exp (-l) / l) * (c₀ + bPhi A l) := by
    rw [hsplit, hH1, hH2]; ring
  rw [← hmain]
  apply integral_congr_ae
  filter_upwards with z
  ring

/-! ## §6  The delay ODE for the Laplace transform -/

theorem bP_pos (l : ℝ) : 0 < bP l := by
  rw [bP]; exact Real.exp_pos _

theorem integral_Ioi_exp_neg_mul (c : ℝ) (hc : 0 < c) (a : ℝ) :
    ∫ s in Set.Ioi a, Real.exp (-(c * s)) = Real.exp (-(c * a)) / c := by
  have h := integral_exp_mul_Ioi (a := -c) (by linarith : -c < 0) a
  have hfun : (fun x : ℝ => Real.exp ((-c) * x)) = (fun x : ℝ => Real.exp (-(c * x))) := by
    funext x; rw [neg_mul]
  rw [hfun] at h
  rw [h]
  rw [neg_mul, neg_div_neg_eq]

theorem bG_hasDerivAt (l : ℝ) (hl : 0 < l) :
    HasDerivAt bG (Real.exp (-l) / l) l := by
  have hg : ContinuousOn (fun q : ℝ => Real.exp (-q) / q) (Set.Ioi (0:ℝ)) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      (fun x hx => ne_of_gt hx)
  have hint : IntervalIntegrable (fun q : ℝ => Real.exp (-q) / q) volume (1:ℝ) l := by
    apply ContinuousOn.intervalIntegrable
    refine hg.mono ?_
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_lt_of_le one_pos h1
    · exact lt_of_lt_of_le hl h1
  have hmem : l ∈ Set.Ioi (0:ℝ) := hl
  have hCat : ContinuousAt (fun q : ℝ => Real.exp (-q) / q) l :=
    hg.continuousAt (isOpen_Ioi.mem_nhds hmem)
  have hSMAF : StronglyMeasurableAtFilter (fun q : ℝ => Real.exp (-q) / q) (nhds l) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun x hx => hg.continuousAt (isOpen_Ioi.mem_nhds hx)) l hmem
  exact intervalIntegral.integral_hasDerivAt_right hint hSMAF hCat

theorem bP_hasDerivAt (l : ℝ) (hl : 0 < l) :
    HasDerivAt bP (-(Real.exp (-l) / l) * bP l) l := by
  have h1 : HasDerivAt (fun x : ℝ => bBeta - bG x) (-(Real.exp (-l) / l)) l :=
    (bG_hasDerivAt l hl).const_sub bBeta
  have h2 := h1.exp
  have hval : Real.exp (bBeta - bG l) * (-(Real.exp (-l) / l))
      = -(Real.exp (-l) / l) * bP l := by
    rw [bP]; ring
  rw [hval] at h2
  exact h2

theorem bPhi_tendsto_zero {A : ℝ → ℝ} {C : ℝ}
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s)) :
    Tendsto (bPhi A) atTop (nhds 0) := by
  have hbound := bF_bound hbd
  have hlim : Tendsto (fun l : ℝ => 2 * |C| * (Real.exp (-l) / l)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-1) 1 (by norm_num)
    have h' : Tendsto (fun l : ℝ => Real.exp (-l) / l) atTop (nhds 0) := by
      simpa [Real.rpow_neg_one, one_mul, div_eq_mul_inv, mul_comm] using h
    simpa using h'.const_mul (2 * |C|)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun l => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_gt_atTop (0:ℝ)] with l hl
  have hl0 : 0 < l := hl
  have hInt : IntegrableOn (fun s : ℝ => (2 * |C|) * Real.exp (-(l * s))) (Set.Ioi (1:ℝ)) :=
    (integrableOn_exp_neg_mul l hl0 1).const_mul (2 * |C|)
  have hle : (fun s : ℝ => ‖Real.exp (-(l * s)) * bF A s‖)
      ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun s : ℝ => (2 * |C|) * Real.exp (-(l * s))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Set.mem_Ioi] at hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hb := hbound s (le_of_lt hs)
    nlinarith [Real.exp_pos (-(l * s)), abs_nonneg (bF A s), hb]
  calc ‖bPhi A l‖ = ‖∫ s in Set.Ioi (1:ℝ), Real.exp (-(l * s)) * bF A s‖ := by
        simp only [bPhi]
    _ ≤ ∫ s in Set.Ioi (1:ℝ), ‖Real.exp (-(l * s)) * bF A s‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioi (1:ℝ), (2 * |C|) * Real.exp (-(l * s)) :=
        integral_mono_of_nonneg (Eventually.of_forall (fun s => norm_nonneg _)) hInt hle
    _ = 2 * |C| * (Real.exp (-l) / l) := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_mul l hl0 1]
        simp

theorem bG_tendsto_bBeta : Tendsto bG atTop (nhds bBeta) := by
  have hg : IntegrableOn (fun q : ℝ => Real.exp (-q)) (Set.Ioi (1:ℝ)) :=
    integrableOn_exp_neg_Ioi 1
  have hInt : IntegrableOn (fun q : ℝ => Real.exp (-q) / q) (Set.Ioi (1:ℝ)) := by
    refine Integrable.mono' hg ?_ ?_
    · exact ((Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
        (fun x hx => ne_of_gt (lt_trans one_pos hx))).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      rw [Set.mem_Ioi] at hq
      have hq0 : 0 < q := lt_trans one_pos hq
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hq0]
      rw [div_le_iff₀ hq0]
      nlinarith [Real.exp_pos (-q), hq.le]
  exact intervalIntegral_tendsto_integral_Ioi 1 hInt tendsto_id

theorem bP_tendsto_one : Tendsto bP atTop (nhds 1) := by
  have h1 : Tendsto (fun l : ℝ => bBeta - bG l) atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => bBeta) atTop (nhds bBeta)).sub bG_tendsto_bBeta
    simpa using h
  have h2 : Tendsto (fun l : ℝ => Real.exp (bBeta - bG l)) atTop (nhds (Real.exp 0)) :=
    (Real.continuous_exp.tendsto 0).comp h1
  rw [Real.exp_zero] at h2
  exact h2

theorem bPhi_eq {A : ℝ → ℝ} {c₀ C : ℝ}
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b)
    (hinit : ∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀)
    (hrec : ∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v)
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s))
    {l : ℝ} (hl : 0 < l) :
    bPhi A l = c₀ * (bP l - 1) := by
  have hRderiv : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun x => (c₀ + bPhi A x) / bP x) 0 x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hPhi : HasDerivAt (bPhi A) (-(Real.exp (-x) / x) * (c₀ + bPhi A x)) x := by
      have h := bPhi_hasDerivAt hint hinit hrec hbd hx0
      have hval : ∫ s in Set.Ioi (1:ℝ), Real.exp (-(x * s)) * A s
          = (Real.exp (-x) / x) * (c₀ + bPhi A x) := bPsi_eq hint hinit hrec hbd hx0
      rw [hval] at h
      simpa using h
    have hnum : HasDerivAt (fun x => c₀ + bPhi A x)
        (-(Real.exp (-x) / x) * (c₀ + bPhi A x)) x := hPhi.const_add c₀
    have hden : HasDerivAt bP (-(Real.exp (-x) / x) * bP x) x := bP_hasDerivAt x hx0
    have hquot := hnum.div hden (ne_of_gt (bP_pos x))
    have hval : ((-(Real.exp (-x) / x) * (c₀ + bPhi A x)) * bP x
        - (c₀ + bPhi A x) * (-(Real.exp (-x) / x) * bP x)) / bP x ^ 2 = 0 := by ring
    rw [hval] at hquot
    exact hquot
  have hRconst : ∀ x ∈ Set.Ioi (0:ℝ), ∀ y ∈ Set.Ioi (0:ℝ),
      (c₀ + bPhi A x) / bP x = (c₀ + bPhi A y) / bP y :=
    fun x hx y hy => isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hRderiv x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hRderiv x hx).deriv) hx hy
  have hRtend : Tendsto (fun x => (c₀ + bPhi A x) / bP x) atTop (nhds c₀) := by
    have hnum : Tendsto (fun x : ℝ => c₀ + bPhi A x) atTop (nhds (c₀ + 0)) :=
      tendsto_const_nhds.add (bPhi_tendsto_zero hbd)
    have h := hnum.div bP_tendsto_one (by norm_num : (1:ℝ) ≠ 0)
    rw [show (c₀ + 0) / 1 = c₀ by ring] at h
    exact h
  have hc : Tendsto (fun x => (c₀ + bPhi A x) / bP x) atTop
      (nhds ((c₀ + bPhi A l) / bP l)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact (hRconst x hx l hl).symm
  have hRl : (c₀ + bPhi A l) / bP l = c₀ := tendsto_nhds_unique hc hRtend
  rw [div_eq_iff (ne_of_gt (bP_pos l))] at hRl
  have : bPhi A l = c₀ * bP l - c₀ := by linarith
  rw [this]; ring

/-! ## §7  Abelian limit -/

theorem bPhi_abel_bound {f : ℝ → ℝ} {L M0 S η l : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioi (1:ℝ))))
    (hM : ∀ s : ℝ, 1 ≤ s → |f s| ≤ M0) (hM0 : 0 ≤ M0)
    (hS : 1 ≤ S) (hη : 0 ≤ η)
    (hconv : ∀ s : ℝ, S ≤ s → |f s - L| ≤ η) (hl : 0 < l) :
    ‖∫ s in Set.Ioi (1:ℝ), l * (Real.exp (-(l*s)) * (f s - L))‖
      ≤ l * ((S - 1) * (M0 + |L|)) + η * Real.exp (-(l*S)) := by
  have hmeas' : AEStronglyMeasurable (fun s : ℝ => f s - L) (volume.restrict (Set.Ioi (1:ℝ))) :=
    hmeas.sub aestronglyMeasurable_const
  have hmeasF : AEStronglyMeasurable (fun s : ℝ => l * (Real.exp (-(l*s)) * (f s - L)))
      (volume.restrict (Set.Ioi (1:ℝ))) :=
    aestronglyMeasurable_const.mul
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable).mul hmeas')
  have hdom_int : IntegrableOn (fun s : ℝ => l * (M0 + |L|) * Real.exp (-(l*s))) (Set.Ioi (1:ℝ)) :=
    (integrableOn_exp_neg_mul l hl 1).const_mul (l * (M0 + |L|))
  have hFbound : ∀ᵐ a ∂(volume.restrict (Set.Ioi (1:ℝ))),
      ‖l * (Real.exp (-(l*a)) * (f a - L))‖ ≤ l * (M0 + |L|) * Real.exp (-(l*a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Set.mem_Ioi] at hs
    have h1 : |f s - L| ≤ M0 + |L| := by
      calc |f s - L| ≤ |f s| + |L| := abs_sub _ _
        _ ≤ M0 + |L| := by linarith [hM s (le_of_lt hs)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hl.le, abs_of_pos (Real.exp_pos _)]
    calc l * (Real.exp (-(l*s)) * |f s - L|)
        = (l * Real.exp (-(l*s))) * |f s - L| := by ring
      _ ≤ (l * Real.exp (-(l*s))) * (M0 + |L|) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = l * (M0 + |L|) * Real.exp (-(l*s)) := by ring
  have hHintF : IntegrableOn (fun s : ℝ => l * (Real.exp (-(l*s)) * (f s - L))) (Set.Ioi (1:ℝ)) :=
    Integrable.mono' hdom_int hmeasF hFbound
  have hHint : IntegrableOn (fun s : ℝ => ‖l * (Real.exp (-(l*s)) * (f s - L))‖) (Set.Ioi (1:ℝ)) :=
    hHintF.norm
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hleft : ∫ s in Set.Ioc (1:ℝ) S, ‖l * (Real.exp (-(l*s)) * (f s - L))‖
      ≤ l * (M0 + |L|) * (S - 1) := by
    have hint : IntegrableOn (fun s : ℝ => ‖l * (Real.exp (-(l*s)) * (f s - L))‖)
        (Set.Ioc (1:ℝ) S) := hHint.mono_set Set.Ioc_subset_Ioi_self
    have hg : IntegrableOn (fun _ : ℝ => l * (M0 + |L|)) (Set.Ioc (1:ℝ) S) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    have hmono := setIntegral_mono_on hint hg measurableSet_Ioc (fun x hx => by
      rw [Set.mem_Ioc] at hx
      have h1 : |f x - L| ≤ M0 + |L| := by
        calc |f x - L| ≤ |f x| + |L| := abs_sub _ _
          _ ≤ M0 + |L| := by linarith [hM x (le_of_lt hx.1)]
      have h2 : Real.exp (-(l*x)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [hl, hx.1]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hl.le, abs_of_pos (Real.exp_pos _)]
      calc l * (Real.exp (-(l*x)) * |f x - L|)
          = (l * Real.exp (-(l*x))) * |f x - L| := by ring
        _ ≤ (l * Real.exp (-(l*x))) * (M0 + |L|) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (l * 1) * (M0 + |L|) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hl.le) (by positivity)
        _ = l * (M0 + |L|) := by ring)
    calc ∫ s in Set.Ioc (1:ℝ) S, ‖l * (Real.exp (-(l*s)) * (f s - L))‖
        ≤ ∫ s in Set.Ioc (1:ℝ) S, l * (M0 + |L|) := hmono
      _ = l * (M0 + |L|) * (S - 1) := by
          rw [← intervalIntegral.integral_of_le hS, intervalIntegral.integral_const, smul_eq_mul]
          ring
  have hright : ∫ s in Set.Ioi S, ‖l * (Real.exp (-(l*s)) * (f s - L))‖
      ≤ η * Real.exp (-(l*S)) := by
    have hHS : IntegrableOn (fun s : ℝ => ‖l * (Real.exp (-(l*s)) * (f s - L))‖)
        (Set.Ioi S) := hHint.mono_set (Set.Ioi_subset_Ioi hS)
    have hdom : IntegrableOn (fun s : ℝ => l * η * Real.exp (-(l*s))) (Set.Ioi S) :=
      (integrableOn_exp_neg_mul l hl S).const_mul (l * η)
    have hle : (fun s : ℝ => ‖l * (Real.exp (-(l*s)) * (f s - L))‖)
        ≤ᵐ[volume.restrict (Set.Ioi S)] (fun s : ℝ => l * η * Real.exp (-(l*s))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [Set.mem_Ioi] at hs
      have h1 : |f s - L| ≤ η := hconv s (le_of_lt hs)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hl.le, abs_of_pos (Real.exp_pos _)]
      calc l * (Real.exp (-(l*s)) * |f s - L|)
          = (l * Real.exp (-(l*s))) * |f s - L| := by ring
        _ ≤ (l * Real.exp (-(l*s))) * η := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = l * η * Real.exp (-(l*s)) := by ring
    calc ∫ s in Set.Ioi S, ‖l * (Real.exp (-(l*s)) * (f s - L))‖
        ≤ ∫ s in Set.Ioi S, l * η * Real.exp (-(l*s)) :=
          integral_mono_of_nonneg (Eventually.of_forall (fun s => norm_nonneg _)) hdom hle
      _ = l * η * (Real.exp (-(l*S)) / l) := by
          rw [MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_mul l hl S]
      _ = η * Real.exp (-(l*S)) := by field_simp
  have hsplit' : (∫ s in Set.Ioi (1:ℝ), ‖l * (Real.exp (-(l*s)) * (f s - L))‖)
      = (∫ s in Set.Ioc (1:ℝ) S, ‖l * (Real.exp (-(l*s)) * (f s - L))‖)
        + ∫ s in Set.Ioi S, ‖l * (Real.exp (-(l*s)) * (f s - L))‖ := by
    have h1 := intervalIntegral.integral_Ioi_sub_Ioi hHint hS
    rw [intervalIntegral.integral_of_le hS] at h1
    linarith
  rw [hsplit']
  calc (∫ s in Set.Ioc (1:ℝ) S, ‖l * (Real.exp (-(l*s)) * (f s - L))‖)
        + ∫ s in Set.Ioi S, ‖l * (Real.exp (-(l*s)) * (f s - L))‖
      ≤ l * (M0 + |L|) * (S - 1) + η * Real.exp (-(l*S)) := add_le_add hleft hright
    _ = l * ((S - 1) * (M0 + |L|)) + η * Real.exp (-(l*S)) := by ring

theorem bPhi_abel {A : ℝ → ℝ} {c₀ C L : ℝ}
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b)
    (hinit : ∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀)
    (hrec : ∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v)
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s))
    (hlim : Tendsto (bF A) atTop (nhds L)) :
    Tendsto (fun l => l * bPhi A l) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have hAcont := bA_continuousOn hint hinit hrec hbd
  have hfcont : ContinuousOn (bF A) (Set.Ioi (1:ℝ)) := bF_continuousOn hAcont
  have hfmeas : AEStronglyMeasurable (bF A) (volume.restrict (Set.Ioi (1:ℝ))) :=
    hfcont.aestronglyMeasurable measurableSet_Ioi
  have hbound := bF_bound hbd
  have hM0 : (0:ℝ) ≤ 2 * |C| := by positivity
  have h1 : Tendsto (fun l : ℝ => ∫ s in Set.Ioi (1:ℝ), l * (Real.exp (-(l*s)) * (bF A s - L)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε/2 := by linarith
    have hev : ∀ᶠ s in atTop, |bF A s - L| < ε/2 :=
      (Metric.tendsto_nhds.mp hlim (ε/2) hε2).mono (fun s hs => by rwa [Real.dist_eq] at hs)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    set S : ℝ := max N 1 with hSdef
    have hS1 : 1 ≤ S := le_max_right _ _
    have hconv : ∀ s : ℝ, S ≤ s → |bF A s - L| ≤ ε/2 :=
      fun s hs => le_of_lt (hN s (le_trans (le_max_left _ _) hs))
    have hK : (0:ℝ) ≤ 2*|C| + |L| := by positivity
    set δ : ℝ := (ε/2) / ((S - 1) * (2*|C| + |L|) + 1) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδpos)] with l hl hld
    have hl0 : 0 < l := hl
    rw [Real.dist_eq, sub_zero]
    have hmain := bPhi_abel_bound (f := bF A) hfmeas hbound hM0 hS1 (le_of_lt hε2) hconv hl0
    rw [Real.norm_eq_abs] at hmain
    have hexp1 : Real.exp (-(l*S)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [hl0, hS1]
    have hE : (ε/2) * Real.exp (-(l*S)) ≤ ε/2 := by
      have := mul_le_mul_of_nonneg_left hexp1 hε2.le; simpa using this
    have hlt : l * ((S-1) * (2*|C| + |L|)) < ε/2 := by
      by_cases hpos : 0 < (S-1) * (2*|C| + |L|)
      · have h1' : l * ((S-1) * (2*|C| + |L|)) < δ * ((S-1) * (2*|C| + |L|)) :=
          mul_lt_mul_of_pos_right hld hpos
        have h2' : δ * ((S-1) * (2*|C| + |L|)) ≤ ε/2 := by
          rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith :
            (0:ℝ) < (S-1) * (2*|C| + |L|) + 1)]
          nlinarith [hε2, hpos]
        linarith
      · have hzero : (S-1) * (2*|C| + |L|) = 0 := le_antisymm (not_lt.mp hpos) (by positivity)
        rw [hzero, mul_zero]; linarith
    linarith [hmain, hE, hlt]
  have h2 : Tendsto (fun l : ℝ => L * Real.exp (-l)) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    have hneg : Tendsto (fun l : ℝ => -l) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h := (continuous_neg.tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhds (0:ℝ))
      simpa using h
    have hexp : Tendsto (fun l : ℝ => Real.exp (-l)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp 0)) :=
      (Real.continuous_exp.tendsto 0).comp hneg
    simpa [Real.exp_zero] using hexp.const_mul L
  have hL : Tendsto (fun l : ℝ => (∫ s in Set.Ioi (1:ℝ), l * (Real.exp (-(l*s)) * (bF A s - L)))
        + L * Real.exp (-l)) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    have := h1.add h2
    simpa using this
  have key : (fun l : ℝ => (∫ s in Set.Ioi (1:ℝ), l * (Real.exp (-(l*s)) * (bF A s - L)))
        + L * Real.exp (-l)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun l => l * bPhi A l) := by
    filter_upwards [self_mem_nhdsWithin] with l hl0m
    have hl0' : (0:ℝ) < l := hl0m
    have hInt1 : IntegrableOn (fun s : ℝ => l * (Real.exp (-(l*s)) * (bF A s - L)))
        (Set.Ioi (1:ℝ)) := by
      have hg : IntegrableOn (fun s : ℝ => l * (2*|C| + |L|) * Real.exp (-(l*s))) (Set.Ioi (1:ℝ)) :=
        (integrableOn_exp_neg_mul l hl0' 1).const_mul (l * (2*|C| + |L|))
      refine Integrable.mono' hg ?_ ?_
      · exact (aestronglyMeasurable_const.mul
          (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable).mul
            (hfmeas.sub aestronglyMeasurable_const)))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [Set.mem_Ioi] at hs
        have h1 : |bF A s - L| ≤ 2*|C| + |L| := by
          calc |bF A s - L| ≤ |bF A s| + |L| := abs_sub _ _
            _ ≤ 2*|C| + |L| := by linarith [hbound s (le_of_lt hs)]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hl0'.le, abs_of_pos (Real.exp_pos _)]
        calc l * (Real.exp (-(l*s)) * |bF A s - L|)
            = (l * Real.exp (-(l*s))) * |bF A s - L| := by ring
          _ ≤ (l * Real.exp (-(l*s))) * (2*|C| + |L|) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = l * (2*|C| + |L|) * Real.exp (-(l*s)) := by ring
    have hInt2 : IntegrableOn (fun s : ℝ => L * (l * Real.exp (-(l*s)))) (Set.Ioi (1:ℝ)) := by
      have hg : IntegrableOn (fun s : ℝ => |L| * (l * 1) * Real.exp (-(l*s))) (Set.Ioi (1:ℝ)) :=
        (integrableOn_exp_neg_mul l hl0' 1).const_mul (|L| * (l * 1))
      refine Integrable.mono' hg ?_ ?_
      · exact (aestronglyMeasurable_const.mul (aestronglyMeasurable_const.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hl0'.le,
            abs_of_nonneg (Real.exp_pos _).le]
        exact le_of_eq (by ring)
    have hid : l * bPhi A l = (∫ s in Set.Ioi (1:ℝ), l * (Real.exp (-(l*s)) * (bF A s - L)))
        + L * Real.exp (-l) := by
      have h1eq : l * bPhi A l = ∫ s in Set.Ioi (1:ℝ), l * (Real.exp (-(l*s)) * bF A s) := by
        rw [bPhi, MeasureTheory.integral_const_mul]
      rw [h1eq]
      rw [show (fun s : ℝ => l * (Real.exp (-(l*s)) * bF A s))
          = (fun s : ℝ => l * (Real.exp (-(l*s)) * (bF A s - L)) + L * (l * Real.exp (-(l*s)))) from
        funext (fun s => by ring)]
      rw [MeasureTheory.integral_add hInt1 hInt2]
      have hB : (∫ s in Set.Ioi (1:ℝ), L * (l * Real.exp (-(l*s)))) = L * Real.exp (-l) := by
        rw [MeasureTheory.integral_const_mul L (fun s : ℝ => l * Real.exp (-(l*s)))]
        rw [MeasureTheory.integral_const_mul l (fun s : ℝ => Real.exp (-(l*s)))]
        rw [integral_Ioi_exp_neg_mul l hl0' 1]
        field_simp
      rw [hB]
    exact hid.symm
  exact Tendsto.congr' key hL

/-! ## §8  The limit `λ · P(λ) → e^{-γ}` -/

theorem bP_tendsto
    (hγ : Tendsto (fun p : ℝ => (∫ q in (1:ℝ)..p, Real.exp (-q) / q) - Real.log p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.eulerMascheroniConstant + bBeta))) :
    Tendsto (fun l => l * bP l) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h2 : Tendsto (fun l : ℝ => Real.exp (bBeta - (bG l - Real.log l)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    have h1 : Tendsto (fun l : ℝ => bBeta - (bG l - Real.log l))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-Real.eulerMascheroniConstant)) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => bBeta) (nhdsWithin 0 (Set.Ioi 0)) (nhds bBeta)).sub hγ
      have he : bBeta - (Real.eulerMascheroniConstant + bBeta) = -Real.eulerMascheroniConstant := by ring
      rw [he] at h
      exact h
    exact (Real.continuous_exp.tendsto (-Real.eulerMascheroniConstant)).comp h1
  refine Tendsto.congr' ?_ h2
  filter_upwards [self_mem_nhdsWithin] with l hl
  have hl0 : 0 < l := hl
  have hstep : Real.exp (bBeta - (bG l - Real.log l)) = l * bP l := by
    rw [bP, show bBeta - (bG l - Real.log l) = Real.log l + (bBeta - bG l) by ring,
        Real.exp_add, Real.exp_log hl0]
  exact hstep

/-! ## §9  Main theorem -/

theorem buchstab_laplace_limit
    (hγ : Filter.Tendsto
      (fun p : ℝ => (∫ q in (1 : ℝ)..p, Real.exp (-q) / q) - Real.log p)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Real.eulerMascheroniConstant + ∫ q in Set.Ioi (1 : ℝ), Real.exp (-q) / q)))
    (A : ℝ → ℝ) (c₀ L C : ℝ)
    (hint : ∀ a b : ℝ, IntervalIntegrable A volume a b)
    (hinit : ∀ s ∈ Set.Icc (1 : ℝ) 2, A s = c₀)
    (hrec : ∀ s : ℝ, 2 ≤ s → A s = c₀ + ∫ v in (1 : ℝ)..(s - 1), A v / v)
    (hbd : ∀ s : ℝ, 1 ≤ s → |A s| ≤ C * (1 + s))
    (hlim : Filter.Tendsto (fun s : ℝ => A s / s) Filter.atTop (nhds L)) :
    L = c₀ * Real.exp (-Real.eulerMascheroniConstant) := by
  have habel : Tendsto (fun l => l * bPhi A l) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    bPhi_abel hint hinit hrec hbd hlim
  have hP := bP_tendsto hγ
  have h2 : Tendsto (fun l : ℝ => c₀ * (l * bP l) - c₀ * l) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (c₀ * Real.exp (-Real.eulerMascheroniConstant))) := by
    have h1 : Tendsto (fun l : ℝ => c₀ * (l * bP l)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (c₀ * Real.exp (-Real.eulerMascheroniConstant))) := hP.const_mul c₀
    have h2' : Tendsto (fun l : ℝ => c₀ * l) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have ht : Tendsto (fun l : ℝ => l) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        (tendsto_id : Tendsto (fun l : ℝ => l) (nhds 0) (nhds 0)).mono_left nhdsWithin_le_nhds
      simpa using ht.const_mul c₀
    simpa using h1.sub h2'
  have heq : (fun l => l * bPhi A l) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun l => c₀ * (l * bP l) - c₀ * l) := by
    filter_upwards [self_mem_nhdsWithin] with l hl
    have hl0 : 0 < l := hl
    rw [bPhi_eq hint hinit hrec hbd hl0]
    ring
  have h2' : Tendsto (fun l => l * bPhi A l) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (c₀ * Real.exp (-Real.eulerMascheroniConstant))) := Tendsto.congr' heq.symm h2
  exact tendsto_nhds_unique habel h2'

end Work.NumberTheory.Chen.ApSumTenth
