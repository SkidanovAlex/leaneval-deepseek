import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_sharp
import Submission.Commons.Analysis.MeasureTheory.iSup_rpow_eq

open MeasureTheory Measure Filter Set
open Commons.Analysis.MeasureTheory
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

/-! ## A layer-cake inequality for `ℝ≥0∞`-valued functions

For an a.e.-measurable `G : β → ℝ≥0∞` and `p > 0` we have
`∫⁻ G^p ≤ p * ∫⁻_{t>0} ν {ofReal t < G} * ofReal (t^(p-1))`, where the level sets are measured
by the outer measure (this is the only thing our weak-type hypothesis controls). The proof
truncates `G` at `n` and uses `banach_lintegral_rpow_le_innerTail`. -/

lemma lintegral_rpow_le_meas_lt {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {G : β → ENNReal} (hG : AEMeasurable G ν) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, G x ^ p ∂ν ≤
      ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ),
        ν {x | ENNReal.ofReal t < G x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have hmct : ∫⁻ x, G x ^ p ∂ν = ⨆ n : ℕ, ∫⁻ x, (G x ⊓ (n : ENNReal)) ^ p ∂ν := by
    have hae : ∀ n : ℕ, AEMeasurable (fun x => (G x ⊓ (n : ENNReal)) ^ p) ν := by
      intro n
      exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable'
        (hG.inf (aemeasurable_const : AEMeasurable (fun _ : β => (n : ENNReal)) ν))
    have hmono : ∀ᵐ x ∂ν, Monotone fun n : ℕ => (G x ⊓ (n : ENNReal)) ^ p :=
      Eventually.of_forall fun x m n hmn =>
        ENNReal.rpow_le_rpow (inf_le_inf_left _ (by exact_mod_cast hmn)) hp.le
    rw [← lintegral_iSup' hae hmono]
    refine lintegral_congr fun x => ?_
    rw [← Commons.Analysis.MeasureTheory.iSup_rpow_eq hp]
    congr 1
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  rw [hmct]
  refine iSup_le fun n => ?_
  have hfin : ∀ x, (G x ⊓ (n : ENNReal)) ≠ ⊤ :=
    fun x => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) inf_le_right
  refine (Commons.Analysis.MeasureTheory.banach_lintegral_rpow_le_innerTail
    (ν := ν) (W := fun x => G x ⊓ (n : ENNReal)) hfin hp).trans ?_
  refine mul_le_mul_right (lintegral_mono_ae ?_) _
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  refine mul_le_mul_left ?_ _
  refine iSup_le fun E => measure_mono (fun x hx =>
    lt_of_lt_of_le (E.2.2 hx) (inf_le_left : G x ⊓ (n : ENNReal) ≤ G x))

/-- The Marcinkiewicz interpolation theorem with sharp (geometric-mean) constant, for a
subadditive and monotone `ℝ≥0∞`-valued operator: weak type `(1,1)` with constant `A₀` and strong
type `(2,2)` with constant `A₁` imply strong type `(p,p)` for `1 < p < 2` with constant
`C · A₀^(2/p-1) A₁^(2-2/p)`. -/
theorem lintegral_rpow_le_of_weak_one_l2
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {ν : MeasureTheory.Measure β}
    (T : (α → ℝ) → (β → ENNReal))
    (hsub : ∀ f h : α → ℝ, ∀ x : β, T (f + h) x ≤ T f x + T h x)
    (hmono : ∀ f h : α → ℝ, (∀ x, ‖f x‖ₑ ≤ ‖h x‖ₑ) → ∀ x : β, T f x ≤ T h x)
    {A0 A1 : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1)
    (hweak : ∀ (f : α → ℝ) (lam : ℝ), 0 < lam →
      ν {x : β | ENNReal.ofReal lam < T f x}
        ≤ ENNReal.ofReal (A0 / lam) * (MeasureTheory.eLpNorm f 1 μ))
    (hl2 : ∀ f : α → ℝ,
      MeasureTheory.eLpNorm (T f) 2 ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f 2 μ)
    (hTmeas : ∀ f : α → ℝ, AEMeasurable (T f) ν)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : α → ℝ,
      MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν
        ≤ ENNReal.ofReal (C * A0 ^ (2 / p - 1) * A1 ^ (2 - 2 / p))
          * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hp1pos : 0 < p - 1 := by linarith
  have h2p : 0 < 2 - p := by linarith
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  set d : ℝ := A0 / A1^2 with hd_def
  have hd : 0 < d := by rw [hd_def]; positivity
  set Bc : ℝ := 12 * 2^(p-1)/(p-1) + 16/(2-p) with hBc_def
  have hBcpos : 0 < Bc := by rw [hBc_def]; positivity
  set C : ℝ := Bc^(1/p) with hC_def
  have hCpos : 0 < C := by rw [hC_def]; exact Real.rpow_pos_of_pos hBcpos _
  refine ⟨C, hCpos, fun f => ?_⟩
  by_cases hfm : AEStronglyMeasurable f μ
  swap
  · have hc : ENNReal.ofReal (C * A0 ^ (2 / p - 1) * A1 ^ (2 - 2 / p)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (mul_pos (mul_pos hCpos (Real.rpow_pos_of_pos hA0 _))
        (Real.rpow_pos_of_pos hA1 _))).ne'
    rw [eLpNorm_of_not_aestronglyMeasurable hfm, ENNReal.mul_top hc]
    exact le_top
  set W : α → ENNReal := fun x => ‖f x‖ₑ with hW_def
  have hWfin : ∀ x, W x ≠ ⊤ := fun x => by
    show ‖f x‖ₑ ≠ ⊤
    rw [← ofReal_norm]
    exact ENNReal.ofReal_ne_top
  -- pointwise (in the level `t`) bound for the distribution function of `T f`
  have hpt : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t^(p-1)) * ν {x | ENNReal.ofReal t < T f x}
        ≤ ENNReal.ofReal (6*A0*t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s)
          + ENNReal.ofReal (4*A1^2*t^(p-3)) *
              (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)) := by
    intro t ht
    have hdt : 0 < d * t := mul_pos hd ht
    set S : Set α := {x | ENNReal.ofReal (d*t) < W x} with hS_def
    set hi : α → ℝ := S.indicator f with hhi_def
    set lo : α → ℝ := Sᶜ.indicator f with hlo_def
    have hSm : NullMeasurableSet S μ := nullMeasurableSet_lt aemeasurable_const hfm.enorm
    have him : AEStronglyMeasurable hi μ := hfm.indicator₀ hSm
    have hlm : AEStronglyMeasurable lo μ := hfm.indicator₀ hSm.compl
    have hsum : hi + lo = f := by
      rw [hhi_def, hlo_def]
      exact Commons.Analysis.MeasureTheory.banach_indicator_add_compl f
    have hsub2 : ∀ x, T f x ≤ T hi x + T lo x := by
      intro x
      have h := hsub hi lo x
      rwa [hsum] at h
    have hsub3 : {x | ENNReal.ofReal t < T f x}
        ⊆ {x | ENNReal.ofReal (t/2) < T hi x} ∪ {x | ENNReal.ofReal (t/2) < T lo x} := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon
      have hle : T f x ≤ ENNReal.ofReal t := by
        calc T f x ≤ T hi x + T lo x := hsub2 x
          _ ≤ ENNReal.ofReal (t/2) + ENNReal.ofReal (t/2) := add_le_add hcon.1 hcon.2
          _ = ENNReal.ofReal t := by
              rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; norm_num
      exact absurd hx (not_lt.2 hle)
    have hmeas1 : ν {x | ENNReal.ofReal t < T f x}
        ≤ ν {x | ENNReal.ofReal (t/2) < T hi x} + ν {x | ENNReal.ofReal (t/2) < T lo x} :=
      (measure_mono hsub3).trans (measure_union_le _ _)
    -- the high-truncation (weak `(1,1)`) estimate
    have hhigh : ENNReal.ofReal (t^(p-1)) * ν {x | ENNReal.ofReal (t/2) < T hi x}
        ≤ ENNReal.ofReal (6*A0*t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s) := by
      have h1 : ν {x | ENNReal.ofReal (t/2) < T hi x}
          ≤ ENNReal.ofReal (A0/(t/2)) * eLpNorm hi 1 μ := hweak hi (t/2) (by positivity)
      have h2 : eLpNorm hi 1 μ = ∫⁻ x, S.indicator W x ∂μ := by
        rw [eLpNorm_one_eq_lintegral_enorm him]
        refine lintegral_congr fun x => ?_
        rw [hhi_def, enorm_indicator_eq_indicator_enorm]
      have h3 : (∫⁻ x, S.indicator W x ∂μ) ≤ 3 * ∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s := by
        rw [hS_def]
        exact Commons.Analysis.MeasureTheory.lintegral_indicator_high_le hWfin hdt
      have hreal : t ^ (p-1) * (A0/(t/2)) = 2*A0*t^(p-2) := by
        have htp1 : t ^ (p-1) = t ^ (p-2) * t := by
          nth_rewrite 3 [← Real.rpow_one t]
          rw [← Real.rpow_add ht (p-2) 1, show p - 2 + 1 = p - 1 by ring]
        rw [htp1]
        have hstep : t * (A0/(t/2)) = 2*A0 := by field_simp
        calc t ^ (p-2) * t * (A0 / (t / 2)) = t ^ (p-2) * (t * (A0 / (t / 2))) := by ring
          _ = t ^ (p-2) * (2*A0) := by rw [hstep]
          _ = 2*A0*t^(p-2) := by ring
      have h5 : ENNReal.ofReal (t^(p-1)) * ENNReal.ofReal (A0/(t/2))
          = ENNReal.ofReal (2*A0*t^(p-2)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (p-1)), hreal]
      have h6 : ENNReal.ofReal (2*A0*t^(p-2)) * 3 = ENNReal.ofReal (6*A0*t^(p-2)) := by
        rw [show (3:ENNReal) = ENNReal.ofReal 3 by norm_num,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
      calc ENNReal.ofReal (t^(p-1)) * ν {x | ENNReal.ofReal (t/2) < T hi x}
          ≤ ENNReal.ofReal (t^(p-1)) * (ENNReal.ofReal (A0/(t/2)) * eLpNorm hi 1 μ) :=
              mul_le_mul_right h1 _
        _ = ENNReal.ofReal (t^(p-1)) *
              (ENNReal.ofReal (A0/(t/2)) * ∫⁻ x, S.indicator W x ∂μ) := by rw [h2]
        _ = (ENNReal.ofReal (t^(p-1)) * ENNReal.ofReal (A0/(t/2))) * ∫⁻ x, S.indicator W x ∂μ := by
              rw [mul_assoc]
        _ = ENNReal.ofReal (2*A0*t^(p-2)) * ∫⁻ x, S.indicator W x ∂μ := by rw [h5]
        _ ≤ ENNReal.ofReal (2*A0*t^(p-2)) * (3 * ∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s) :=
              mul_le_mul_right h3 _
        _ = ENNReal.ofReal (6*A0*t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s) := by
              rw [← mul_assoc, h6]
    -- the low-truncation (strong `(2,2)`) estimate
    have hlow : ENNReal.ofReal (t^(p-1)) * ν {x | ENNReal.ofReal (t/2) < T lo x}
        ≤ ENNReal.ofReal (4*A1^2*t^(p-3)) *
            (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)) := by
      have h2t : (2:ENNReal).toReal = (2:ℝ) := by norm_num
      have hTLae : AEMeasurable (fun x => (T lo x)^(2:ℝ)) ν :=
        (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp_aemeasurable' (hTmeas lo)
      have hcheb : ENNReal.ofReal ((t/2)^2) * ν {x | ENNReal.ofReal ((t/2)^2) ≤ (T lo x)^(2:ℝ)}
          ≤ ∫⁻ x, (T lo x)^(2:ℝ) ∂ν := mul_meas_ge_le_lintegral₀ hTLae _
      have hset : {x | ENNReal.ofReal (t/2) < T lo x}
          ⊆ {x | ENNReal.ofReal ((t/2)^2) ≤ (T lo x)^(2:ℝ)} := by
        intro x hx
        have h1 : (ENNReal.ofReal (t/2))^(2:ℝ) ≤ (T lo x)^(2:ℝ) :=
          ENNReal.rpow_le_rpow hx.le (by norm_num)
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 2)] at h1
        simpa [show (t/2)^(2:ℝ) = (t/2)^2 by norm_num] using h1
      have hcheb2 : ENNReal.ofReal ((t/2)^2) * ν {x | ENNReal.ofReal (t/2) < T lo x}
          ≤ ∫⁻ x, (T lo x)^(2:ℝ) ∂ν :=
        (mul_le_mul_right (measure_mono hset) (ENNReal.ofReal ((t/2)^2))).trans hcheb
      have heLpTh : (eLpNorm (T lo) 2 ν)^(2:ℝ) = ∫⁻ x, (T lo x)^(2:ℝ) ∂ν := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ENNReal)) (by norm_num) (by norm_num)
          (hTmeas lo).aestronglyMeasurable]
        simp_rw [h2t, enorm_eq_self]
        rw [← ENNReal.rpow_mul, show (1:ℝ)/2 * 2 = 1 by norm_num, ENNReal.rpow_one]
      have heLpl : (eLpNorm lo 2 μ)^(2:ℝ) = ∫⁻ x, ‖lo x‖ₑ^(2:ℝ) ∂μ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ENNReal)) (by norm_num) (by norm_num) hlm]
        simp_rw [h2t]
        rw [← ENNReal.rpow_mul, show (1:ℝ)/2 * 2 = 1 by norm_num, ENNReal.rpow_one]
      have hL : (∫⁻ x, ‖lo x‖ₑ^(2:ℝ) ∂μ) = ∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ := by
        refine lintegral_congr fun x => ?_
        have h1 : ‖lo x‖ₑ = Sᶜ.indicator W x := by
          rw [hlo_def, enorm_indicator_eq_indicator_enorm]
        rw [h1]
        exact Commons.Analysis.MeasureTheory.banach_trunc_sq W Sᶜ x
      have hstrong' : (eLpNorm (T lo) 2 ν)^(2:ℝ)
          ≤ ENNReal.ofReal (A1^2) * ∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ := by
        calc (eLpNorm (T lo) 2 ν)^(2:ℝ) ≤ (ENNReal.ofReal A1 * eLpNorm lo 2 μ)^(2:ℝ) :=
              ENNReal.rpow_le_rpow (hl2 lo) (by norm_num)
          _ = (ENNReal.ofReal A1)^(2:ℝ) * (eLpNorm lo 2 μ)^(2:ℝ) :=
              ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
          _ = ENNReal.ofReal (A1^2) * ∫⁻ x, ‖lo x‖ₑ^(2:ℝ) ∂μ := by
              rw [heLpl, Commons.Analysis.MeasureTheory.ofReal_sq A1 hA1.le]
          _ = ENNReal.ofReal (A1^2) * ∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ := by rw [hL]
      have hne0 : ENNReal.ofReal ((t/2)^2) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      have hnetop : ENNReal.ofReal ((t/2)^2) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hlow2 : (∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ)
          ≤ ∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) := by
        have hseteq : Sᶜ = {x : α | W x ≤ ENNReal.ofReal (d*t)} := by
          ext x; rw [hS_def]; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
        rw [hseteq]
        exact Commons.Analysis.MeasureTheory.lintegral_indicator_low_le (μ := μ) (W := W) (a := d*t) hdt
      have hmain2 : ν {x | ENNReal.ofReal (t/2) < T lo x}
          ≤ (ENNReal.ofReal ((t/2)^2))⁻¹ *
              (ENNReal.ofReal (A1^2) * ∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ) := by
        have hkey : ν {x | ENNReal.ofReal (t/2) < T lo x}
            ≤ (ENNReal.ofReal ((t/2)^2))⁻¹ *
                (ENNReal.ofReal ((t/2)^2) * ν {x | ENNReal.ofReal (t/2) < T lo x}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
        refine hkey.trans (mul_le_mul_right ?_ _)
        exact (hcheb2.trans (le_of_eq heLpTh.symm)).trans hstrong'
      have hcoef : ENNReal.ofReal (t^(p-1)) * (ENNReal.ofReal ((t/2)^2))⁻¹
          = ENNReal.ofReal (4*t^(p-3)) := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have h1 : (((t/2))^2)⁻¹ = 4*t^(-2:ℝ) := by
          have ha : t^(-2:ℝ) = (t^(2:ℝ))⁻¹ := by
            rw [show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg ht.le]
          have hb : t^(2:ℝ) = t^2 := by norm_num
          rw [ha, hb]
          field_simp
          ring
        rw [h1]
        have h2 : t^(p-1) * t^(-2:ℝ) = t^(p-3) := by
          rw [← Real.rpow_add ht (p-1) (-2), show p - 1 + (-2) = p - 3 by ring]
        calc t^(p-1) * (4*t^(-2:ℝ)) = 4*(t^(p-1) * t^(-2:ℝ)) := by ring
          _ = 4*t^(p-3) := by rw [h2]
      have hcoef2 : ENNReal.ofReal (4*t^(p-3)) * ENNReal.ofReal (A1^2)
          = ENNReal.ofReal (4*A1^2*t^(p-3)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
      calc ENNReal.ofReal (t^(p-1)) * ν {x | ENNReal.ofReal (t/2) < T lo x}
          ≤ ENNReal.ofReal (t^(p-1)) *
              ((ENNReal.ofReal ((t/2)^2))⁻¹ *
                (ENNReal.ofReal (A1^2) * ∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ)) :=
              mul_le_mul_right hmain2 _
        _ = (ENNReal.ofReal (t^(p-1)) * (ENNReal.ofReal ((t/2)^2))⁻¹) *
              (ENNReal.ofReal (A1^2) * ∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ) := by
              rw [mul_assoc]
        _ = (ENNReal.ofReal (4*t^(p-3)) * ENNReal.ofReal (A1^2)) *
              ∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ := by rw [hcoef, mul_assoc]
        _ = ENNReal.ofReal (4*A1^2*t^(p-3)) * ∫⁻ x, Sᶜ.indicator (fun x => W x^2) x ∂μ := by
              rw [hcoef2]
        _ ≤ ENNReal.ofReal (4*A1^2*t^(p-3)) *
              (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)) :=
              mul_le_mul_right hlow2 _
    calc ENNReal.ofReal (t^(p-1)) * ν {x | ENNReal.ofReal t < T f x}
        ≤ ENNReal.ofReal (t^(p-1)) *
            (ν {x | ENNReal.ofReal (t/2) < T hi x} + ν {x | ENNReal.ofReal (t/2) < T lo x}) :=
            mul_le_mul_right hmeas1 _
      _ = ENNReal.ofReal (t^(p-1)) * ν {x | ENNReal.ofReal (t/2) < T hi x}
            + ENNReal.ofReal (t^(p-1)) * ν {x | ENNReal.ofReal (t/2) < T lo x} := by ring
      _ ≤ _ := add_le_add hhigh hlow
  -- the layer cake
  have hlayer : ∫⁻ x, T f x ^ p ∂ν ≤
      ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ),
        ν {x | ENNReal.ofReal t < T f x} * ENNReal.ofReal (t^(p-1)) :=
    lintegral_rpow_le_meas_lt (hTmeas f) hp0
  -- measurability of the two summands of the pointwise bound
  have hTi : Measurable (Commons.Analysis.MeasureTheory.innerTail μ W) := Commons.Analysis.MeasureTheory.innerTail_measurable μ W
  have hMA : AEMeasurable (fun t : ℝ => ENNReal.ofReal (6*A0*t^(p-2)) *
      (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s)) (volume.restrict (Set.Ioi (0:ℝ))) :=
    ((Commons.Analysis.MeasureTheory.measurable_ofReal_mul_rpow (c := 6*A0) (q := p-2)).mul
      ((Commons.Analysis.MeasureTheory.measurable_lintegral_Ioi_half hTi).comp
        (measurable_const.mul measurable_id))).aemeasurable
  have hMB : AEMeasurable (fun t : ℝ => ENNReal.ofReal (4*A1^2*t^(p-3)) *
      (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)))
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    ((Commons.Analysis.MeasureTheory.measurable_ofReal_mul_rpow (c := 4*A1^2) (q := p-3)).mul
      ((Commons.Analysis.MeasureTheory.measurable_lintegral_Ioc_sq hTi).comp
        (measurable_const.mul measurable_id))).aemeasurable
  have hsplit := lintegral_add_left' hMA
    (fun t : ℝ => ENNReal.ofReal (4*A1^2*t^(p-3)) *
      (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)))
  have hint : ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
        ν {x | ENNReal.ofReal t < T f x} * ENNReal.ofReal (t^(p-1)))
      ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
          (ENNReal.ofReal (6*A0*t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s)
          + ENNReal.ofReal (4*A1^2*t^(p-3)) *
              (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)))) := by
    refine mul_le_mul_right (lintegral_mono_ae ?_) _
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have h := hpt t (Set.mem_Ioi.mp ht)
    rwa [mul_comm (ENNReal.ofReal (t ^ (p - 1)))] at h
  -- the high part of the `t`-integral
  have hHigh : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6*A0*t^(p-2)) *
        (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s))
      ≤ ENNReal.ofReal (6*A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
          (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s * ENNReal.ofReal (s^(p-1))) := by
    have hc : Measurable (fun t : ℝ => ENNReal.ofReal (6*A0*t^(p-2))) :=
      Commons.Analysis.MeasureTheory.measurable_ofReal_mul_rpow (c := 6*A0) (q := p-2)
    calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6*A0*t^(p-2)) *
          (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s)
        = ∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s *
            (∫⁻ t in Set.Ioo (0:ℝ) (2*s/d), ENNReal.ofReal (6*A0*t^(p-2))) :=
          Commons.Analysis.MeasureTheory.lintegral_Ioi_mul_Ioi_half hc hTi hd
      _ = ∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s *
            (ENNReal.ofReal (6*A0) * ∫⁻ t in Set.Ioo (0:ℝ) (2*s/d), ENNReal.ofReal (t^(p-2))) := by
          refine lintegral_congr fun s => ?_
          congr 1
          rw [show (∫⁻ t in Set.Ioo (0:ℝ) (2*s/d), ENNReal.ofReal (6*A0*t^(p-2)))
              = ∫⁻ t in Set.Ioo (0:ℝ) (2*s/d), ENNReal.ofReal (6*A0) * ENNReal.ofReal (t^(p-2)) from
              lintegral_congr fun t => ENNReal.ofReal_mul (by positivity),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s *
            (ENNReal.ofReal (6*A0) * ENNReal.ofReal ((2*s/d)^(p-1)/(p-1))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
          congr 1; congr 1
          rw [Commons.Analysis.MeasureTheory.lintegral_Ioo_ofReal_rpow (X := 2*s/d) (q := p-2)
              (by linarith) (le_of_lt (div_pos (mul_pos (by norm_num) hs) hd)),
            show p - 2 + 1 = p - 1 by ring]
      _ = ∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s *
            (ENNReal.ofReal (6*A0) *
              (ENNReal.ofReal ((2/d)^(p-1)/(p-1)) * ENNReal.ofReal (s^(p-1)))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
          congr 1; congr 1
          rw [← Commons.Analysis.MeasureTheory.rpow_scale_high (le_of_lt hs) hd,
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2/d)^(p-1)/(p-1))]
      _ ≤ ENNReal.ofReal (6*A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
            (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s * ENNReal.ofReal (s^(p-1))) := by
          refine le_of_eq ?_
          refine Eq.trans (lintegral_congr fun s => ?_) (lintegral_const_mul' _ _ ?_)
          · ring
          · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- the low part of the `t`-integral
  have hLow : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4*A1^2*t^(p-3)) *
        (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)))
      ≤ ENNReal.ofReal (4*A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
          (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := by
    have hTs : Measurable (fun s : ℝ => Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)) :=
      hTi.comp Real.continuous_sqrt.measurable
    have hc : Measurable (fun t : ℝ => ENNReal.ofReal (4*A1^2*t^(p-3))) :=
      Commons.Analysis.MeasureTheory.measurable_ofReal_mul_rpow (c := 4*A1^2) (q := p-3)
    calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4*A1^2*t^(p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s))
        = ∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) *
            (∫⁻ t in Set.Ioi (Real.sqrt s / d), ENNReal.ofReal (4*A1^2*t^(p-3))) :=
          Commons.Analysis.MeasureTheory.lintegral_Ioi_mul_Ioc_sq hc hTs hd
      _ = ∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) *
            (ENNReal.ofReal (4*A1^2) * ∫⁻ t in Set.Ioi (Real.sqrt s / d), ENNReal.ofReal (t^(p-3))) := by
          refine lintegral_congr fun s => ?_
          congr 1
          rw [show (∫⁻ t in Set.Ioi (Real.sqrt s / d), ENNReal.ofReal (4*A1^2*t^(p-3)))
              = ∫⁻ t in Set.Ioi (Real.sqrt s / d), ENNReal.ofReal (4*A1^2) * ENNReal.ofReal (t^(p-3)) from
              lintegral_congr fun t => ENNReal.ofReal_mul (by positivity),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) *
            (ENNReal.ofReal (4*A1^2) * ENNReal.ofReal ((Real.sqrt s / d)^(p-2)/(2-p))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
          congr 1; congr 1
          rw [Commons.Analysis.MeasureTheory.lintegral_Ioi_ofReal_rpow (X := Real.sqrt s / d)
              (q := p-3) (by linarith) (div_pos (Real.sqrt_pos.2 hs) hd)]
          rw [show p - 3 + 1 = p - 2 by ring, ← div_neg, show (-(p-2)) = 2-p by ring]
      _ = ∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) *
            (ENNReal.ofReal (4*A1^2) * (ENNReal.ofReal (d^(2-p)) *
              (ENNReal.ofReal (1/(2-p)) * ENNReal.ofReal (s^((p-2)/2))))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
          congr 1; congr 1
          rw [Commons.Analysis.MeasureTheory.rpow_scale_low (le_of_lt hs) hd,
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ d^(2-p)),
            Commons.Analysis.MeasureTheory.ofReal_sqrt_rpow (le_of_lt hs) hp2]
      _ ≤ ENNReal.ofReal (4*A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
            (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := by
          refine le_of_eq ?_
          refine Eq.trans (lintegral_congr fun s => ?_) (lintegral_const_mul' _ _ ?_)
          · ring
          · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
              ENNReal.ofReal_ne_top
  -- the two `μ`-integrals
  have hWT : ENNReal.ofReal p *
        (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s * ENNReal.ofReal (s^(p-1)))
      ≤ 2 * ∫⁻ x, W x ^ p ∂μ := by
    rw [show (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s * ENNReal.ofReal (s^(p-1)))
        = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^(p-1)) * Commons.Analysis.MeasureTheory.innerTail μ W s from
        lintegral_congr fun s => mul_comm _ _]
    exact Commons.Analysis.MeasureTheory.rpow_mul_innerTail_integral_le (μ := μ) (W := W) hp1
  have hST : ENNReal.ofReal p *
        (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))
      ≤ 4 * ∫⁻ x, W x ^ p ∂μ := by
    rw [show (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))
        = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^((p-2)/2)) * Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) from
        lintegral_congr fun s => mul_comm _ _]
    exact Commons.Analysis.MeasureTheory.sqrt_innerTail_integral_le (μ := μ) (W := W) hp1
  have hCH : ENNReal.ofReal (6*A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) * 2
      = ENNReal.ofReal (12*A0*(2/d)^(p-1)/(p-1)) := by
    rw [show (2:ENNReal) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6*A0),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6*A0 * ((2/d)^(p-1)/(p-1)))]
    congr 1; ring
  have hCL : ENNReal.ofReal (4*A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) * 4
      = ENNReal.ofReal (16*A1^2*d^(2-p)/(2-p)) := by
    rw [show (4:ENNReal) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4*A1^2),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4*A1^2 * d^(2-p)),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4*A1^2 * d^(2-p) * (1/(2-p)))]
    congr 1; ring
  have hHighB : ENNReal.ofReal p * (ENNReal.ofReal (6*A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
        (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s * ENNReal.ofReal (s^(p-1))))
      ≤ ENNReal.ofReal (12*A0*(2/d)^(p-1)/(p-1)) * ∫⁻ x, W x ^ p ∂μ := by
    calc ENNReal.ofReal p * (ENNReal.ofReal (6*A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
          (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s * ENNReal.ofReal (s^(p-1))))
        = ENNReal.ofReal (6*A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
            (ENNReal.ofReal p * (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W s * ENNReal.ofReal (s^(p-1)))) := by
          ring
      _ ≤ ENNReal.ofReal (6*A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) * (2 * ∫⁻ x, W x ^ p ∂μ) :=
          mul_le_mul_right hWT _
      _ = ENNReal.ofReal (12*A0*(2/d)^(p-1)/(p-1)) * ∫⁻ x, W x ^ p ∂μ := by rw [← hCH]; ring
  have hLowB : ENNReal.ofReal p * (ENNReal.ofReal (4*A1^2) * ENNReal.ofReal (d^(2-p)) *
        ENNReal.ofReal (1/(2-p)) *
        (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))))
      ≤ ENNReal.ofReal (16*A1^2*d^(2-p)/(2-p)) * ∫⁻ x, W x ^ p ∂μ := by
    calc ENNReal.ofReal p * (ENNReal.ofReal (4*A1^2) * ENNReal.ofReal (d^(2-p)) *
          ENNReal.ofReal (1/(2-p)) *
          (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))))
        = ENNReal.ofReal (4*A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
            (ENNReal.ofReal p *
              (∫⁻ s in Set.Ioi (0:ℝ), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))) := by
          ring
      _ ≤ ENNReal.ofReal (4*A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
            (4 * ∫⁻ x, W x ^ p ∂μ) := mul_le_mul_right hST _
      _ = ENNReal.ofReal (16*A1^2*d^(2-p)/(2-p)) * ∫⁻ x, W x ^ p ∂μ := by rw [← hCL]; ring
  have hconst : 12*A0*(2/d)^(p-1)/(p-1) + 16*A1^2*d^(2-p)/(2-p) = Bc*A0^(2-p)*A1^(2*p-2) := by
    rw [hBc_def, hd_def, Commons.Analysis.MeasureTheory.sharp_const_high hA0 hA1,
      Commons.Analysis.MeasureTheory.sharp_const_low hA0 hA1]
    ring
  have hmain : ∫⁻ x, T f x ^ p ∂ν
      ≤ ENNReal.ofReal (Bc * A0^(2-p) * A1^(2*p-2)) * ∫⁻ x, W x ^ p ∂μ := by
    calc ∫⁻ x, T f x ^ p ∂ν
        ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
            ν {x | ENNReal.ofReal t < T f x} * ENNReal.ofReal (t^(p-1))) := hlayer
      _ ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (6*A0*t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s)
            + ENNReal.ofReal (4*A1^2*t^(p-3)) *
                (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s)))) := hint
      _ = ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6*A0*t^(p-2)) *
              (∫⁻ s in Set.Ioi (d*t/2), Commons.Analysis.MeasureTheory.innerTail μ W s))
            + ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4*A1^2*t^(p-3)) *
              (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), Commons.Analysis.MeasureTheory.innerTail μ W (Real.sqrt s))) := by
          rw [hsplit, mul_add]
      _ ≤ ENNReal.ofReal (12*A0*(2/d)^(p-1)/(p-1)) * ∫⁻ x, W x ^ p ∂μ
            + ENNReal.ofReal (16*A1^2*d^(2-p)/(2-p)) * ∫⁻ x, W x ^ p ∂μ :=
          add_le_add ((mul_le_mul_right hHigh _).trans hHighB) ((mul_le_mul_right hLow _).trans hLowB)
      _ = ENNReal.ofReal (12*A0*(2/d)^(p-1)/(p-1) + 16*A1^2*d^(2-p)/(2-p)) * ∫⁻ x, W x ^ p ∂μ := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ = ENNReal.ofReal (Bc * A0^(2-p) * A1^(2*p-2)) * ∫⁻ x, W x ^ p ∂μ := by rw [hconst]
  have hWp : ∫⁻ x, W x ^ p ∂μ = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
    lintegral_congr fun x => by simp [hW_def]
  have hTf_eq : eLpNorm (T f) (ENNReal.ofReal p) ν
      = (∫⁻ x, T f x ^ p ∂ν) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      (hTmeas f).aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
    simp only [enorm_eq_self]
  have hf_eq : eLpNorm f (ENNReal.ofReal p) μ
      = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hfm, ENNReal.toReal_ofReal hp0.le]
  rw [hTf_eq, hf_eq]
  calc (∫⁻ x, T f x ^ p ∂ν) ^ (1/p)
      ≤ (ENNReal.ofReal (Bc * A0^(2-p) * A1^(2*p-2)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        rw [← hWp]; exact hmain
    _ = (ENNReal.ofReal (Bc * A0^(2-p) * A1^(2*p-2)))^(1/p) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂μ)^(1/p) := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal ((Bc * A0^(2-p) * A1^(2*p-2))^(1/p)) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂μ)^(1/p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    _ = ENNReal.ofReal (C * A0 ^ (2 / p - 1) * A1 ^ (2 - 2 / p)) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂μ)^(1/p) := by
        rw [hC_def, Commons.Analysis.MeasureTheory.sharp_final_const hA0 hA1 hBcpos hp1]

end Work.BourgainPlan.Maximal
