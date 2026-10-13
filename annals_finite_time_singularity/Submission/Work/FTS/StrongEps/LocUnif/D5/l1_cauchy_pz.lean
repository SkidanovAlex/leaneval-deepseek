import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.LocUnif.D5.window_bound
import Submission.Work.FTS.StrongEps.LocUnif.D5.slice_pointwise_le
import Submission.Work.FTS.StrongEps.LocUnif.D5.box_integral_eq
import Submission.Work.FTS.StrongEps.LocUnif.D5.intervalIntegral_swap
import Submission.Work.FTS.StrongEps.LocUnif.D5.continuousOn_intervalIntegral_shift
import Submission.Work.FTS.StrongEps.LocUnif.D5.integrableOn_slice_integrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option linter.unusedVariables false

/-! ## The engine: a small `L¹` bound for `∂_z` from a small sup-bound for `L` and a
uniform `L²` bound for `∂_z²` -/

theorem l1_box_le {a b a₀ b₀ c d h δ M : ℝ}
    (ha : a₀ ≤ a) (hab : a ≤ b) (hbb₀ : b + h ≤ b₀) (hh : 0 < h)
    (hcd : c ≤ d)
    {P G G' : ℝ → ℝ → ℝ}
    (hP : ∀ z ∈ Set.Icc a (b + h), ∀ θ ∈ Set.Icc c d, |P z θ| ≤ δ)
    (hG : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + h), HasDerivAt (fun z' => P z' θ) (G z θ) z)
    (hG' : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + h), HasDerivAt (fun z' => G z' θ) (G' z θ) z)
    (hGcont : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hG'cont : ContinuousOn (fun p : ℝ × ℝ => G' p.1 p.2) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hint : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d, (G' p.1 p.2) ^ 2 ≤ M) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc c d, |G p.1 p.2|
      ≤ 2 * (b - a) * (d - c) * δ / h + h * (M + (b - a + h) * (d - c) / 4) := by
  have hab₂ : a ≤ b + h := by linarith
  have hbb : b ≤ b₀ := by linarith
  -- (A) the `L²` hypothesis, moved to the small box and to the θ-outer iterated form
  have hsub : Set.Icc a (b + h) ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
    Set.prod_mono (Set.Icc_subset_Icc ha hbb₀) Subset.rfl
  have hFcont : ContinuousOn (fun p : ℝ × ℝ => (G' p.1 p.2) ^ 2)
      (Set.Icc a (b + h) ×ˢ Set.Icc c d) := (hG'cont.mono hsub).pow 2
  have hFint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (G' p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) (hG'cont.pow 2)
  have hnnF : 0 ≤ᵐ[volume.restrict (Set.Icc a₀ b₀ ×ˢ Set.Icc c d)]
      (fun p : ℝ × ℝ => (G' p.1 p.2) ^ 2) := Filter.Eventually.of_forall fun p => sq_nonneg _
  have hreal_sub : ∫ p in Set.Icc a (b + h) ×ˢ Set.Icc c d, (G' p.1 p.2) ^ 2 ≤ M :=
    (MeasureTheory.setIntegral_mono_set hFint hnnF (Filter.Eventually.of_forall hsub)).trans hint
  have hiter : ∫ θ in c..d, ∫ u in a..(b + h), (G' u θ) ^ 2 ≤ M := by
    rw [box_integral_eq (g := fun z θ => (G' z θ) ^ 2) hab₂ hcd hFcont,
      intervalIntegral_swap (g := fun z θ => (G' z θ) ^ 2) hab₂ hcd hFcont] at hreal_sub
    exact hreal_sub
  -- (B) the pointwise slice inequality, for every θ
  have hsmall : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
    Set.prod_mono (Set.Icc_subset_Icc ha hbb) Subset.rfl
  have hslice : ∀ θ ∈ Set.Icc c d, ContinuousOn (fun u : ℝ => G' u θ) (Set.Icc a (b + h)) := by
    intro θ hθ
    have h2 : ContinuousOn (fun u : ℝ => (u, θ)) (Set.Icc a (b + h)) :=
      continuousOn_id.prodMk continuousOn_const
    exact (hG'cont.mono hsub).comp h2 (fun u hu => ⟨hu, hθ⟩)
  have hsliceG : ∀ θ ∈ Set.Icc c d, ContinuousOn (fun u : ℝ => G u θ) (Set.Icc a (b + h)) := by
    intro θ hθ
    have h2 : ContinuousOn (fun u : ℝ => (u, θ)) (Set.Icc a (b + h)) :=
      continuousOn_id.prodMk continuousOn_const
    exact (hGcont.mono hsub).comp h2 (fun u hu => ⟨hu, hθ⟩)
  have hpt : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a b,
      |G z θ| ≤ 2 * δ / h + ∫ u in z..(z + h), |G' u θ| := by
    intro θ hθ z hz
    exact slice_pointwise_le hab hh (fun x hx => hP x hx θ hθ)
      (fun x hx => hG θ hθ x hx) (fun x hx => hG' θ hθ x hx) (hslice θ hθ) z hz
  -- (C) integrate in `z`, for every θ
  have hzbd : ∀ θ ∈ Set.Icc c d,
      ∫ z in a..b, |G z θ| ≤ 2 * (b - a) * δ / h + h * ∫ u in a..(b + h), |G' u θ| := by
    intro θ hθ
    have hshift : ContinuousOn (fun z => ∫ u in z..(z + h), |G' u θ|) (Set.Icc a b) :=
      continuousOn_intervalIntegral_shift hab hh ((hslice θ hθ).abs)
    have hIL : IntervalIntegrable (fun z => |G z θ|) volume a b := by
      have h : ContinuousOn (fun z => |G z θ|) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab]
        exact ((hsliceG θ hθ).abs).mono (Set.Icc_subset_Icc le_rfl (by linarith))
      exact h.intervalIntegrable
    have hIR : IntervalIntegrable (fun z => 2 * δ / h + ∫ u in z..(z + h), |G' u θ|)
        volume a b := by
      have hc : ContinuousOn (fun z => 2 * δ / h + ∫ u in z..(z + h), |G' u θ|)
          (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab]
        exact continuousOn_const.add hshift
      exact hc.intervalIntegrable
    have hstep : ∫ z in a..b, |G z θ| ≤
        ∫ z in a..b, (2 * δ / h + ∫ u in z..(z + h), |G' u θ|) :=
      intervalIntegral.integral_mono_on hab hIL hIR (fun z hz => hpt θ hθ z hz)
    have hsum : ∫ z in a..b, (2 * δ / h + ∫ u in z..(z + h), |G' u θ|)
        = (b - a) * (2 * δ / h) + ∫ z in a..b, ∫ u in z..(z + h), |G' u θ| := by
      have hc : IntervalIntegrable (fun _ : ℝ => 2 * δ / h) volume a b := by
        have hcc : ContinuousOn (fun _ : ℝ => 2 * δ / h) (Set.uIcc a b) := continuousOn_const
        exact hcc.intervalIntegrable
      have hs : IntervalIntegrable (fun z => ∫ u in z..(z + h), |G' u θ|) volume a b := by
        have hcc : ContinuousOn (fun z => ∫ u in z..(z + h), |G' u θ|) (Set.uIcc a b) := by
          rw [Set.uIcc_of_le hab]
          exact hshift
        exact hcc.intervalIntegrable
      rw [intervalIntegral.integral_add hc hs, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    have hwin : ∫ z in a..b, ∫ u in z..(z + h), |G' u θ| ≤ h * ∫ u in a..(b + h), |G' u θ| :=
      window_bound hab hh ((hslice θ hθ).abs) (fun u => abs_nonneg _)
    calc ∫ z in a..b, |G z θ|
        ≤ ∫ z in a..b, (2 * δ / h + ∫ u in z..(z + h), |G' u θ|) := hstep
      _ = (b - a) * (2 * δ / h) + ∫ z in a..b, ∫ u in z..(z + h), |G' u θ| := hsum
      _ ≤ (b - a) * (2 * δ / h) + h * ∫ u in a..(b + h), |G' u θ| := by linarith
      _ = 2 * (b - a) * δ / h + h * ∫ u in a..(b + h), |G' u θ| := by ring
  -- (D) integrate in θ
  have hGab : ContinuousOn (Function.uncurry (fun z θ => |G z θ|))
      (Set.Icc a b ×ˢ Set.Icc c d) := (hGcont.mono hsmall).abs
  have habs' : ContinuousOn (Function.uncurry (fun u θ => |G' u θ|))
      (Set.Icc a (b + h) ×ˢ Set.Icc c d) := (hG'cont.mono hsub).abs
  have hGFint : MeasureTheory.IntegrableOn (fun θ => ∫ u in a..(b + h), |G' u θ|)
      (Set.Ioc c d) := (integrableOn_slice_integrals (f := fun u θ => |G' u θ|) hab₂ hcd habs').1
  have hGF2int : MeasureTheory.IntegrableOn (fun θ => ∫ u in a..(b + h), (G' u θ) ^ 2)
      (Set.Ioc c d) :=
    (integrableOn_slice_integrals (f := fun z θ => (G' z θ) ^ 2) hab₂ hcd hFcont).1
  set C : ℝ := 2 * (b - a) * δ / h with hCdef
  have hstepD : ∫ θ in Set.Ioc c d, (∫ z in a..b, |G z θ|) ∂volume
      ≤ ∫ θ in Set.Ioc c d, (C + h * ∫ u in a..(b + h), |G' u θ|) ∂volume := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun θ => intervalIntegral.integral_nonneg hab (fun z _ => abs_nonneg _))
    · exact (MeasureTheory.integrable_const C).add (hGFint.const_mul h)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
      exact hzbd θ ⟨hθ.1.le, hθ.2⟩
  have hstepD_eq : ∫ θ in Set.Ioc c d, (C + h * ∫ u in a..(b + h), |G' u θ|) ∂volume
      = (d - c) * C + h * ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume := by
    rw [MeasureTheory.integral_add (MeasureTheory.integrable_const C) (hGFint.const_mul h),
      MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hcd, smul_eq_mul]
  -- (E) the AM–GM step
  have hiterIoc : ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), (G' u θ) ^ 2) ∂volume ≤ M := by
    rw [← intervalIntegral.integral_of_le hcd]
    exact hiter
  have hptE : ∀ θ ∈ Set.Icc c d, ∫ u in a..(b + h), |G' u θ|
      ≤ (∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4) := by
    intro θ hθ
    have hIL : IntervalIntegrable (fun u => |G' u θ|) volume a (b + h) := by
      have h : ContinuousOn (fun u => |G' u θ|) (Set.uIcc a (b + h)) := by
        rw [Set.uIcc_of_le hab₂]
        exact (hslice θ hθ).abs
      exact h.intervalIntegrable
    have hIR : IntervalIntegrable (fun u => (G' u θ) ^ 2 + 1 / 4) volume a (b + h) := by
      have h : ContinuousOn (fun u => (G' u θ) ^ 2 + 1 / 4) (Set.uIcc a (b + h)) := by
        rw [Set.uIcc_of_le hab₂]
        exact (hslice θ hθ).pow 2 |>.add continuousOn_const
      exact h.intervalIntegrable
    have hstep : ∫ u in a..(b + h), |G' u θ| ≤ ∫ u in a..(b + h), ((G' u θ) ^ 2 + 1 / 4) :=
      intervalIntegral.integral_mono_on hab₂ hIL hIR (fun u _ => by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (G' u θ - 1 / 2), sq_nonneg (G' u θ + 1 / 2)])
    have hsum : ∫ u in a..(b + h), ((G' u θ) ^ 2 + 1 / 4)
        = (∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4) := by
      have hs : IntervalIntegrable (fun u => (G' u θ) ^ 2) volume a (b + h) := by
        have h : ContinuousOn (fun u => (G' u θ) ^ 2) (Set.uIcc a (b + h)) := by
          rw [Set.uIcc_of_le hab₂]
          exact (hslice θ hθ).pow 2
        exact h.intervalIntegrable
      have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 4) volume a (b + h) :=
        (continuousOn_const (s := Set.uIcc a (b + h)) (c := (1 : ℝ) / 4)).intervalIntegrable
      rw [intervalIntegral.integral_add hs hc, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    rw [hsum] at hstep
    exact hstep
  have hstepE : ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume
      ≤ M + (b + h - a) * (d - c) / 4 := by
    have hmono : ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume
        ≤ ∫ θ in Set.Ioc c d,
          ((∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4)) ∂volume := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall
          (fun θ => intervalIntegral.integral_nonneg hab₂ (fun u _ => abs_nonneg _))
      · exact hGF2int.add (MeasureTheory.integrable_const _)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
        exact hptE θ ⟨hθ.1.le, hθ.2⟩
    have heq : ∫ θ in Set.Ioc c d,
          ((∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4)) ∂volume
        = (∫ θ in Set.Ioc c d, (∫ u in a..(b + h), (G' u θ) ^ 2) ∂volume)
          + (d - c) * ((b + h - a) * (1 / 4)) := by
      rw [MeasureTheory.integral_add hGF2int (MeasureTheory.integrable_const _)]
      congr 1
      rw [MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hcd, smul_eq_mul]
    calc ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume
        ≤ ∫ θ in Set.Ioc c d,
          ((∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4)) ∂volume := hmono
      _ = (∫ θ in Set.Ioc c d, (∫ u in a..(b + h), (G' u θ) ^ 2) ∂volume)
          + (d - c) * ((b + h - a) * (1 / 4)) := heq
      _ ≤ M + (d - c) * ((b + h - a) * (1 / 4)) := by linarith [hiterIoc]
      _ = M + (b + h - a) * (d - c) / 4 := by ring
  -- (F) assemble
  calc ∫ p in Set.Icc a b ×ˢ Set.Icc c d, |G p.1 p.2|
      = ∫ θ in c..d, ∫ z in a..b, |G z θ| := by
        rw [box_integral_eq (g := fun z θ => |G z θ|) hab hcd hGab,
          intervalIntegral_swap (g := fun z θ => |G z θ|) hab hcd hGab]
    _ = ∫ θ in Set.Ioc c d, (∫ z in a..b, |G z θ|) ∂volume := by
        rw [intervalIntegral.integral_of_le hcd]
    _ ≤ ∫ θ in Set.Ioc c d, (C + h * ∫ u in a..(b + h), |G' u θ|) ∂volume := hstepD
    _ = (d - c) * C + h * ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume := hstepD_eq
    _ ≤ (d - c) * C + h * (M + (b + h - a) * (d - c) / 4) := by
        have hstepE' := mul_le_mul_of_nonneg_left hstepE hh.le
        linarith [hstepE']
    _ = 2 * (b - a) * (d - c) * δ / h + h * (M + (b - a + h) * (d - c) / 4) := by
        rw [hCdef]; ring


/-! ## The final theorem (dev version) -/

theorem l1_cauchy_pz {a b a₀ b₀ c d M : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a < b)
    (hbb₀ : b < b₀) (hc : 0 < c) (hcd : c < d) (hd : d < π / 2) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hsm : ∀ n, Work.FTS.EllipticEst.SmoothOpen (L n))
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (h1 : ∀ n, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M)
    (h2 : ∀ n, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε := by
  intro ε hε
  have ha_pos : 0 < a := lt_trans ha₀ ha₀a
  have hdc : 0 < d - c := by linarith
  have hba : 0 < b - a := by linarith
  have hbnb : 0 < b₀ - b := by linarith
  -- constants
  set c₁ : ℝ := 2 * (b - a) * (d - c) with hc₁def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; positivity
  set M₄ : ℝ := 4 * M with hM₄def
  have hM₄nn : 0 ≤ M₄ := by rw [hM₄def]; linarith
  set K₂ : ℝ := M₄ + (b₀ - a) * (d - c) / 4 with hK₂def
  have hK₂nn : 0 ≤ K₂ := by
    rw [hK₂def]
    have h : 0 ≤ (b₀ - a) * (d - c) := by nlinarith [hM₄nn]
    linarith
  set hh : ℝ := min ((b₀ - b) / 2) (ε / (2 * (K₂ + 1))) with hhhdef
  have hhhpos : 0 < hh := by
    rw [hhhdef]
    exact lt_min (by linarith) (by positivity)
  have hhhle₁ : hh ≤ (b₀ - b) / 2 := by rw [hhhdef]; exact min_le_left _ _
  have hhhle₂ : hh ≤ ε / (2 * (K₂ + 1)) := by rw [hhhdef]; exact min_le_right _ _
  have hbhh : b + hh ≤ b₀ := by linarith
  have hK₂hh : hh * K₂ ≤ ε / 2 := by
    have h1 : K₂ ≤ K₂ + 1 := by linarith
    have h3 : hh * K₂ ≤ hh * (K₂ + 1) := mul_le_mul_of_nonneg_left h1 hhhpos.le
    have h4 : hh * (K₂ + 1) ≤ (ε / (2 * (K₂ + 1))) * (K₂ + 1) :=
      mul_le_mul_of_nonneg_right hhhle₂ (by linarith)
    have h5 : (ε / (2 * (K₂ + 1))) * (K₂ + 1) = ε / 2 := by
      field_simp
    linarith
  set δ : ℝ := ε * hh / (2 * c₁) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδeq : c₁ * δ / hh = ε / 2 := by
    have hc₁ne : c₁ ≠ 0 := ne_of_gt hc₁pos
    have hhne : hh ≠ 0 := ne_of_gt hhhpos
    rw [hδdef]
    field_simp
  -- the uniform-convergence threshold
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      dist (Llim p.1 p.2) (L n p.1 p.2) < δ / 2 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hconv) (δ / 2) (by linarith)
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => hN n hn⟩
  refine ⟨N, fun n m hn hm => ?_⟩
  -- the box inclusions
  have hbox : Set.Icc a₀ b₀ ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha₀ hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hsubbox : Set.Icc a (b + hh) ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
    Set.prod_mono (Set.Icc_subset_Icc ha₀a.le hbhh) Subset.rfl
  -- the pointwise bound on the difference
  have hPbound : ∀ z ∈ Set.Icc a (b + hh), ∀ θ ∈ Set.Icc c d,
      |L n z θ - L m z θ| ≤ δ := by
    intro z hz θ hθ
    have hz' : (z, θ) ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      ⟨⟨le_trans ha₀a.le hz.1, le_trans hz.2 hbhh⟩, hθ⟩
    have h1 := hN n hn (z, θ) hz'
    have h2 := hN m hm (z, θ) hz'
    have h3 : dist (L n z θ) (L m z θ) < δ := by
      calc dist (L n z θ) (L m z θ)
          ≤ dist (L n z θ) (Llim z θ) + dist (Llim z θ) (L m z θ) := dist_triangle _ _ _
        _ = dist (Llim z θ) (L n z θ) + dist (Llim z θ) (L m z θ) := by
            rw [dist_comm (L n z θ) (Llim z θ)]
        _ < δ / 2 + δ / 2 := add_lt_add h1 h2
        _ = δ := by ring
    rw [Real.dist_eq] at h3
    exact le_of_lt h3
  -- the derivative relations
  have hGderiv : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + hh),
      HasDerivAt (fun z' => L n z' θ - L m z' θ)
        (Work.Spaces.pz (L n) z θ - Work.Spaces.pz (L m) z θ) z := by
    intro θ hθ z hz
    have hθ' : θ ∈ Set.Ioo 0 (π / 2) :=
      ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
    have hz' : 0 < z := lt_of_lt_of_le ha_pos hz.1
    exact ((hsm n).hasDerivAt_slice hθ' hz').sub ((hsm m).hasDerivAt_slice hθ' hz')
  have hG'deriv : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + hh),
      HasDerivAt (fun z' => Work.Spaces.pz (L n) z' θ - Work.Spaces.pz (L m) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (L n)) z θ
          - Work.Spaces.pz (Work.Spaces.pz (L m)) z θ) z := by
    intro θ hθ z hz
    have hθ' : θ ∈ Set.Ioo 0 (π / 2) :=
      ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
    have hz' : 0 < z := lt_of_lt_of_le ha_pos hz.1
    exact ((hsm n).pz.hasDerivAt_slice hθ' hz').sub ((hsm m).pz.hasDerivAt_slice hθ' hz')
  -- joint continuity
  have hGcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    (((hsm n).pz.continuousOn).mono hbox).sub (((hsm m).pz.continuousOn).mono hbox)
  have hG'cont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
        - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    (((hsm n).pz.pz.continuousOn).mono hbox).sub (((hsm m).pz.pz.continuousOn).mono hbox)
  -- the `L²` bound on the difference
  have hIntN : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((((hsm n).pz.pz.continuousOn).mono hbox).pow 2)
  have hIntM : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((((hsm m).pz.pz.continuousOn).mono hbox).pow 2)
  have hreN : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2 ≤ M := by
    have h := h2 n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntN
      (Filter.Eventually.of_forall fun p => sq_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  have hreM : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 ≤ M := by
    have h := h2 m
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntM
      (Filter.Eventually.of_forall fun p => sq_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  have hcomb : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
        - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 ≤ M₄ := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => 2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
          + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
        (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
      (hIntN.const_mul 2).add (hIntM.const_mul 2)
    have hpt : ∀ᵐ p ∂(volume.restrict (Set.Icc a₀ b₀ ×ˢ Set.Icc c d)),
        (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
          - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2
        ≤ 2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
          + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 :=
      Filter.Eventually.of_forall fun p => by nlinarith [sq_nonneg (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2 + Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2)]
    have hstep : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
            - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2
        ≤ ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
            + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun p => sq_nonneg _) hmaj hpt
    have hsplit : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
            + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
        = 2 * (∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
            (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
          + 2 * (∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
            (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2) := by
      rw [MeasureTheory.integral_add (hIntN.const_mul 2) (hIntM.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hsplit] at hstep
    rw [hM₄def]
    linarith
  -- the engine
  have hmain := l1_box_le ha₀a.le (le_of_lt hab) hbhh hhhpos (le_of_lt hcd)
    hPbound hGderiv hG'deriv hGcont hG'cont hcomb
  have hreal : ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
      |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2| ≤ ε := by
    have hK₂' : M₄ + (b - a + hh) * (d - c) / 4 ≤ K₂ := by
      rw [hK₂def]
      have hle : b - a + hh ≤ b₀ - a := by linarith
      have hmul : (b - a + hh) * (d - c) ≤ (b₀ - a) * (d - c) :=
        mul_le_mul_of_nonneg_right hle hdc.le
      have hdiv : (b - a + hh) * (d - c) / 4 ≤ (b₀ - a) * (d - c) / 4 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      linarith
    have hstep : hh * (M₄ + (b - a + hh) * (d - c) / 4) ≤ hh * K₂ :=
      mul_le_mul_of_nonneg_left hK₂' hhhpos.le
    have hstep' : hh * (M₄ + (b - a + hh) * (d - c) / 4) ≤ ε / 2 := le_trans hstep hK₂hh
    have h1 : 2 * (b - a) * (d - c) * δ / hh = c₁ * δ / hh := by rw [hc₁def]
    rw [h1] at hmain
    linarith [hmain, hstep', hδeq]
  -- convert the real bound into the lower integral
  have hIntabs : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    have hsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      Set.prod_mono (Set.Icc_subset_Icc ha₀a.le (le_of_lt hbb₀)) Subset.rfl
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((hGcont.mono hsub).abs)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntabs
    (Filter.Eventually.of_forall fun p => abs_nonneg _)]
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mpr hreal

end Work.FTS.StrongEps.LocUnif.D5
