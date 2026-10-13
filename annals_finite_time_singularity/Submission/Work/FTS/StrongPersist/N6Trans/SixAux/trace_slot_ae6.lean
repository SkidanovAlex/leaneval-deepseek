import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceBase
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.TransportS.T2Sup.smainBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Two weight dominations

`w² = (1+z)⁴/z⁴` is dominated by both the `η`-weight and the `γ`-weight of the
`ℋ^k`-integrand, on the open angular interval where `sin(2θ) > 0`. -/

/-- `w² ≤ (w / sin(2θ)^{η/2})²` on the open angular interval. -/
theorem w_sq_le_wdivsin_sq {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
  have h2 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [sq, ← Real.rpow_add hσ]
    congr 1
    ring
  calc (Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hone (sq_nonneg _)
    _ = (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
        rw [div_pow, h2, div_eq_mul_inv, Real.rpow_neg hσ.le]

/-- `w² ≤ (Wt α z θ)²` on the open angular interval, for `0 < α`. -/
theorem w_sq_le_Wt_sq {α : ℝ} (hα : 0 < α) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    Work.FTS.TransportS.one_le_rpow_neg hgam hθ
  have h2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hσ]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  calc (Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left hone (sq_nonneg _)
    _ = (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
        rw [mul_pow, h2]

/-! ## Weighted slots are dominated by the `ℋ^k`-integrand -/

/-- A weighted pure `D_z`-slot is dominated by the `ℋ^k`-integrand. -/
theorem wsq_dzIter_le_HkIntegrand {α : ℝ} {g : ℝ → ℝ → ℝ} {b k : ℕ} (hb : b ≤ k) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsq := Work.Spaces.sq_le_HkIntegrand_z α k g z θ b hb
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b g z θ) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter b g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (w_sq_le_wdivsin_sq hθ) (sq_nonneg _)
    _ = (Work.Spaces.DzIter b g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ := hsq

/-- A weighted mixed slot (`a ≥ 1`) is dominated by the `ℋ^k`-integrand. -/
theorem wsq_mixed_le_HkIntegrand {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {a b k : ℕ}
    (ha : 1 ≤ a) (hab : a + b ≤ k) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsq := Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ a b ha hab
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (w_sq_le_Wt_sq hα hθ) (sq_nonneg _)
    _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ := hsq

/-- **The a.e. boundary trace of an `ℋ^6`-slot.**

For almost every angle `θ`, the radial trace `z · (D_z^b D_θ^a g z θ · w z)²` vanishes both at
`0⁺` and at `+∞`, as soon as the slot is of order at most `6` and `g` is smooth on the open
quadrant with `g ∈ ℋ⁶ ∩ ℋ⁷` (the extra order is needed for the `z`-derivative of the slot).

Route: `ℋ^k`-integrability gives, for a.e. `θ`, the `z`-integrability of the `θ`-slice of
`HkIntegrand`; the two weighted slots `w²·(D_z^bD_θ^ag)²` and `w²·(D_z(D_z^bD_θ^ag))²` are
pointwise dominated by `HkIntegrand α 6 g` resp. `HkIntegrand α 7 g`; the one-dimensional
`H¹`-lemma `Hon.trace_of_weights` then yields the two limits. -/
theorem trace_slot_ae6 (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (h6 : Work.Spaces.HkMem α 6 g) (h7 : Work.Spaces.HkMem α 7 g) (hab : a + b ≤ 6) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z : ℝ => z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z : ℝ => z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) := by
  have hI6 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 6 g z θ)
        Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsm h6).1
  have hI7 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 7 g z θ)
        Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsm h7).1
  filter_upwards [hI6, hI7, Work.FTS.TransportS.ae_mem_Ioo_Iθ] with θ hJ6 hJ7 hθ
  have hJ6' : MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 6 g z θ)
      (Set.Ioi (0 : ℝ)) := (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hJ6
  have hJ7' : MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 7 g z θ)
      (Set.Ioi (0 : ℝ)) := (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hJ7
  -- the two pointwise dominations of the weighted slots by the `ℋ^k`-integrands
  have hdom1 : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0
      simpa only [Work.Spaces.mixed_zero_right] using
        wsq_dzIter_le_HkIntegrand (α := α) (g := g) (b := b) (k := 6) (by omega) hθ
    · exact wsq_mixed_le_HkIntegrand hα (Nat.one_le_iff_ne_zero.mpr ha0) hab hθ
  have hdom2 : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 g z θ := by
    intro z
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0
      simpa only [Work.Spaces.mixed_zero_right] using
        wsq_dzIter_le_HkIntegrand (α := α) (g := g) (b := b + 1) (k := 7) (by omega) hθ
    · exact wsq_mixed_le_HkIntegrand hα (Nat.one_le_iff_ne_zero.mpr ha0) (by omega) hθ
  -- continuity of the two slots in `z` on `(0,∞)` (via the `z`-slices of the smooth extension)
  have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z; rfl
    rw [hfun]
    exact ContinuousOn.pow (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))) 2
  have hcd1 := (hsm.mixed b a).curry_z hθ
  have hcd2 := (hsm.mixed (b + 1) a).curry_z hθ
  have hv1c : ContinuousOn (fun z : ℝ => Work.Spaces.mixed b a g z θ) (Set.Ioi (0 : ℝ)) :=
    hcd1.continuousOn
  have hv2c : ContinuousOn (fun z : ℝ => Work.Spaces.mixed (b + 1) a g z θ)
      (Set.Ioi (0 : ℝ)) :=
    hcd2.continuousOn
  -- integrability of the two weighted slots over `(0,∞)`
  have hW1 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' hJ6' ((hw2.mul (hv1c.pow 2)).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact hdom1 z)
  have hW2 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' hJ7' ((hw2.mul (hv2c.pow 2)).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact hdom2 z)
  -- the `z`-derivative of the slot `D_z^bD_θ^ag` is the order-`(b+1)` slot
  have hderiv_eq : (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (z * deriv (fun z' : ℝ => Work.Spaces.mixed b a g z' θ) z) ^ 2)
      = fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2 := by
    funext z
    rfl
  have hW2' : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * (z * deriv (fun z' : ℝ => Work.Spaces.mixed b a g z' θ) z) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    rw [hderiv_eq]
    exact hW2
  -- differentiability of the slot in `z`
  have hv : ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed b a g z' θ) z := fun z hz =>
    (hcd1.differentiableOn (by simp [Work.Stability.smoothOrder])).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  exact Work.FTS.StrongPersist.N6Trans.Hon.trace_of_weights
    (v := fun z' => Work.Spaces.mixed b a g z' θ) hv
    (MeasureTheory.IntegrableOn.mono_set hW1 Set.Ioo_subset_Ioi_self)
    (MeasureTheory.IntegrableOn.mono_set hW2' Set.Ioo_subset_Ioi_self)
    (MeasureTheory.IntegrableOn.mono_set hW1 (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
    (MeasureTheory.IntegrableOn.mono_set hW2' (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))

end Work.FTS.StrongPersist.N6Trans.SixAux
