/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/TraceAe`: the a.e. boundary traces from the honest bundle

The honest transport clauses replace `BdryTraces α 4 g` by `SmoothOpen g`, `HkMem α 4 g`,
`HkMem α 5 g` (and `DecayAll 4 g`).  This file proves that those hypotheses force the
*radial* traces `z (Thard g k z θ · w z)² → 0` at `0⁺` and `+∞` — for almost every angle `θ`,
which is all any consumer (an integral over `θ`) needs.

The route: `HkMem α K g` gives the product-integrability of the `ℋ^K`-integrand
(`Hon/HkProdOpen.lean`), hence, for a.e. `θ`, the `z`-integrability of the `θ`-slice of
`HkIntegrand α K g`.  Every order-`4`/order-`5` slot of `g` weighted by `w²` is pointwise
dominated by `HkIntegrand` (`w_sq_le_wdivsin_sq`, `sq_le_HkIntegrand_z`,
`sq_le_HkIntegrand_mixed`, `H_le_Wt`), so for a.e. `θ` both `∫ w² (Thard g k z θ)² dz` and
`∫ w² (D_z(Thard g k) z θ)² dz` are finite on `(0,1)` and on `(1,∞)`.  The one-dimensional
`H¹`-lemma `Hon/TraceBase.trace_of_weights` then yields the two traces.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceDefs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceBase
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.Spaces.H_le_Wt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The two weighted slot dominations -/

/-- The `θ`-slice of the hard slot `Thard g k` is the corresponding mixed slot. -/
theorem thard_slice_eq (g : ℝ → ℝ → ℝ) (k : Fin 5) (θ : ℝ) :
    (fun z => Work.FTS.H2.Thard g k z θ)
      = fun z => Work.Spaces.mixed (4 - k.val) k.val g z θ := by
  funext z
  rw [Work.FTS.H2.Thard_eq_mixed]

/-- `w² ≤ (w / sin(2θ)^{η/2})²` on the open angular interval. -/
theorem w_sq_le_wdivsin_sq {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
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

/-- `(w / sin(2θ)^{η/2})² ≤ Wt α z θ ^ 2`, for `0 < α` and every `z`. -/
theorem wdivsin_sq_le_Wt_sq {α : ℝ} (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (z : ℝ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs0 : 0 ≤ Real.sin (2 * θ) := le_of_lt hσ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ha : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hkey : 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [one_div, ← Real.rpow_neg hs0]
    exact Real.rpow_le_rpow_of_exponent_ge hσ hs1 (by
      have h1 : Work.Spaces.eta ≤ Work.Spaces.gam α :=
        le_of_lt (lt_trans Work.Spaces.eta_lt_one (Work.Spaces.one_lt_gam hα))
      linarith)
  calc (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z * (1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [div_eq_mul_one_div]
    _ ≤ (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
        apply pow_le_pow_left₀ _ _ 2
        · exact mul_nonneg ha (div_nonneg zero_le_one (Real.rpow_nonneg hs0 _))
        · exact mul_le_mul_of_nonneg_left hkey ha

/-- `w² ≤ Wt α z θ ^ 2` on the open angular interval, for `0 < α`. -/
theorem w_sq_le_Wt_sq {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (z : ℝ) : (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.Wt α z θ) ^ 2 :=
  le_trans (w_sq_le_wdivsin_sq hθ) (wdivsin_sq_le_Wt_sq hα hθ z)

/-- The order-`4` hard slot of `g`, weighted by `w²`, is dominated by `HkIntegrand α 4 g`. -/
theorem wsq_thard_le_hk4 {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.FTS.H2.Thard g k z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rw [Work.FTS.H2.Thard_eq_mixed]
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    have hsq := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 (by norm_num)
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 4 g z θ) ^ 2
        ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
            * (Work.Spaces.DzIter 4 g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_sq_le_wdivsin_sq hθ) (sq_nonneg _)
      _ = (Work.Spaces.DzIter 4 g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := hsq
  · have h1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
    have hsq := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ k.val (4 - k.val) h1 (by omega)
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (4 - k.val) k.val g z θ) ^ 2
        ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed (4 - k.val) k.val g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_sq_le_Wt_sq hα hθ z) (sq_nonneg _)
      _ = (Work.Spaces.mixed (4 - k.val) k.val g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := hsq

/-- The order-`5` slot belonging to the order-`4` hard slot `k` is dominated by
`HkIntegrand α 5 g`. -/
theorem wsq_mixed5_le_hk5 {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (5 - k.val) k.val g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    have hsq := Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ 5 (by norm_num)
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 g z θ) ^ 2
        ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
            * (Work.Spaces.DzIter 5 g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_sq_le_wdivsin_sq hθ) (sq_nonneg _)
      _ = (Work.Spaces.DzIter 5 g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 5 g z θ := hsq
  · have h1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
    have hsq := Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ k.val (5 - k.val) h1 (by omega)
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (5 - k.val) k.val g z θ) ^ 2
        ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed (5 - k.val) k.val g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (w_sq_le_Wt_sq hα hθ z) (sq_nonneg _)
      _ = (Work.Spaces.mixed (5 - k.val) k.val g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 5 g z θ := hsq

/-! ## The a.e. trace from the honest bundle -/

/-- **The honest bundle gives the a.e. radial traces.** -/
theorem traceAe_of_honG {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (h4 : Work.Spaces.HkMem α 4 g) (h5 : Work.Spaces.HkMem α 5 g) :
    TraceAe g := by
  have hI4 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 4 g z θ)
        Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice (HkProdOpen hsm h4).1
  have hI5 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 5 g z θ)
        Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice (HkProdOpen hsm h5).1
  filter_upwards [hI4, hI5, Work.FTS.TransportS.ae_mem_Ioo_Iθ] with θ hJ4 hJ5 hθ
  intro k
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hJ4' : MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 4 g z θ)
      (Set.Ioi (0 : ℝ)) := (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hJ4
  have hJ5' : MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 5 g z θ)
      (Set.Ioi (0 : ℝ)) := (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hJ5
  -- continuity of the two weighted slots in `z`
  have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.TransportS.continuousOn_w_sq_Qd.comp
      (continuousOn_id.prodMk continuousOn_const) (fun z hz => ⟨hz, hθ⟩)
  have hth : ContinuousOn (fun z : ℝ => Work.FTS.H2.Thard g k z θ) (Set.Ioi (0 : ℝ)) := by
    rw [Work.FTS.H2.Thard_eq_mixed]
    exact ((hsm.mixed (4 - k.val) k.val).continuousOn).comp
      (continuousOn_id.prodMk continuousOn_const) (fun z hz => ⟨hz, hθ⟩)
  have hmx : ContinuousOn (fun z : ℝ => Work.Spaces.mixed (5 - k.val) k.val g z θ)
      (Set.Ioi (0 : ℝ)) :=
    ((hsm.mixed (5 - k.val) k.val).continuousOn).comp
      (continuousOn_id.prodMk continuousOn_const) (fun z hz => ⟨hz, hθ⟩)
  -- integrability of the two weighted slots
  have hW4 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.FTS.H2.Thard g k z θ) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' hJ4' ((hw2.mul (hth.pow 2)).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact wsq_thard_le_hk4 hα k hθ)
  have hW5 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (5 - k.val) k.val g z θ) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' hJ5' ((hw2.mul (hmx.pow 2)).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact wsq_mixed5_le_hk5 hα k hθ)
  -- the `z`-derivative of the slot is the order-`5` slot
  have hderiv_eq : (fun z => (Work.Spaces.w z) ^ 2
        * (z * deriv (fun z' => Work.FTS.H2.Thard g k z' θ) z) ^ 2)
      = fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (5 - k.val) k.val g z θ) ^ 2 := by
    funext z
    have hpt : deriv (fun z' : ℝ => Work.FTS.H2.Thard g k z' θ) z
        = Work.Spaces.pz (Work.Spaces.mixed (4 - k.val) k.val g) z θ := by
      rw [thard_slice_eq g k θ]
      rfl
    have hjk : 5 - k.val = (4 - k.val) + 1 := by omega
    rw [hpt, hjk]
    rfl
  have hW5' : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv (fun z' => Work.FTS.H2.Thard g k z' θ) z) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    rw [hderiv_eq]; exact hW5
  -- differentiability of the slot in `z`
  have hv : ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Work.FTS.H2.Thard g k z' θ) z := by
    intro z hz
    have hcd : ContDiffOn ℝ 1 (fun z' => Work.FTS.H2.Thard g k z' θ) (Set.Ioi (0 : ℝ)) := by
      rw [Work.FTS.H2.Thard_eq_mixed]
      exact ((hsm.mixed (4 - k.val) k.val).curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
    exact (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  -- split the weighted integrability to `(0,1)` and `(1,∞)` and apply the `H¹`-lemma
  exact trace_of_weights (v := fun z' => Work.FTS.H2.Thard g k z' θ) hv
    (IntegrableOn.mono_set hW4 (Set.Ioo_subset_Ioi_self))
    (IntegrableOn.mono_set hW5' (Set.Ioo_subset_Ioi_self))
    (IntegrableOn.mono_set hW4 (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
    (IntegrableOn.mono_set hW5' (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))

end Work.FTS.StrongPersist.N6Trans.Hon
