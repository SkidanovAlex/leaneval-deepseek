import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.SlotIntegrableHonest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Reduction of the slot exponent.**  On the open angular interval `(0,π/2)` the weight
`θ ↦ sin(2θ)^{-q}` is increasing in the exponent `q` (because `0 < sin(2θ) ≤ 1` there).  Hence
if the `p`-weighted square of a fixed function `V` — which is continuous on `(0,π/2)`, so that
every such slice is a.e. strongly measurable — is integrable, the same holds for the `q`-weighted
square for every `q ≤ p`. -/
theorem integrable_slot_rpow_le {V : ℝ → ℝ} {p q : ℝ} (hpq : q ≤ p)
    (hV : ContinuousOn V (Set.Ioo (0 : ℝ) (π / 2)))
    (hI : Integrable (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-p))
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))) :
    Integrable (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
  have hsin : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Work.Spaces.sin_two_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  refine Integrable.mono' hI ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable
      ((hV.pow 2).mul (Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_sin_two_rpow (-q)))
      measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) (-q)))]
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le hpq hθ) (sq_nonneg _)

/-- Angular integrability of a single `ℋ⁴`-slot, generalized from the proved
`Work.FTS.StrongPersist.N6Trans.HardSlotAux.SlotIntegrableHonest`
(`Submission/Work/FTS/StrongPersist/N6Trans/HardSlotAux/SlotIntegrableHonest.lean`), whose
statement is the special case `a + b = 4` with the extra hypothesis `a = 0 → q = eta`:

* the constraint on the *total* order is relaxed from `a + b = 4` to `a + b ≤ 4`;
* for `a = 0` the exponent `q = 0` is allowed as well (it is needed for the `w²` leaf weight of
  the slot `(a,b) = (0,4)`; the existing result only allows `q = eta` there).

Route: the slot is dominated by a summand of the integrable `ℋ⁴`-integrand:
`a = 0` gives `V = DzIter b g`, `b ≤ 4`, and `w²σ^{-q} V² ≤ w²σ^{-eta} V² = (DzIter b g · wσ^{-eta/2})²`
(since `σ ≤ 1` and `q ≤ eta`), the `i`-th summand of `HkIntegrand`; `a ≥ 1` gives
`w²σ^{-q}V² ≤ w²σ^{-gam α}V² = (mixed b a g · Wt)²`, a summand of `HkIntegrand` since `1 ≤ a` and
`a + b ≤ 4`.  Everything else (a.e. strong measurability of the slots, the reduction of `Iθ` to the
open interval) is already in `HardSlotAux.SlotIntegrableHonest`. -/
theorem SlotIntegrableGen (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ := by
  have hwne : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwne
  change Integrable (fun θ : ℝ =>
      (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
    (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo]
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- ## `a = 0`: the pure `D_z`-slot with exponent `q ∈ {0, η}`
    subst ha0
    have hb : b ≤ 4 := by omega
    rw [Work.Spaces.mixed_zero_right]
    have hslice : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter b g z θ)
        (Set.Ioo (0 : ℝ) (π / 2)) := ((hg.DzIter b).curry_θ hz).continuousOn
    -- the `η`-weighted slot is a summand of `HkIntegrand`
    have hZ : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have h : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hg hmem b hb (z := z) (le_of_lt hz)
      rwa [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo] at h
    have heta : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine (hZ.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_whz_sq z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.DzIter b g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter b g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    rcases hq0 rfl with hq | hq
    · rw [hq]
      simpa using integrable_slot_rpow_le (V := fun θ => Work.Spaces.DzIter b g z θ)
        (p := Work.Spaces.eta) (q := 0) Work.Spaces.eta_nonneg hslice heta
    · rw [hq]
      exact heta
  · -- ## `a ≥ 1`: every slot is a summand of the `ℋ⁴`-integrand with weight `σ^{-γ}`
    have hcontm : ContinuousOn (fun θ : ℝ => Work.Spaces.mixed b a g z θ)
        (Set.Ioo (0 : ℝ) (π / 2)) := ((hg.mixed b a).curry_θ hz).continuousOn
    have hM : Integrable (fun θ : ℝ =>
        (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have hHk : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
        have h : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
            (volume.restrict Work.Spaces.Iθ) := hmem.1 z (le_of_lt hz)
        rwa [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo] at h
      refine Integrable.mono' hHk ?_ ?_
      · exact ContinuousOn.aestronglyMeasurable
          ((hcontm.mul (Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_Wt_slice α z)).pow 2)
          measurableSet_Ioo
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ a b hapos hab
    have hgamma : Integrable (fun θ : ℝ => (Work.Spaces.mixed b a g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine (hM.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_wt_sq α z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.mixed b a g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed b a g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    rcases hqa hapos with hq | hq | hq
    · rw [hq]
      simpa using integrable_slot_rpow_le (V := fun θ => Work.Spaces.mixed b a g z θ)
        (p := Work.Spaces.gam α) (q := 0) (le_of_lt (Work.Spaces.gam_pos hα)) hcontm hgamma
    · rw [hq]
      exact integrable_slot_rpow_le (V := fun θ => Work.Spaces.mixed b a g z θ)
        (p := Work.Spaces.gam α) (q := Work.Spaces.eta)
        (le_trans (le_of_lt Work.Spaces.eta_lt_one) (le_of_lt (Work.Spaces.one_lt_gam hα)))
        hcontm hgamma
    · rw [hq]
      exact hgamma

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
