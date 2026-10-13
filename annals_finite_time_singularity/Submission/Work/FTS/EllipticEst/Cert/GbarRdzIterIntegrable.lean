/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted `L²` integrability of the radial iterates of `Ḡ(α,F)`

This module proves `Work.FTS.EllipticEst.Cert.GbarRdzIterIntegrable`: for a source `F` which is
`C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`) and lies in
`ℋ^k` (`Work.Spaces.HkMem`), and for every `j ≤ k`, the function

  `z ↦ w(z)² (D_z^j Ḡ(α,F)(z))²`

is integrable on `[0,∞)` (`w(z) = (1+z)²/z²`, `D_z^j` the `j`-th iterate of `z ∂_z`, and
`Ḡ(α,F)` the singular term of Elgindi's §'Elliptic Regularity Estimates').

This is the *integrability half* of `Cert.GbarSin.Gbar_rDzIter_bound`.  The proof of the latter
is tainted by `Cert.GbarSin.HarOp_weighted_integral_le`, whose real-integral form is still
missing; its **`lintegral` form** `Work.FTS.EllipticEst.HarOp_weighted_lintegral` *is* proved
(it needs only `IntegrableOn (fun z => f z ^ 2) (Ioi 0)`).  We therefore redo the conversion
from the `lintegral` bound to the honest Bochner-integral bound here, with the one ingredient
that the generic conversion needs — a.e. strong measurability of `HarOp β f` — supplied by
*continuity* in the one place where it is used.

## The route

* the exact radial identity `Cert.GbarSin.rDzIter_Gbar_eq_open` gives, on `(0,∞)`,
  `D_z^j Ḡ = -(3/(4α))·HarOp β (U_j)` with `β = 5/α` and `U_j = F_*(D_z^j F)`
  (`Cert.GbarSin.Uj`);
* `Cert.GbarSin.Uj_sq_mul_w_integrable` gives `∫ w²U_j² < ∞` (and the pointwise domination by
  the `ℋ^k`-integrand gives `∫ U_j² < ∞`);
* the weighted Hardy inequality in `lintegral` form
  (`Work.FTS.EllipticEst.HarOp_weighted_lintegral`) bounds
  `∫⁻ ofReal(w²(HarOp β U_j)²) ≤ ofReal(100/β²)·∫⁻ ofReal(w²U_j²) < ∞`, and — `HarOp β U_j`
  being *continuous* on `(0,∞)` by `Cert.GbarSin.continuousOn_primitive_Ioi`
  (continuity of the primitive of the interval-integrable `s ↦ s^{β-1}U_j s`,
  `Cert.GbarSin.intervalIntegrable_rpow_Uj`) times the continuous factor `z^{-β}` — the
  `Integrable` criterion `lintegral_ofReal_ne_top_iff_integrable` applies;
* the a.e. equality with `-(3/(4α))·HarOp β U_j` transports the integrability to
  `z ↦ w(z)²(D_z^j Ḡ(z))²`.

The hypothesis `α ≤ 1` is only used through `β = 5/α ≥ 5`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.HarOp_weighted_lintegral
import Submission.Work.FTS.EllipticEst.Blocks.integral_le_of_lintegral_le
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.OpenCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

open Work.FTS.EllipticEst.Cert.GbarSin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Two elementary facts about the radial weight -/

/-- The radial weight `w(z)² = ((1+z)²/z²)²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hw0 : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun z hz => by
        simp only [Set.mem_Ioi] at hz
        positivity)
  exact hw0.pow 2

/-- The radial weight dominates `1` on `(0,∞)`: `w(z) = (1+z)²/z² ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  rw [Work.Spaces.w, le_div_iff₀ hz2]
  nlinarith

/-! ## The real-integral form of the weighted Hardy inequality -/

/-- **The weighted `L²` Hardy inequality in Bochner-integral form.**  For `β ≥ 5` and a source
`f` whose square and whose `w²`-weighted square are integrable on `(0,∞)`, the `lintegral` Hardy
bound `Work.FTS.EllipticEst.HarOp_weighted_lintegral` upgrades to the honest real inequality

  `∫₀^∞ w(z)² (HarOp β f z)² dz ≤ (100/β²) ∫₀^∞ w(z)² f(z)² dz`,

and the left-hand side is integrable.  The one hypothesis beyond the `lintegral` version is the
a.e. strong measurability of `HarOp β f`, which is needed to pass from a finite `lintegral` to
`Integrable`; in the application it is supplied by continuity of the Hardy operator. -/
theorem harOp_weighted_integral_le_ae (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0))
    (hfw : IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * f z ^ 2) (Set.Ioi 0))
    (hmeas : AEStronglyMeasurable (HarOp β f) (volume.restrict (Set.Ioi 0))) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ (100 / β ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 := by
  have hC : (0 : ℝ) ≤ 100 / β ^ 2 := by positivity
  have hlin : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2))
      ≤ ENNReal.ofReal (100 / β ^ 2) *
        ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2) :=
    HarOp_weighted_lintegral β hβ f hf
  -- finiteness of the right-hand `lintegral`, from the integrability of `w²f²`
  have hHfin : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * f z ^ 2)) < ⊤ := by
    have hEq : ENNReal.ofReal (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2)
        = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2) :=
      ofReal_integral_eq_lintegral_ofReal hfw
        (Eventually.of_forall fun z => by positivity)
    rw [← hEq]
    exact ENNReal.ofReal_lt_top
  -- finiteness of the left-hand `lintegral`
  have hGfin : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
      ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)) < ⊤ :=
    lt_of_le_of_lt hlin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHfin)
  -- the two halves of `IntegrableOn`
  have hnn : ∀ z : ℝ, 0 ≤ (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2 :=
    fun z => by positivity
  have hHasFin : HasFiniteIntegral
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) (volume.restrict (Set.Ioi 0)) :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)).mpr hGfin
  have hAESM : AEStronglyMeasurable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi).mul (hmeas.pow 2)
  refine ⟨⟨hAESM, hHasFin⟩, ?_⟩
  exact Blocks.integral_le_of_lintegral_le hC
    (fun z => by positivity) (fun z => by positivity) hfw hlin

/-! ## Continuity of the Hardy operator applied to the angular moment -/

/-- **The Hardy operator applied to `U_j = F_*(D_z^j F)` is continuous on `(0,∞)`.**

The primitive `z ↦ ∫_0^z s^{β-1}U_j s ds` is continuous by
`Cert.GbarSin.continuousOn_primitive_Ioi`, whose hypothesis is the interval integrability of
`s ↦ s^{β-1}U_j s` on `[0,z]` for `z > 0` (`Cert.GbarSin.intervalIntegrable_rpow_Uj`, itself a
consequence of the Cauchy–Schwarz bound `|U_j| ≤ √(π/2)√(A_j)/w`); multiplying by the
continuous factor `z^{-β}` gives the claim.  No regularity of `U_j` is used beyond this. -/
theorem continuousOn_HarOp_Uj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun z => HarOp (bet α) (Uj F j) z) (Set.Ioi 0) := by
  have hprim : ContinuousOn
      (fun z => ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s) (Set.Ioi 0) :=
    continuousOn_primitive_Ioi fun z hz =>
      intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hj hz
  have hzpow : ContinuousOn (fun z : ℝ => z ^ (-(bet α))) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
  have hfun : (fun z => HarOp (bet α) (Uj F j) z)
      = fun z => z ^ (-(bet α)) * ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s := by
    funext z; rfl
  rw [hfun]
  exact hzpow.mul hprim

/-! ## The main theorem -/

/-- **The weighted `L²` integrability of the radial iterates of `Ḡ(α,F)`.**
For a source `F` which is `C^∞` on the open quadrant and lies in `ℋ^k`, and for `j ≤ k`,
`z ↦ w(z)² (D_z^j Ḡ(α,F)(z))²` is integrable on `[0,∞)` (`0 < α ≤ 1`).

This is the *integrability half* of `Cert.GbarSin.Gbar_rDzIter_bound`; the existing proof is
tainted by the missing weighted Hardy inequality `Cert.GbarSin.HarOp_weighted_integral_le`,
whose **lintegral** form `Work.FTS.EllipticEst.HarOp_weighted_lintegral` IS proved
(it needs only `IntegrableOn (fun z => f z ^ 2) (Ioi 0)`).  Route (copying `OpenCore`):
* the exact radial identity `Cert.GbarSin.rDzIter_Gbar_eq_open` (proved) gives
  `D_z^j Ḡ = -(3/(4α))·HarOp β (U_j)` on `(0,∞)`, with `U_j = F_*(D_z^j F)`;
* `Cert.GbarSin.Uj_sq_mul_w_integrable` (proved) gives `∫ w²U_j² < ∞` and `∫ U_j² < ∞`;
* the weighted Hardy inequality bounds `∫ w²(HarOp β U_j)² ≤ (100/β²)∫ w²U_j² < ∞`.
Proving the real-valued Hardy inequality
`∫_0^∞ w²(HarOp β f)² ≤ (100/β²)∫_0^∞ w²f²` (for `β ≥ 5`, `f²` and `w²f²` integrable) as a
helper in your own file from `HarOp_weighted_lintegral` is expected; do NOT use
`Cert.GbarSin.HarOp_weighted_integral_le` or `Gbar_rDzIter_bound` themselves (they are tainted
by `sorryAx`; check with `#print axioms`). -/
theorem GbarRdzIterIntegrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (Work.FTS.EllipticEst.rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) Work.Spaces.Iz := by
  -- work on `(0,∞)` rather than `[0,∞)`
  rw [MeasureTheory.IntegrableOn, ← restrict_Ioi_eq_restrict_Iz]
  have hβ5 : 5 ≤ bet α := by rw [bet, le_div_iff₀ hα]; linarith
  -- the two integrability facts for the angular moment `U_j`
  have hUw : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2) (Set.Ioi 0) :=
    (Uj_sq_mul_w_integrable α k F hF hmem j hj).1
  have hU2 : IntegrableOn (fun z => (Uj F j z) ^ 2) (Set.Ioi 0) := by
    refine hUw.mono' ((Uj_aesm α k F hF j).pow 2) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hw1 : 1 ≤ Work.Spaces.w z := one_le_w hz
    have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    nlinarith [hw2, sq_nonneg (Uj F j z)]
  -- the Hardy operator applied to `U_j` is continuous, hence a.e. strongly measurable
  have hmeasH : AEStronglyMeasurable (HarOp (bet α) (Uj F j))
      (volume.restrict (Set.Ioi 0)) :=
    (continuousOn_HarOp_Uj α hα hα1 k F hF hmem j hj).aestronglyMeasurable measurableSet_Ioi
  obtain ⟨hIntH, -⟩ :=
    harOp_weighted_integral_le_ae (bet α) hβ5 (Uj F j) hU2 hUw hmeasH
  -- transport along the exact radial identity `D_z^j Ḡ = -(3/(4α))·HarOp β U_j`
  have hid := rDzIter_Gbar_eq_open α hα hα1 k F hF hmem j hj
  refine (hIntH.const_mul ((-(3 / (4 * α))) ^ 2)).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun z hz => ?_
  rw [hid hz]
  ring

end Work.FTS.EllipticEst.Cert
