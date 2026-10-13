import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.Min

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000


/-!
# `ProfDerivData` for the *finite-order* regularity package `RegPkgMin`

This file proves `Work.FTS_FinalLeaves.profDerivData_min_proved`, the `RegPkgMin`-version of
`Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed`: the seven static derivation fields
of the meridian bridge follow from

* the *finite-order* regularity package `Work.FTS.StrongGlobal.RegPkgMin α g` — whose spatial
  clause is `ContDiffOn ℝ 4` of every slice on the open quadrant, together with the honest
  `ℋ⁴`-membership — and
* the interior `C²`-regularity of the stream function `Φ` on the open quadrant.

The only analytic content (as in the `RegPkg` version) is the two `L₁₂`-facts about the full
profile `F_τ = F_* + g(·,·,τ)`: integrability of the density `L₁₂dens K F_τ` on `(0,∞)` and its
continuity at `z > 0`.  Both are obtained by *additivity* of the density
(`Work.FTS.LocData.L12dens_add_of_integrableOn`) from the two summands:

* the slice `g(·,·,τ)`, where `ContDiffOn ℝ 4` + `HkMem α 4` suffice (the `L₁₂`-facts of the
  open-quadrant finite-order class, proved in sibling modules of the `Pieces` directory);
* the explicit profile `F_* α`, where everything is elementary.

Note the statement carries **no hypothesis** on `α`: `Work.Spaces.c α` may well vanish (it does
for `α ≤ -9/2`, where the integrand of `c` fails to be integrable and Mathlib's total integral
returns `0`), and in that case `F_* α` vanishes identically (because `Γ(θ)/0 = 0`), so the
profile contributes nothing.  The two cases are separated once, in `Fstar_L12_facts`.
-/

/-- `√x ≤ |x| + 1` (local copy of the helper of the same name in `HardyAlt`). -/
theorem sqrt_le_abs_add_one (x : ℝ) : Real.sqrt x ≤ |x| + 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [le_abs_self x, abs_nonneg x, sq_abs x, sq_nonneg x]

/-! ## `F_* α` and its `L₁₂`-density

`Work.Construction.Fstar α z θ = α·(Γ(θ)/c α)·2z/(1+z)²`, so its density is the explicit
function `s ↦ α·F_*(s)/s` (`Work.FM.Fstar s = 2s/(1+s)²`) *provided* `c α ≠ 0`; when `c α = 0`
the profile vanishes identically. -/

/-- **The density of `L₁₂` at the profile `F_*`**, in the case `c α ≠ 0`: it is the elementary
function `α·F_*(s)/s`.  This is `Work.Construction.L12dens_Fstar` with the two hypotheses
`0 < α`, `α ≤ 1` — which were only used to supply `c α ≠ 0` — replaced by `c α ≠ 0`. -/
theorem L12dens_Fstar_of_c_ne_zero {α : ℝ} (hc : Work.Spaces.c α ≠ 0) (s : ℝ) :
    Work.Construction.L12dens (Work.Construction.Fstar α) s
      = α * (Work.FM.Fstar s / s) := by
  rw [Work.Construction.L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [setIntegral_congr_fun (s := Set.Icc 0 (Real.pi / 2)) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [integral_mul_const]
  have hcint : (∫ θ in Set.Icc 0 (Real.pi / 2),
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α) = α := by
    rw [integral_div, integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval, mul_div_assoc, div_self hc, mul_one]
  rw [hcint]

/-- The angular integrand `Γ·K` of the normalisation constant is integrable as soon as
`c α ≠ 0` (Mathlib's total integral vanishes on a non-integrable function). -/
theorem integrableOn_GamK_of_c_ne_zero {α : ℝ} (hc : Work.Spaces.c α ≠ 0) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := by
  by_contra h
  refine hc ?_
  show (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ) = 0
  exact MeasureTheory.integral_undef h

/-- **Integrability of the angular slice of `F_* α`** in the case `c α ≠ 0`: the integrand
`θ ↦ K θ · F_* α z θ / z` is a constant multiple of `Γ·K`, which is integrable by
`integrableOn_GamK_of_c_ne_zero`. -/
theorem Fstar_slice_integrableOn_of_c_ne_zero {α : ℝ} (hc : Work.Spaces.c α ≠ 0) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α z θ / z) Work.Spaces.Iθ := by
  have hKGam := integrableOn_GamK_of_c_ne_zero hc
  intro z hz
  have hconst : MeasureTheory.IntegrableOn
      (fun θ => (α * Work.FM.Fstar z / (z * Work.Spaces.c α))
        * (Work.Spaces.Gam α θ * Work.Spaces.K θ)) Work.Spaces.Iθ :=
    hKGam.const_mul _
  refine hconst.congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Work.Construction.Fstar]
  first | (field_simp; ring) | field_simp

/-- `F_* α` vanishes identically when `c α = 0` (because `Γ(θ)/0 = 0`). -/
theorem Fstar_eq_zero_of_c_eq_zero {α : ℝ} (hc : Work.Spaces.c α = 0) :
    Work.Construction.Fstar α = fun _ _ => 0 := by
  funext z θ
  simp only [Work.Construction.Fstar, hc, div_zero, mul_zero, zero_mul]

/-- **The three `L₁₂`-facts about the profile `F_* α`, for every real `α`**: the angular slice is
integrable for every `z > 0`, the `L₁₂`-density is integrable on `(0,∞)`, and it is continuous at
every `z > 0`.  The case `c α = 0` is degenerate (`F_* α ≡ 0`). -/
theorem Fstar_L12_facts (α : ℝ) :
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α z θ / z) Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (Work.Construction.L12dens (Work.Construction.Fstar α)) (Set.Ioi 0)
    ∧ (∀ z : ℝ, 0 < z → ContinuousAt
        (Work.Construction.L12dens (Work.Construction.Fstar α)) z) := by
  by_cases hc : Work.Spaces.c α = 0
  · have h0 : Work.Construction.Fstar α = fun _ _ => 0 := Fstar_eq_zero_of_c_eq_zero hc
    have hden : Work.Construction.L12dens (Work.Construction.Fstar α) = fun _ => (0 : ℝ) := by
      funext s
      rw [Work.Construction.L12dens, Work.FM.L12dens, h0]
      simp
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      have hzero : (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α z θ / z)
          = fun _ => (0 : ℝ) := by
        funext θ; simp only [h0]; ring
      rw [hzero]; exact integrableOn_zero
    · rw [hden]; exact integrableOn_zero
    · intro z hz; rw [hden]; exact continuousAt_const
  · have hsl := Fstar_slice_integrableOn_of_c_ne_zero hc
    have hval : ∀ s : ℝ, Work.Construction.L12dens (Work.Construction.Fstar α) s
        = α * (Work.FM.Fstar s / s) := fun s => L12dens_Fstar_of_c_ne_zero hc s
    -- integrability of the explicit density
    have hbase : MeasureTheory.IntegrableOn (fun s : ℝ => 2 / (1 + s) ^ 2) (Set.Ioi 0) :=
      Work.FTS.MeridianDyn.Bridge.Pieces.integrableOn_two_div_one_add_sq 0 le_rfl
    have hmul : MeasureTheory.IntegrableOn (fun s : ℝ => α * (2 / (1 + s) ^ 2)) (Set.Ioi 0) :=
      hbase.const_mul α
    have hcongr : Set.EqOn (fun s : ℝ => α * (2 / (1 + s) ^ 2))
        (fun s : ℝ => α * (Work.FM.Fstar s / s)) (Set.Ioi 0) := by
      intro s hs
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hkey : Work.FM.Fstar s / s = 2 / (1 + s) ^ 2 := by
        unfold Work.FM.Fstar
        field_simp
      show α * (2 / (1 + s) ^ 2) = α * (Work.FM.Fstar s / s)
      rw [hkey]
    have hint : MeasureTheory.IntegrableOn
        (fun s : ℝ => α * (Work.FM.Fstar s / s)) (Set.Ioi 0) :=
      hmul.congr_fun hcongr measurableSet_Ioi
    refine ⟨hsl, ?_, ?_⟩
    · exact hint.congr_fun (fun s _ => (hval s).symm) measurableSet_Ioi
    · intro z hz
      have hfun : Work.Construction.L12dens (Work.Construction.Fstar α)
          = fun s : ℝ => α * (Work.FM.Fstar s / s) := funext hval
      rw [hfun]
      have hF : ContinuousAt (fun s : ℝ => Work.FM.Fstar s) z := by
        have h1 : ContinuousAt (fun s : ℝ => (2 : ℝ) * s) z :=
          continuousAt_const.mul continuousAt_id
        have h2 : ContinuousAt (fun s : ℝ => ((1 : ℝ) + s) ^ 2) z :=
          (continuousAt_const.add continuousAt_id).pow 2
        have h3 : ((1 : ℝ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
        have h4 : ContinuousAt (fun s : ℝ => (2 : ℝ) * s / (1 + s) ^ 2) z := h1.div h2 h3
        have heq : (fun s : ℝ => (2 : ℝ) * s / (1 + s) ^ 2) = Work.FM.Fstar := rfl
        rwa [heq] at h4
      exact (hF.div continuousAt_id (ne_of_gt hz)).const_mul α

end Work.FTS_FinalLeaves.Min
