import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.ProductTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# From `H^0`-membership (weighted) to plain `L²`-membership

The `H^0`-weighted integrand of `g` is

`HkIntegrand α 0 g z θ = (g z θ · w(z) / sin(2θ)^{η/2})²`

and on the *interior* of the quadrant (`z > 0`, `0 < θ < π/2`) the weight
`w(z)/sin(2θ)^{η/2}` is `≥ 1` (both `w z ≥ 1` and `sin(2θ)^{η/2} ≤ 1` there), so the
weighted integrand dominates `g²` pointwise a.e.  Together with the vanishing hypothesis
`g 0 θ = 0` at the degenerate line `z = 0` (where `w = 0` by Lean's totalised division and
the weighted integrand carries no information) this gives the honesty of `∫_θ g²` for
every `z ≥ 0`, and — with the a.e. measurability hypotheses ensuring that the sliced
integrals are measurable — also the honesty of `∫_z ∫_θ g²`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- At angular order `0` the `H^0`-integrand of `g` is exactly the square of the weighted
function `g · w / sin(2θ)^{η/2}`. -/
lemma HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.DzIter]

/-- The radial weight is at least `1` on the open half-line: `w(z) = ((1+z)/z)² ≥ 1`. -/
lemma one_le_w (z : ℝ) (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have h : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by
    rw [Work.Spaces.w, div_pow]
  rw [h]
  have h1 : 1 ≤ (1 + z) / z := by
    rw [le_div_iff₀ hz]
    linarith
  exact one_le_pow₀ h1

/-- `sin(2θ)^{η/2} ≤ 1` on the open angular interval. -/
lemma sin_two_rpow_le_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  exact Real.rpow_le_one hs0 hs1 (by norm_num [Work.Spaces.eta])

/-- The `H^0`-weight `w(z)/sin(2θ)^{η/2}` is at least `1` in the interior of the quadrant. -/
lemma one_le_weight {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs0 : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hpos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  refine (one_le_div hpos).mpr ?_
  exact le_trans (sin_two_rpow_le_one h0 h1) (one_le_w z hz)

/-- Pointwise domination of `g²` by the `H^0`-integrand in the interior of the quadrant. -/
lemma sq_le_HkIntegrand_zero_pt {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 g z θ := by
  rw [HkIntegrand_zero_eq]
  have hle : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    one_le_weight hz h0 h1
  have hsq : (1 : ℝ) ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
    one_le_pow₀ hle
  calc (g z θ) ^ 2 = (g z θ) ^ 2 * 1 := by ring
    _ ≤ (g z θ) ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        ring

/-- The pointwise domination holds a.e. on `Iθ` for every `z ∈ Iz`: on the interior this is
`sq_le_HkIntegrand_zero_pt`, on the null set `{0, π/2}` the angular coordinate is discarded,
and at `z = 0` it is the vanishing hypothesis `h0`. -/
lemma ae_sq_le_HkIntegrand_zero {α : ℝ} {g : ℝ → ℝ → ℝ} (h0 : ∀ θ, g 0 θ = 0) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 g z θ := by
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with h | h
  · subst h
    filter_upwards with θ
    have hz0 : g 0 θ = 0 := h0 θ
    simp only [HkIntegrand_zero_eq, hz0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact sq_nonneg _
  · have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      have heq : MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))
          = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
        rw [Work.Spaces.Iθ]
        exact MeasureTheory.restrict_Ioo_eq_restrict_Icc
      rw [← heq]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)
    filter_upwards [hae] with θ hθ
    exact sq_le_HkIntegrand_zero_pt h hθ.1 hθ.2

theorem L2Mem_of_HkMem_zero {α : ℝ} {g : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 0 g)
    (h0 : ∀ θ, g 0 θ = 0)
    (hjoint : AEMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hslice : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => g z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    Work.Spaces.L2Mem g := by
  obtain ⟨hsl, hout⟩ := h
  constructor
  · -- angular slices: dominated by the integrable weighted integrand on a.e. all of `Iθ`
    intro z hz
    have hmeas : AEStronglyMeasurable (fun θ : ℝ => (g z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hslice z hz).pow_const 2).aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' (hsl z hz) hmeas ?_
    filter_upwards [ae_sq_le_HkIntegrand_zero (α := α) h0 hz] with θ hθ
    simpa only [Real.norm_of_nonneg (sq_nonneg (g z θ))] using hθ
  · -- the outer integral
    have hmeas : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        (hjoint.pow_const 2).aestronglyMeasurable
      exact h2.integral_prod_right'
    refine MeasureTheory.Integrable.mono' hout hmeas ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) ?_
    intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg (g z θ))]
    exact MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg (g z θ))
      (hsl z hz)
      (ae_sq_le_HkIntegrand_zero (α := α) h0 hz)

end Work.FTS_EllLimOK
