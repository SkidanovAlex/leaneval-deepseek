import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular slices of `F` and `∂_zF` are `L¹`

For a source `F` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` and honest in the
weighted space `ℋ^1` (`Work.Spaces.HkMem α 1 F`), the two angular slices at any radius
`t > 0`,

  `θ ↦ |F t θ|`  and  `θ ↦ |∂_zF t θ|`,

are integrable on `Iθ = [0, π/2]`.

The route is the `i = 0` resp. `i = 1` summand of `HkIntegrand α 1 F`: on the open
quadrant the weight factor `w z / sin(2θ)^{η/2}` is `≥ 1`, so the weighted squares dominate
the plain squares,

  `(F t θ)² ≤ HkIntegrand α 1 F t θ`,   `(∂_zF t θ)² ≤ (1/t²)·HkIntegrand α 1 F t θ`,

and `HkMem α 1 F` makes the right hand sides integrable on the slice.  On the finite
measure space `Iθ` an `L²` function is `L¹`, via the pointwise bound `|x| ≤ x² + 1`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Elementary weight facts on the open quadrant -/

/-- `Iθ = [0,π/2]` is measurable. -/
private lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- On the open quadrant the weight factor `w z / sin(2θ)^{η/2}` is `≥ 1`: `w z ≥ 1` for
`z > 0` and `sin(2θ)^{η/2} ≤ 1`. -/
private lemma one_le_wdiv {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hw : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinpos _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsinpos) (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
  rw [one_le_div hspos]
  exact le_trans hsle hw

/-- Multiplying by a factor `A ≥ 1` does not decrease a square. -/
private lemma sq_le_sq_mul_of_one_le {x A : ℝ} (hA : 1 ≤ A) : x ^ 2 ≤ (x * A) ^ 2 := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have habs : |x| ≤ |x * A| := by
    rw [abs_mul, abs_of_nonneg hA0]
    exact le_mul_of_one_le_right (abs_nonneg _) hA
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) habs 2

/-- The plain square of a function is dominated by its weighted square on the open
quadrant. -/
private lemma sq_le_wdiv_sq {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (g z θ) ^ 2
      ≤ (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
  sq_le_sq_mul_of_one_le (one_le_wdiv hz hθ)

/-- On the finite measure space `Iθ` an `L²` function is `L¹`. -/
private lemma integrableOn_abs_of_sq {u : ℝ → ℝ}
    (hsq : IntegrableOn (fun θ : ℝ => (u θ) ^ 2) Work.Spaces.Iθ)
    (haesm : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ)) :
    IntegrableOn (fun θ : ℝ => |u θ|) Work.Spaces.Iθ := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hdom : IntegrableOn (fun θ : ℝ => (u θ) ^ 2 + 1) Work.Spaces.Iθ := hsq.add hconst
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => |u θ|) (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using haesm.norm
  refine MeasureTheory.Integrable.mono' hdom hmeas ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ (fun θ _ => ?_)
  rw [Real.norm_of_nonneg (abs_nonneg (u θ))]
  nlinarith [sq_abs (u θ), sq_nonneg (|u θ| - 1)]

/-- The `i = 1` summand of `HkIntegrand α 1 F` dominates `(∂_zF t θ)²` up to the constant
`1/t²`. -/
private lemma sq_pz_le_HkIntegrand {α t : ℝ} {F : ℝ → ℝ → ℝ} (ht : 0 < t) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.pz F t θ) ^ 2
      ≤ (1 / t ^ 2) * Work.Spaces.HkIntegrand α 1 F t θ := by
  have hDz : Work.Spaces.DzIter 1 F t θ = t * Work.Spaces.pz F t θ := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  have hstep : (Work.Spaces.DzIter 1 F t θ
      * (Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 F t θ :=
    Work.Spaces.sq_le_HkIntegrand_z α 1 F t θ 1 (by norm_num)
  have hmono : (t * Work.Spaces.pz F t θ) ^ 2
      ≤ (Work.Spaces.DzIter 1 F t θ
          * (Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hDz]
    exact sq_le_sq_mul_of_one_le (one_le_wdiv ht hθ)
  have hkey : t ^ 2 * (Work.Spaces.pz F t θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ := by
    have h1 : t ^ 2 * (Work.Spaces.pz F t θ) ^ 2 = (t * Work.Spaces.pz F t θ) ^ 2 := by ring
    rw [h1]
    exact le_trans hmono hstep
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have h3 : (1 / t ^ 2) * Work.Spaces.HkIntegrand α 1 F t θ
      = Work.Spaces.HkIntegrand α 1 F t θ / t ^ 2 := by ring
  rw [h3]
  exact (le_div_iff₀ ht2).mpr (by rw [mul_comm]; exact hkey)

/-! ## The main lemma -/

theorem slice_abs_integrable {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {t : ℝ} (ht : 0 < t) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |F t θ|) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.Spaces.pz F t θ|) Work.Spaces.Iθ := by
  have htIz : t ∈ Work.Spaces.Iz := Set.mem_Ici.mpr ht.le
  have hHk : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ) Work.Spaces.Iθ :=
    hF.1 t htIz
  -- `Iθ` and the open interval `(0,π/2)` differ by a null set
  have hmeq : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  -- a.e. strong measurability of the two slices, from smoothness on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.continuousOn
  have haesmF : AEStronglyMeasurable (fun θ : ℝ => F t θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => F p.1 p.2) hcont ht
  have haesmP : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pz F t θ)
      (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using
      hsm.aesm_slice_pzIter 1 ht
  -- the square of the `F`-slice is integrable, dominated by the `ℋ^1`-integrand
  have hsqF : IntegrableOn (fun θ : ℝ => (F t θ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hHk (haesmF.pow 2) ?_
    rw [hmeq]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_trans (sq_le_wdiv_sq ht hθ)
      (Work.Spaces.sq_le_HkIntegrand_z α 1 F t θ 0 (by norm_num))
  -- the square of the `∂_zF`-slice is integrable
  have hsqP : IntegrableOn (fun θ : ℝ => (Work.Spaces.pz F t θ) ^ 2) Work.Spaces.Iθ := by
    have hdom : IntegrableOn (fun θ : ℝ => (1 / t ^ 2) * Work.Spaces.HkIntegrand α 1 F t θ)
        Work.Spaces.Iθ := hHk.const_mul _
    refine MeasureTheory.Integrable.mono' hdom (haesmP.pow 2) ?_
    rw [hmeq]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_pz_le_HkIntegrand ht hθ
  exact ⟨integrableOn_abs_of_sq hsqF haesmF, integrableOn_abs_of_sq hsqP haesmP⟩

end Work.FTS.PhiStar.Honesty
