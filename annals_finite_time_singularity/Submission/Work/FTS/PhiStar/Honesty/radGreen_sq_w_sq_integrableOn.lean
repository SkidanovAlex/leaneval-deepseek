/-
# `Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_integrableOn`

Weighted `L²`-honesty of the mode-`m` radial Green function on `(0,∞)`:

  `∫_0^∞ (radGreen α m c z)² · w(z)² dz < ∞`,   `w(z) = (1+z)²/z²`,

from a *near* `L²`-condition on the source `c` (`∫_0^1 c²/z⁴ < ∞`) and a *far* `L²`-condition
(`∫_1^∞ c² < ∞`).  No pointwise decay of `c` is assumed: the two-sided Green's function of the
radial Euler operator regularises any `c` whose weighted square is integrable.

**Proof structure.**

* `radGreen = K·(G1 + G2)`, `K = 1/(α(4m+5))`, with
  `G1 z = z^{-A}∫_0^z c t^{A-1}` (`A = (2m+5)/α`, singular at `0`) and
  `G2 z = z^{p}∫_z^∞ c t^{-p-1}` (`p = 2m/α`, controlled by the behaviour at `∞`); so
  `(G1+G2)² ≤ 2G1² + 2G2²`, and it suffices to treat the two Green terms separately.

* **Near `0`** (`(0,1)`, weight `w² = (1+z)⁴/z⁴ ≤ 16 z^{-4}`): `∫_0^1 radGreen²/z⁴ < ∞` is
  `Work.FTS.EllExist.Honesty.radGreen_l2_near_zero`, whose extra hypothesis
  `∫_1^∞ |c| t^{-p-1} < ∞` follows from `∫_1^∞ c² < ∞` by AM–GM
  (`integrableOn_abs_mul_rpow_of_sq`).

* **Far `∞`** (`(1,∞)`, weight `w² ≤ 16`): `∫_1^∞ G_i² w² < ∞` for `i = 1,2` — the two
  `farG1_sq_w_integrable` / `farG2_sq_w_integrable` halves, in which the *sharp* decay of the two
  Green terms (their square is only `≈ z^{-1}` pointwise, so no pointwise domination by the `L²`
  hypotheses is possible) comes from the energy identities `zG1' = -A G1 + c`, `zG2' = p G2 - c`
  together with the fundamental theorem of calculus.

* The two halves are glued with `IntegrableOn.union` (`(0,1) ∪ (1,∞) = (0,∞)` up to the null set
  `{1}`), which also absorbs the behaviour at `z = 0` and on the boundary `z = 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.Honesty.radGreen_l2_near_zero
import Submission.Work.FTS.EllExist.Honesty.FarAux.Basic
import Submission.Work.FTS.PhiStar.Honesty.IoiTool
import Submission.Work.FTS.PhiStar.Honesty.RadGreenFarField
import Submission.Work.FTS.PhiStar.Honesty.RadGreenFarG1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Topology

/-- **`c² ∈ L¹(1,∞)` ⟹ `|c| t^{-2m/α-1} ∈ L¹(1,∞)`.**

This is the hypothesis `hinf` of `Work.FTS.EllExist.Honesty.radGreen_l2_near_zero` (and of the
`radGreen` differentiability lemmas), derived here from the far-field `L²`-hypothesis by AM–GM. -/
private theorem hinf_of_hfar {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hα : 0 < α) (hm : 1 ≤ m)
    (hc : ContinuousOn c (Set.Ioi 0))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1) := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : (-1 / 2 : ℝ) < 2 * (m : ℝ) / α := by
    have h2 : (0 : ℝ) < 2 * (m : ℝ) / α := div_pos (by linarith) hα
    linarith
  exact integrableOn_abs_mul_rpow_of_sq hp
    (hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))) hfar

/-- **The near half**: `∫_0^1 radGreen² w² < ∞`.

On `(0,1)` we have `w z² = (1+z)⁴/z⁴ ≤ 16/z⁴`, so it suffices to know
`∫_0^1 radGreen²/z⁴ < ∞` — the near-zero honesty
`Work.FTS.EllExist.Honesty.radGreen_l2_near_zero` — whose far-field side condition follows from
`hfar` (`hinf_of_hfar`). -/
private theorem radGreen_sq_w_sq_integrableOn_Ioo {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1) := by
  have hinf := hinf_of_hfar hα hm hc hfar
  have hz4 := Work.FTS.EllExist.Honesty.radGreen_l2_near_zero α hα hα4 m hm hc hnear hinf
  have hw : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    intro z
    rw [Work.Spaces.w, div_pow]
    rw [show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring, show (z ^ 2) ^ 2 = z ^ 4 by ring]
  have hbdd : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      ‖(fun z : ℝ => (1 + z) ^ 4) z‖ ≤ 16 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine ae_of_all _ fun z hz => ?_
    have h1 : (0 : ℝ) ≤ 1 + z := by linarith [hz.1]
    have h2 : 1 + z ≤ 2 := by linarith [hz.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h1 h2 4
      _ = 16 := by norm_num
  have hmeas : AEStronglyMeasurable (fun z : ℝ => (1 + z) ^ 4)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ((continuous_const.add continuous_id).pow 4).continuousOn.aestronglyMeasurable
      measurableSet_Ioo
  have h := Integrable.bdd_mul hz4 hmeas hbdd
  refine IntegrableOn.congr_fun h ?_ measurableSet_Ioo
  intro z _
  show (1 + z) ^ 4 * (Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 / z ^ 4)
      = Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 * (Work.Spaces.w z) ^ 2
  rw [hw z]
  ring

/-- **The assembly**: if the two far-field halves `∫_1^∞ G_i² w² < ∞` are known, then
`∫_0^∞ radGreen² w² < ∞`.

The far-field integrand is split with `(G1+G2)² ≤ 2G1² + 2G2²` and `radGreen = K(G1+G2)`; the
continuity of `G1` and `G2` on `(1,∞)` (measurability of the target integrand) comes from the
differentiability lemmas `G1_hasDerivAt_of_intervalIntegrable` / `G2_hasDerivAt` of
`Work.FTS.EllExist.Honesty`, and the two halves are glued by `IntegrableOn.union`. -/
private theorem radGreen_sq_w_sq_integrableOn_of_far {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    (hG1 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1))
    (hG2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
  have hnear' := radGreen_sq_w_sq_integrableOn_Ioo hα hα4 hm hc hnear hfar
  -- measurability of the far-field integrand: `radGreen` is a constant times `G1 + G2`
  have haesmG1 : AEStronglyMeasurable (fun z : ℝ => Work.FTS.EllExist.Honesty.G1 α m c z)
      (volume.restrict (Set.Ioi 1)) :=
    Work.FTS.EllExist.Honesty.G1_far_measurable α hα m hc
  have hinf := hinf_of_hfar hα hm hc hfar
  have hG2deriv := Work.FTS.EllExist.Honesty.G2_hasDerivAt hα hα4 m hm hc hinf
  have haesmG2 : AEStronglyMeasurable (fun z : ℝ => Work.FTS.EllExist.Honesty.G2 α m c z)
      (volume.restrict (Set.Ioi 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro z hz
    exact ((hG2deriv z hz).continuousAt).continuousWithinAt
  have haesmSum : AEStronglyMeasurable
      (fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5))
        * (Work.FTS.EllExist.Honesty.G1 α m c z + Work.FTS.EllExist.Honesty.G2 α m c z))
      (volume.restrict (Set.Ioi 1)) :=
    (haesmG1.add haesmG2).const_mul _
  have hfun : (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      = fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5))
        * (Work.FTS.EllExist.Honesty.G1 α m c z + Work.FTS.EllExist.Honesty.G2 α m c z) := by
    funext z
    exact Work.FTS.EllExist.Honesty.radGreen_eq_G1_add_G2 α m c z
  have haesmRad : AEStronglyMeasurable (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      (volume.restrict (Set.Ioi 1)) := by
    rw [hfun]
    exact haesmSum
  have haesmW : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (ContinuousOn.div ?_ ?_ ?_).pow 2
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · exact (continuous_id.pow 2).continuousOn
    · intro z hz
      exact pow_ne_zero 2 (ne_of_gt (lt_trans one_pos (Set.mem_Ioi.mp hz)))
  have haesm : AEStronglyMeasurable
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 1)) := (haesmRad.pow 2).mul haesmW
  -- the dominating integrable function on `(1,∞)`
  have hsum : Integrable
      (fun z : ℝ => 2 * (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
        * ((Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2
          + (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2))
      (volume.restrict (Set.Ioi 1)) :=
    (hG1.add hG2).const_mul _
  have hfarint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) := by
    refine Integrable.mono' hsum haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hK2 : 0 ≤ (1 / (α * (4 * (m : ℝ) + 5))) ^ 2 := sq_nonneg _
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hsq : (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
        = (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
          * (Work.FTS.EllExist.Honesty.G1 α m c z
              + Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 := by
      rw [Work.FTS.EllExist.Honesty.radGreen_eq_G1_add_G2 α m c z]
      ring
    have hab : (Work.FTS.EllExist.Honesty.G1 α m c z
        + Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2
        ≤ 2 * (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2
          + 2 * (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 := by
      nlinarith [sq_nonneg (Work.FTS.EllExist.Honesty.G1 α m c z
        - Work.FTS.EllExist.Honesty.G2 α m c z)]
    have hfnn : 0 ≤ (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) hw2
    rw [Real.norm_of_nonneg hfnn]
    calc (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
            * ((Work.FTS.EllExist.Honesty.G1 α m c z
                + Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          rw [hsq]; ring
      _ ≤ (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
            * ((2 * (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2
                + 2 * (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2)
              * (Work.Spaces.w z) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab hw2) hK2
      _ = 2 * (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
            * ((Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2
              + (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          ring
  -- glue `(0,1)` and `(1,∞)`
  have hA : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    hnear'.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hB : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ici (1 : ℝ)) :=
    hfarint.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
  have hU := hA.union hB
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1, _⟩ | h3) <;> linarith
    · intro h
      rcases le_or_gt x 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'.le
  rw [hset] at hU
  exact hU.mono_set Set.Ioi_subset_Ici_self

theorem radGreen_sq_w_sq_integrableOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) :=
  radGreen_sq_w_sq_integrableOn_of_far hα hα4 hm hc hnear hfar
    (G1_sq_w_sq_integrableOn_far hα hα4 hm hc hnear hfar)
    (G2_sq_w_sq_integrableOn_far hα hα4 hm hc hfar)

end Work.FTS.PhiStar.Honesty
