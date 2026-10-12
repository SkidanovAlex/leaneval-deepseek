import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.firstMoment_alias
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kinFirst_le_of_heatSpec_closed`

The row `2·R₁ ≤ 3·S₁` for states `g` supported in the **closed** ball `closedBall 0 (ℓ/2)` —
the class of the admissible states `g = χ_Λ·h` (the corpus's `χ_Λ` vanishes outside the closed
ball) — derived from the pointwise heat row

`hspec :  0 ≤ hsN ℓ g + 2·contHeat g t − 3·latHeat ℓ t g`   for all `t > 0`.

**A note on the argument order of `latHeat`.**  The statement of this lemma as it reached this
file had `latHeat ℓ g t` in the places where the (correctly ordered) reviewed statement
(`.fm3_reviews.json`, key `BoseBoxFock/kinFirst_le_of_heatSpec_closed`) has `latHeat ℓ t g`.
Since `latHeat : ℝ → ℝ → (ℝ³ → ℂ) → ℝ` (its arguments are `ℓ`, `t`, `g`), the string
`latHeat ℓ g t` is *ill-typed*: it demands `g : ℝ`.  The well-typed reading — which is the one
reviewed, the one of the open-ball sibling `Work.BoseBoxFock.kinFirst_le_of_heatSpec`, and the one
whose integrand is literally the one of `three_latMoment_sub_two_kinFirst` — is used here verbatim.

The corpus's chain (`firstMoment_alias.lean`, `firstMoment_heatForm.lean`) proves the same
implication for the *open* ball `ball 0 (ℓ/2)`; the only reason it is stated with the open ball is
that the three identities it rests on were stated that way:

* `frame_lattice_ball` (the frame identity `hsN = (2π)⁻³∫‖kinFT g‖²`),
* `lattice_heatSubordination`, `continuum_heatSubordination_v2` (the two heat subordinations).

All three are used only through the facts `HasCompactSupport g` and `tsupport g ⊆ boxL ℓ`, and
the **closed** ball is contained in the box `boxL ℓ = ℓ•[−1/2,1/2]³` as well (the translates now
meet on the faces of the cube, which are null).  This file therefore reproves the two heat
subordinations under the (weaker) hypothesis `HasCompactSupport g`, the identity
`3·latMoment − 2·kinFirst = (2√π)⁻¹∫t^{-3/2}(hsN + 2·contHeat − 3·latHeat)` under the closed-ball
support hypothesis, and finally the requested row.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real BigOperators Pointwise

namespace Work.BoseBoxFock

set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The closed ball is contained in the box `boxL ℓ` -/

/-- **The closed ball `closedBall 0 (ℓ/2)` sits in the box `Λ(ℓ) = boxL ℓ = ℓ•[−1/2,1/2]³`**:
a coordinate of a point of the closed ball is bounded by its norm, and the closed ball is the
closure of the open one (`ball_subset_corpusBox_boxL` with `≤` in place of `<`). -/
lemma closedBall_subset_corpusBox_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Metric.closedBall (0 : E3) (ℓ/2) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
  show x ∈ (ℓ : ℝ) • (Work.BoseB4.unitCell : Set E3)
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
  intro i
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : ‖x.ofLp i‖ ≤ ‖x‖ := by
    rw [EuclideanSpace.norm_eq]
    exact Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖x.ofLp j‖) (Finset.mem_univ i))
  have h2 : |x.ofLp i| ≤ ‖x‖ := by rwa [Real.norm_eq_abs] at h1
  rw [abs_mul, abs_inv, abs_of_pos hℓ]
  calc ℓ⁻¹ * |x.ofLp i| ≤ ℓ⁻¹ * ‖x‖ :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hℓ))
    _ ≤ ℓ⁻¹ * (ℓ/2) := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hℓ))
    _ = 1/2 := by field_simp

/-! ## 2. The two heat subordinations under the hypothesis `HasCompactSupport g`

These are the corpus's `lattice_heatSubordination` and `continuum_heatSubordination_v2` with the
ball-support hypothesis relaxed to `HasCompactSupport g`; only the latter is used by their proofs
(`summable_lattice_kinFT_weight` / `SqrtKin.subordination_t_p_swap`). -/

/-- **Lattice heat subordination, compact-support form.**  The corpus's
`lattice_heatSubordination`, with `HasCompactSupport g` in place of
`tsupport g ⊆ ball 0 (ℓ/2)` (the latter is used only to produce the former). -/
theorem lattice_heatSubordination_compact {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖^2)
      = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi 0, t^(-3/2:ℝ) *
            ((∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹
                * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖^2)
             - (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * Real.exp (-t * ‖Work.BoseBoxFock.kmomInt ℓ n‖^2)
                * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖^2)) := by
  have ha0 : ∀ n : Fin 3 → ℤ,
      0 ≤ (ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2 :=
    fun n => by positivity
  have ha : Summable (fun n : Fin 3 → ℤ =>
      (ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2) := by
    simpa using summable_lattice_kinFT_weight hℓ hg hgc 0
  have hm : Summable (fun n : Fin 3 → ℤ =>
      ((ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2) * ‖kmomInt ℓ n‖) := by
    refine (summable_lattice_kinFT_weight hℓ hg hgc 1).congr (fun n => ?_)
    ring
  have hkey := heatSubordination_lattice hℓ ha0 ha hm
  calc (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * ‖kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2)
      = ∑' n : Fin 3 → ℤ,
          ‖kmomInt ℓ n‖ * ((ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2) :=
        tsum_congr (fun n => by ring)
    _ = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi (0:ℝ), t^(-(3:ℝ)/2) *
            ((∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹
                * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2)
             - (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2))
                * ((ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2))) := hkey
    _ = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi (0:ℝ), t^(-3/2:ℝ) *
            ((∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹
                * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2)
             - (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * Real.exp (-t * ‖kmomInt ℓ n‖^2)
                * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2)) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        have h1 : (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2))
              * ((ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2))
            = ∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * Real.exp (-t * ‖kmomInt ℓ n‖^2)
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2 := by
          refine tsum_congr (fun n => ?_)
          rw [neg_mul]
          ring
        rw [h1]

/-- **Continuum heat subordination, compact-support form.**  The corpus's
`continuum_heatSubordination_v2`, with `HasCompactSupport g` in place of
`tsupport g ⊆ ball 0 (ℓ/2)`. -/
theorem continuum_heatSubordination_v2_compact {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    ((2*Real.pi)^3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖p‖ * ‖Submission.BoseGases.kinFT g p‖^2
      = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi 0, t^(-3/2:ℝ) *
            ( ((2*Real.pi)^3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
                ‖Submission.BoseGases.kinFT g p‖^2)
             - ((2*Real.pi)^3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
                Real.exp (-t * ‖p‖^2) * ‖Submission.BoseGases.kinFT g p‖^2) ) := by
  have hkey := SqrtKin.subordination_t_p_swap (g := g) hg hgc
  have hheat : ∀ t : ℝ,
      kinHeat g t = ((2*Real.pi)^3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          Real.exp (-t * ‖p‖^2) * ‖Submission.BoseGases.kinFT g p‖^2 := by
    intro t
    unfold kinHeat
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with p
    simp only [neg_mul]
  have hInt : (∫ t in Set.Ioi 0, t^(-3/2:ℝ) * (kinMass g - kinHeat g t))
      = ∫ t in Set.Ioi 0, t^(-3/2:ℝ) *
          ( ((2*Real.pi)^3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
              ‖Submission.BoseGases.kinFT g p‖^2)
           - ((2*Real.pi)^3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
              Real.exp (-t * ‖p‖^2) * ‖Submission.BoseGases.kinFT g p‖^2) ) := by
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards with t ht
    unfold kinMass
    rw [hheat t]
  rw [← hInt, hkey]
  change kinFirst g = (2 * Real.sqrt Real.pi)⁻¹ * (2 * Real.sqrt Real.pi * kinFirst g)
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-! ## 3. The heat identity for the closed ball -/

/-- **The deficit identity `3·S₁ − 2·R₁ = (2√π)⁻¹∫t^{-3/2}(N + 2·contHeat − 3·latHeat)`**, in the
vocabulary of the target, for `g` smooth of compact support with `tsupport g ⊆ boxL ℓ`
(the corpus's `three_latMoment_sub_two_kinFirst` with the support hypothesis weakened from
`ball 0 (ℓ/2)` to `boxL ℓ`). -/
theorem three_latMoment_sub_two_kinFirst_compact {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hbox : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    3 * latMoment ℓ g - 2 * kinFirst g
      = (2 * Real.sqrt Real.pi)⁻¹ *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
          (hsN ℓ g + 2 * contHeat g t - 3 * latHeat ℓ t g) := by
  have hM0 : hsN ℓ g
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
    frame_lattice_ball hℓ hg hgc hbox
  have hIlat := integrableOn_heatDeficit_lat hℓ hg hgc
  have hIcont := integrableOn_heatDeficit_cont hg hgc
  have hA : latMoment ℓ g = (2 * Real.sqrt Real.pi)⁻¹ *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - latHeat ℓ t g) := by
    rw [latMoment_eq, lattice_heatSubordination_compact hℓ hg hgc]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      simp only [hsN, latHeat]; ring)
  have hB : kinFirst g = (2 * Real.sqrt Real.pi)⁻¹ *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - contHeat g t) := by
    rw [show kinFirst g = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2 from rfl,
      continuum_heatSubordination_v2_compact hℓ hg hgc, ← hM0]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      simp only [hsN, contHeat]; ring)
  have hIa : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) *
      (hsN ℓ g - latHeat ℓ t g)) (Set.Ioi 0) volume := hIlat
  have hIb : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) *
      (hsN ℓ g - contHeat g t)) (Set.Ioi 0) volume := by
    rw [hM0]; exact hIcont
  rw [hA, hB,
    show (3 : ℝ) * ((2 * Real.sqrt Real.pi)⁻¹ * (∫ t in Set.Ioi (0 : ℝ),
          t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - latHeat ℓ t g)))
        - 2 * ((2 * Real.sqrt Real.pi)⁻¹ * (∫ t in Set.Ioi (0 : ℝ),
          t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - contHeat g t)))
      = (2 * Real.sqrt Real.pi)⁻¹ *
        (3 * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - latHeat ℓ t g))
          - 2 * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - contHeat g t)))
      from by ring]
  congr 1
  have h1 : (3 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
        (hsN ℓ g - latHeat ℓ t g))
      = ∫ t in Set.Ioi (0 : ℝ), 3 * (t ^ (-(3 / 2 : ℝ)) *
        (hsN ℓ g - latHeat ℓ t g)) := by
    rw [MeasureTheory.integral_const_mul]
  have h2 : (2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
        (hsN ℓ g - contHeat g t))
      = ∫ t in Set.Ioi (0 : ℝ), 2 * (t ^ (-(3 / 2 : ℝ)) *
        (hsN ℓ g - contHeat g t)) := by
    rw [MeasureTheory.integral_const_mul]
  rw [h1, h2, ← MeasureTheory.integral_sub (hIa.const_mul 3) (hIb.const_mul 2)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)

/-- **The deficit identity for the closed ball.**  Same as
`three_latMoment_sub_two_kinFirst_compact`, with the support hypothesis `tsupport g ⊆ boxL ℓ`
discharged from `tsupport g ⊆ closedBall 0 (ℓ/2)` (`closedBall_subset_corpusBox_boxL`). -/
theorem three_latMoment_sub_two_kinFirst_closed {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    3 * latMoment ℓ g - 2 * kinFirst g
      = (2 * Real.sqrt Real.pi)⁻¹ *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
          (hsN ℓ g + 2 * contHeat g t - 3 * latHeat ℓ t g) := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E3) (ℓ/2))
      (fun x hx => hgsupp (subset_closure hx))
  exact three_latMoment_sub_two_kinFirst_compact hℓ hg hgc
    (hgsupp.trans (closedBall_subset_corpusBox_boxL hℓ))

/-! ## 4. The row, for the well-typed (reviewed) form of the request

**The requested statement is ill-typed as it reached this file.**  It had `latHeat ℓ g t` where
`latHeat`'s arguments are `(ℓ) (t) (g)` (`Work.BoseBoxFock.latHeat : ℝ → ℝ → (ℝ³ → ℂ) → ℝ`), so
the type checker demands `g : ℝ` there; hence no declaration with that text can exist.  The
recorded *review* of this path (`.fm3_reviews.json`, key
`BoseBoxFock/kinFirst_le_of_heatSpec_closed`) has the correctly ordered `latHeat ℓ t g`, which is
also the order of the open-ball sibling `Work.BoseBoxFock.kinFirst_le_of_heatSpec` and of the
integrand of `three_latMoment_sub_two_kinFirst`; the declaration below is that (unique well-typed)
statement, verbatim, under the requested name — so a re-request of this path with the argument
order repaired is already discharged by this file.
See `FINDING_kinFirst_le_of_heatSpec_closed.md`. -/

theorem kinFirst_le_of_heatSpec_closed {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    (hspec : ∀ t : ℝ, 0 < t →
      0 ≤ hsN ℓ g + 2 * contHeat g t - 3 * latHeat ℓ t g) :
    2 * kinFirst g ≤ 3 * latMoment ℓ g := by
  have hkey := three_latMoment_sub_two_kinFirst_closed hℓ hg hgsupp
  have hnn : 0 ≤ ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
      (hsN ℓ g + 2 * contHeat g t - 3 * latHeat ℓ t g) := by
    refine MeasureTheory.setIntegral_nonneg_of_ae_restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (hspec t ht)
  have hfin := mul_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.sqrt Real.pi)⁻¹) hnn
  rw [← hkey] at hfin
  linarith

end Work.BoseBoxFock
