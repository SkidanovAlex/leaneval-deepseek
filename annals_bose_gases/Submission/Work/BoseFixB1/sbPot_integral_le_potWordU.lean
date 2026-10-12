import ChallengeDeps
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword_radial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.sbPot_integral_le_potWordU`

FS `lem:LocPotential` at FS's small-box parameters, per state: the `u`-integral of the localised
potential word `sbPot = qLHSwordB h M ℓ d μ` is the potential part of the large-box word, i.e. is
*at most* the whole-space potential word against the state,

    ∫_u sbPot h μ u Φ ≤ ∫_{abox n ℓ} (Φ x)² · potWordU n v (g₀ v h) ℓ μ 0 x ,

together with the `u`-marginal integrability of `sbPot h μ · Φ`.

The proof is the composition of the two delivered identities:

* `Work.UBBInputs8.A.qLHSwordB_integral_u_box` — the sliding telescope
  `∫_u qLHSwordB h M ℓ d μ · Φ = qLHSword ℓ μ (wPairC ℓ v) (wPairC ℓ (g₀ v h)) Φ`;
* `Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword_of_radial` — the dictionary between FS
  `eq:Def_HB`'s potential word and the corpus word,
  `∫_{abox n ℓ} Φ² potWordU = qLHSword ℓ μ (wPairC ℓ v) (wPairC ℓ (g₀ v h)) Φ`
  (which uses `IsRadial v` and `0 < ℓ`, and is *false* without them);

so the inequality is an equality.  The marginal integrability comes from the box-restricted
*joint* integrability of the localised integrand (`qLHSBIntegrand_box_integrable`, proved below)
by Fubini.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The box-restricted joint integrability of the localised potential integrand**, at arbitrary
real `μ`, arbitrary real small-box parameters `d > 0`, `L > 0` and `M ≥ 1`, and single-scale
regime hypotheses: for every continuous state `Φ`,
`p ↦ qLHSBIntegrand h M L d μ Φ p.1 p.2` is integrable for
`volume.prod (volume.restrict (abox N L))`.

This is `Work.UBBInputs8.A.integrable_qLHSBIntegrand_box` with its two restrictions removed (it
carries `d : ℕ` and the *uniform* regime `∀ L ≥ 1, R0 ≤ L d/16`, and it fixes `μ = dens N L`);
the per-state marginal integrability — and hence the telescoping identity — is what needs it. -/
theorem qLHSBIntegrand_box_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} {R0 L d μ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv1 : MeasureTheory.MemLp v 1) (hM : 1 ≤ M) (hL : 0 < L) (hd : 0 < d)
    (hreg : R0 ≤ L * d / 16) (hregχ : R0 ≤ L * chiR0)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N L))) := by
  -- ## 0. Support data
  have hvsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => eq_zero_of_tsupport_subset_ball hv_supp hz
  have hgsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hg0int : Integrable (g0 v h) := g0_integrable hR0 hv_supp h
  -- the small bump is supported in the unit cube, hence in the unit ball
  have hsupp1 : ∀ {z : EuclideanSpace ℝ (Fin 3)}, chiSmall M z ≠ 0 → ‖z‖ ≤ 1 := by
    intro z hz
    have hcoord : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2 := fun j => chiSmall_support_mem_abs_le hM hz j
    have hsq : ‖z‖ ^ 2 = ∑ j : Fin 3, |z.ofLp j| ^ 2 := by
      simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) z)
    have hsum : (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ 3 * (1 / 2 : ℝ) ^ 2 := by
      calc (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ ∑ _j : Fin 3, (1 / 2 : ℝ) ^ 2 :=
            Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2)
        _ = 3 * (1 / 2 : ℝ) ^ 2 := by simp
    have hsq1 : ‖z‖ ^ 2 ≤ 1 := by rw [hsq]; nlinarith [hsum]
    have hx0 : 0 ≤ ‖z‖ := norm_nonneg z
    have habs : |‖z‖| ≤ |(1 : ℝ)| := sq_le_sq.mp (by simpa using hsq1)
    simpa [abs_of_nonneg hx0] using habs
  -- ## 1. The `u`-profile `ψ` (a compactly supported majorant of the sliding bump) and its `0-1`
  -- indicator `Λ`
  set Kd : ℝ := (L * d)⁻¹ * (Real.sqrt 3 * (L / 2)) with hKddef
  set ball1 : Set (EuclideanSpace ℝ (Fin 3)) :=
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (Kd + 1) with hball1def
  set ψ : EuclideanSpace ℝ (Fin 3) → ℝ := ball1.indicator (fun _ => chiSmallDecay M) with hψdef
  set Λ : EuclideanSpace ℝ (Fin 3) → ℝ := ball1.indicator (fun _ => (1 : ℝ)) with hΛdef
  have hψnn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ ψ u := by
    intro u
    by_cases hu : u ∈ ball1
    · rw [hψdef, Set.indicator_of_mem hu]; exact chiSmallDecay_nonneg M
    · rw [hψdef, Set.indicator_of_notMem hu]
  have hψle : ∀ u : EuclideanSpace ℝ (Fin 3), ψ u ≤ chiSmallDecay M := by
    intro u
    by_cases hu : u ∈ ball1
    · rw [hψdef, Set.indicator_of_mem hu]
    · rw [hψdef, Set.indicator_of_notMem hu]; exact chiSmallDecay_nonneg M
  have hΛnn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Λ u := by
    intro u
    by_cases hu : u ∈ ball1
    · rw [hΛdef, Set.indicator_of_mem hu]; norm_num
    · rw [hΛdef, Set.indicator_of_notMem hu]
  have hψ_eq : ∀ u : EuclideanSpace ℝ (Fin 3), ψ u = chiSmallDecay M * Λ u := by
    intro u
    by_cases hu : u ∈ ball1
    · rw [hψdef, hΛdef, Set.indicator_of_mem hu, Set.indicator_of_mem hu]; ring
    · rw [hψdef, hΛdef, Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]; ring
  have hψint : Integrable ψ := by
    rw [hψdef, hball1def]
    refine (MeasureTheory.integrableOn_const (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
      (Kd + 1)) (C := chiSmallDecay M) ?_).integrable_indicator measurableSet_closedBall
    exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (Kd + 1)).measure_lt_top.ne
  have hΛint : Integrable Λ := by
    rw [hΛdef, hball1def]
    refine (MeasureTheory.integrableOn_const (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
      (Kd + 1)) (C := (1 : ℝ)) ?_).integrable_indicator measurableSet_closedBall
    exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (Kd + 1)).measure_lt_top.ne
  -- ## 2. Pointwise bounds for the localised kernels
  have hcube_norm : ∀ a : EuclideanSpace ℝ (Fin 3), a ∈ acube L → ‖(L * d)⁻¹ • a‖ ≤ Kd := by
    intro a ha
    have hcoord : ∀ j : Fin 3, |a.ofLp j| ≤ L / 2 := by
      intro j
      have h := ha j
      rw [Set.mem_Icc] at h
      exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
    have hnorm : ‖a‖ ≤ Real.sqrt 3 * (L / 2) :=
      coord_box_subset_eucl_ball (by linarith) hcoord
    have hLi : 0 ≤ (L * d)⁻¹ := by positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hLi, hKddef]
    exact mul_le_mul_of_nonneg_left hnorm hLi
  have hχψ : ∀ (a u : EuclideanSpace ℝ (Fin 3)), a ∈ acube L →
      chiSmall M ((L * d)⁻¹ • a - u) ≤ ψ u := by
    intro a u ha
    by_cases hz : chiSmall M ((L * d)⁻¹ • a - u) = 0
    · rw [hz]; exact hψnn u
    · have hsupp : ‖(L * d)⁻¹ • a - u‖ ≤ 1 := hsupp1 hz
      have hnorm : ‖(L * d)⁻¹ • a‖ ≤ Kd := hcube_norm a ha
      have hmem : u ∈ ball1 := by
        rw [hball1def, Metric.mem_closedBall, dist_zero_right]
        have hsub : (L * d)⁻¹ • a - ((L * d)⁻¹ • a - u) = u := by abel
        rw [← hsub]
        exact le_trans (norm_sub_le _ _) (add_le_add hnorm hsupp)
      rw [hψdef, Set.indicator_of_mem hmem]
      have hh := chiSmall_decay_coord_le_decay hM ((L * d)⁻¹ • a - u)
      rwa [abs_of_nonneg (chiSmall_nonneg M _)] at hh
  have hchiB_le_psi : ∀ (a u : EuclideanSpace ℝ (Fin 3)), a ∈ acube L →
      ‖chiSmallB M L d u a‖ ≤ chiSup * ψ u := by
    intro a u ha
    have h1 : |chiScale L a| ≤ chiSup := abs_chiScale_le_chiSup L a
    have h2 : |chiSmall M ((L * d)⁻¹ • a - u)| ≤ ψ u := by
      rw [abs_of_nonneg (chiSmall_nonneg M _)]
      exact hχψ a u ha
    have hgoal : |chiScale L a| * |chiSmall M ((L * d)⁻¹ • a - u)| ≤ chiSup * ψ u :=
      mul_le_mul h1 h2 (abs_nonneg _) (le_of_lt chiSup_pos)
    simpa only [Submission.BoseGases.chiSmallB, norm_mul, Real.norm_eq_abs] using hgoal
  have hchiB_le_decay : ∀ (a u : EuclideanSpace ℝ (Fin 3)),
      ‖chiSmallB M L d u a‖ ≤ chiSup * chiSmallDecay M := by
    intro a u
    have h1 : |chiScale L a| ≤ chiSup := abs_chiScale_le_chiSup L a
    have h2 : |chiSmall M ((L * d)⁻¹ • a - u)| ≤ chiSmallDecay M :=
      chiSmall_decay_coord_le_decay hM _
    have hgoal : |chiScale L a| * |chiSmall M ((L * d)⁻¹ • a - u)| ≤
        chiSup * chiSmallDecay M :=
      mul_le_mul h1 h2 (abs_nonneg _) (le_of_lt chiSup_pos)
    simpa only [Submission.BoseGases.chiSmallB, norm_mul, Real.norm_eq_abs] using hgoal
  -- the renormalisation constant: on the support of the numerator the two denominators are `≥ c0`
  set c0 : ℝ := (1 / 2) * smallConvLower M with hc0def
  have hc0pos : 0 < c0 := by
    rw [hc0def]; exact mul_pos (by norm_num) (smallConvLower_pos M)
  have hden : ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → f z = 0) → ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖wSmallScaled M (L * d) f z / convScale L z‖ ≤ c0⁻¹ * ‖f z‖ := by
    intro f hfsupp z
    by_cases hz : f z = 0
    · have hzero : wSmallScaled M (L * d) f z = 0 := by
        rw [Submission.BoseGases.wSmallScaled, hz, zero_div]
      rw [hzero, hz]
      simp
    · have hlt : ‖z‖ < R0 := by
        by_contra hcon
        exact hz (hfsupp z (le_of_not_gt hcon))
      have hzn : ‖(L * d)⁻¹ • z‖ < 1 / 16 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (L * d)⁻¹)]
        have hmul : (L * d)⁻¹ * ‖z‖ < (L * d)⁻¹ * (L * d / 16) :=
          mul_lt_mul_of_pos_left (lt_of_lt_of_le hlt hreg) (by positivity)
        have heq : (L * d)⁻¹ * (L * d / 16) = 1 / 16 := by field_simp
        linarith [hmul, heq.le, heq.ge]
      have hcoord : ∀ j : Fin 3, |((L * d)⁻¹ • z).ofLp j| ≤ 1 / 16 :=
        fun j => le_of_lt (lt_of_le_of_lt (coord_abs_le_norm _ j) hzn)
      have hc2 : smallConvLower M ≤ convScaleSmall M (L * d) z :=
        conv3Small_coord_lower hM ((L * d)⁻¹ • z) hcoord
      have hp2 : 0 < convScaleSmall M (L * d) z :=
        lt_of_lt_of_le (smallConvLower_pos M) hc2
      have hc1 : (1 / 2 : ℝ) ≤ convScale L z :=
        convScale_ge_half_ball hL hR0.le hregχ (le_of_lt hlt)
      have hp1 : 0 < convScale L z := lt_of_lt_of_le (by norm_num) hc1
      have hprod : c0 ≤ convScaleSmall M (L * d) z * convScale L z := by
        rw [hc0def, mul_comm (1 / 2)]
        exact mul_le_mul hc2 hc1 (by norm_num) (le_of_lt hp2)
      have hc12 : 0 < convScaleSmall M (L * d) z * convScale L z := mul_pos hp2 hp1
      have hkey : 1 ≤ c0⁻¹ * (convScaleSmall M (L * d) z * convScale L z) := by
        have hh := mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hc0pos.le)
        rwa [inv_mul_cancel₀ (ne_of_gt hc0pos)] at hh
      have hsplit : wSmallScaled M (L * d) f z / convScale L z
          = f z / (convScaleSmall M (L * d) z * convScale L z) := by
        rw [Submission.BoseGases.wSmallScaled, div_div]
      rw [hsplit, norm_div, norm_mul, Real.norm_of_nonneg (le_of_lt hp2),
        Real.norm_of_nonneg (le_of_lt hp1), div_le_iff₀ hc12]
      calc ‖f z‖ = ‖f z‖ * 1 := (mul_one _).symm
        _ ≤ ‖f z‖ * (c0⁻¹ * (convScaleSmall M (L * d) z * convScale L z)) :=
            mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
        _ = c0⁻¹ * ‖f z‖ * (convScaleSmall M (L * d) z * convScale L z) := by ring
  -- the kernel constant
  set Kc : ℝ := chiSup * c0⁻¹ * (chiSup * chiSmallDecay M) with hKcdef
  have hKcnonneg : 0 ≤ Kc := by
    rw [hKcdef]
    exact mul_nonneg (mul_nonneg (le_of_lt chiSup_pos) (inv_nonneg.mpr hc0pos.le))
      (mul_nonneg (le_of_lt chiSup_pos) (chiSmallDecay_nonneg M))
  have hpair_le : ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ) (u a b : EuclideanSpace ℝ (Fin 3)),
      (∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → f z = 0) →
      ‖wSmallPair M L d u f a b‖ ≤ Kc * ψ u * ‖f (a - b)‖ := by
    intro f u a b hfsupp
    have hS : ‖wSmallScaled M (L * d) f (a - b) / convScale L (a - b)‖ ≤ c0⁻¹ * ‖f (a - b)‖ :=
      hden f hfsupp (a - b)
    have hBd : ‖chiSmallB M L d u b‖ ≤ chiSup * chiSmallDecay M := hchiB_le_decay b u
    by_cases hsa : chiScale L a = 0
    · have hzero : chiSmallB M L d u a = 0 := by
        simp only [Submission.BoseGases.chiSmallB, hsa, zero_mul]
      rw [Submission.BoseGases.wSmallPair, hzero, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg hKcnonneg (hψnn u)) (norm_nonneg _)
    · have ha : a ∈ acube L := by
        rw [mem_acube_iff]
        intro j
        rw [Set.mem_Icc]
        have hle : |a.ofLp j| ≤ L / 2 :=
          le_trans (coord_abs_le_norm a j) (chiScale_support_le hL hsa)
        exact ⟨by linarith [neg_abs_le (a.ofLp j), hle], le_trans (le_abs_self _) hle⟩
      have hAa : ‖chiSmallB M L d u a‖ ≤ chiSup * ψ u := hchiB_le_psi a u ha
      have hstep1 : ‖chiSmallB M L d u a
            * (wSmallScaled M (L * d) f (a - b) / convScale L (a - b))‖
          ≤ (chiSup * ψ u) * (c0⁻¹ * ‖f (a - b)‖) := by
        rw [norm_mul]
        exact mul_le_mul hAa hS (norm_nonneg _) (mul_nonneg (le_of_lt chiSup_pos) (hψnn u))
      rw [Submission.BoseGases.wSmallPair, norm_mul]
      refine le_trans (mul_le_mul hstep1 hBd (norm_nonneg _)
        (mul_nonneg (mul_nonneg (le_of_lt chiSup_pos) (hψnn u))
          (mul_nonneg (inv_nonneg.mpr hc0pos.le) (norm_nonneg _)))) (le_of_eq ?_)
      rw [hKcdef]; ring
  -- ## 3. The fibre bound (the `y`-integral of the one-body kernel)
  set G1 : ℝ := ∫ z : EuclideanSpace ℝ (Fin 3), ‖g0 v h z‖ with hG1def
  have hG1nonneg : 0 ≤ G1 := by
    rw [hG1def]; exact integral_nonneg (fun z => norm_nonneg _)
  have hfib_le : ∀ (u a : EuclideanSpace ℝ (Fin 3)), a ∈ acube L →
      ‖∫ y in acube L, wSmall1Pair h M L d u a y‖ ≤ Kc * ψ u * G1 := by
    intro u a ha
    have hstep1 : ‖∫ y in acube L, wSmall1Pair h M L d u a y‖ ≤
        ∫ y in acube L, ‖wSmall1Pair h M L d u a y‖ := by
      have hh := norm_integral_le_integral_norm
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))
        (f := fun y : EuclideanSpace ℝ (Fin 3) => wSmall1Pair h M L d u a y)
      simpa only [Real.norm_eq_abs] using hh
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
        ‖wSmall1Pair h M L d u a y‖ ≤ Kc * ψ u * ‖g0 v h (a - y)‖ := fun y =>
      hpair_le (g0 v h) u a y hgsupp
    have hmajOn : IntegrableOn (fun y : EuclideanSpace ℝ (Fin 3) =>
        Kc * ψ u * ‖g0 v h (a - y)‖) (acube L) :=
      ((hg0int.norm.comp_sub_left a).const_mul (Kc * ψ u)).integrableOn
    have hstep2 : (∫ y in acube L, ‖wSmall1Pair h M L d u a y‖) ≤
        ∫ y in acube L, (Kc * ψ u * ‖g0 v h (a - y)‖) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun y => norm_nonneg _)
      · exact hmajOn
      · filter_upwards with y
        exact hpt y
    have hstep3 : (∫ y in acube L, (Kc * ψ u * ‖g0 v h (a - y)‖)) =
        (Kc * ψ u) * (∫ y in acube L, ‖g0 v h (a - y)‖) := integral_const_mul _ _
    have hstep4 : (∫ y in acube L, ‖g0 v h (a - y)‖) ≤
        ∫ y : EuclideanSpace ℝ (Fin 3), ‖g0 v h (a - y)‖ :=
      setIntegral_le_integral (hg0int.norm.comp_sub_left a)
        (ae_of_all _ (fun y => norm_nonneg _))
    have hstep5 : (∫ y : EuclideanSpace ℝ (Fin 3), ‖g0 v h (a - y)‖) = G1 := by
      rw [hG1def]
      exact integral_sub_left_eq_self (fun w : EuclideanSpace ℝ (Fin 3) => ‖g0 v h w‖) volume a
    calc ‖∫ y in acube L, wSmall1Pair h M L d u a y‖
        ≤ ∫ y in acube L, ‖wSmall1Pair h M L d u a y‖ := hstep1
      _ ≤ ∫ y in acube L, (Kc * ψ u * ‖g0 v h (a - y)‖) := hstep2
      _ = (Kc * ψ u) * (∫ y in acube L, ‖g0 v h (a - y)‖) := hstep3
      _ ≤ (Kc * ψ u) * (∫ y : EuclideanSpace ℝ (Fin 3), ‖g0 v h (a - y)‖) :=
          mul_le_mul_of_nonneg_left hstep4 (mul_nonneg hKcnonneg (hψnn u))
      _ = (Kc * ψ u) * G1 := by rw [hstep5]
      _ = Kc * ψ u * G1 := rfl
  -- ## 4. The state bound and the Urysohn bump on the box
  have hK : IsCompact (Submission.BoseGases.abox N L) := Submission.BoseGases.abox_compact N hL
  obtain ⟨BΦ, hBΦ⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : Submission.BoseGases.X N => Φ x ^ 2) (hΦc.pow 2).continuousOn
  have hBΦ0 : 0 ≤ BΦ := by
    have h := hBΦ 0 (by
      rw [Submission.BoseGases.mem_abox_iff]
      intro i
      rw [Submission.BoseGases.mem_acube_iff]
      intro m
      rw [Set.mem_Icc]
      constructor <;> simp <;> linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Φ 0))] at h
    exact le_trans (sq_nonneg (Φ 0)) h
  obtain ⟨ff, hff1, -, hffcs, -⟩ := exists_continuous_one_zero_of_isCompact
    (s := Submission.BoseGases.abox N L) (t := (∅ : Set (Submission.BoseGases.X N)))
    hK isClosed_empty (Set.disjoint_empty _)
  have hbig := Work.UBBInputs2.integrable_pairSum_v (N := N) (v := v) hv1
    (Φ := fun x : Submission.BoseGases.X N => ff x) ff.continuous hffcs
  -- ## 5. The dominating function
  set Gen : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N → ℝ := fun p =>
    (BΦ * chiSmallDecay M) * (Λ p.1 * (|μ| * ((N : ℝ) * Kc * G1)
      + (1 / 2) * (Kc * (ff p.2 ^ 2 * ∑ q ∈ Submission.BoseGases.pairSet N,
          ‖v (p.2 q.1 - p.2 q.2)‖)))) with hGendef
  have hXint : Integrable (fun x : Submission.BoseGases.X N => |μ| * ((N : ℝ) * Kc * G1)
      + (1 / 2) * (Kc * (ff x ^ 2 * ∑ q ∈ Submission.BoseGases.pairSet N,
          ‖v (x q.1 - x q.2)‖)))
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L)) :=
    (MeasureTheory.integrableOn_const (s := Submission.BoseGases.abox N L)
      (C := |μ| * ((N : ℝ) * Kc * G1)) hK.measure_lt_top.ne).add
      ((hbig.integrableOn.const_mul Kc).const_mul (1 / 2))
  have hGenint : Integrable Gen
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L))) := by
    rw [hGendef]
    exact (hΛint.mul_prod hXint).const_mul (BΦ * chiSmallDecay M)
  -- ## 6. Pointwise domination of the integrand
  have hpoint : ∀ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N,
      p.2 ∈ Submission.BoseGases.abox N L →
      ‖Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ p.1 p.2‖ ≤ Gen p := by
    intro p hp
    obtain ⟨u, x⟩ := p
    have hxall : ∀ i : Fin N, x i ∈ acube L :=
      fun i => (Submission.BoseGases.mem_abox_iff N L x).mp hp i
    have hS : ‖∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d u (x i) y‖
        ≤ (N : ℝ) * (Kc * ψ u * G1) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ i : Fin N, ‖∫ y in acube L, wSmall1Pair h M L d u (x i) y‖
          ≤ ∑ _i : Fin N, Kc * ψ u * G1 :=
            Finset.sum_le_sum (fun i _ => hfib_le u (x i) (hxall i))
        _ = (N : ℝ) * (Kc * ψ u * G1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hT : ‖∑ q ∈ Submission.BoseGases.pairSet N, wSmallPair M L d u v (x q.1) (x q.2)‖
        ≤ Kc * ψ u * (∑ q ∈ Submission.BoseGases.pairSet N, ‖v (x q.1 - x q.2)‖) := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun q _ => hpair_le v u (x q.1) (x q.2) hvsupp)
    have hbr : ‖-μ * (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d u (x i) y)
        + (1 / 2) * (∑ q ∈ Submission.BoseGases.pairSet N,
            wSmallPair M L d u v (x q.1) (x q.2))‖
        ≤ ψ u * (|μ| * ((N : ℝ) * Kc * G1)
            + (1 / 2) * (Kc * (∑ q ∈ Submission.BoseGases.pairSet N, ‖v (x q.1 - x q.2)‖))) := by
      have h1 : ‖-μ * (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d u (x i) y)‖
          ≤ |μ| * ((N : ℝ) * (Kc * ψ u * G1)) := by
        rw [norm_mul, Real.norm_eq_abs, abs_neg]
        exact mul_le_mul_of_nonneg_left hS (abs_nonneg μ)
      have h2 : ‖(1 / 2) * (∑ q ∈ Submission.BoseGases.pairSet N,
            wSmallPair M L d u v (x q.1) (x q.2))‖
          ≤ (1 / 2) * (Kc * ψ u * (∑ q ∈ Submission.BoseGases.pairSet N, ‖v (x q.1 - x q.2)‖)) := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_left hT (by norm_num)
      calc ‖-μ * (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d u (x i) y)
            + (1 / 2) * (∑ q ∈ Submission.BoseGases.pairSet N,
                wSmallPair M L d u v (x q.1) (x q.2))‖
          ≤ ‖-μ * (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d u (x i) y)‖
            + ‖(1 / 2) * (∑ q ∈ Submission.BoseGases.pairSet N,
                wSmallPair M L d u v (x q.1) (x q.2))‖ := norm_add_le _ _
        _ ≤ |μ| * ((N : ℝ) * (Kc * ψ u * G1))
            + (1 / 2) * (Kc * ψ u * (∑ q ∈ Submission.BoseGases.pairSet N,
                ‖v (x q.1 - x q.2)‖)) := add_le_add h1 h2
        _ = ψ u * (|μ| * ((N : ℝ) * Kc * G1)
            + (1 / 2) * (Kc * (∑ q ∈ Submission.BoseGases.pairSet N,
                ‖v (x q.1 - x q.2)‖))) := by ring
    have hΦb : (Φ x) ^ 2 ≤ BΦ := by
      have h := hBΦ x hp
      rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    have hffsq : ff x ^ 2 = 1 := by rw [hff1 hp]; norm_num
    have hbr' : ‖-μ * (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d u (x i) y)
        + (1 / 2) * (∑ q ∈ Submission.BoseGases.pairSet N,
            wSmallPair M L d u v (x q.1) (x q.2))‖
        ≤ ψ u * (|μ| * ((N : ℝ) * Kc * G1)
            + (1 / 2) * (Kc * (ff x ^ 2 * (∑ q ∈ Submission.BoseGases.pairSet N,
                ‖v (x q.1 - x q.2)‖)))) := by
      rw [hffsq, one_mul]
      exact hbr
    rw [Work.SmallBoxSliding.qLHSBIntegrand, hGendef]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Φ x) ^ 2 * ‖-μ * (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d u (x i) y)
          + (1 / 2) * (∑ q ∈ Submission.BoseGases.pairSet N,
              wSmallPair M L d u v (x q.1) (x q.2))‖
        ≤ BΦ * (ψ u * (|μ| * ((N : ℝ) * Kc * G1)
            + (1 / 2) * (Kc * (ff x ^ 2 * (∑ q ∈ Submission.BoseGases.pairSet N,
                ‖v (x q.1 - x q.2)‖))))) :=
          mul_le_mul hΦb hbr' (norm_nonneg _) hBΦ0
      _ = (BΦ * chiSmallDecay M) * (Λ u * (|μ| * ((N : ℝ) * Kc * G1)
            + (1 / 2) * (Kc * (ff x ^ 2 * (∑ q ∈ Submission.BoseGases.pairSet N,
                ‖v (x q.1 - x q.2)‖))))) := by rw [hψ_eq u]; ring
  -- ## 7. A.e. strong measurability of the integrand
  have hmeas : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ p.1 p.2)
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (Submission.BoseGases.X N))) := by
    have hvA : AEMeasurable v (volume : Measure (EuclideanSpace ℝ (Fin 3))) := hv1.aemeasurable
    have hg0A : AEMeasurable (g0 v h) (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      hg0int.aemeasurable
    have hconvScale : Continuous (convScale L) := by
      unfold convScale
      exact conv_contDiff.continuous.comp (by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => L⁻¹ • x))
    have hchiB1 : ∀ i : Fin N, AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N => chiSmallB M L d p.1 (p.2 i))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (Submission.BoseGases.X N))) := by
      intro i
      have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
          chiSmallB M L d p.1 (p.2 i)) := by
        simp only [Submission.BoseGases.chiSmallB]
        exact ((chiScale_continuous L).comp (by fun_prop)).mul
          ((chiSmall_continuous hM).comp (by fun_prop))
      exact hcont.aestronglyMeasurable
    have hpair_meas : ∀ q : Fin N × Fin N, AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
          wSmallPair M L d p.1 v (p.2 q.1) (p.2 q.2))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (Submission.BoseGases.X N))) := by
      intro q
      have hvAq : AEStronglyMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
            v (p.2 q.1 - p.2 q.2))
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (Submission.BoseGases.X N))) :=
        Work.UBBInputs2.aemeasurable_comp_sub_index hvA q.1 q.2
      have hdenA : AEStronglyMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
            convScaleSmall M (L * d) (p.2 q.1 - p.2 q.2))
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (Submission.BoseGases.X N))) :=
        ((Submission.BoseGases.conv3Small_continuous hM).comp
          (by fun_prop : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
            (L * d)⁻¹ • (p.2 q.1 - p.2 q.2)))).aestronglyMeasurable
      have hdenB : AEStronglyMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
            convScale L (p.2 q.1 - p.2 q.2))
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (Submission.BoseGases.X N))) :=
        (hconvScale.comp (by fun_prop)).aestronglyMeasurable
      have hmid : AEStronglyMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
            v (p.2 q.1 - p.2 q.2) / convScaleSmall M (L * d) (p.2 q.1 - p.2 q.2)
              / convScale L (p.2 q.1 - p.2 q.2))
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (Submission.BoseGases.X N))) :=
        ((hvAq.aemeasurable.div hdenA.aemeasurable).div hdenB.aemeasurable).aestronglyMeasurable
      have h : AEStronglyMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
            chiSmallB M L d p.1 (p.2 q.1) * (v (p.2 q.1 - p.2 q.2)
              / convScaleSmall M (L * d) (p.2 q.1 - p.2 q.2) / convScale L (p.2 q.1 - p.2 q.2))
              * chiSmallB M L d p.1 (p.2 q.2))
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (Submission.BoseGases.X N))) :=
        ((hchiB1 q.1).mul hmid).mul (hchiB1 q.2)
      simpa only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled] using h
    have hone : ∀ i : Fin N, AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
          ∫ y in acube L, wSmall1Pair h M L d p.1 (p.2 i) y)
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (Submission.BoseGases.X N))) := by
      intro i
      have hjoint : AEStronglyMeasurable
          (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => wSmall1Pair h M L d q.1.1 (q.1.2 i) q.2)
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (Submission.BoseGases.X N))).prod
            ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))) := by
        have hg0Aq : AEStronglyMeasurable
            (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => g0 v h (q.1.2 i - q.2))
            (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
              (volume : Measure (Submission.BoseGases.X N))).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))) :=
          Work.UBBInputs2.aemeasurable_comp_sub_coord hg0A i L
        have hchiA : AEStronglyMeasurable
            (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => chiSmallB M L d q.1.1 (q.1.2 i))
            (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
              (volume : Measure (Submission.BoseGases.X N))).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))) := by
          have hcont : Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => chiSmallB M L d q.1.1 (q.1.2 i)) := by
            simp only [Submission.BoseGases.chiSmallB]
            exact ((chiScale_continuous L).comp (by fun_prop)).mul
              ((chiSmall_continuous hM).comp (by fun_prop))
          exact hcont.aestronglyMeasurable
        have hchiC : AEStronglyMeasurable
            (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => chiSmallB M L d q.1.1 q.2)
            (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
              (volume : Measure (Submission.BoseGases.X N))).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))) := by
          have hcont : Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => chiSmallB M L d q.1.1 q.2) := by
            simp only [Submission.BoseGases.chiSmallB]
            exact ((chiScale_continuous L).comp (by fun_prop)).mul
              ((chiSmall_continuous hM).comp (by fun_prop))
          exact hcont.aestronglyMeasurable
        have hdenA : AEStronglyMeasurable
            (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => convScaleSmall M (L * d) (q.1.2 i - q.2))
            (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
              (volume : Measure (Submission.BoseGases.X N))).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))) :=
          ((Submission.BoseGases.conv3Small_continuous hM).comp
            (by fun_prop : Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => (L * d)⁻¹ • (q.1.2 i - q.2)))).aestronglyMeasurable
        have hdenB : AEStronglyMeasurable
            (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => convScale L (q.1.2 i - q.2))
            (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
              (volume : Measure (Submission.BoseGases.X N))).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))) :=
          (hconvScale.comp (by fun_prop)).aestronglyMeasurable
        have hmid : AEStronglyMeasurable
            (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => g0 v h (q.1.2 i - q.2)
                / convScaleSmall M (L * d) (q.1.2 i - q.2) / convScale L (q.1.2 i - q.2))
            (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
              (volume : Measure (Submission.BoseGases.X N))).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))) :=
          ((hg0Aq.aemeasurable.div hdenA.aemeasurable).div hdenB.aemeasurable).aestronglyMeasurable
        have h : AEStronglyMeasurable
            (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
              EuclideanSpace ℝ (Fin 3) => chiSmallB M L d q.1.1 (q.1.2 i)
                * (g0 v h (q.1.2 i - q.2) / convScaleSmall M (L * d) (q.1.2 i - q.2)
                  / convScale L (q.1.2 i - q.2)) * chiSmallB M L d q.1.1 q.2)
            (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
              (volume : Measure (Submission.BoseGases.X N))).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube L))) :=
          (hchiA.mul hmid).mul hchiC
        simpa only [wSmall1Pair, Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
          using h
      exact AEStronglyMeasurable.integral_prod_right' hjoint
    have hsum1 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
          ∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d p.1 (p.2 i) y)
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (Submission.BoseGases.X N))) := by
      refine (Finset.aestronglyMeasurable_sum (Finset.univ)
        (fun i (_ : i ∈ Finset.univ) => hone i)).congr ?_
      filter_upwards with p
      simp only [Finset.sum_apply]
    have hsum2 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
          ∑ q ∈ Submission.BoseGases.pairSet N, wSmallPair M L d p.1 v (p.2 q.1) (p.2 q.2))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (Submission.BoseGases.X N))) := by
      refine (Finset.aestronglyMeasurable_sum (Submission.BoseGases.pairSet N)
        (fun q (_ : q ∈ Submission.BoseGases.pairSet N) => hpair_meas q)).congr ?_
      filter_upwards with p
      simp only [Finset.sum_apply]
    have hm : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N => Φ p.2 ^ 2 *
          ((-μ * (∑ i : Fin N, ∫ y in acube L, wSmall1Pair h M L d p.1 (p.2 i) y))
            + (1 / 2) * (∑ q ∈ Submission.BoseGases.pairSet N,
                wSmallPair M L d p.1 v (p.2 q.1) (p.2 q.2))))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (Submission.BoseGases.X N))) :=
      ((hΦc.comp continuous_snd).pow 2).aestronglyMeasurable.mul
        ((hsum1.const_mul (-μ)).add (hsum2.const_mul (1 / 2)))
    simpa only [Work.SmallBoxSliding.qLHSBIntegrand] using hm
  -- ## 8. Conclusion: dominate the (a.e. strongly measurable) integrand
  have hae : ∀ᵐ p ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L))),
      p.2 ∈ Submission.BoseGases.abox N L := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      (p := fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        p.2 ∈ Submission.BoseGases.abox N L)
      ((Submission.BoseGases.abox_measurable N L).preimage measurable_snd)]
    filter_upwards with u
    exact MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N L)
  refine MeasureTheory.Integrable.mono' hGenint
    (hmeas.mono_measure (Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self)) ?_
  filter_upwards [hae] with p hp
  exact hpoint p hp

theorem sbPot_integral_le_potWordU {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R μ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hreg : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hregχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)) ∧
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ))
      ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 x := by
  -- (1) the box-restricted joint integrability of the localised integrand
  have hint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.SmallBoxSliding.qLHSBIntegrand h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
          (Φ : Submission.BoseGases.X n → ℝ) p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
    qLHSBIntegrand_box_integrable (v := v) (h := h)
      (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) (R0 := R)
      (L := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ)
      hv_supp hR hv1 hM hℓ hd hreg hregχ
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous
  -- (2) the `u`-marginal integrability of `sbPot`, by Fubini
  have hInt : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)) := by
    have h1 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ x, Work.SmallBoxSliding.qLHSBIntegrand h
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
            (Φ : Submission.BoseGases.X n → ℝ) u x
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
      hint.integral_prod_left
    refine h1.congr ?_
    filter_upwards with u
    rw [Work.BoseFixB1.sbPot]
    exact (Work.SmallBoxSliding.qLHSwordB_eq_integral h
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
      (Φ : Submission.BoseGases.X n → ℝ)).symm
  -- (3) the sliding telescope
  have htel : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.sbPot h μ u
        (Φ : Submission.BoseGases.X n → ℝ))
      = Submission.BoseGases.qLHSword (N := n) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v)
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h))
          (Φ : Submission.BoseGases.X n → ℝ) := by
    have hbase := Work.UBBInputs8.A.qLHSwordB_integral_u_box (v := v) (R0 := R)
      (hv_supp := hv_supp) (hR0 := hR) (h := h)
      (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) (hM := hM)
      (L := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ)
      (hL := hℓ) (hd := hd) (hR := hreg) (hRχ := hregχ)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hint
    rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.sbPot h μ u
          (Φ : Submission.BoseGases.X n → ℝ))
        = fun u : EuclideanSpace ℝ (Fin 3) => Work.SmallBoxSliding.qLHSwordB h
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
            (Φ : Submission.BoseGases.X n → ℝ) from rfl]
    exact hbase
  -- (4) the potential-word dictionary
  have hrhs : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 x)
      = Submission.BoseGases.qLHSword (N := n) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v)
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h))
          (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword_of_radial (v := v) (h := h) hvrad hℓ
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff
  exact ⟨hInt, le_of_eq (htel.trans hrhs.symm)⟩

end Work.BoseFixB1
