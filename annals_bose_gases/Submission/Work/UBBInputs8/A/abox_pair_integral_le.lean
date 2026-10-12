import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.integral_abox_comp_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two-coordinate `abox` integral bound for the localised cutoff

For two distinct particles `i ≠ j` and the localised cutoff
`χ_{B(u)} = chiSmallB M L d u`, the `abox`-integral of the product
`χ_{B(u)}(x i) · χ_{B(u)}(x j)` is at most `(L³)^{N-1}` times the single-particle
`χ²`-mass `chiMass M L d u = ∫_x χ_{B(u)}(x)² dx`.

The proof does **not** need the two-coordinate fibre computation: the elementary
pointwise inequality `a·b ≤ (a² + b²)/2` turns the product into a sum of two
one-coordinate functions, and each of those integrates to
`(L³)^{N-1} · chiMass` by the single-coordinate fibre lemma
`A.integral_abox_comp_apply`, using that `χ_{B(u)}²` is supported in the centred
cube `acube L` (so that `∫_{acube L} χ_{B(u)}² = ∫ χ_{B(u)}² = chiMass`).
-/

namespace Work.UBBInputs8.A

open Submission.BoseGases
open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The centred cube `acube L` is compact: it is the intersection of the three closed
slabs `|x_j| ≤ L/2` and is contained in the closed ball of radius `√3·(L/2)`. -/
lemma isCompact_acube (L : ℝ) : IsCompact (acube L) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have h1 : acube L
        = ⋂ m : Fin 3, {y : ℝ³ | y.ofLp m ∈ Set.Icc (-L / 2) (L / 2)} := by
      ext y; simp [Submission.BoseGases.acube]
    rw [h1]
    exact isClosed_iInter
      (fun m => isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) m))
  · have hsub : acube L ⊆ Metric.closedBall (0 : ℝ³) (Real.sqrt 3 * (L / 2)) := by
      intro y hy
      have hcoord : ∀ m : Fin 3, |y.ofLp m| ≤ L / 2 := by
        intro m
        have hm := hy m
        rw [Set.mem_Icc] at hm
        exact abs_le.mpr ⟨by linarith [hm.1], hm.2⟩
      have hb0 : 0 ≤ L / 2 := le_trans (abs_nonneg _) (hcoord 0)
      have h2 := Submission.BoseGases.coord_box_subset_eucl_ball (A := L / 2) hb0 hcoord
      simp only [Set.mem_setOf_eq] at h2
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact h2
    exact Metric.isBounded_closedBall.subset hsub

/-- The `N`-particle centred box `abox N L` is compact (a product of compact cubes). -/
lemma isCompact_abox (N : ℕ) (L : ℝ) : IsCompact (abox N L) := by
  rw [abox_eq_pi_acube]
  exact isCompact_univ_pi (fun _ => isCompact_acube L)

theorem abox_pair_integral_le {N : ℕ} {L : ℝ} (hL : 0 < L) {M : ℕ} (hM : 1 ≤ M) {dd : ℝ}
    (hd : 0 < dd) (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ i j : Fin N, i ≠ j →
      (∫ x in Submission.BoseGases.abox N L,
          Submission.BoseGases.chiSmallB M L dd u (x i) * Submission.BoseGases.chiSmallB M L dd u (x j))
        ≤ (L ^ 3) ^ (N - 1) * Work.SmallBoxSliding.chiMass M L dd u := by
  intro i j _
  let f : ℝ³ → ℝ := fun y => chiSmallB M L dd u y
  have hfcont : Continuous f := chiSmallB_continuous hM hL hd u
  have hfcs : HasCompactSupport f := chiSmallB_hasCompactSupport hM hL u
  have hfnonneg : ∀ y, 0 ≤ f y := fun y => chiSmallB_nonneg M L dd u y
  -- `f²` is integrable on `ℝ³` (continuous with compact support).
  have hf2int : Integrable (fun y => f y ^ 2) := by
    have hc : Continuous (fun y => f y ^ 2) := hfcont.pow 2
    have hcs : HasCompactSupport (fun y => f y ^ 2) := by
      apply hfcs.mono
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      exact fun h => hy (by simp [h])
    exact hc.integrable_of_hasCompactSupport hcs
  have hf2On : IntegrableOn (fun y => f y ^ 2) (acube L) := hf2int.integrableOn
  -- The single-coordinate fibre computation: `χ_{B(u)}²` is supported in `acube L`.
  have hsingle : ∀ k : Fin N, ∫ x in abox N L, f (x k) ^ 2
      = (L ^ 3) ^ (N - 1) * Work.SmallBoxSliding.chiMass M L dd u := by
    intro k
    rw [integral_abox_comp_apply (le_of_lt hL) k hf2On]
    congr 1
    rw [Work.SmallBoxSliding.chiMass_def]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    have hy0 : f y = 0 := by
      by_contra h
      apply hy
      rw [mem_acube_iff]
      intro m
      have hb := chiSmallB_support_big_box hM hL (show chiSmallB M L dd u y ≠ 0 from h) m
      rw [Set.mem_Icc]
      have h2 := abs_le.mp hb
      exact ⟨by linarith [h2.1], h2.2⟩
    rw [hy0]; norm_num
  have hcompact : IsCompact (abox N L) := isCompact_abox N L
  -- Integrability of the two sides over `abox`, from continuity on a compact box.
  have hcontsum : Continuous (fun x : X N => (f (x i) ^ 2 + f (x j) ^ 2) / 2) :=
    (((hfcont.pow 2).comp (continuous_apply i)).add
      ((hfcont.pow 2).comp (continuous_apply j))).div_const 2
  have hIntR : IntegrableOn (fun x : X N => (f (x i) ^ 2 + f (x j) ^ 2) / 2) (abox N L) :=
    ContinuousOn.integrableOn_compact hcompact hcontsum.continuousOn
  have hInti : IntegrableOn (fun x : X N => f (x i) ^ 2) (abox N L) :=
    ContinuousOn.integrableOn_compact hcompact
      ((hfcont.pow 2).comp (continuous_apply i)).continuousOn
  have hIntj : IntegrableOn (fun x : X N => f (x j) ^ 2) (abox N L) :=
    ContinuousOn.integrableOn_compact hcompact
      ((hfcont.pow 2).comp (continuous_apply j)).continuousOn
  -- The pointwise AM–GM inequality `a·b ≤ (a²+b²)/2`.
  have hpt : ∀ x : X N, f (x i) * f (x j) ≤ (f (x i) ^ 2 + f (x j) ^ 2) / 2 := by
    intro x; nlinarith [sq_nonneg (f (x i) - f (x j))]
  have hmono : ∫ x in abox N L, f (x i) * f (x j)
      ≤ ∫ x in abox N L, (f (x i) ^ 2 + f (x j) ^ 2) / 2 :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hfnonneg _) (hfnonneg _)))
      hIntR (Filter.Eventually.of_forall hpt)
  -- Evaluation of the upper bound: two single-coordinate integrals.
  have hRHS : ∫ x in abox N L, (f (x i) ^ 2 + f (x j) ^ 2) / 2
      = (L ^ 3) ^ (N - 1) * Work.SmallBoxSliding.chiMass M L dd u := by
    rw [show (fun x : X N => (f (x i) ^ 2 + f (x j) ^ 2) / 2)
        = (fun x : X N => (1 / 2) * (f (x i) ^ 2 + f (x j) ^ 2)) by funext x; ring]
    rw [integral_const_mul, integral_add hInti hIntj, hsingle i, hsingle j]
    ring
  calc ∫ x in abox N L, f (x i) * f (x j)
      ≤ ∫ x in abox N L, (f (x i) ^ 2 + f (x j) ^ 2) / 2 := hmono
    _ = (L ^ 3) ^ (N - 1) * Work.SmallBoxSliding.chiMass M L dd u := hRHS

end Work.UBBInputs8.A
