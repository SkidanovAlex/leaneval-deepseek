import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseRowsL.LatticeCoulomb.ballInvNormSq
import Submission.Work.BoseRowsL.LatticeCoulomb.csiAux
import Submission.Work.BoseRowsL.LatticeCoulomb.sum_integral_ucell_eq_integral_iUnion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.cellSumVsIntegral`

The lattice-vs-continuum comparison of the Coulomb kernel at equal truncation radius:

  `|Σ_{n∈T} ∫_{q ∈ ucell n} cos(2π⟪q,z⟫)/‖q‖² − ∫_{‖q‖≤R} cos(2π⟪q,z⟫)/‖q‖²| ≤ 100`

for `R ≥ 1`, `‖z‖ ≤ 1/2` and `T` exactly the set of non-zero lattice points with `‖nvec n‖ ≤ R`.

## Route (volume only — the oscillation of the cosine is *not* used)

* `Σ_{n∈T} ∫_{ucell n} f = ∫_{U} f` with `U = ⋃_{n∈T} ucell n`
  (`sum_integral_ucell_eq_integral_iUnion`): the closed cells overlap only on their faces, which
  are null.
* `U ⊆ closedBall 0 (R+1)`, and a point of `B_R \ U` either has norm `> R - 1` or lies in the
  central cell `ucell 0` (`closedBall_sdiff_cellUnion_subset` in `csiAux`).
* Both pieces of the symmetric difference carry the weight `‖q‖⁻²`, whose primitive is
  `∫_{ball ρ} ‖q‖⁻² = 4πρ` (`ballInvNormSq`: constant density `4π` per unit radius), so

  `|Ω_R| ≤ 4π + (4π + 2π√3) = 8π + 2π√3 < 100`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The analytic input `∫_{ball ρ} ‖q‖⁻² = 4πρ` (with its integrability): the imported
`Work.BoseRowsL.LatticeCoulomb.ballInvNormSq`. -/
private lemma cellSum_ballInputs (ρ : ℝ) (hρ : 0 ≤ ρ) :
    IntegrableOn (fun q : E3 => (‖q‖ ^ 2)⁻¹) (Metric.closedBall (0 : E3) ρ) volume ∧
      (∫ q in Metric.closedBall (0 : E3) ρ, (‖q‖ ^ 2)⁻¹ ∂volume = 4 * Real.pi * ρ) ∧
      (∫ q in Metric.ball (0 : E3) ρ, (‖q‖ ^ 2)⁻¹ ∂volume = 4 * Real.pi * ρ) := by
  have h := ballInvNormSq ρ hρ
  exact h

/-- The cell decomposition `Σ_{n∈T} ∫_{ucell n} f = ∫_{⋃ ucell} f`: the imported
`Work.BoseRowsL.LatticeCoulomb.sum_integral_ucell_eq_integral_iUnion`. -/
private lemma cellSum_unionInput (T : Finset (Fin 3 → ℤ)) (z : E3)
    (hne : ∀ n ∈ T, n ≠ 0) :
    (∑ n ∈ T, ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 ∂volume)
      = ∫ q in (⋃ n ∈ T, ucell n),
          Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 ∂volume := by
  have h := sum_integral_ucell_eq_integral_iUnion T z hne
  exact h

theorem cellSumVsIntegral (R : ℝ) (T : Finset (Fin 3 → ℤ)) (z : E3)
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ 1 / 2) (h1 : ∀ n ∈ T, n ≠ 0) (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    |(∑ n ∈ T, ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2)
      - ∫ q in Metric.closedBall 0 R, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2| ≤ 100 := by
  show |(∑ n ∈ T, ∫ q in ucell n, Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 ∂volume)
      - ∫ q in Metric.closedBall (0 : E3) R,
          Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 ∂volume| ≤ 100
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hRnn : (0 : ℝ) ≤ R := le_of_lt hRpos
  have hRm1 : (0 : ℝ) ≤ R - 1 := by linarith
  have hsqrt3 : Real.sqrt 3 / 2 ≤ R := by
    have h : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    linarith
  set f : E3 → ℝ := fun q => Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 with hf
  set g : E3 → ℝ := fun q => (‖q‖ ^ 2)⁻¹ with hgdef
  set U : Set E3 := ⋃ n ∈ T, ucell n with hU
  set B : Set E3 := Metric.closedBall (0 : E3) R with hB
  have hgnn : ∀ q : E3, 0 ≤ g q := fun q => inv_nonneg.mpr (sq_nonneg _)
  -- ## geometry and integrability
  have hUmeas : MeasurableSet U := by
    rw [hU]; exact MeasurableSet.biUnion T.countable_toSet (fun n _ => ucell_measurableSet n)
  have hBmeas : MeasurableSet B := by
    rw [hB]; exact Metric.isClosed_closedBall.measurableSet
  have hUsub : U ⊆ Metric.closedBall (0 : E3) (R + 1) := by
    rw [hU]
    intro q hq
    obtain ⟨n, hnT, hqn⟩ := Set.mem_iUnion₂.mp hq
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖q‖ ≤ ‖nvec n‖ + 1 := norm_le_of_mem_ucell hqn
      _ ≤ R + 1 := by linarith [h2 n hnT]
  have hfinBall : volume (Metric.closedBall (0 : E3) (R + 1)) < ⊤ := by
    rw [EuclideanSpace.volume_closedBall_fin_three]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (n := 3) ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top
  have hUfin : volume U < ⊤ := lt_of_le_of_lt (measure_mono hUsub) hfinBall
  have hhalf : ∀ q ∈ U, (1 : ℝ) / 2 ≤ ‖q‖ := by
    intro q hq
    rw [hU] at hq
    obtain ⟨n, hnT, hqn⟩ := Set.mem_iUnion₂.mp hq
    exact half_le_norm_of_mem_ucell hqn (h1 n hnT)
  have hfU : ∀ q ∈ U, ‖f q‖ ≤ 4 := by
    intro q hq
    have hq2 : (1 / 2 : ℝ) ^ 2 ≤ ‖q‖ ^ 2 := by nlinarith [hhalf q hq, norm_nonneg q]
    have hcos : |Real.cos (2 * Real.pi * inner ℝ q z)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    rw [hf, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖q‖ ^ 2)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖q‖ ^ 2)]
    nlinarith [hcos, hq2]
  have hfmeas : Measurable f := by
    rw [hf]
    exact Measurable.div (by fun_prop) (by fun_prop)
  have hintU : IntegrableOn f U volume := by
    refine IntegrableOn.of_bound hUfin hfmeas.aestronglyMeasurable 4 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict hUmeas] with q hq
    exact hfU q hq
  have hintB : IntegrableOn f B volume := by
    have hinv : IntegrableOn g B volume := by rw [hB]; exact (cellSum_ballInputs R hRnn).1
    have hbdd : ∀ q : E3, ‖Real.cos (2 * Real.pi * inner ℝ q z)‖ ≤ 1 := by
      intro q
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hb := hinv.bdd_mul (f := fun q : E3 => Real.cos (2 * Real.pi * inner ℝ q z))
      (by fun_prop : AEStronglyMeasurable _ (volume.restrict B))
      (Filter.Eventually.of_forall hbdd)
    rw [hf]
    show Integrable (fun q : E3 => Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2)
      (volume.restrict B)
    simpa only [div_eq_mul_inv] using hb
  have hgB : IntegrableOn g B volume := by
    rw [hB]; exact (cellSum_ballInputs R hRnn).1
  have hgU : IntegrableOn g U volume :=
    ((cellSum_ballInputs (R + 1) (by linarith)).1).mono_set hUsub
  -- ## the sum is the integral over the union
  have hsum : (∑ n ∈ T, ∫ q in ucell n, f q ∂volume) = ∫ q in U, f q ∂volume := by
    rw [hU, hf]
    exact cellSum_unionInput T z h1
  -- ## splitting both integrals along `U ∩ B`
  have hsplitU : ∫ q in U, f q ∂volume
      = ∫ q in U ∩ B, f q ∂volume + ∫ q in U \ B, f q ∂volume := by
    have hUeq : U = U ∩ B ∪ (U \ B) := by
      ext q; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
    conv_lhs => rw [hUeq]
    exact MeasureTheory.setIntegral_union
      (by rw [Set.disjoint_left]; intro q h1q h2q; exact h2q.2 h1q.2)
      (hUmeas.diff hBmeas) (hintU.mono_set Set.inter_subset_left)
      (hintU.mono_set Set.sdiff_subset)
  have hsplitB : ∫ q in B, f q ∂volume
      = ∫ q in U ∩ B, f q ∂volume + ∫ q in B \ U, f q ∂volume := by
    have hBeq : B = U ∩ B ∪ (B \ U) := by
      ext q; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
    conv_lhs => rw [hBeq]
    exact MeasureTheory.setIntegral_union
      (by rw [Set.disjoint_left]; intro q h1q h2q; exact h2q.2 h1q.1)
      (hBmeas.diff hUmeas) (hintB.mono_set Set.inter_subset_right)
      (hintB.mono_set Set.sdiff_subset)
  -- ## the two boundary pieces
  have hshellsub : Metric.ball (0 : E3) (R - 1) ⊆ B := by
    rw [hB]
    exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hshell : ∫ q in (B \ Metric.ball (0 : E3) (R - 1)), g q ∂volume = 4 * Real.pi := by
    have hdisj : Disjoint (B \ Metric.ball (0 : E3) (R - 1)) (Metric.ball (0 : E3) (R - 1)) := by
      rw [Set.disjoint_left]; intro q h1q h2q; exact h1q.2 h2q
    have hun := MeasureTheory.setIntegral_union hdisj Metric.isOpen_ball.measurableSet
      (hgB.mono_set Set.sdiff_subset)
      ((cellSum_ballInputs (R - 1) hRm1).1.mono_set Metric.ball_subset_closedBall)
    have hBeq : B = (B \ Metric.ball (0 : E3) (R - 1)) ∪ Metric.ball (0 : E3) (R - 1) := by
      rw [Set.union_comm]
      exact (Set.union_sdiff_cancel hshellsub).symm
    rw [← hBeq] at hun
    rw [hB, (cellSum_ballInputs R hRnn).2.1, (cellSum_ballInputs (R - 1) hRm1).2.2] at hun
    linarith
  have hcell0sub : ucell (0 : Fin 3 → ℤ) ⊆ Metric.closedBall (0 : E3) (Real.sqrt 3 / 2) :=
    ucell_zero_subset_closedBall
  have hgcell0 : IntegrableOn g (ucell (0 : Fin 3 → ℤ)) volume :=
    hgB.mono_set (hcell0sub.trans (Metric.closedBall_subset_closedBall hsqrt3))
  have hcell0 : ∫ q in ucell (0 : Fin 3 → ℤ), g q ∂volume ≤ 2 * Real.pi * Real.sqrt 3 := by
    calc ∫ q in ucell (0 : Fin 3 → ℤ), g q ∂volume
        ≤ ∫ q in Metric.closedBall (0 : E3) (Real.sqrt 3 / 2), g q ∂volume :=
          MeasureTheory.setIntegral_mono_set
            ((cellSum_ballInputs (Real.sqrt 3 / 2) (by positivity)).1)
            (Filter.Eventually.of_forall hgnn) (Filter.Eventually.of_forall hcell0sub)
      _ = 4 * Real.pi * (Real.sqrt 3 / 2) :=
          (cellSum_ballInputs (Real.sqrt 3 / 2) (by positivity)).2.1
      _ = 2 * Real.pi * Real.sqrt 3 := by ring
  -- ## bound on `U \ B`: it sits in the shell `R < ‖q‖ ≤ R+1`
  have hUB : |∫ q in U \ B, f q ∂volume| ≤ 4 * Real.pi := by
    have hshellP : U \ B ⊆ Metric.closedBall (0 : E3) (R + 1) \ Metric.closedBall (0 : E3) R := by
      intro q hq
      obtain ⟨hqU, hqB⟩ := hq
      refine ⟨hUsub hqU, ?_⟩
      rw [hB, Metric.mem_closedBall, dist_zero_right] at hqB
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hqB
    have hshellInt : IntegrableOn g
        (Metric.closedBall (0 : E3) (R + 1) \ Metric.closedBall (0 : E3) R) volume :=
      ((cellSum_ballInputs (R + 1) (by linarith)).1).mono_set Set.sdiff_subset
    have step1 : ∫ q in U \ B, |f q| ∂volume ≤ ∫ q in U \ B, g q ∂volume := by
      refine MeasureTheory.setIntegral_mono_on ((hintU.mono_set Set.sdiff_subset).norm)
        (hgU.mono_set Set.sdiff_subset) (hUmeas.diff hBmeas) ?_
      intro q hq
      show |Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2| ≤ (‖q‖ ^ 2)⁻¹
      have hcos : |Real.cos (2 * Real.pi * inner ℝ q z)| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      rw [abs_div]
      have hden : |‖q‖ ^ 2| = ‖q‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [hden]
      have hstep := div_le_div_of_nonneg_right (c := ‖q‖ ^ 2) hcos (sq_nonneg (‖q‖))
      simpa only [one_div] using hstep
    have step2 : ∫ q in U \ B, g q ∂volume
        ≤ ∫ q in Metric.closedBall (0 : E3) (R + 1) \ Metric.closedBall (0 : E3) R,
            g q ∂volume :=
      MeasureTheory.setIntegral_mono_set hshellInt (Filter.Eventually.of_forall hgnn)
        (Filter.Eventually.of_forall hshellP)
    have hshellval : ∫ q in Metric.closedBall (0 : E3) (R + 1) \ Metric.closedBall (0 : E3) R,
        g q ∂volume = 4 * Real.pi := by
      have hdisj : Disjoint (Metric.closedBall (0 : E3) (R + 1) \ Metric.closedBall (0 : E3) R)
          (Metric.closedBall (0 : E3) R) := by
        rw [Set.disjoint_left]; intro q h1q h2q; exact h1q.2 h2q
      have hun := MeasureTheory.setIntegral_union hdisj Metric.isClosed_closedBall.measurableSet
        hshellInt ((cellSum_ballInputs R hRnn).1)
      have heq : (Metric.closedBall (0 : E3) (R + 1) \ Metric.closedBall (0 : E3) R)
          ∪ Metric.closedBall (0 : E3) R = Metric.closedBall (0 : E3) (R + 1) := by
        rw [Set.union_comm]
        exact Set.union_sdiff_cancel (Metric.closedBall_subset_closedBall (by linarith))
      rw [heq] at hun
      rw [(cellSum_ballInputs (R + 1) (by linarith)).2.1,
        (cellSum_ballInputs R hRnn).2.1] at hun
      linarith
    calc |∫ q in U \ B, f q ∂volume| ≤ ∫ q in U \ B, |f q| ∂volume :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ q in U \ B, g q ∂volume := step1
      _ ≤ ∫ q in Metric.closedBall (0 : E3) (R + 1) \ Metric.closedBall (0 : E3) R,
            g q ∂volume := step2
      _ = 4 * Real.pi := hshellval
  -- ## bound on `B \ U`
  have hBU : |∫ q in B \ U, f q ∂volume| ≤ 4 * Real.pi + 2 * Real.pi * Real.sqrt 3 := by
    have hsub : B \ U ⊆ (B \ Metric.ball (0 : E3) (R - 1)) ∪ ucell 0 := by
      rw [hB, hU]
      exact closedBall_sdiff_cellUnion_subset R T h1 h2 h4
    have hucellB : ucell (0 : Fin 3 → ℤ) ⊆ B :=
      hcell0sub.trans (Metric.closedBall_subset_closedBall hsqrt3)
    have hshellucell : IntegrableOn g ((B \ Metric.ball (0 : E3) (R - 1)) ∪ ucell 0) volume :=
      hgB.mono_set (Set.union_subset Set.sdiff_subset hucellB)
    have hgBs : IntegrableOn g (B \ Metric.ball (0 : E3) (R - 1)) volume :=
      hgB.mono_set Set.sdiff_subset
    have hgucshell : IntegrableOn g
        (ucell 0 \ (B \ Metric.ball (0 : E3) (R - 1))) volume :=
      hgB.mono_set (Set.sdiff_subset.trans hucellB)
    have step1 : ∫ q in B \ U, |f q| ∂volume ≤ ∫ q in B \ U, g q ∂volume := by
      refine MeasureTheory.setIntegral_mono_on ((hintB.mono_set Set.sdiff_subset).norm)
        (hgB.mono_set Set.sdiff_subset) (hBmeas.diff hUmeas) ?_
      intro q hq
      show |Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2| ≤ (‖q‖ ^ 2)⁻¹
      have hcos : |Real.cos (2 * Real.pi * inner ℝ q z)| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      rw [abs_div]
      have hden : |‖q‖ ^ 2| = ‖q‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [hden]
      have hstep := div_le_div_of_nonneg_right (c := ‖q‖ ^ 2) hcos (sq_nonneg (‖q‖))
      simpa only [one_div] using hstep
    have step2 : ∫ q in B \ U, g q ∂volume
        ≤ ∫ q in (B \ Metric.ball (0 : E3) (R - 1)) ∪ ucell 0, g q ∂volume :=
      MeasureTheory.setIntegral_mono_set hshellucell (Filter.Eventually.of_forall hgnn)
        (Filter.Eventually.of_forall hsub)
    have step3 : ∫ q in (B \ Metric.ball (0 : E3) (R - 1)) ∪ ucell 0, g q ∂volume
        ≤ ∫ q in (B \ Metric.ball (0 : E3) (R - 1)), g q ∂volume
          + ∫ q in ucell 0, g q ∂volume := by
      have hdisj : Disjoint (B \ Metric.ball (0 : E3) (R - 1))
          (ucell 0 \ (B \ Metric.ball (0 : E3) (R - 1))) := by
        rw [Set.disjoint_left]; intro q h1q h2q; exact h2q.2 h1q
      have hun := MeasureTheory.setIntegral_union hdisj
        ((ucell_measurableSet 0).diff (hBmeas.diff Metric.isOpen_ball.measurableSet))
        hgBs hgucshell
      have heq : (B \ Metric.ball (0 : E3) (R - 1))
          ∪ (ucell 0 \ (B \ Metric.ball (0 : E3) (R - 1)))
          = (B \ Metric.ball (0 : E3) (R - 1)) ∪ ucell 0 := by
        ext q; simp only [Set.mem_union, Set.mem_sdiff]; tauto
      rw [heq] at hun
      have hle : ∫ q in ucell 0 \ (B \ Metric.ball (0 : E3) (R - 1)), g q ∂volume
          ≤ ∫ q in ucell 0, g q ∂volume :=
        MeasureTheory.setIntegral_mono_set hgcell0 (Filter.Eventually.of_forall hgnn)
          (Filter.Eventually.of_forall Set.sdiff_subset)
      linarith [hun, hle]
    calc |∫ q in B \ U, f q ∂volume| ≤ ∫ q in B \ U, |f q| ∂volume :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ q in B \ U, g q ∂volume := step1
      _ ≤ ∫ q in (B \ Metric.ball (0 : E3) (R - 1)) ∪ ucell 0, g q ∂volume := step2
      _ ≤ ∫ q in (B \ Metric.ball (0 : E3) (R - 1)), g q ∂volume
            + ∫ q in ucell 0, g q ∂volume := step3
      _ ≤ 4 * Real.pi + 2 * Real.pi * Real.sqrt 3 := by linarith [hshell, hcell0]
  -- ## assembly
  have hgoal : |(∑ n ∈ T, ∫ q in ucell n, f q ∂volume) - ∫ q in B, f q ∂volume| ≤ 100 := by
    have habs : |(∑ n ∈ T, ∫ q in ucell n, f q ∂volume) - ∫ q in B, f q ∂volume|
        = |(∫ q in U \ B, f q ∂volume) - ∫ q in B \ U, f q ∂volume| := by
      rw [hsum, hsplitU, hsplitB]
      congr 1
      ring
    rw [habs]
    have h2' : 4 * Real.pi + (4 * Real.pi + 2 * Real.pi * Real.sqrt 3) ≤ 100 := by
      have h : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
      nlinarith [Real.pi_lt_four, Real.pi_pos, Real.sqrt_nonneg 3, h]
    have h1' : |(∫ q in U \ B, f q ∂volume) - ∫ q in B \ U, f q ∂volume|
        ≤ |∫ q in U \ B, f q ∂volume| + |∫ q in B \ U, f q ∂volume| := by
      have := abs_add_le (∫ q in U \ B, f q ∂volume) (-(∫ q in B \ U, f q ∂volume))
      simpa only [sub_eq_add_neg, abs_neg] using this
    linarith [h1', hUB, hBU]
  simpa only [hf, hB] using hgoal

end Work.BoseRowsL.LatticeCoulomb
