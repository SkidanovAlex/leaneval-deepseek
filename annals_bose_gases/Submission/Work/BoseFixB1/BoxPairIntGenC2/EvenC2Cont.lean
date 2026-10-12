import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxPairIntGenC2.EvenC2Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.EvenC2Cont`

Continuity of the unwindowed slot means `Work.BoseFixB1S.oneMean`/`twoMean`, of the
indicator-free peeled pair integrand `evenC2Integrand`, and of the indicator-free fibre
`evenC2Free` (in the two distinguished values).  The continuity of `evenC2Free` is what allows
the a.e. symmetry proved in `EvenC2Peel` to be upgraded to an identity valid everywhere.

All proofs are dominated-convergence arguments: `A ⊆ acube ℓ` bounds the region of integration,
so a continuous state is uniformly bounded on the configurations that occur.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- A uniform bound of `Φ` on the configurations obtained from a compact set of `x` by
overwriting one slot with a point of `acube ℓ`. -/
lemma exists_update_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : Continuous Φ) (i : Fin N) (K : Set (Submission.BoseGases.X N)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ a ∈ Submission.BoseGases.acube ℓ,
      |Φ (Function.update x i a)| ≤ C := by
  have hK' : IsCompact (K ×ˢ Submission.BoseGases.acube ℓ) :=
    hK.prod (Submission.BoseGases.acube_compact hℓ)
  have hcont : ContinuousOn
      (fun p : Submission.BoseGases.X N × E3 => Φ (Function.update p.1 i p.2))
      (K ×ˢ Submission.BoseGases.acube ℓ) :=
    hΦ.continuousOn.comp (continuous_update i).continuousOn (fun p _ => Set.mem_univ _)
  obtain ⟨C, hC⟩ := hK'.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx a ha => ?_⟩
  have h := hC (x, a) ⟨hx, ha⟩
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- The `i`-slot mean of a continuous state is continuous. -/
theorem continuous_oneMean {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) :
    Continuous (fun x => Work.BoseFixB1S.oneMean volA A i Φ x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hAfin : (volume : Measure E3) A < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono hAc)
      (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hAfin.ne
  obtain ⟨C, hC0, hC⟩ := exists_update_bound hℓ hΦ i (Metric.closedBall x₀ 1)
    (isCompact_closedBall x₀ 1)
  have hmain : ContinuousAt
      (fun x => ∫ a in A, Φ (Function.update x i a)) x₀ := by
    refine continuousAt_of_dominated
      (μ := (volume : Measure E3).restrict A)
      (F := fun x a => Φ (Function.update x i a)) (bound := fun _ => C)
      (x₀ := x₀) ?_ ?_ ?_ ?_
    · filter_upwards with x
      exact (hΦ.comp ((continuous_update i).comp
        (Continuous.prodMk continuous_const continuous_id))).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
      rw [ae_restrict_iff' hA]
      filter_upwards with a ha
      exact hC x (Metric.ball_subset_closedBall hx) a (hAc ha)
    · exact MeasureTheory.integrable_const C
    · filter_upwards with a
      exact (hΦ.comp ((continuous_update i).comp
        (Continuous.prodMk continuous_id continuous_const))).continuousAt
  have hfun : (fun x => Work.BoseFixB1S.oneMean volA A i Φ x)
      = fun x => (1 / volA) * ∫ a in A, Φ (Function.update x i a) := rfl
  rw [hfun]
  exact hmain.const_mul (1 / volA)

/-- The two-slot mean of a continuous state, as the iterated `i`-slot mean of the `j`-slot mean. -/
lemma twoMean_eq_oneMean_comp {N : ℕ} (volA : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) :
    Work.BoseFixB1S.twoMean volA A i j Φ
      = Work.BoseFixB1S.oneMean volA A i (Work.BoseFixB1S.oneMean volA A j Φ) := by
  funext x
  simp only [Work.BoseFixB1S.twoMean, Work.BoseFixB1S.oneMean]
  rw [MeasureTheory.integral_const_mul]

/-- The two-slot mean of a continuous state is continuous. -/
theorem continuous_twoMean {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) (i j : Fin N) :
    Continuous (fun x => Work.BoseFixB1S.twoMean volA A i j Φ x) := by
  rw [twoMean_eq_oneMean_comp]
  exact continuous_oneMean hA hℓ hAc (continuous_oneMean hA hℓ hAc hΦ j) i

/-- The indicator-free peeled pair integrand of the box is continuous. -/
theorem continuous_evenC2Integrand {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) :
    Continuous (fun x => evenC2Integrand volA A Φ i j' x) := by
  have h1 : Continuous (fun x => Work.BoseFixB1S.twoMean volA A i (i.succAbove j') Φ x) :=
    continuous_twoMean hA hℓ hAc hΦ i (i.succAbove j')
  have h2 : Continuous (fun x =>
      Φ x - Work.BoseFixB1S.oneMean volA A (i.succAbove j') Φ x
        - Work.BoseFixB1S.oneMean volA A i Φ x
        + Work.BoseFixB1S.twoMean volA A i (i.succAbove j') Φ x) :=
    ((hΦ.sub (continuous_oneMean hA hℓ hAc hΦ (i.succAbove j'))).sub
      (continuous_oneMean hA hℓ hAc hΦ i)).add h1
  exact h1.mul h2

/-! ## The double insertion -/

/-- Continuity of the double insertion in the two distinguished values. -/
lemma continuous_ins2_pair {N : ℕ} (i : Fin (N + 2)) (j' : Fin (N + 1)) :
    Continuous (fun p : (E3 × E3) × Submission.BoseGases.X N =>
      Submission.BoseGases.ins2 i j' p.1.1 p.1.2 p.2) := by
  have h : (fun p : (E3 × E3) × Submission.BoseGases.X N =>
      Submission.BoseGases.ins2 i j' p.1.1 p.1.2 p.2)
      = fun p : (E3 × E3) × Submission.BoseGases.X N =>
          Submission.BoseGases.kcInsN (N + 1) i
            (p.1.1, Submission.BoseGases.kcInsN N j' (p.1.2, p.2)) := rfl
  rw [h]
  exact (Submission.BoseGases.kcInsN_cont i).comp (Continuous.prodMk
    (by fun_prop : Continuous fun p : (E3 × E3) × Submission.BoseGases.X N => p.1.1)
    ((Submission.BoseGases.kcInsN_cont j').comp (Continuous.prodMk
      (by fun_prop : Continuous fun p : (E3 × E3) × Submission.BoseGases.X N => p.1.2)
      (by fun_prop : Continuous fun p : (E3 × E3) × Submission.BoseGases.X N => p.2))))

/-- Continuity of the double insertion in the two distinguished values, rest fixed. -/
lemma continuous_ins2_fst {N : ℕ} (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N) :
    Continuous (fun q : E3 × E3 => Submission.BoseGases.ins2 i j' q.1 q.2 r2) := by
  have h : (fun q : E3 × E3 => Submission.BoseGases.ins2 i j' q.1 q.2 r2)
      = fun q => Submission.BoseGases.kcInsN (N + 1) i
          (q.1, Submission.BoseGases.kcInsN N j' (q.2, r2)) := rfl
  rw [h]
  exact (Submission.BoseGases.kcInsN_cont i).comp (Continuous.prodMk continuous_fst
    ((Submission.BoseGases.kcInsN_cont j').comp
      (Continuous.prodMk continuous_snd continuous_const)))

/-- Continuity of the double insertion in the remaining configuration, the values fixed. -/
lemma continuous_ins2_snd {N : ℕ} (i : Fin (N + 2)) (j' : Fin (N + 1)) (y z : E3) :
    Continuous (fun r2 : Submission.BoseGases.X N =>
      Submission.BoseGases.ins2 i j' y z r2) := by
  have h : (fun r2 : Submission.BoseGases.X N => Submission.BoseGases.ins2 i j' y z r2)
      = fun r2 => Submission.BoseGases.kcInsN (N + 1) i
          (y, Submission.BoseGases.kcInsN N j' (z, r2)) := rfl
  rw [h]
  exact (Submission.BoseGases.kcInsN_cont i).comp (Continuous.prodMk continuous_const
    ((Submission.BoseGases.kcInsN_cont j').comp
      (Continuous.prodMk continuous_const continuous_id)))

/-! ## Continuity of the indicator-free fibre -/

/-- The indicator-free fibre is continuous in the two distinguished values. -/
theorem continuous_evenC2Free {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) :
    Continuous (fun q : E3 × E3 => evenC2Free volA ℓ A Φ i j' q.1 q.2) := by
  have hInt : Continuous (fun x => evenC2Integrand volA A Φ i j' x) :=
    continuous_evenC2Integrand hA hℓ hAc hΦ i j'
  have hcontjoint : Continuous (fun p : (E3 × E3) × Submission.BoseGases.X N =>
      evenC2Integrand volA A Φ i j' (Submission.BoseGases.ins2 i j' p.1.1 p.1.2 p.2)) :=
    hInt.comp (continuous_ins2_pair i j')
  have hjoint : ContDiff ℝ 0 (Function.uncurry (fun p : E3 × E3 =>
      fun r2 : Submission.BoseGases.X N =>
        evenC2Integrand volA A Φ i j' (Submission.BoseGases.ins2 i j' p.1 p.2 r2))) := by
    rw [contDiff_zero]
    exact hcontjoint
  have h := Commons.Analysis.Calculus.contDiff_zero_setIntegral_isCompact_pi
    (P := E3 × E3) (d := N) (E := ℝ) (k := Submission.BoseGases.abox N ℓ)
    (Submission.BoseGases.abox_compact N hℓ) hjoint
  rw [contDiff_zero] at h
  exact h

end Work.BoseFixB1.BoxPairIntGenC2
