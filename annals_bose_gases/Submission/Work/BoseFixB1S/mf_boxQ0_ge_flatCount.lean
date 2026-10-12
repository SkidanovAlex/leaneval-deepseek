import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.flatBranchDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-! ## Auxiliary facts about the degenerate box

The stored statement of `mf_boxQ0_ge_flatCount` has the weak hypothesis `0 ≤ μ` (not
`0 < μ`), so the box side `ℓ = sideAt μ (a v)` cannot be proved positive through
`Work.BoseFixB1.adm_ell_pos` (which needs `Adm v ε₀ μ`, hence `0 < μ`).  Instead, `0 < ℓ`
is read off the hypothesis `0 < mfV v μ u = boxMass ℓ d u` by contraposition: for `ℓ ≤ 0`
the cube `acube ℓ` is contained in the singleton `{0}`, so `dlBox ℓ d u` is null and the
box mass vanishes (`boxMass_eq_zero_of_nonpos` below, through `boxMass_eq_measureReal`).
The same three geometric facts (`measurableSet_boxA`, `boxA_subset_acube`,
`mfV_eq_measureReal`) are the side conditions of `Work.BoseFixB1S.boxQ0_ge_counts` at FS's
parameters. -/

open MeasureTheory

/-- The centred cube of side `ℓ ≤ 0` is contained in the singleton `{0}`, hence null. -/
lemma volume_acube_of_nonpos {ℓ : ℝ} (hℓ : ℓ ≤ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.acube ℓ) = 0 := by
  have hsub : Submission.BoseGases.acube ℓ ⊆ ({0} : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro x hx
    rw [Set.mem_singleton_iff]
    ext m
    have hm : -ℓ / 2 ≤ x m ∧ x m ≤ ℓ / 2 := hx m
    simpa using (show x m = (0 : EuclideanSpace ℝ (Fin 3)) m from by
      have : (0 : EuclideanSpace ℝ (Fin 3)) m = 0 := by simp
      linarith [hm.1, hm.2, this])
  have h1 : (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.acube ℓ)
      ≤ (volume : Measure (EuclideanSpace ℝ (Fin 3))) ({0} : Set (EuclideanSpace ℝ (Fin 3))) :=
    measure_mono hsub
  have h2 : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      ({0} : Set (EuclideanSpace ℝ (Fin 3))) = 0 := measure_singleton 0
  exact le_antisymm (by simpa [h2] using h1) bot_le

/-- The sliding box `dlBox ℓ d u` is null when `ℓ ≤ 0` (`dlBox ⊆ acube ℓ ⊆ {0}`), hence the
box mass vanishes there. -/
lemma boxMass_eq_zero_of_nonpos {ℓ d : ℝ} (hℓ : ℓ ≤ 0)
    (u : EuclideanSpace ℝ (Fin 3)) : Work.SmallBoxSliding.boxMass ℓ d u = 0 := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hle : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.dlBox ℓ d u) ≤ 0 :=
    le_trans (measure_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u))
      (le_of_eq (volume_acube_of_nonpos hℓ))
  have hzero : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.dlBox ℓ d u) = 0 := le_antisymm hle bot_le
  rw [hzero]
  simp

/-- The box `B(u) = boxA v μ u` is measurable. -/
lemma measurableSet_boxA (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : MeasurableSet (boxA v μ u) :=
  Work.SmallBoxSliding.measurableSet_dlBox _ _ _

/-- The box `B(u) = boxA v μ u` sits inside the big centred cube `acube ℓ`. -/
lemma boxA_subset_acube (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    boxA v μ u ⊆ Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
  Work.SmallBoxSliding.dlBox_subset_acube _ _ _

/-- The box volume `mfV v μ u = boxMass ℓ d u` is the real measure of `B(u)`. -/
lemma mfV_eq_measureReal (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    mfV v μ u = (MeasureTheory.volume (boxA v μ u)).toReal := by
  simp only [mfV, boxA, Work.SmallBoxSliding.boxMass_eq_measureReal,
    MeasureTheory.Measure.real_def]

/-- **`boxQ₀` dominates the flat-count (Jensen) form at FS's parameters.**  This is
`Work.BoseFixB1S.boxQ0_ge_counts` (`boxQ0 ≥ ½(M₁/|B|²)(S² − S‖Φ‖²)/‖Φ‖² − μ(M₁/|B|)S`) with its
hypotheses discharged, read through the abbreviations of `flatBranchDefs`: `ℓ = sideAt μ (a v)`,
`volA = mfV v μ u = boxMass ℓ d u`, `A = boxA v μ u = dlBox ℓ d u`, `w1 = boxW1 h μ u`
(giving `boxM1 = mfM1 h μ u`), `w2 = boxW2 h μ u`, `S = mfS v μ n Φ u`, `I = mfI v μ n Φ`,
`boxQ0 = mfQ0 h μ n Φ u`.  The remaining side conditions are `0 ≤ μ`, `0 < volA`, `0 ≤ M₁` and
`M₁ ≤ M₂` (passed in as hypotheses — in the callers they come from
`Work.BoseFixB1S.boxM1Info`), the two integrability hypotheses `hw2i`/`hfib`, and
`0 ≤ boxPairCount volA ℓ A Φ` and `0 < ℓ`, `MeasurableSet A`, `volA = (volume A).toReal`,
`A ⊆ acube ℓ`, which are proved internally (a sum of integrals of squares,
`boxMass_eq_zero_of_nonpos`, `measurableSet_dlBox`, `boxMass_eq_measureReal`,
`dlBox_subset_acube`). -/
theorem mf_boxQ0_ge_flatCount {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} {μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hμ : 0 ≤ μ) (hvol : 0 < Work.BoseFixB1S.mfV v μ u) (hΦc : Continuous Φ)
    (hM1nn : 0 ≤ Work.BoseFixB1S.mfM1 h μ u)
    (hM2 : Work.BoseFixB1S.mfM1 h μ u ≤ Work.BoseFixB1S.mfM2 h μ u)
    (hw2i : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1S.boxW2 h μ u p.1 p.2)
      (MeasureTheory.volume.restrict (Work.BoseFixB1S.boxA v μ u ×ˢ Work.BoseFixB1S.boxA v μ u)))
    (hfib : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseFixB1S.boxW1 h μ u) z)
      (Work.BoseFixB1S.boxA v μ u)) :
    (1 / 2) * (Work.BoseFixB1S.mfM1 h μ u / (Work.BoseFixB1S.mfV v μ u) ^ 2)
        * ((Work.BoseFixB1S.mfS v μ n Φ u) ^ 2
            - Work.BoseFixB1S.mfS v μ n Φ u * Work.BoseFixB1S.mfI v μ n Φ)
        / Work.BoseFixB1S.mfI v μ n Φ
      - μ * (Work.BoseFixB1S.mfM1 h μ u / Work.BoseFixB1S.mfV v μ u)
          * Work.BoseFixB1S.mfS v μ n Φ u
      ≤ Work.BoseFixB1S.mfQ0 h μ n Φ u := by
  -- `0 < ℓ` from `0 < boxMass ℓ d u` by contraposition: for `ℓ ≤ 0` the box is null.
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    by_contra hc
    push Not at hc
    have hz := boxMass_eq_zero_of_nonpos
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hc u
    rw [Work.BoseFixB1S.mfV_def] at hvol
    rw [hz] at hvol
    exact lt_irrefl 0 hvol
  have hA : MeasurableSet (Work.BoseFixB1S.boxA v μ u) := measurableSet_boxA v μ u
  have hAc := boxA_subset_acube v μ u
  have hvolA : Work.BoseFixB1S.mfV v μ u =
      (MeasureTheory.volume (Work.BoseFixB1S.boxA v μ u)).toReal := mfV_eq_measureReal v μ u
  -- the pair count is a sum of integrals of squares
  have hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1S.mfV v μ u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseFixB1S.boxA v μ u) Φ := by
    rw [Work.BoseFixB1S.boxPairCount]
    apply Finset.sum_nonneg
    intro p hp
    apply MeasureTheory.integral_nonneg
    intro x
    positivity
  exact Work.BoseFixB1S.boxQ0_ge_counts hℓ hvol hA hvolA hAc hw2i hfib hΦc hμ hM1nn hM2 hPcnn

end Work.BoseFixB1S
