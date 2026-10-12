import ChallengeDeps
import Submission.Work.BoseFixB1S.mfGatesV2B1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.slidingBoxGates` — the two sliding-box gates

At FS's parameters `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `t = μ(a v)³`,
an admissible point with `ε₀ ≤ min 1 ((a v)³)` (so that `μ ≤ 1` and `t ≤ 1`) satisfies,
for **every** `u` in the good set `G`:

1. `0 < boxMass ℓ d u` — the sliding box has positive volume on `G`
   (`Work.BoseFixB1.boxMass_pos_of_goodSet`);
2. `1 ≤ ℓ³` — the big box has volume at least one;
3. `boxMass ℓ d u ≤ ℓ³` — the sliding box is contained in the big box `acube ℓ`.

The middle gate is the only one that needs the smallness hypothesis.  At FS's
parameters `ℓ³ = μ⁻¹ · t^{-166/323}` (`Work.BoseFixB1.mu_ell_cube_eq`), so `ℓ³ ≥ 1`
is exactly `μ ≤ 1 ∧ t ≤ 1`; and `μ ≤ 1` is precisely what the hypothesis
`ε₀ ≤ (a v)³` added to the diluteness `μ(a v)³ ≤ ε₀` supplies.  The third gate
does not use the regime at all: `dlBox ℓ d u ⊆ acube ℓ`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB1Cube

/-! ## 1. The elementary consequences of the threshold `ε₀ ≤ (a v)³` -/

/-- **The chemical potential is at most one.**  The diluteness hypothesis
`μ(a v)³ ≤ ε₀` together with the threshold `ε₀ ≤ (a v)³` gives `μ ≤ 1` (after
dividing by `(a v)³ > 0`).  This is the only place the threshold is used. -/
lemma adm_mu_le_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hε0 : ε₀ ≤ (_root_.BoseGases.a v) ^ 3) : μ ≤ 1 := by
  have hA : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have h : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 * (_root_.BoseGases.a v) ^ 3 := by
    rw [one_mul]
    exact le_trans (Work.BoseFixB1.adm_dilute hAdm) hε0
  exact le_of_mul_le_mul_right h (pow_pos hA 3)

/-- The diluteness is at most one, from the threshold `ε₀ ≤ 1`. -/
lemma adm_dilute_le_one' {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hε0 : ε₀ ≤ 1) : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
  le_trans (Work.BoseFixB1.adm_dilute hAdm) hε0

/-- FS's small parameter `d = t^{6/323}` is at most one. -/
lemma adm_d_le_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hε0 : ε₀ ≤ 1) : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hA : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  rw [Work.BoseFixB1.d_eq_fsXp]
  exact Work.BoseBox.fsXp_le_one (mul_pos hμ (pow_pos hA 3)) (adm_dilute_le_one' hAdm hε0)
    (by norm_num)

/-! ## 2. The two gates that use the parameters -/

/-- **Gate 2**: the big box has volume at least one.  At FS's parameters
`ℓ³ = μ⁻¹ t^{-166/323}` with `t = μ(a v)³ ≤ 1` and `μ ≤ 1`, so both factors are
`≥ 1`. -/
lemma one_le_sideAt_cube {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hε0 : ε₀ ≤ min 1 ((_root_.BoseGases.a v) ^ 3)) :
    1 ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hA : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hA 3)
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm) (le_trans hε0 (min_le_left _ _))
  have hμle1 : μ ≤ 1 := adm_mu_le_one hAdm (le_trans hε0 (min_le_right _ _))
  have hkey : 1 ≤ μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
    rw [Work.BoseFixB1.mu_ell_cube_eq (A := _root_.BoseGases.a v) (μ := μ) hA hμ]
    exact Work.BoseFixB1.one_le_fsXp_of ht0 ht1 (by norm_num)
  have hnn : 0 ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 :=
    pow_nonneg (le_of_lt (Work.BoseFixB1.adm_ell_pos hAdm)) 3
  calc (1 : ℝ) ≤ μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := hkey
    _ ≤ 1 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 :=
        mul_le_mul_of_nonneg_right hμle1 hnn
    _ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := one_mul _

/-! ## 3. The geometric gate `boxMass ≤ ℓ³` -/

/-- **Gate 3**: the sliding box is contained in the big box `acube ℓ`, so its
volume is at most `|acube ℓ| = ℓ³`.  No regime hypothesis is needed. -/
lemma boxMass_le_sideAt_cube (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  calc ((volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)).toReal
      ≤ ((volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.acube
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))).toReal :=
        ENNReal.toReal_mono
          (by rw [Submission.BoseGases.acube_volume _ hℓ.le]; exact ENNReal.ofReal_ne_top)
          (measure_mono (Work.SmallBoxSliding.dlBox_subset_acube _ _ _))
    _ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
        rw [Submission.BoseGases.acube_volume _ hℓ.le,
          ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]

/-! ## 4. The target -/

theorem slidingBoxGates {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hε0 : ε₀ ≤ min 1 ((_root_.BoseGases.a v) ^ 3))
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) :
    0 < Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ∧ 1 ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
      ∧ Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  exact ⟨Work.BoseFixB1.boxMass_pos_of_goodSet hℓ (Work.BoseFixB1.adm_d_pos hAdm)
      (Work.BoseFixB1.adm_mu_pos hAdm) hu,
    one_le_sideAt_cube hAdm hε0,
    boxMass_le_sideAt_cube v μ hℓ u⟩

end Work.BoseB1Cube
