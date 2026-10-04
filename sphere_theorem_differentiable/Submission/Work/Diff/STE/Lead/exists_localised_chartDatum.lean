import Mathlib
import Submission.Work.Diff.STE.Lead.JointSmoothKit
import Submission.Work.Diff.STE.Man.isDeTurckNonlin_chartNonlin
import Submission.Work.Diff.STE.Lead.det_ne_zero_smul_add_one_of_nonneg_quadForm
import Submission.Work.Diff.STE.Lead.contDiff_smul_of_contDiffOn_tsupport
import Submission.Work.Diff.STE.Lead.chartMatFun_quadForm_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A localised chart datum which is a chart matrix near a ball

`Work.Diff.STE.Lead.exists_localised_chartDatum` produces, for a chart `i` of the finite atlas `D`
of Layer B3 and a ball `B(c, ρ')` of flat coordinates contained in the `2σᵢ`-ball of the chart
(`hball`), a **globally smooth** matrix-valued function `bg` on the flat coordinates which

* agrees with the chart matrix `flatChartMat g₀ (x₀ i)` on the whole open ball `B(c, ρ')`,
* is invertible everywhere, and
* has a chart nonlinearity `chartNonlin bg` which is smooth on the non-degeneracy region
  `{det (reMat J.1) ≠ 0}` of the value jet.

The construction is a bump blending: with `A` the chart matrix read in the flat coordinate (a smooth
function on the `2σᵢ`-ball by `Work.Diff.EXT.kz_contDiffAt_chartMatFun`) and `M₀` the identity matrix,
one takes

  `bg z = χ z • A z + (1 - χ z) • M₀`

where `χ` is a `ContDiffBump` which is `1` on the closed ball of radius `ρ'` around `c` and vanishes
outside a slightly larger ball of radius `ρ''` still contained in the `2σᵢ`-ball (this is where
`hball` is used, and it is the reason `ρ'' := (ρ' + (2σᵢ - ‖c‖))/2` is introduced).  On the
`1`-region `bg = A` is the chart matrix (agreement), on the `0`-region `bg = M₀` is the identity, and
in between it is a convex combination of the (positive semidefinite, by
`Work.Diff.STE.Lead.chartMatFun_quadForm_nonneg`) chart matrix and the identity, hence invertible
(`Work.Diff.STE.Lead.det_ne_zero_smul_add_one_of_nonneg_quadForm`).  The smoothness of `bg` uses
`Work.Diff.STE.Lead.contDiff_smul_of_contDiffOn_tsupport`, and the final smoothness of
`chartNonlin bg` is the composition `secOpFlat + chartNonlinN` of the already proved smoothness of
the two pieces (`Work.Diff.STE.Man.contDiffOn_secOpFlat`, `..._pNfull`).
-/

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem exists_localised_chartDatum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (i : ι₀) (c : Fin (Module.finrank ℝ E) → ℝ) (ρ ρ' : ℝ) (hρ : 0 < ρ) (hρ' : ρ < ρ')
    (hball : ‖c‖ + ρ' < 2 * D.σ i) :
    ∃ bg : (Fin (Module.finrank ℝ E) → ℝ) → Work.Diff.EXT.MatE (E := E),
      ContDiff ℝ (⊤ : ℕ∞) bg ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z - c‖ < ρ' →
        bg z = Work.Diff.STE.Man.flatChartMat (I := I) g₀ (D.x₀ i) z) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, (Matrix.of (bg z)).det ≠ 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.Man.chartNonlin (E := E) bg)
        (Set.univ ×ˢ {J : Work.Diff.STE.Flat.Jet (Work.Diff.STE.Man.dim E) |
          (Work.Diff.STE.Flat.reMat (J.1)).det ≠ 0}) := by
  classical
  -- The three analytic/algebraic inputs of the construction are proved in the sibling modules
  -- `det_ne_zero_smul_add_one_of_nonneg_quadForm`, `contDiff_smul_of_contDiffOn_tsupport` and
  -- `chartMatFun_quadForm_nonneg` (used below).
  -- The outer radius of the localisation: strictly between `ρ'` and `2σᵢ - ‖c‖`, so that the
  -- closed support of the bump lies in the region where the chart matrix is non-degenerate.
  have hρ'pos : 0 < ρ' := lt_trans hρ hρ'
  let ρ'' : ℝ := (ρ' + (2 * D.σ i - ‖c‖)) / 2
  have hρ'lt : ρ' < ρ'' := by dsimp only [ρ'']; linarith
  have hρ''bd : ‖c‖ + ρ'' < 2 * D.σ i := by dsimp only [ρ'']; linarith
  -- The bump: `1` on the closed ball of radius `ρ'` around `c`, supported in the ball of
  -- radius `ρ''`.
  let χb : ContDiffBump c := ContDiffBump.mk ρ' ρ'' hρ'pos hρ'lt
  have hχrIn : χb.rIn = ρ' := rfl
  have hχrOut : χb.rOut = ρ'' := rfl
  have hχsm : ContDiff ℝ (⊤ : ℕ∞) (χb : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) := χb.contDiff
  have hχone : ∀ z : Fin (Module.finrank ℝ E) → ℝ, dist z c ≤ ρ' → (χb : _) z = 1 := by
    intro z hz
    exact χb.one_of_mem_closedBall (by rw [Metric.mem_closedBall, hχrIn]; exact hz)
  have hχtsup : tsupport (χb : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) ⊆
      Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i) := by
    intro z hz
    have hzd : dist z c ≤ ρ'' := by
      rw [χb.tsupport_eq, hχrOut, Metric.mem_closedBall] at hz; exact hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
      calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
    have h2 : ‖z - c‖ = dist z c := (dist_eq_norm z c).symm
    linarith
  -- The chart matrix, read in the flat coordinate of the chart at `x₀ i`.
  let A : (Fin (Module.finrank ℝ E) → ℝ) → Work.Diff.EXT.MatE (E := E) :=
    fun z => Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
  have hAsm : ContDiffOn ℝ (⊤ : ℕ∞) A
      (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i)) := by
    intro z hz
    have hz' : ‖z‖ < 2 * D.σ i := by rwa [Metric.mem_ball, dist_zero_right] at hz
    have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
      D.htarget i z (le_of_lt hz')
    have h1 := Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g₀ (D.x₀ i) hzt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.flatToE (I := I) (D.x₀ i)) z :=
      (Work.Diff.STE.contDiff_flatToE (I := I) (M := M) (D.x₀ i)).contDiffAt
    exact (h1.comp z h2).contDiffWithinAt
  have hsm1 : ContDiff ℝ (⊤ : ℕ∞) (fun z => (χb : _) z • A z) :=
    contDiff_smul_of_contDiffOn_tsupport hχsm hAsm Metric.isOpen_ball hχtsup
  -- The comparison matrix: the identity, written as a `MatE`.
  let M₀ : Work.Diff.EXT.MatE (E := E) := fun a b => if a = b then (1 : ℝ) else 0
  have hsm2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => (1 - (χb : _) z) • M₀) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ => 1 - (χb : _) z) :=
      contDiff_const.sub hχsm
    exact h1.smul contDiff_const
  -- The localised chart datum: the chart matrix near `c`, blended towards the identity away from
  -- it (so that it is non-degenerate everywhere).
  let bg : (Fin (Module.finrank ℝ E) → ℝ) → Work.Diff.EXT.MatE (E := E) :=
    fun z => (χb : _) z • A z + (1 - (χb : _) z) • M₀
  have hsmbg : ContDiff ℝ (⊤ : ℕ∞) bg := hsm1.add hsm2
  have hagree : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z - c‖ < ρ' →
      bg z = Work.Diff.STE.Man.flatChartMat (I := I) g₀ (D.x₀ i) z := by
    intro z hz
    have hχz : (χb : _) z = 1 := hχone z (by rw [dist_eq_norm]; exact le_of_lt hz)
    have hbgz : bg z = A z := by
      dsimp only [bg]
      rw [hχz, one_smul, sub_self, zero_smul, add_zero]
    rw [hbgz]
    simp only [A, Work.Diff.STE.Man.flatChartMat, Work.Diff.STE.Lead.flatToE_eq_chartCoordSymm]
  have hdet : ∀ z : Fin (Module.finrank ℝ E) → ℝ, (Matrix.of (bg z)).det ≠ 0 := by
    intro z
    by_cases hz0 : (χb : _) z = 0
    · -- outside the support of the bump the datum is the identity
      have hbgz : bg z = M₀ := by
        dsimp only [bg]
        rw [hz0, zero_smul, sub_zero, one_smul, zero_add]
      rw [hbgz]
      have hM : Matrix.of M₀ = (1 : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) := by
        ext a b
        simp only [Matrix.of_apply, Matrix.one_apply, M₀]
      rw [hM, Matrix.det_one]
      exact one_ne_zero
    · -- inside the support of the bump, the chart matrix is available
      have hzsup : z ∈ Metric.ball c ρ'' := by
        have h1 : z ∈ Function.support (χb : _) := by rw [Function.mem_support]; exact hz0
        rwa [χb.support_eq, hχrOut] at h1
      have hz2 : ‖z‖ < 2 * D.σ i := by
        rw [Metric.mem_ball] at hzsup
        have h1 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
          calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
            _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        have h2 : ‖z - c‖ = dist z c := (dist_eq_norm z c).symm
        linarith
      -- the quadratic form of the chart matrix is non-negative
      have hAPSD : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
          0 ≤ dotProduct v ((Matrix.of (A z)).mulVec v) := by
        intro v
        have hC := chartMatFun_quadForm_nonneg (I := I) (M := M) g₀ (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) v
        have hA' : A z = Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) := rfl
        rw [hA', ← Work.Diff.STE.flat.sum_sum_mul_eq_dotProduct_quadForm]
        simpa only [Matrix.of_apply] using hC
      by_cases hz1 : (χb : _) z = 1
      · -- the bump equals `1`: the datum is the chart matrix itself, which is invertible
        have hbgA : bg z = A z := by
          dsimp only [bg]
          rw [hz1, one_smul, sub_self, zero_smul, add_zero]
        rw [hbgA]
        have hA' : A z = Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) := rfl
        rw [hA']
        exact Work.Diff.EXT.chartMat_det_ne_zero (I := I) (M := M) g₀ (D.x₀ i)
          (D.htarget i z (le_of_lt hz2))
      · -- `0 < χb z < 1`: the datum is a convex combination of the chart matrix and the identity
        have hχle : (χb : _) z ≤ 1 := χb.le_one
        have hχnn : 0 ≤ (χb : _) z := χb.nonneg
        have hmat : Matrix.of (bg z) = (χb : _) z • Matrix.of (A z)
            + (1 - (χb : _) z) • (1 : Matrix (Fin (Module.finrank ℝ E))
              (Fin (Module.finrank ℝ E)) ℝ) := by
          ext a b
          simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
            bg, M₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hmat]
        exact det_ne_zero_smul_add_one_of_nonneg_quadForm (Matrix.of (A z)) hχnn
          (lt_of_le_of_ne hχle hz1) hAPSD
  refine ⟨bg, hsmbg, hagree, hdet, ?_⟩
  -- the chart nonlinearity of a smooth, everywhere non-degenerate chart matrix is smooth on the
  -- non-degeneracy region of its value jet
  rw [Work.Diff.STE.Man.chartNonlin_eq_secOpFlat_add_pNfull]
  exact (Work.Diff.STE.Man.contDiffOn_secOpFlat (E := E)).add
    (Work.Diff.STE.Man.contDiffOn_pNfull (E := E)
      (Work.Diff.STE.Man.contDiff_bgJet hsmbg) (fun x => hdet x))

end Work.Diff.STE.Lead
