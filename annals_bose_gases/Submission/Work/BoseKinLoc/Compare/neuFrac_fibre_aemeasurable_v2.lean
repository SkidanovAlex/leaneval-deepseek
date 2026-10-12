import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt
import Submission.Work.BoseKinLoc.Kinetic.continuous_fibre_sq_diff
import Submission.Work.BoseKinLoc.Kinetic.neuFrac_translate
import Submission.Work.BoseKinLoc.NeuFrac.bddBelow_trialSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Compare.neuFrac_fibre_aemeasurable_v2`

**The slot-`i` fibre of the box Neumann fraction `neuFrac` is a.e. strongly measurable in the
pair `(u, q₂)`** (the translation parameter `u = q.1` and the remaining coordinates `q.2`),
for a *smooth compactly supported* `Φ : X (n+1) → ℝ` — **without** any hypothesis that `Φ` be
supported in the box `abox (n+1) ℓ`.

## Strategy

`neuFrac ℓ a2 u ψ` is an `sInf` over the smooth compactly supported trials, so it is *not*
manifestly an integral; measurability is obtained from **continuity**, in three steps:

1. **Translation covariance** (`neuFrac_translate`): `neuFrac ℓ a2 u ψ = neuFrac ℓ a2 0 (ψ(ℓu+·))`,
   so only the fixed box `Λ(0) = acube ℓ` matters.
2. **Lipschitz estimate in the state** (`NeuFracV2.neuFrac_lipschitz_meas`): for measurable
   states with `∫_{acube ℓ} ψ² ≤ R²`, `∫_{acube ℓ} ψ'² ≤ R²` and globally square-integrable,
   `|neuFrac ℓ a2 0 ψ − neuFrac ℓ a2 0 ψ'| ≤ 6R √(∫_{acube ℓ}(ψ−ψ')²)`.
3. **Continuity of the fibre map**: `q ↦ ∫_{acube ℓ}(φ_q − φ_{q'})²` is continuous for the
   shifted fibres `φ_q = z ↦ Φ(kcInsN n i (ℓ q.1 + z, q.2))` (parametric integral on the
   compact cube, using only the continuity of `Φ`).

The uniform radius is `R = max 1 (M·ℓ·√ℓ)` with `M` a bound for `|Φ|` (available since `Φ` is
continuous with compact support): `∫_{acube ℓ} φ_q² ≤ M²·ℓ³ ≤ R²`.

The only difference from the v1 statement of the chapter
(`Work.BoseKinLoc.Kinetic.neuFrac_fibre_aemeasurable`) is that the bound on `Φ` and the
compact support / square-integrability of the fibres are derived from `HasCompactSupport Φ`
instead of `tsupport Φ ⊆ abox (n+1) ℓ`.

## The Lipschitz estimate (section 2)

`neuFrac ℓ a2 u ψ` is the `sInf` of the trial functional
`F ψ g = ∫_Λψ² − 2a²∫_Λψg + a²(Σ_k∫_Λ(∂_kg)² + a²∫_Λg²)` over smooth compactly supported
`g`, `Λ = lamBox ℓ u`.  Two ingredients:

* **ball reduction** (`sInf_ball_eq`): if `∫_Λψ² ≤ R²` then the `sInf` is unchanged when the
  trials are restricted to `∫_Λg² ≤ (2R/a²)²`, since for `a²‖g‖ > 2R ≥ 2‖ψ‖` one has
  `F ψ g − F ψ 0 ≥ a²‖g‖(a²‖g‖ − 2‖ψ‖) ≥ 0` (`big_g_helper`);
* **Lipschitz on the ball** (`trialVal_lipschitz_ball`): for trials in the ball,
  `|F ψ g − F ψ' g| ≤ (‖ψ+ψ'‖ + 2a²‖g‖)‖ψ−ψ'‖ ≤ (2R + 4R)‖ψ−ψ'‖ = 6R‖ψ−ψ'‖`
  by Cauchy–Schwarz (`abs_integral_mul_le_sqrt_mul_sqrt`).

Both infima are then taken over the *same* ball, giving the estimate (`sInf_ball_lipschitz`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Compare

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace NeuFracV2

open Submission.BoseGases

/-! ## 1. The shifted slot-`i` fibre and its analytic properties -/

/-- The slot-`i` fibre of `Φ` with the inserted variable translated by `ℓ • q.1`:
`z ↦ Φ (kcInsN n i (ℓ • q.1 + z, q.2))`.  By `neuFrac_translate` its Neumann fraction on the
*fixed* box `Λ(0) = acube ℓ` is `neuFrac ℓ a2 q.1 (z ↦ Φ (kcInsN n i (z, q.2)))`. -/
abbrev fibreState {n : ℕ} (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ) (ℓ : ℝ)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun z => Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))

/-- The shifted slot-`i` fibre is continuous. -/
lemma fibreState_continuous {ℓ : ℝ} {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    Continuous (fibreState i Φ ℓ q) := by
  have hins : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.kcInsN n i (z, q.2)) := by
    have h1 : (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kcInsN n i (z, q.2))
        = Function.update (Submission.BoseGases.kcInsN n i (0, q.2)) i := by
      funext z
      exact Submission.BoseGases.kcInsN_update_zero i z q.2
    rw [h1]
    have hupd : ContDiff ℝ (⊤ : ENat)
        (Function.update (Submission.BoseGases.kcInsN n i (0, q.2)) i) :=
      contDiff_update (⊤ : ENat) (Submission.BoseGases.kcInsN n i (0, q.2)) i
    exact hupd.continuous
  exact hΦ.continuous.comp (hins.comp (by fun_prop))

/-- A continuous compactly supported function on the configuration space is bounded. -/
lemma exists_bound_of_hasCompactSupport {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hcs : HasCompactSupport Φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M := by
  obtain ⟨K, hK, hKeq⟩ := exists_compact_iff_hasCompactSupport.mpr hcs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ K
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [hKeq x hx, abs_zero]
    exact le_max_right _ _

/-- The shifted slot-`i` fibre of an arbitrary smooth compactly supported state is compactly
supported: its support is contained in the ball of radius `D + |ℓ|·‖q.1‖`, where `D` bounds the
compact support of `Φ`. -/
lemma fibreState_hasCompactSupport {ℓ : ℝ} {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hcs : HasCompactSupport Φ)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    HasCompactSupport (fibreState i Φ ℓ q) := by
  obtain ⟨K, hK, hKeq⟩ := exists_compact_iff_hasCompactSupport.mpr hcs
  obtain ⟨D, hD⟩ := hK.isBounded.subset_closedBall (0 : Submission.BoseGases.X (n + 1))
  have hD' : ∀ x ∈ K, ‖x‖ ≤ D := by
    intro x hx
    have := hD hx
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (D + |ℓ| * ‖q.1‖)) ?_
  intro z hz
  have hzK : Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2) ∈ K := by
    by_contra hcon
    exact hz (hKeq _ hcon)
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖ℓ • q.1 + z‖ ≤ D := by
    have h2 := norm_le_pi_norm (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2)) i
    rw [Submission.BoseGases.kc_insN_apply_same] at h2
    exact le_trans h2 (hD' _ hzK)
  calc ‖z‖ = ‖(ℓ • q.1 + z) - ℓ • q.1‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖ℓ • q.1 + z‖ + ‖ℓ • q.1‖ := norm_sub_le _ _
    _ ≤ D + |ℓ| * ‖q.1‖ := by
        have hsm : ‖ℓ • q.1‖ = |ℓ| * ‖q.1‖ := by rw [norm_smul, Real.norm_eq_abs]
        linarith

/-- The square of the shifted slot-`i` fibre is integrable (continuous with compact support). -/
lemma fibreState_sq_integrable {ℓ : ℝ} {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hcs : HasCompactSupport Φ)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (fibreState i Φ ℓ q z) ^ 2) :=
  Continuous.integrable_of_hasCompactSupport ((fibreState_continuous i hΦ q).pow 2)
    ((fibreState_hasCompactSupport i hcs q).comp_left
      (g := fun t : ℝ => t ^ 2) (by norm_num))

/-- The square of the difference of two shifted slot-`i` fibres is integrable. -/
lemma fibreState_diff_sq_integrable {ℓ : ℝ} {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hcs : HasCompactSupport Φ)
    (q q' : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      (fibreState i Φ ℓ q z - fibreState i Φ ℓ q' z) ^ 2) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      fibreState i Φ ℓ q z - fibreState i Φ ℓ q' z) :=
    (fibreState_continuous i hΦ q).sub (fibreState_continuous i hΦ q')
  have hs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
      fibreState i Φ ℓ q z - fibreState i Φ ℓ q' z) :=
    (fibreState_hasCompactSupport i hcs q).sub (fibreState_hasCompactSupport i hcs q')
  exact Continuous.integrable_of_hasCompactSupport (hc.pow 2)
    (hs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))

/-- The `L²`-mass of the shifted slot-`i` fibre over the cube is at most `M²ℓ³`. -/
lemma integral_fibreState_sq_le {ℓ M : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hM : ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    ∫ z in Submission.BoseGases.acube ℓ, (fibreState i Φ ℓ q z) ^ 2 ≤ M ^ 2 * ℓ ^ 3 := by
  have hvol : (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.acube ℓ) ≠ ⊤ := by
    rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
    exact ENNReal.ofReal_lt_top.ne
  have hfint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (fibreState i Φ ℓ q z) ^ 2)
      (Submission.BoseGases.acube ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      ((fibreState_continuous i hΦ q).pow 2).continuousOn
  have hgint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => M ^ 2)
      (Submission.BoseGases.acube ℓ) volume := integrableOn_const hvol
  have hpoint : ∀ z ∈ Submission.BoseGases.acube ℓ,
      (fibreState i Φ ℓ q z) ^ 2 ≤ M ^ 2 := fun z _ => by
    have h := pow_le_pow_left₀ (abs_nonneg (fibreState i Φ ℓ q z)) (hM _) 2
    rwa [sq_abs] at h
  have hstep := MeasureTheory.setIntegral_mono_on hfint hgint
    (Submission.BoseGases.acube_measurable ℓ) hpoint
  have hconst : (∫ z in Submission.BoseGases.acube ℓ, M ^ 2 : ℝ) = M ^ 2 * ℓ ^ 3 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
      Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity),
      smul_eq_mul]
    ring
  linarith [hstep, hconst.le]

/-- The two-point fibre difference square
`(q, q') ↦ ∫_{acube ℓ} (Φ(kcInsN n i (ℓ q₁ + z, r₁)) − Φ(kcInsN n i (ℓ q₂ + z, r₂)))² dz`
is continuous.  (Same proof as `Work.BoseKinLoc.Kinetic.continuous_fibre_sq_diff`, from which
the support hypothesis is dropped: it is never used.) -/
theorem continuous_fibre_sq_diff_cs {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) =>
      ∫ z in Submission.BoseGases.acube ℓ,
        (Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1.1 + z, q.1.2))
          - Φ (Submission.BoseGases.kcInsN n i (ℓ • q.2.1 + z, q.2.2))) ^ 2) := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hins : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Submission.BoseGases.kcInsN n i p) := Work.BoseKinLoc.Kinetic.continuous_kcInsN_pair i
  have hmain : Continuous (Function.uncurry fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) =>
      fun z : EuclideanSpace ℝ (Fin 3) =>
        (Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1.1 + z, q.1.2))
          - Φ (Submission.BoseGases.kcInsN n i (ℓ • q.2.1 + z, q.2.2))) ^ 2) := by
    have h1 : Continuous (fun u : ((EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) × EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN n i (ℓ • u.1.1.1 + u.2, u.1.1.2))) :=
      hΦc.comp (hins.comp (by fun_prop))
    have h2 : Continuous (fun u : ((EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) × EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN n i (ℓ • u.1.2.1 + u.2, u.1.2.2))) :=
      hΦc.comp (hins.comp (by fun_prop))
    have h3 : Continuous (fun u : ((EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) × EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN n i (ℓ • u.1.1.1 + u.2, u.1.1.2))
          - Φ (Submission.BoseGases.kcInsN n i (ℓ • u.1.2.1 + u.2, u.1.2.2))) := h1.sub h2
    exact h3.pow 2
  simpa only [Function.uncurry] using
    continuous_parametric_integral_of_continuous
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      hmain (Submission.BoseGases.acube_compact hℓ)

/-! ## 2. The Lipschitz estimate for `neuFrac` at the anchored box -/

/-- The full set of trial values of `neuFrac`. -/
def allTrials (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (φ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Set ℝ :=
  {y | ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      y = Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u φ g}

/-- The trial values restricted to the `L²`-ball of radius `M`. -/
def ballTrials (ℓ a2 M : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) : Set ℝ :=
  {y | ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) ≤ M ^ 2 ∧
      y = Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u φ g}

/-- `neuFrac` is by definition the `sInf` of the trial values. -/
lemma neuFrac_eq_sInf_all (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.neuFrac ℓ a2 u φ = sInf (allTrials ℓ a2 u φ) := rfl

/-- **Trials outside the ball never lower the infimum.**  If `∫_Λψ² ≤ R²` and `∫_Λg² > (2R/a²)²`
then `F ψ 0 ≤ F ψ g`, where `F` is the `neuFrac` trial functional. -/
lemma big_g_helper {ℓ a2 R : ℝ} (hR : 0 ≤ R) (ha2 : 0 < a2) (u : ℝ³)
    {ψ g : ℝ³ → ℝ} (hψ : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z) ^ 2))
    (hψm : Measurable ψ) (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g)
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2)
    (hM2 : (2 * R / a2) ^ 2 < ∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) :
    Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ 0
      ≤ Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g := by
  have hV0 : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ 0
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 := by
    unfold Work.BoseKinLoc.NeuFrac.neuFracTrialVal; simp
  have hVg : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g
      = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * g z)
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
              (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)) := rfl
  rw [hV0, hVg]
  set Λ := Work.BoseKinLoc.lamBox ℓ u with hΛdef
  set W := ∫ z in Λ, (ψ z) ^ 2 with hWdef
  set G := ∫ z in Λ, (g z) ^ 2 with hGdef
  set P := ∫ z in Λ, ψ z * g z with hPdef
  set K := ∑ k : Fin 3, ∫ z in Λ,
    (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _
  have hCS : |P| ≤ Real.sqrt W * Real.sqrt G := by
    rw [hPdef, hWdef, hGdef]
    refine Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt ?_ ?_
    · refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
      · exact hψm.aestronglyMeasurable.restrict
      · exact hψ.integrableOn
    · refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
      · exact hg.continuous.aestronglyMeasurable.restrict
      · exact Work.BoseKinLoc.NeuFrac.integrableOn_sq_of_contDiff hg hgs u
  have hGnn : 0 ≤ G := hGdef ▸ integral_nonneg fun z => sq_nonneg _
  have hsqrtW : Real.sqrt W ≤ R := by
    rw [← Real.sqrt_sq hR]
    exact Real.sqrt_le_sqrt (by rw [hWdef]; exact hRψ)
  have hlt : 2 * R / a2 < Real.sqrt G := by
    have hnn : 0 ≤ 2 * R / a2 := by positivity
    rw [← Real.sqrt_sq hnn]
    exact Real.sqrt_lt_sqrt (by positivity) (by rw [hGdef]; exact hM2)
  have ha2sqrtG : 2 * R < a2 * Real.sqrt G := by
    have := mul_lt_mul_of_pos_left hlt ha2
    rwa [mul_div_cancel₀ (2 * R) (ne_of_gt ha2)] at this
  have h2sqrtW : 2 * Real.sqrt W ≤ a2 * Real.sqrt G := by linarith
  have hPG : 2 * a2 * P ≤ a2 ^ 2 * G := by
    have hPle : P ≤ Real.sqrt W * Real.sqrt G := le_trans (le_abs_self P) hCS
    have hstep : 2 * a2 * P ≤ 2 * a2 * (Real.sqrt W * Real.sqrt G) :=
      mul_le_mul_of_nonneg_left hPle (by positivity)
    have hposG : 0 ≤ a2 * Real.sqrt G := mul_nonneg ha2.le (Real.sqrt_nonneg _)
    have hstep2 : 2 * a2 * (Real.sqrt W * Real.sqrt G) ≤ a2 ^ 2 * G := by
      have h := mul_le_mul_of_nonneg_right h2sqrtW hposG
      have e1 : (2 * Real.sqrt W) * (a2 * Real.sqrt G)
          = 2 * a2 * (Real.sqrt W * Real.sqrt G) := by ring
      have e2 : (a2 * Real.sqrt G) * (a2 * Real.sqrt G) = a2 ^ 2 * G := by
        rw [mul_mul_mul_comm, Real.mul_self_sqrt hGnn]; ring
      nlinarith [h, e1, e2]
    linarith
  linarith [hKnn, hPG, mul_nonneg ha2.le hKnn]

/-- **The ball reduction**: for `∫_Λψ² ≤ R²`, restricting the trials of `neuFrac` to the `L²`-ball
of radius `2R/a²` does not change the `sInf`. -/
lemma sInf_ball_eq {ℓ a2 R : ℝ} (hR : 0 ≤ R) (ha2 : 0 < a2) (u : ℝ³)
    {ψ : ℝ³ → ℝ} (hψ : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z) ^ 2))
    (hψm : Measurable ψ)
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2) :
    sInf (allTrials ℓ a2 u ψ) = sInf (ballTrials ℓ a2 (2 * R / a2) u ψ) := by
  have hTbdd : BddBelow (allTrials ℓ a2 u ψ) :=
    Work.BoseKinLoc.NeuFrac.bddBelow_trialSet ha2.le u hψ
  have hTne : (allTrials ℓ a2 u ψ).Nonempty :=
    ⟨_, 0, contDiff_const, HasCompactSupport.zero, rfl⟩
  have hBne : (ballTrials ℓ a2 (2 * R / a2) u ψ).Nonempty :=
    ⟨_, 0, contDiff_const, HasCompactSupport.zero, by
      show (∫ z in Work.BoseKinLoc.lamBox ℓ u, (0 : ℝ³ → ℝ) z ^ 2) ≤ (2 * R / a2) ^ 2
      simp only [Pi.zero_apply, sq, mul_zero, integral_zero]
      positivity, rfl⟩
  have hBsub : ballTrials ℓ a2 (2 * R / a2) u ψ ⊆ allTrials ℓ a2 u ψ := by
    rintro y ⟨g, hd, hcs, _, rfl⟩
    exact ⟨g, hd, hcs, rfl⟩
  have hBbdd : BddBelow (ballTrials ℓ a2 (2 * R / a2) u ψ) := hTbdd.mono hBsub
  refine le_antisymm (csInf_le_csInf hTbdd hBne hBsub) ?_
  refine le_csInf hTne fun y hy => ?_
  obtain ⟨g, hd, hcs, rfl⟩ := hy
  by_cases hle : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) ≤ (2 * R / a2) ^ 2
  · exact csInf_le hBbdd ⟨g, hd, hcs, hle, rfl⟩
  · push_neg at hle
    have hmem : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ 0
        ∈ ballTrials ℓ a2 (2 * R / a2) u ψ :=
      ⟨0, contDiff_const, HasCompactSupport.zero, by
        show (∫ z in Work.BoseKinLoc.lamBox ℓ u, (0 : ℝ³ → ℝ) z ^ 2) ≤ (2 * R / a2) ^ 2
        simp only [Pi.zero_apply, sq, mul_zero, integral_zero]
        positivity, rfl⟩
    exact le_trans (csInf_le hBbdd hmem) (big_g_helper hR ha2 u hψ hψm hd hcs hRψ hle)

/-- **Lipschitz estimate on the trial ball**: for trials with `∫_Λg² ≤ (2R/a²)²`,
`|F ψ g − F ψ' g| ≤ 6R√(∫_Λ(ψ−ψ')²)`. -/
lemma trialVal_lipschitz_ball {ℓ a2 R : ℝ} (hR : 0 ≤ R) (ha2 : 0 < a2) (u : ℝ³)
    {ψ ψ' : ℝ³ → ℝ} (hψm : Measurable ψ) (hψ'm : Measurable ψ')
    (hψ : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z) ^ 2))
    (hψ' : MeasureTheory.Integrable (fun z : ℝ³ => (ψ' z) ^ 2))
    (hψd : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z - ψ' z) ^ 2))
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2)
    (hRψ' : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2 ≤ R ^ 2)
    {g : ℝ³ → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g)
    (hgb : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2 ≤ (2 * R / a2) ^ 2) :
    |Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g
        - Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g|
      ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
  set Λ := Work.BoseKinLoc.lamBox ℓ u with hΛ
  set D := ∫ z in Λ, (ψ z - ψ' z) ^ 2 with hD
  set S := ∫ z in Λ, (ψ z + ψ' z) ^ 2 with hS
  set G2 := ∫ z in Λ, (g z) ^ 2 with hG2
  set W := ∫ z in Λ, (ψ z) ^ 2 with hW
  set W' := ∫ z in Λ, (ψ' z) ^ 2 with hW'
  set P := ∫ z in Λ, ψ z * g z with hP
  set P' := ∫ z in Λ, ψ' z * g z with hP'
  set K := ∑ k : Fin 3, ∫ z in Λ,
    (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 with hK
  have hmm : Measurable (fun z => ψ z - ψ' z) := hψm.sub hψ'm
  have hpm : Measurable (fun z => ψ z + ψ' z) := hψm.add hψ'm
  have hψΛ : Integrable (fun z => (ψ z) ^ 2) (volume.restrict Λ) := hψ.integrableOn
  have hψ'Λ : Integrable (fun z => (ψ' z) ^ 2) (volume.restrict Λ) := hψ'.integrableOn
  have hψdΛ : Integrable (fun z => (ψ z - ψ' z) ^ 2) (volume.restrict Λ) := hψd.integrableOn
  have hg2Λ : Integrable (fun z => (g z) ^ 2) (volume.restrict Λ) :=
    Work.BoseKinLoc.NeuFrac.integrableOn_sq_of_contDiff hg hgs u
  have hSint : Integrable (fun z => (ψ z + ψ' z) ^ 2) (volume.restrict Λ) := by
    have hb : Integrable (fun z => 2 * (ψ z) ^ 2 + 2 * (ψ' z) ^ 2) (volume.restrict Λ) :=
      (hψΛ.const_mul 2).add (hψ'Λ.const_mul 2)
    refine hb.mono' (hpm.pow_const 2).aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (ψ z - ψ' z)]
  have hψgΛ : Integrable (fun z => ψ z * g z) (volume.restrict Λ) := by
    have hb : Integrable (fun z => (ψ z) ^ 2 / 2 + (g z) ^ 2 / 2) (volume.restrict Λ) :=
      (hψΛ.div_const 2).add (hg2Λ.div_const 2)
    refine hb.mono' ((hψm.mul hg.continuous.measurable).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|ψ z| - |g z|), sq_abs (ψ z), sq_abs (g z)]
  have hψ'gΛ : Integrable (fun z => ψ' z * g z) (volume.restrict Λ) := by
    have hb : Integrable (fun z => (ψ' z) ^ 2 / 2 + (g z) ^ 2 / 2) (volume.restrict Λ) :=
      (hψ'Λ.div_const 2).add (hg2Λ.div_const 2)
    refine hb.mono' ((hψ'm.mul hg.continuous.measurable).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|ψ' z| - |g z|), sq_abs (ψ' z), sq_abs (g z)]
  have hWbound : |W - W'| ≤ Real.sqrt D * Real.sqrt S := by
    have hsplit : W - W' = ∫ z in Λ, (ψ z - ψ' z) * (ψ z + ψ' z) := by
      rw [hW, hW', ← MeasureTheory.integral_sub hψΛ hψ'Λ]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    rw [hsplit]
    refine Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt ?_ ?_
    · exact (MeasureTheory.memLp_two_iff_integrable_sq hmm.aestronglyMeasurable.restrict).mpr hψdΛ
    · exact (MeasureTheory.memLp_two_iff_integrable_sq hpm.aestronglyMeasurable.restrict).mpr hSint
  have hPbound : |P - P'| ≤ Real.sqrt D * Real.sqrt G2 := by
    have hsplit : P - P' = ∫ z in Λ, (ψ z - ψ' z) * g z := by
      rw [hP, hP', ← MeasureTheory.integral_sub hψgΛ hψ'gΛ]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    rw [hsplit]
    refine Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt ?_ ?_
    · exact (MeasureTheory.memLp_two_iff_integrable_sq hmm.aestronglyMeasurable.restrict).mpr hψdΛ
    · exact (MeasureTheory.memLp_two_iff_integrable_sq
        hg.continuous.aestronglyMeasurable.restrict).mpr hg2Λ
  have hSle : Real.sqrt S ≤ 2 * R := by
    have hmono : S ≤ 2 * W + 2 * W' := by
      have hb : Integrable (fun z => 2 * (ψ z) ^ 2 + 2 * (ψ' z) ^ 2) (volume.restrict Λ) :=
        (hψΛ.const_mul 2).add (hψ'Λ.const_mul 2)
      have hmono0 := MeasureTheory.setIntegral_mono_on hSint hb
        (Work.BoseKinLoc.NeuFrac.measurableSet_lamBox ℓ u)
        (fun z _ => by nlinarith [sq_nonneg (ψ z - ψ' z)])
      have hsp : (∫ z in Λ, (2 * (ψ z) ^ 2 + 2 * (ψ' z) ^ 2)) = 2 * W + 2 * W' := by
        rw [MeasureTheory.integral_add (hψΛ.const_mul 2) (hψ'Λ.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hW, hW']
      rw [hS]; linarith [hmono0, hsp.le, hsp.ge]
    have : S ≤ 4 * R ^ 2 := by linarith [hmono, hRψ, hRψ']
    calc Real.sqrt S ≤ Real.sqrt (4 * R ^ 2) := Real.sqrt_le_sqrt this
      _ = 2 * R := by
          rw [show (4 : ℝ) * R ^ 2 = (2 * R) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have hG2le : Real.sqrt G2 ≤ 2 * R / a2 := by
    have hnn : 0 ≤ 2 * R / a2 := by positivity
    calc Real.sqrt G2 ≤ Real.sqrt ((2 * R / a2) ^ 2) := Real.sqrt_le_sqrt (by rw [hG2]; exact hgb)
      _ = 2 * R / a2 := by rw [Real.sqrt_sq hnn]
  have hVg : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g
      = W - 2 * a2 * P + a2 * (K + a2 * G2) := rfl
  have hVg' : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g
      = W' - 2 * a2 * P' + a2 * (K + a2 * G2) := rfl
  rw [hVg, hVg']
  have hrew : W - 2 * a2 * P + a2 * (K + a2 * G2) - (W' - 2 * a2 * P' + a2 * (K + a2 * G2))
      = (W - W') - 2 * a2 * (P - P') := by ring
  rw [hrew]
  have hB : |2 * a2 * (P - P')| = 2 * a2 * |P - P'| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a2)]
  have hstep1 : |(W - W') - 2 * a2 * (P - P')| ≤ |W - W'| + 2 * a2 * |P - P'| := by
    calc |(W - W') - 2 * a2 * (P - P')| ≤ |W - W'| + |2 * a2 * (P - P')| := abs_sub _ _
      _ = |W - W'| + 2 * a2 * |P - P'| := by rw [hB]
  have hstep2 : |W - W'| + 2 * a2 * |P - P'|
      ≤ Real.sqrt D * Real.sqrt S + 2 * a2 * (Real.sqrt D * Real.sqrt G2) := by
    have := mul_le_mul_of_nonneg_left hPbound (by positivity : (0 : ℝ) ≤ 2 * a2)
    linarith [hWbound, this]
  have hC : Real.sqrt D * Real.sqrt S + 2 * a2 * (Real.sqrt D * Real.sqrt G2)
      ≤ 6 * R * Real.sqrt D := by
    have h1 : Real.sqrt D * Real.sqrt S ≤ Real.sqrt D * (2 * R) :=
      mul_le_mul_of_nonneg_left hSle (Real.sqrt_nonneg D)
    have h2 : Real.sqrt D * Real.sqrt G2 ≤ Real.sqrt D * (2 * R / a2) :=
      mul_le_mul_of_nonneg_left hG2le (Real.sqrt_nonneg D)
    have h2' : 2 * a2 * (Real.sqrt D * Real.sqrt G2)
        ≤ 2 * a2 * (Real.sqrt D * (2 * R / a2)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h3 : 2 * a2 * (Real.sqrt D * (2 * R / a2)) = 4 * R * Real.sqrt D := by
      field_simp; ring
    linarith [h1, h2', h3]
  linarith [hstep1, hstep2, hC]

/-- **Lipschitz estimate for the `sInf` over the common trial ball.** -/
lemma sInf_ball_lipschitz {ℓ a2 R : ℝ} (hR : 0 ≤ R) (ha2 : 0 < a2) (u : ℝ³)
    {ψ ψ' : ℝ³ → ℝ} (hψm : Measurable ψ) (hψ'm : Measurable ψ')
    (hψ : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z) ^ 2))
    (hψ' : MeasureTheory.Integrable (fun z : ℝ³ => (ψ' z) ^ 2))
    (hψd : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z - ψ' z) ^ 2))
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2)
    (hRψ' : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2 ≤ R ^ 2) :
    |sInf (ballTrials ℓ a2 (2 * R / a2) u ψ) - sInf (ballTrials ℓ a2 (2 * R / a2) u ψ')|
      ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
  set ε := 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) with hε
  have hsub : ballTrials ℓ a2 (2 * R / a2) u ψ ⊆ allTrials ℓ a2 u ψ := by
    rintro y ⟨g, hd, hcs, _, rfl⟩; exact ⟨g, hd, hcs, rfl⟩
  have hsub' : ballTrials ℓ a2 (2 * R / a2) u ψ' ⊆ allTrials ℓ a2 u ψ' := by
    rintro y ⟨g, hd, hcs, _, rfl⟩; exact ⟨g, hd, hcs, rfl⟩
  have hBbdd : BddBelow (ballTrials ℓ a2 (2 * R / a2) u ψ) :=
    (Work.BoseKinLoc.NeuFrac.bddBelow_trialSet ha2.le u hψ).mono hsub
  have hBbdd' : BddBelow (ballTrials ℓ a2 (2 * R / a2) u ψ') :=
    (Work.BoseKinLoc.NeuFrac.bddBelow_trialSet ha2.le u hψ').mono hsub'
  have hBne : (ballTrials ℓ a2 (2 * R / a2) u ψ).Nonempty :=
    ⟨_, 0, contDiff_const, HasCompactSupport.zero, by
      show (∫ z in Work.BoseKinLoc.lamBox ℓ u, (0 : ℝ³ → ℝ) z ^ 2) ≤ (2 * R / a2) ^ 2
      simp only [Pi.zero_apply, sq, mul_zero, integral_zero]
      positivity, rfl⟩
  have hBne' : (ballTrials ℓ a2 (2 * R / a2) u ψ').Nonempty :=
    ⟨_, 0, contDiff_const, HasCompactSupport.zero, by
      show (∫ z in Work.BoseKinLoc.lamBox ℓ u, (0 : ℝ³ → ℝ) z ^ 2) ≤ (2 * R / a2) ^ 2
      simp only [Pi.zero_apply, sq, mul_zero, integral_zero]
      positivity, rfl⟩
  have hdir1 : sInf (ballTrials ℓ a2 (2 * R / a2) u ψ) - ε
      ≤ sInf (ballTrials ℓ a2 (2 * R / a2) u ψ') := by
    refine le_csInf hBne' (fun y' hy' => ?_)
    obtain ⟨g, hd, hcs, hgb, rfl⟩ := hy'
    have hmem : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g
        ∈ ballTrials ℓ a2 (2 * R / a2) u ψ := ⟨g, hd, hcs, hgb, rfl⟩
    have h1 : sInf (ballTrials ℓ a2 (2 * R / a2) u ψ)
        ≤ Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g := csInf_le hBbdd hmem
    have h2 : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g
        - Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g ≤ ε := by
      have h3 := trialVal_lipschitz_ball hR ha2 u hψm hψ'm hψ hψ' hψd hRψ hRψ' hd hcs hgb
      rw [hε]
      linarith [le_abs_self (Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g
        - Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g), h3]
    linarith
  have hdir2 : sInf (ballTrials ℓ a2 (2 * R / a2) u ψ') - ε
      ≤ sInf (ballTrials ℓ a2 (2 * R / a2) u ψ) := by
    refine le_csInf hBne (fun y' hy' => ?_)
    obtain ⟨g, hd, hcs, hgb, rfl⟩ := hy'
    have hmem : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g
        ∈ ballTrials ℓ a2 (2 * R / a2) u ψ' := ⟨g, hd, hcs, hgb, rfl⟩
    have h1 : sInf (ballTrials ℓ a2 (2 * R / a2) u ψ')
        ≤ Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g := csInf_le hBbdd' hmem
    have h2 : Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g
        - Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g ≤ ε := by
      have h3 := trialVal_lipschitz_ball hR ha2 u hψm hψ'm hψ hψ' hψd hRψ hRψ' hd hcs hgb
      have h4 : |Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g
            - Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g|
          ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
        rw [abs_sub_comm]; exact h3
      rw [hε]
      linarith [le_abs_self (Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ' g
        - Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g), h4]
    linarith
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Lipschitz continuity of `neuFrac` in the state.**  For measurable states with
`∫_Λψ² ≤ R²`, `∫_Λψ'² ≤ R²` and globally square-integrable,
`|neuFrac ℓ a² u ψ − neuFrac ℓ a² u ψ'| ≤ 6R√(∫_Λ(ψ−ψ')²)`, `Λ = lamBox ℓ u`. -/
theorem neuFrac_lipschitz_meas {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    (u : ℝ³) {ψ ψ' : ℝ³ → ℝ}
    (hψm : Measurable ψ) (hψ'm : Measurable ψ')
    (hψ : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z) ^ 2))
    (hψ' : MeasureTheory.Integrable (fun z : ℝ³ => (ψ' z) ^ 2))
    (hψd : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z - ψ' z) ^ 2))
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2)
    (hRψ' : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2 ≤ R ^ 2) :
    |Work.BoseKinLoc.neuFrac ℓ a2 u ψ - Work.BoseKinLoc.neuFrac ℓ a2 u ψ'|
      ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
  rw [neuFrac_eq_sInf_all, neuFrac_eq_sInf_all,
    sInf_ball_eq hR.le ha2 u hψ hψm hRψ, sInf_ball_eq hR.le ha2 u hψ' hψ'm hRψ']
  exact sInf_ball_lipschitz hR.le ha2 u hψm hψ'm hψ hψ' hψd hRψ hRψ'

end NeuFracV2

/-! ## 3. The main theorem -/

open NeuFracV2 in
/-- The slot-`i` fibre of the box Neumann fraction is a.e. strongly measurable in the pair
`(u, q₂)`, for a smooth compactly supported `Φ`. -/
theorem neuFrac_fibre_aemeasurable_v2 {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hcs : HasCompactSupport Φ) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ a2 q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) := by
  -- a global bound on `Φ`
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_hasCompactSupport hΦ hcs
  -- the uniform radius
  set R : ℝ := max 1 (M * ℓ * Real.sqrt ℓ) with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hRsq : M ^ 2 * ℓ ^ 3 ≤ R ^ 2 := by
    have h1 : M * ℓ * Real.sqrt ℓ ≤ R := le_max_right _ _
    have h2 : 0 ≤ M * ℓ * Real.sqrt ℓ := mul_nonneg (mul_nonneg hM0 hℓ.le) (Real.sqrt_nonneg _)
    have h3 : (M * ℓ * Real.sqrt ℓ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h2 h1 2
    have h4 : (M * ℓ * Real.sqrt ℓ) ^ 2 = M ^ 2 * ℓ ^ 3 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hℓ.le]
      ring
    rwa [h4] at h3
  -- the uniform `L²` bound on the cube
  have hbox : ∀ q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
      ∫ z in Submission.BoseGases.acube ℓ, (fibreState i Φ ℓ q z) ^ 2 ≤ R ^ 2 :=
    fun q => le_trans (integral_fibreState_sq_le (M := M) hℓ i hΦ hM q) hRsq
  -- the Lipschitz estimate on the fixed box
  have hlip : ∀ q q' : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
      |Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q)
          - Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q')|
        ≤ 6 * R * Real.sqrt (∫ z in Submission.BoseGases.acube ℓ,
            (fibreState i Φ ℓ q z - fibreState i Φ ℓ q' z) ^ 2) := by
    intro q q'
    have h := neuFrac_lipschitz_meas hℓ ha2 hRpos (0 : EuclideanSpace ℝ (Fin 3))
      (fibreState_continuous i hΦ q).measurable (fibreState_continuous i hΦ q').measurable
      (fibreState_sq_integrable i hΦ hcs q)
      (fibreState_sq_integrable i hΦ hcs q')
      (fibreState_diff_sq_integrable i hΦ hcs q q')
      (by rw [Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube]; exact hbox q)
      (by rw [Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube]; exact hbox q')
    rwa [Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube] at h
  -- continuity of the squared difference integral
  have hG : Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) =>
      ∫ z in Submission.BoseGases.acube ℓ,
        (fibreState i Φ ℓ q.1 z - fibreState i Φ ℓ q.2 z) ^ 2) :=
    continuous_fibre_sq_diff_cs hℓ hΦ i
  -- continuity of the normalized Neumann fraction
  have hcont : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q)) := by
    rw [continuous_iff_continuousAt]
    intro q₀
    show Tendsto (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q)) (𝓝 q₀)
      (𝓝 (Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q₀)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        ∫ z in Submission.BoseGases.acube ℓ,
          (fibreState i Φ ℓ q z - fibreState i Φ ℓ q₀ z) ^ 2) (𝓝 q₀) (𝓝 0) := by
      have h1 : Tendsto (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          (q, q₀)) (𝓝 q₀) (𝓝 (q₀, q₀)) :=
        Filter.Tendsto.prodMk_nhds tendsto_id tendsto_const_nhds
      have h2 := (hG.continuousAt).tendsto.comp h1
      have hzero : (∫ z in Submission.BoseGases.acube ℓ,
            (fibreState i Φ ℓ (q₀, q₀).1 z - fibreState i Φ ℓ (q₀, q₀).2 z) ^ 2) = 0 := by
        simp
      rwa [hzero] at h2
    refine squeeze_zero
      (f := fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        ‖Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q)
          - Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q₀)‖)
      (g := fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        6 * R * Real.sqrt (∫ z in Submission.BoseGases.acube ℓ,
          (fibreState i Φ ℓ q z - fibreState i Φ ℓ q₀ z) ^ 2))
      (fun q => norm_nonneg _) (fun q => ?_) ?_
    · simpa [Real.norm_eq_abs] using hlip q q₀
    · have hfin := (hlim.sqrt).const_mul (6 * R)
      simpa using hfin
  -- assemble
  have hAE : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :=
    hcont.aestronglyMeasurable
  refine hAE.congr (Filter.Eventually.of_forall (fun q => ?_))
  exact (Work.BoseKinLoc.Kinetic.neuFrac_translate ℓ a2 q.1
    (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, q.2)))).symm

end Work.BoseKinLoc.Compare
