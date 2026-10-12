import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.chiCubeBump
import Submission.Work.BoseFixB1S.win.chiSmallB_windowIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.chiCubeB_windowIntegrable`

`q`-integrability of the two genuine windowed mode contents of the sliding small box
`A = dlBox ℓ d u` at the **smooth cube** window `χ = chiCubeB M ℓ d u` (`chiCubeBump.lean`,
decision (B) of the lead):

    Integrable (q ↦ boxWinModePGen ℓ |A| A χ Ψ q) ∧ Integrable (q ↦ boxWinModeRGen ℓ |A| A χ Ψ q).

This is the `chiSmallB ↦ chiCubeB` **name swap** of
`Work.BoseFixB1S.win.chiSmallB_windowIntegrable`, whose proof already isolates the two analytic
engines in a form that needs only `ContDiff ℝ 3` (resp. `Continuous`) for the window:

* `Work.BoseFixB1S.win.boxWinModePGen_integrable_three` — the P-half;
* `Work.BoseFixB1S.win.boxWinModeRGen_integrable_three` — the R-half;

so the whole content of the swap is the three window facts `ContDiff ℝ 3 χ`, `HasCompactSupport χ`
and `χ = 0` off `dlBox ℓ d u`.  The first is `chiCubeB_contDiff` (`chiCubeBump.lean`); the other
two are the geometry of the *cube* bump, which is re-derived here (`private`) rather than imported,
so that this module's cone is exactly `chiCubeBump` + the `chiSmallB` engine:

* `chiCubeScale_ofLp_abs_lt_half` — `chiCubeScale ℓ x ≠ 0` forces `|x_j| < ℓ/2` (the cube bump is
  flat at `‖z‖_∞ = 1/2`, so there is no ball cut — this is what `chiSmallB` cannot give);
* `chiCubeB_mem_dlBox` — both factors nonvanishing puts `x` in `acube ℓ ∩ (acube (ℓd) + (ℓd)u)`;
* `chiCubeB_hasCompactSupport` — the support is a coordinate box, hence bounded.

The hypotheses `d ≤ 1` and `5 ≤ M` of the statement are carried for compatibility with the
`chiSmallB` statements and are not used (the cube bump is `C^∞` and its support drops out of the
*first* factor alone, so any `M`, any `d`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The geometry of the cube bump -/

/-- **Coordinatewise consequence of the first factor not vanishing**: if `chiCubeScale ℓ x ≠ 0`,
then every coordinate of `x` satisfies `|x_j| < ℓ/2`.  `chiCubeScale ℓ z = chiCubeBase (ℓ⁻¹ • z)`
and `chiCubeBase` vanishes once a coordinate reaches `1/2`. -/
private lemma chiCubeScale_ofLp_abs_lt_half {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : chiCubeScale ℓ x ≠ 0) (j : Fin 3) : |x.ofLp j| < ℓ / 2 := by
  have hb : chiCubeBase ((ℓ⁻¹ : ℝ) • x) ≠ 0 := hx
  have hhalf : |(((ℓ⁻¹ : ℝ) • x)).ofLp j| < 1 / 2 := by
    by_contra hc
    rw [not_lt] at hc
    refine hb ?_
    fin_cases j
    · exact chiCubeBase_eq_zero_of_half_le _ (Or.inl hc)
    · exact chiCubeBase_eq_zero_of_half_le _ (Or.inr (Or.inl hc))
    · exact chiCubeBase_eq_zero_of_half_le _ (Or.inr (Or.inr hc))
  have hsm : (((ℓ⁻¹ : ℝ) • x)).ofLp j = ℓ⁻¹ * x.ofLp j := by simp
  rw [hsm, abs_mul, abs_of_pos (inv_pos.mpr hℓ)] at hhalf
  have h := mul_lt_mul_of_pos_left hhalf hℓ
  have hsplit : ℓ * (ℓ⁻¹ * |x.ofLp j|) = |x.ofLp j| := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ), one_mul]
  rw [hsplit] at h
  linarith

/-- **The smooth cube window is supported in the sliding box** `dlBox ℓ d u`: both factors of
`chiCubeB M ℓ d u` are cube bumps, so nonvanishing is exactly
`x ∈ acube ℓ ∩ (acube (ℓd) + (ℓd)•u)`.  (The `chiSmallB` twin of this statement is
`chiSmallB_support_mem_dlBox`; there the first factor alone already needs the `ℓ`-ball cut.) -/
private lemma chiCubeB_mem_dlBox {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u x : E3}
    (hx : chiCubeB M ℓ d u x ≠ 0) : x ∈ Submission.BoseGases.dlBox ℓ d u := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have h1 : chiCubeScale ℓ x ≠ 0 := fun h => hx (by rw [chiCubeB, h, zero_mul])
  have h2 : chiCubeScale (ℓ * d) (x - (ℓ * d) • u) ≠ 0 :=
    fun h => hx (by rw [chiCubeB, h, mul_zero])
  rw [Submission.BoseGases.mem_dlBox_iff]
  refine ⟨?_, ?_⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro m
    rw [Set.mem_Icc]
    have hb := chiCubeScale_ofLp_abs_lt_half hℓ h1 m
    obtain ⟨ha, hb⟩ := abs_le.mp (le_of_lt hb)
    exact ⟨by linarith, by linarith⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro m
    rw [Set.mem_Icc]
    have hb := chiCubeScale_ofLp_abs_lt_half hℓd h2 m
    obtain ⟨ha, hb⟩ := abs_le.mp (le_of_lt hb)
    exact ⟨by linarith, by linarith⟩

/-- **`chiCubeB M ℓ d u` has compact support for `0 < ℓ`** — the support lies in the coordinate box
`{z | ∀ j, |z_j| ≤ ℓ/2}` (first factor only, so no hypothesis on `d` is needed), which sits in the
closed ball of radius `√3·ℓ/2`. -/
private lemma chiCubeB_hasCompactSupport {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    HasCompactSupport (chiCubeB M ℓ d u) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : E3) (Real.sqrt 3 * (ℓ / 2))) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hz1 : chiCubeScale ℓ z ≠ 0 := fun h => hz (by rw [chiCubeB, h, zero_mul])
  have hcoord : ∀ j : Fin 3, |z.ofLp j| ≤ ℓ / 2 := fun j =>
    le_of_lt (chiCubeScale_ofLp_abs_lt_half hℓ hz1 j)
  have hsq : ‖z‖ ^ 2 = ∑ j : Fin 3, |z.ofLp j| ^ 2 := by
    simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) z)
  have hsum : (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ 3 * (ℓ / 2) ^ 2 := by
    calc (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ ∑ _j : Fin 3, (ℓ / 2) ^ 2 :=
          Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2)
      _ = 3 * (ℓ / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hfin : ‖z‖ ^ 2 ≤ (Real.sqrt 3 * (ℓ / 2)) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    exact hsum
  calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
    _ ≤ Real.sqrt ((Real.sqrt 3 * (ℓ / 2)) ^ 2) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt 3 * (ℓ / 2) := Real.sqrt_sq (by positivity)

/-! ## 2. The target -/

theorem chiCubeB_windowIntegrable {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {M : ℕ} (hM : 5 ≤ M) (u : EuclideanSpace ℝ (Fin 3))
    (hVpos : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.boxWinModePGen ℓ
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        (Work.BoseFixB1B.chiCubeB M ℓ d u) Ψ q) ∧
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.boxWinModeRGen ℓ
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        (Work.BoseFixB1B.chiCubeB M ℓ d u) Ψ q) := by
  have hAcm : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAcsub : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvol : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u, MeasureTheory.Measure.real_def]
  have hχc3 : ContDiff ℝ 3 (chiCubeB M ℓ d u) :=
    (chiCubeB_contDiff M ℓ d u).of_le (WithTop.coe_le_coe.mpr le_top)
  have hχs : HasCompactSupport (chiCubeB M ℓ d u) := chiCubeB_hasCompactSupport hℓ u
  have hχsupp : ∀ z, z ∉ Submission.BoseGases.dlBox ℓ d u → chiCubeB M ℓ d u z = 0 := by
    intro z hz
    by_contra h
    exact hz (chiCubeB_mem_dlBox hℓ hd h)
  exact ⟨Work.BoseFixB1S.win.boxWinModePGen_integrable_three hℓ hAcm hAcsub hvol hVpos hχc3 hχs
      hχsupp hΨc,
    Work.BoseFixB1S.win.boxWinModeRGen_integrable_three hℓ hAcm hAcsub hvol hVpos hχc3.continuous
      hχs hχsupp hΨc⟩

end Work.BoseFixB1B
