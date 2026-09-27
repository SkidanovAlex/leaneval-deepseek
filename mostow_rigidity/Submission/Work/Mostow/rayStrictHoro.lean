import Mathlib
import Submission.Work.Mostow.KMdefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspMap
import Submission.Work.Mostow.cuspCocompactAllLevels

/-!
# Strict increase of horospherical displacements just off a point (`KM-E`, clause (iii))

Let `ξ ∈ Sph n` be a boundary point and `G_ξ` the group of isometries fixing `ξ` and preserving the
Busemann function `busemann ξ` (equivalently `lev ξ u = exp (busemann ξ u)`), i.e. the horospherical
group of `ξ`.  The lemma says that the displacement function `u ↦ hdist u (g • u)` of every `g ∈ G_ξ`
which moves `x` is *simultaneously* strictly increased by moving `x` a little way along the geodesic
ray from `x` away from `ξ` (the direction in which the level `lev ξ` grows).

The proof uses the horospherical form of the law of cosines (`levYcFormula`)

`cosh (hdist u v) = cosh (log (lev ξ u / lev ξ v)) + (lev ξ u * lev ξ v / 2) ‖yc ξ u - yc ξ v‖²`

together with the fact (`hptOf_smul_level`) that an isometry fixing `ξ` and preserving the levels
acts on the normalised flat coordinate `yc ξ` by a level-independent Euclidean isometry
`flatAct ξ g`.  For such a `g` and any `u`,

`cosh (hdist u (g • u)) = 1 + (lev ξ u)²/2 * ‖yc ξ u - flatAct ξ g (yc ξ u)‖²`,

so the displacement is strictly increasing in the level `lev ξ u` as soon as it is positive
(the flat factor is positive exactly when `g` moves `u`).  Moving `x` to the point of the ray with
level `Real.exp (τ/2) * lev ξ x` therefore increases every such displacement strictly, while the
hyperbolic distance travelled is `τ/2 < τ`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- Auxiliary computation, valid for every point `u`: an isometry `g` fixing `ξ` and preserving the
level function satisfies `lev ξ (g • u) = lev ξ u` and `yc ξ (g • u) = flatAct ξ g (yc ξ u)`. -/
theorem rayStrictHoro_lev_yc {n : ℕ} (hB : POBasic n) (hId : HypIsoData n)
    {ξ : E n} (hξ : ξ ∈ Sph n) {g : PO n 1} (hg : bd g ξ = ξ)
    (h0 : lev ξ (g • (0 : E n)) = 1) (u : E n) :
    lev ξ (g • u) = lev ξ u ∧ yc ξ (g • u) = flatAct ξ g (yc ξ u) := by
  have hD : 0 < lev ξ u := lev_pos ξ hξ u
  refine ⟨?_, ?_⟩
  · rw [lev_smul_self hId hB ξ hξ g u hg, h0, mul_one]
  · have h1 : g • u = g • hptOf ξ (yc ξ u) (lev ξ u) := by rw [hptOf_yc_lev hξ u]
    have h2 : g • hptOf ξ (yc ξ u) (lev ξ u) = hptOf ξ (flatAct ξ g (yc ξ u)) (lev ξ u) :=
      hptOf_smul_level hB hId hξ hg h0 (yc_orth hξ) hD
    rw [h1, h2]
    exact (hptOfLevelYc ξ hξ (flatAct_mem hξ g (yc ξ u)) hD).2.1

/-- The horospherical displacement formula: for `g` fixing `ξ` and preserving the levels,
`cosh (hdist u (g • u)) = 1 + (lev ξ u)²/2 * ‖yc ξ u - flatAct ξ g (yc ξ u)‖²`. -/
theorem cosh_hdist_smul_horo {n : ℕ} (hB : POBasic n) (hId : HypIsoData n)
    {ξ : E n} (hξ : ξ ∈ Sph n) {g : PO n 1} (hg : bd g ξ = ξ)
    (h0 : lev ξ (g • (0 : E n)) = 1) (u : E n) :
    Real.cosh (hdist u (g • u)) =
      1 + (lev ξ u) ^ 2 / 2 * ‖yc ξ u - flatAct ξ g (yc ξ u)‖ ^ 2 := by
  obtain ⟨hlev, hyc⟩ := rayStrictHoro_lev_yc hB hId hξ hg h0 u
  have hLu : lev ξ u ≠ 0 := ne_of_gt (lev_pos ξ hξ u)
  have hf := levYcFormula hξ u (g • u)
  rw [hyc, hlev, div_self hLu, Real.log_one, Real.cosh_zero] at hf
  rw [hf]
  ring

theorem rayStrictHoro (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ : E n) (hξ : ξ ∈ Sph n) :
    ∀ x : E n, ∀ τ : ℝ, 0 < τ → ∃ x' : E n, hdist x x' < τ ∧ ∀ g : PO n 1,
      bd g ξ = ξ → busemann ξ (g • (0 : E n)) = 0 → 0 < hdist x (g • x) →
      hdist x (g • x) < hdist x' (g • x') := by
  intro x τ hτ
  have hB : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- move `x` along the ray away from `ξ`, to the level `ρ * lev ξ x` with `ρ = exp (τ/2)`
  obtain ⟨ρ, hρpos, hρ1, hρlog⟩ : ∃ r : ℝ, 0 < r ∧ 1 < r ∧ Real.log r = τ / 2 :=
    ⟨Real.exp (τ / 2), Real.exp_pos _, Real.one_lt_exp_iff.mpr (by linarith), Real.log_exp _⟩
  refine ⟨hptOf ξ (yc ξ x) (ρ * lev ξ x), ?_, ?_⟩
  · -- the distance travelled is `τ / 2`
    have hD : 0 < ρ * lev ξ x := mul_pos (lt_trans zero_lt_one hρ1) (lev_pos ξ hξ x)
    rw [hdist_hptOf_yc hξ x hD]
    have hlog : Real.log (lev ξ x) - Real.log (ρ * lev ξ x) = -(τ / 2) := by
      rw [Real.log_mul (ne_of_gt hρpos) (ne_of_gt (lev_pos ξ hξ x)), hρlog]
      ring
    rw [hlog, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < τ / 2)]
    linarith
  · intro g hg hbus hpos
    have h0 : lev ξ (g • (0 : E n)) = 1 := by
      rw [lev_eq_exp hξ (g • (0 : E n)), hbus, Real.exp_zero]
    obtain ⟨hlev', hyc', -⟩ := hptOfLevelYc ξ hξ (yc_orth hξ : inner ℝ (yc ξ x) ξ = 0)
      (mul_pos (lt_trans zero_lt_one hρ1) (lev_pos ξ hξ x))
    have hc1 := cosh_hdist_smul_horo hB hId hξ (g := g) hg h0 x
    have hc2 := cosh_hdist_smul_horo hB hId hξ (g := g) hg h0 (hptOf ξ (yc ξ x) (ρ * lev ξ x))
    rw [hlev', hyc'] at hc2
    -- the flat factor is positive, because `g` moves `x`
    have hZpos : 0 < ‖yc ξ x - flatAct ξ g (yc ξ x)‖ ^ 2 := by
      have hgt : (1 : ℝ) < Real.cosh (hdist x (g • x)) := Real.one_lt_cosh.mpr (ne_of_gt hpos)
      rw [hc1] at hgt
      have hcoef : 0 < (lev ξ x) ^ 2 / 2 := by
        have := lev_pos ξ hξ x
        positivity
      exact pos_of_mul_pos_right (by linarith) (le_of_lt hcoef)
    -- the level strictly increases, hence so does the displacement
    have hLT : (lev ξ x) ^ 2 / 2 < (ρ * lev ξ x) ^ 2 / 2 := by
      have hLx : 0 < lev ξ x := lev_pos ξ hξ x
      have hDL : lev ξ x < ρ * lev ξ x := by nlinarith
      nlinarith
    have hcoslt : Real.cosh (hdist x (g • x))
        < Real.cosh (hdist (hptOf ξ (yc ξ x) (ρ * lev ξ x)) (g • hptOf ξ (yc ξ x) (ρ * lev ξ x))) := by
      rw [hc1, hc2]
      have := mul_lt_mul_of_pos_right hLT hZpos
      linarith
    have habs := Real.cosh_lt_cosh.mp hcoslt
    rwa [abs_of_nonneg (hId.nonneg x (g • x)),
      abs_of_nonneg (hId.nonneg _ _)] at habs

end Work.Mostow
