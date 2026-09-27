import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_hdist

/-!
# The horosphere at a boundary point: `lev`/`yc` coordinates, distances, and the action

For `ξ ∈ Sph n` and `D > 0`, `hptOf ξ y D` is the point of ℍⁿ at horospherical level `D` at `ξ`
whose normalised flat coordinate at `ξ` is `y`:

`hptOf ξ y D = ((1 + D²‖y‖²)/(2D) - D/2) • ξ + D • y`.

The lemmas `hptOf_level`, `hptOf_yc`, `hptOf_hdist` (proved in the sibling modules) supply the
three coordinate facts; this file assembles them into `horSpec`, which additionally describes the
map induced by an isometry `g : PO n 1` fixing `ξ` and preserving the level function `lev ξ`: the
induced isometry `ρ` of the flat space `ξ^⊥` (`ρ y = yc ξ (g • hptOf ξ y D)`) is a surjective
(Euclidean) isometry.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

set_option linter.unusedVariables false

variable {n : ℕ}

/-- The normalised flat coordinate at `ξ` lands in `ξ^⊥`. -/
lemma yc_inner_orth {ξ u : E n} (hξ : ξ ∈ Sph n) : inner ℝ (yc ξ u) ξ = 0 := by
  have hξξ : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, (mem_Sph_iff ξ).mp hξ]; norm_num
  rw [yc, real_inner_smul_left, wc, inner_sub_left, real_inner_smul_left, hξξ, mul_one,
    sub_self, mul_zero]

theorem horSpec (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ : E n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (g : PO n 1) (hg : bd g ξ = ξ) (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u) :
    (∀ y : E n, inner ℝ y ξ = 0 → lev ξ (hptOf ξ y D) = D ∧ yc ξ (hptOf ξ y D) = y) ∧
    (∀ u : E n, lev ξ u = D → hptOf ξ (yc ξ u) D = u) ∧
    (∀ y y' : E n, inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 →
      hdist (hptOf ξ y D) (hptOf ξ y' D) = Real.arcosh (1 + (D * ‖y - y'‖) ^ 2 / 2)) ∧
    (∃ ρ : E n → E n,
      (∀ y : E n, inner ℝ y ξ = 0 → inner ℝ (ρ y) ξ = 0 ∧ hptOf ξ (ρ y) D = g • hptOf ξ y D) ∧
      (∀ y y' : E n, inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 → ‖ρ y - ρ y'‖ = ‖y - y'‖) ∧
      (∀ y : E n, inner ℝ y ξ = 0 → ∃ y₀ : E n, inner ℝ y₀ ξ = 0 ∧ ρ y₀ = y)) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  -- `g • (g⁻¹ • u) = u`, from the action laws.
  have smul_inv_smul : ∀ (g : PO n 1) (u : E n), g • (g⁻¹ • u) = u := by
    intro g u
    rw [← hA'.mul_smul g g⁻¹ u, mul_inv_cancel, hA'.one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy; exact hptOf_level ξ hξ D hD y hy
  · intro u hu; exact hptOf_yc ξ hξ D hD u hu
  · intro y y' hy hy'; exact hptOf_hdist ξ hξ D hD y y' hy hy'
  · refine ⟨fun y => yc ξ (g • hptOf ξ y D), ?_, ?_, ?_⟩
    · intro y hy
      refine ⟨yc_inner_orth hξ, ?_⟩
      apply hptOf_yc ξ hξ D hD
      rw [hlev (hptOf ξ y D)]
      exact (hptOf_level ξ hξ D hD y hy).1
    · intro y y' hy hy'
      have hyr : inner ℝ (yc ξ (g • hptOf ξ y D)) ξ = 0 := yc_inner_orth hξ
      have hyr' : inner ℝ (yc ξ (g • hptOf ξ y' D)) ξ = 0 := yc_inner_orth hξ
      have hlevr : lev ξ (g • hptOf ξ y D) = D := by
        rw [hlev (hptOf ξ y D)]; exact (hptOf_level ξ hξ D hD y hy).1
      have hlevr' : lev ξ (g • hptOf ξ y' D) = D := by
        rw [hlev (hptOf ξ y' D)]; exact (hptOf_level ξ hξ D hD y' hy').1
      have hptr : hptOf ξ (yc ξ (g • hptOf ξ y D)) D = g • hptOf ξ y D :=
        hptOf_yc ξ hξ D hD _ hlevr
      have hptr' : hptOf ξ (yc ξ (g • hptOf ξ y' D)) D = g • hptOf ξ y' D :=
        hptOf_yc ξ hξ D hD _ hlevr'
      have e1 : hdist (hptOf ξ (yc ξ (g • hptOf ξ y D)) D)
            (hptOf ξ (yc ξ (g • hptOf ξ y' D)) D)
          = Real.arcosh
              (1 + (D * ‖yc ξ (g • hptOf ξ y D) - yc ξ (g • hptOf ξ y' D)‖) ^ 2 / 2) :=
        hptOf_hdist ξ hξ D hD _ _ hyr hyr'
      rw [hptr, hptr'] at e1
      rw [hI'.isom_smul g (hptOf ξ y D) (hptOf ξ y' D)] at e1
      rw [hptOf_hdist ξ hξ D hD y y' hy hy'] at e1
      have hA1 : 1 ≤ 1 + (D * ‖yc ξ (g • hptOf ξ y D) - yc ξ (g • hptOf ξ y' D)‖) ^ 2 / 2 := by
        have : 0 ≤ (D * ‖yc ξ (g • hptOf ξ y D) - yc ξ (g • hptOf ξ y' D)‖) ^ 2 / 2 := by
          positivity
        linarith
      have hA2 : 1 ≤ 1 + (D * ‖y - y'‖) ^ 2 / 2 := by
        have : 0 ≤ (D * ‖y - y'‖) ^ 2 / 2 := by positivity
        linarith
      -- `cosh` is injective on the two `arcosh` arguments (both `≥ 1`).
      have harg : 1 + (D * ‖yc ξ (g • hptOf ξ y D) - yc ξ (g • hptOf ξ y' D)‖) ^ 2 / 2
          = 1 + (D * ‖y - y'‖) ^ 2 / 2 := by
        have hc := congrArg Real.cosh e1
        rw [Real.cosh_arcosh hA2, Real.cosh_arcosh hA1] at hc
        exact hc.symm
      have hsq : (D * ‖yc ξ (g • hptOf ξ y D) - yc ξ (g • hptOf ξ y' D)‖)
            * (D * ‖yc ξ (g • hptOf ξ y D) - yc ξ (g • hptOf ξ y' D)‖)
          = (D * ‖y - y'‖) * (D * ‖y - y'‖) := by
        have : (D * ‖yc ξ (g • hptOf ξ y D) - yc ξ (g • hptOf ξ y' D)‖) ^ 2
            = (D * ‖y - y'‖) ^ 2 := by linarith
        simpa [pow_two] using this
      have hnnr : 0 ≤ D * ‖yc ξ (g • hptOf ξ y D) - yc ξ (g • hptOf ξ y' D)‖ :=
        mul_nonneg (le_of_lt hD) (norm_nonneg _)
      have hnny : 0 ≤ D * ‖y - y'‖ := mul_nonneg (le_of_lt hD) (norm_nonneg _)
      exact mul_left_cancel₀ (ne_of_gt hD) ((mul_self_inj_of_nonneg hnnr hnny).mp hsq)
    · intro y hy
      let y₀ : E n := yc ξ (g⁻¹ • hptOf ξ y D)
      have hlev0 : lev ξ (g⁻¹ • hptOf ξ y D) = D := by
        have h1 : lev ξ (g⁻¹ • hptOf ξ y D) = lev ξ (g • (g⁻¹ • hptOf ξ y D)) :=
          (hlev (g⁻¹ • hptOf ξ y D)).symm
        rw [h1, smul_inv_smul g (hptOf ξ y D)]
        exact (hptOf_level ξ hξ D hD y hy).1
      have hpt0 : hptOf ξ y₀ D = g⁻¹ • hptOf ξ y D := hptOf_yc ξ hξ D hD _ hlev0
      refine ⟨y₀, yc_inner_orth hξ, ?_⟩
      show yc ξ (g • hptOf ξ y₀ D) = y
      rw [hpt0, smul_inv_smul g (hptOf ξ y D)]
      exact (hptOf_level ξ hξ D hD y hy).2

end Work.Mostow
