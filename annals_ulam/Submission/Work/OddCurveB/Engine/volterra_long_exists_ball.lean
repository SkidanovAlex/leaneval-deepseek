import Mathlib
import Submission.Work.VolterraLong.Main

/-!
# The Volterra engine on a ball of radius `ρ ≤ 1`

`Work.OddCurveB.Engine.volterra_long_exists_ball` is
`Work.VolterraLong.volterra_long_exists_eps` with `Metric.closedBall (Z₀ s) 1` replaced by
`Metric.closedBall (Z₀ s) ρ` in every hypothesis (`ρ ∈ (0,1]` fixed), the same constants
`M = 2 + (b - a)`, `EE = Real.exp ((4 * B * L + 1) * (b - a))` and the same conclusion
`dist (Z s) (Z₀ s) ≤ 2 * B * M * EE * ε`; only the thresholds on `ε` shrink with `ρ`.

It is needed for the odd Ulam data: on the radius-`1` ball the second diagonal kernel
`Kdiag2 = const · X^{n-1} √X · (t + h')` is not differentiable in the state at a simple zero of
`X` when `n = 1` (`Work.OddCurveB.Est.not_differentiableAt_Godd_one_bump`).

The proof is a corollary of the radius-`1` engine, applied to the *dilated* data
`u ↦ (G s (ρ • u), Θ s σ (ρ • u), Ξ s, ρ⁻¹ • Z₀ s)`: the dilation `φ u = ρ • u` maps the ball of
radius `1` around `ρ⁻¹ • Z₀ s` onto the ball of radius `ρ` around `Z₀ s`, and the engine's
numerical data transform as `B' = ρ⁻¹ B`, `L' = ρ L`, `Cg' = ρ² Cg`, `ε' = ε`, so that
`4 B' L' + 1 = 4 B L + 1` and the conclusion scales back by `ρ` into the same bound.
See `Submission/Work/OddCurveB/Engine/README.md`.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace Work.OddCurveB.Engine

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scalar multiplication by a nonzero real, as a continuous linear equivalence. -/
def smulEquiv (ρ : ℝ) (hρ : ρ ≠ 0) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toFun := fun u => ρ • u
      invFun := fun u => ρ⁻¹ • u
      left_inv := fun u => by
        show ρ⁻¹ • (ρ • u) = u
        rw [smul_smul, inv_mul_cancel₀ hρ, one_smul]
      right_inv := fun u => by
        show ρ • (ρ⁻¹ • u) = u
        rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]
      map_add' := fun u v => by
        show ρ • (u + v) = ρ • u + ρ • v
        rw [smul_add]
      map_smul' := fun c u => by
        show ρ • (c • u) = c • (ρ • u)
        rw [smul_comm] }
  continuous_toFun := continuous_const_smul ρ
  continuous_invFun := continuous_const_smul ρ⁻¹

/-- Dilation of a continuous linear equivalence: `u ↦ e (ρ • u)`. -/
def dilate (ρ : ℝ) (hρ : ρ ≠ 0) (e : E ≃L[ℝ] E) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toFun := fun u => e (ρ • u)
      invFun := fun u => ρ⁻¹ • e.symm u
      left_inv := by
        intro u
        show ρ⁻¹ • e.symm (e (ρ • u)) = u
        rw [e.symm_apply_apply, smul_smul, inv_mul_cancel₀ hρ, one_smul]
      right_inv := by
        intro u
        show e (ρ • (ρ⁻¹ • e.symm u)) = u
        rw [smul_smul, mul_inv_cancel₀ hρ, one_smul, e.apply_symm_apply]
      map_add' := fun u v => by
        show e (ρ • (u + v)) = e (ρ • u) + e (ρ • v)
        rw [smul_add, map_add]
      map_smul' := fun c u => by
        show e (ρ • (c • u)) = c • e (ρ • u)
        rw [smul_comm, map_smul] }
  continuous_toFun := e.continuous.comp (continuous_const_smul ρ)
  continuous_invFun := (continuous_const_smul ρ⁻¹).comp e.symm.continuous

@[simp] lemma dilate_apply (ρ : ℝ) (hρ : ρ ≠ 0) (e : E ≃L[ℝ] E) (u : E) :
    dilate ρ hρ e u = e (ρ • u) := rfl

@[simp] lemma dilate_symm_apply (ρ : ℝ) (hρ : ρ ≠ 0) (e : E ≃L[ℝ] E) (u : E) :
    (dilate ρ hρ e).symm u = ρ⁻¹ • e.symm u := rfl

/-- The dilation `u ↦ ρ • u` multiplies distances by `ρ` (for `ρ ≥ 0`). -/
lemma dist_smul_smul (ρ : ℝ) (hρ : 0 ≤ ρ) (z w : E) :
    dist (ρ • z) (ρ • w) = ρ * dist z w := by
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]

theorem volterra_long_exists_ball [CompleteSpace E] {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (A : ℝ → E ≃L[ℝ] E) (G0 G : ℝ → E → E) (Θ0 Θ : ℝ → ℝ → E → E) (Ξ0 Ξ : ℝ → E)
    (Z₀ : ℝ → E) {B L Cg : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hCg : 0 ≤ Cg)
    (hG0_diff : ∀ s ∈ Set.Icc a b, DifferentiableAt ℝ (fun z => G0 s z) (Z₀ s))
    (hA_spec : ∀ s ∈ Set.Icc a b, (A s : E →L[ℝ] E) = fderiv ℝ (fun z => G0 s z) (Z₀ s))
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hAb : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (Z₀ s) = (∫ σ in s..b, Θ0 s σ (Z₀ σ)) + Ξ0 s)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) ρ,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) ρ, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) ρ,
      DifferentiableAt ℝ (fun w => G s w) z)
    (M EE : ℝ) (hM_def : M = 2 + (b - a))
    (hEE_def : EE = Real.exp ((4 * B * L + 1) * (b - a)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hε2 : ε < ρ / (2 * B * M * EE))
    (hε3 : ε < ρ / (4 * B * (2 * ρ * B * Cg * M * EE + 1)))
    (hΞc : ∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε)
    (hGc : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) ρ, dist (G s z) (G0 s z) < ε)
    (hΘc : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) ρ,
      dist (Θ s σ z) (Θ0 s σ z) < ε)
    (hder : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) ρ,
      ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + ε) :
    ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧ Work.VolterraLong.SolvesOn a b G Θ Ξ Z ∧
      (∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ 2 * B * M * EE * ε) := by
  classical
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  set A' : ℝ → E ≃L[ℝ] E := fun s => dilate ρ hρne (A s) with hA'def
  set Z₀' : ℝ → E := fun s => ρ⁻¹ • Z₀ s with hZ₀'def
  set G' : ℝ → E → E := fun s z => G s (ρ • z) with hG'def
  set G0' : ℝ → E → E := fun s z => G0 s (ρ • z) with hG0'def
  set Θ' : ℝ → ℝ → E → E := fun s σ z => Θ s σ (ρ • z) with hΘ'def
  set Θ0' : ℝ → ℝ → E → E := fun s σ z => Θ0 s σ (ρ • z) with hΘ0'def
  set B' : ℝ := ρ⁻¹ * B with hB'def
  set L' : ℝ := ρ * L with hL'def
  set Cg' : ℝ := ρ ^ 2 * Cg with hCg'def
  set lam : ℝ := 4 * B' * L' + 1 with hlamdef
  have hsmul_inv : ∀ z : E, ρ • (ρ⁻¹ • z) = z := by
    intro z; rw [smul_smul, mul_inv_cancel₀ hρne, one_smul]
  have hZ₀_eq : ∀ s, Z₀ s = ρ • Z₀' s := by
    intro s; rw [hZ₀'def]; simp only; exact (hsmul_inv (Z₀ s)).symm
  have hdist_all : ∀ z w : E, dist (ρ • z) (ρ • w) = ρ * dist z w :=
    fun z w => dist_smul_smul ρ hρ.le z w
  have hball : ∀ (s : ℝ) (z : E),
      z ∈ Metric.closedBall (Z₀' s) 1 ↔ ρ • z ∈ Metric.closedBall (Z₀ s) ρ := by
    intro s z
    have h1 : Z₀ s = ρ • Z₀' s := hZ₀_eq s
    rw [Metric.mem_closedBall, Metric.mem_closedBall, h1, dist_smul_smul ρ hρ.le]
    constructor
    · intro h
      calc ρ * dist z (Z₀' s) ≤ ρ * 1 := mul_le_mul_of_nonneg_left h hρ.le
        _ = ρ := mul_one ρ
    · intro h
      by_contra hc
      have hc' : 1 < dist z (Z₀' s) := not_le.mp hc
      have h' : ρ * 1 < ρ * dist z (Z₀' s) := mul_lt_mul_of_pos_left hc' hρ
      rw [mul_one] at h'
      linarith
  have hA'_coe : ∀ s, ((A' s : E ≃L[ℝ] E) : E →L[ℝ] E)
      = (A s : E →L[ℝ] E).comp (ρ • (1 : E →L[ℝ] E)) := by
    intro s
    ext u
    simp [hA'def, dilate]
  have hA'_symm : ∀ s, (((A' s).symm : E →L[ℝ] E))
      = ρ⁻¹ • ((A s).symm : E →L[ℝ] E) := by
    intro s
    ext u
    simp [hA'def]
  have hB'pos : 0 < B' := by rw [hB'def]; positivity
  have hL'nonneg : 0 ≤ L' := by rw [hL'def]; positivity
  have hCg'nonneg : 0 ≤ Cg' := by rw [hCg'def]; positivity
  have hA_spec' : ∀ s ∈ Set.Icc a b,
      (A' s : E →L[ℝ] E) = fderiv ℝ (fun z => G0' s z) (Z₀' s) := by
    intro s hs
    have hd : DifferentiableAt ℝ (fun u : E => ρ • u) (Z₀' s) :=
      (differentiableAt_id (x := Z₀' s)).const_smul ρ
    have hchain : fderiv ℝ (fun z => G0 s (ρ • z)) (Z₀' s)
        = (fderiv ℝ (fun z => G0 s z) (ρ • Z₀' s)).comp
            (fderiv ℝ (fun u : E => ρ • u) (Z₀' s)) :=
      fderiv_comp (Z₀' s) (by rw [← hZ₀_eq s]; exact hG0_diff s hs) hd
    have hfd : fderiv ℝ (fun u : E => ρ • u) (Z₀' s) = ρ • (1 : E →L[ℝ] E) :=
      ((hasFDerivAt_id (Z₀' s)).const_smul ρ).fderiv
    rw [hG0'def, hchain, hfd, ← hZ₀_eq s, ← hA_spec s hs, hA'_coe s]
  have hA_cont' : ContinuousOn (fun s => ((A' s).symm : E →L[ℝ] E)) (Set.Icc a b) := by
    have : (fun s => ((A' s).symm : E →L[ℝ] E))
        = fun s => ρ⁻¹ • ((A s).symm : E →L[ℝ] E) := by
      funext s; exact hA'_symm s
    rw [this]
    exact hA_cont.const_smul ρ⁻¹
  have hAb' : ∀ s ∈ Set.Icc a b, ‖((A' s).symm : E →L[ℝ] E)‖ ≤ B' := by
    intro s hs
    rw [hA'_symm s, hB'def]
    calc ‖ρ⁻¹ • ((A s).symm : E →L[ℝ] E)‖
        ≤ ‖(ρ⁻¹ : ℝ)‖ * ‖((A s).symm : E →L[ℝ] E)‖ :=
          norm_smul_le (ρ⁻¹) ((A s).symm : E →L[ℝ] E)
      _ ≤ ρ⁻¹ * B := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
          exact mul_le_mul_of_nonneg_left (hAb s hs) (inv_nonneg.mpr hρ.le)
  have hG_cont' : Continuous (fun p : ℝ × E => G' p.1 p.2) := by
    have : (fun p : ℝ × E => G' p.1 p.2) = fun p : ℝ × E => G p.1 (ρ • p.2) := by
      funext p; rw [hG'def]
    rw [this]
    exact hG_cont.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ))
  have hΘ_cont' : Continuous (fun p : ℝ × ℝ × E => Θ' p.1 p.2.1 p.2.2) := by
    have : (fun p : ℝ × ℝ × E => Θ' p.1 p.2.1 p.2.2)
        = fun p : ℝ × ℝ × E => Θ p.1 p.2.1 (ρ • p.2.2) := by
      funext p; rw [hΘ'def]
    rw [this]
    exact hΘ_cont.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd |>.prodMk
      ((continuous_snd.comp continuous_snd).const_smul ρ)))
  have hΘ0_cont' : Continuous (fun p : ℝ × ℝ × E => Θ0' p.1 p.2.1 p.2.2) := by
    have : (fun p : ℝ × ℝ × E => Θ0' p.1 p.2.1 p.2.2)
        = fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 (ρ • p.2.2) := by
      funext p; rw [hΘ0'def]
    rw [this]
    exact hΘ0_cont.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd |>.prodMk
      ((continuous_snd.comp continuous_snd).const_smul ρ)))
  have hZ₀_cont' : ContinuousOn Z₀' (Set.Icc a b) := by
    have : Z₀' = fun s => ρ⁻¹ • Z₀ s := by funext s; rw [hZ₀'def]
    rw [this]
    exact hZ₀_cont.const_smul ρ⁻¹
  have hbase' : ∀ s ∈ Set.Icc a b,
      G0' s (Z₀' s) = (∫ σ in s..b, Θ0' s σ (Z₀' σ)) + Ξ0 s := by
    intro s hs
    have h1 : G0' s (Z₀' s) = G0 s (Z₀ s) := by
      rw [hG0'def]; simp only [hZ₀_eq s]
    have h2 : (∫ σ in s..b, Θ0' s σ (Z₀' σ)) = ∫ σ in s..b, Θ0 s σ (Z₀ σ) := by
      refine intervalIntegral.integral_congr fun σ _ => ?_
      rw [hΘ0'def]; simp only [hZ₀_eq σ]
    rw [h1, h2]
    exact hbase s hs
  have hΘ_lip' : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
      ∀ z ∈ Metric.closedBall (Z₀' σ) 1, ∀ z' ∈ Metric.closedBall (Z₀' σ) 1,
      ‖Θ' s σ z - Θ' s σ z'‖ ≤ L' * ‖z - z'‖ := by
    intro s hs σ hσ z hz z' hz'
    have h1 : ρ • z ∈ Metric.closedBall (Z₀ σ) ρ := (hball σ z).mp hz
    have h2 : ρ • z' ∈ Metric.closedBall (Z₀ σ) ρ := (hball σ z').mp hz'
    have h3 := hΘ_lip s hs σ hσ (ρ • z) h1 (ρ • z') h2
    have h4 : ‖ρ • z - ρ • z'‖ = ρ * ‖z - z'‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    rw [h4] at h3
    have h5 : Θ' s σ z = Θ s σ (ρ • z) := by rw [hΘ'def]
    have h6 : Θ' s σ z' = Θ s σ (ρ • z') := by rw [hΘ'def]
    rw [h5, h6, hL'def]
    calc ‖Θ s σ (ρ • z) - Θ s σ (ρ • z')‖ ≤ L * (ρ * ‖z - z'‖) := h3
      _ = (ρ * L) * ‖z - z'‖ := by ring
  have hdiff' : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀' s) 1,
      DifferentiableAt ℝ (fun w => G' s w) z := by
    intro s hs z hz
    have h1 : ρ • z ∈ Metric.closedBall (Z₀ s) ρ := (hball s z).mp hz
    have h2 : (fun w : E => G' s w) = fun w : E => G s (ρ • w) := by
      funext w; rw [hG'def]
    rw [h2]
    exact (hdiff s hs (ρ • z) h1).comp z ((differentiableAt_id (x := z)).const_smul ρ)
  have hGc' : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀' s) 1,
      dist (G' s z) (G0' s z) < ε := by
    intro s hs z hz
    have h1 : ρ • z ∈ Metric.closedBall (Z₀ s) ρ := (hball s z).mp hz
    have h2 : G' s z = G s (ρ • z) := by rw [hG'def]
    have h3 : G0' s z = G0 s (ρ • z) := by rw [hG0'def]
    rw [h2, h3]
    exact hGc s hs (ρ • z) h1
  have hΘc' : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀' σ) 1,
      dist (Θ' s σ z) (Θ0' s σ z) < ε := by
    intro s hs σ hσ z hz
    have h1 : ρ • z ∈ Metric.closedBall (Z₀ σ) ρ := (hball σ z).mp hz
    have h2 : Θ' s σ z = Θ s σ (ρ • z) := by rw [hΘ'def]
    have h3 : Θ0' s σ z = Θ0 s σ (ρ • z) := by rw [hΘ0'def]
    rw [h2, h3]
    exact hΘc s hs σ hσ (ρ • z) h1
  have hder' : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀' s) 1,
      ‖fderiv ℝ (fun w => G' s w) z - (A' s : E →L[ℝ] E)‖ ≤ Cg' * ‖z - Z₀' s‖ + ε := by
    intro s hs z hz
    have h1 : ρ • z ∈ Metric.closedBall (Z₀ s) ρ := (hball s z).mp hz
    have hd : DifferentiableAt ℝ (fun u : E => ρ • u) z :=
      (differentiableAt_id (x := z)).const_smul ρ
    have hfd : fderiv ℝ (fun w => G s (ρ • w)) z
        = (fderiv ℝ (fun w => G s w) (ρ • z)).comp (ρ • (1 : E →L[ℝ] E)) := by
      have hchain : fderiv ℝ (fun w => G s (ρ • w)) z
          = (fderiv ℝ (fun w => G s w) (ρ • z)).comp (fderiv ℝ (fun u : E => ρ • u) z) :=
        fderiv_comp z (hdiff s hs (ρ • z) h1) hd
      have h2 : fderiv ℝ (fun u : E => ρ • u) z = ρ • (1 : E →L[ℝ] E) :=
        ((hasFDerivAt_id z).const_smul ρ).fderiv
      rw [hchain, h2]
    have hsub : ((fderiv ℝ (fun w => G s w) (ρ • z)).comp (ρ • (1 : E →L[ℝ] E))
          - (A s : E →L[ℝ] E).comp (ρ • (1 : E →L[ℝ] E)))
        = ρ • ((fderiv ℝ (fun w => G s w) (ρ • z)) - (A s : E →L[ℝ] E)) := by
      ext u
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul, smul_sub]
    have hG'eq : (fun w : E => G' s w) = fun w : E => G s (ρ • w) := by
      funext w; rw [hG'def]
    rw [hG'eq, hfd, hA'_coe s, hsub, hCg'def]
    have hbound := hder s hs (ρ • z) h1
    have hnorm : ‖ρ • z - Z₀ s‖ = ρ * ‖z - Z₀' s‖ := by
      have : ρ • z - Z₀ s = ρ • (z - Z₀' s) := by rw [smul_sub, hZ₀_eq s]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hstep : ‖(fderiv ℝ (fun w => G s w) (ρ • z)) - (A s : E →L[ℝ] E)‖
        ≤ Cg * (ρ * ‖z - Z₀' s‖) + ε := by
      rw [← hnorm]; exact hbound
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    calc ρ * ‖(fderiv ℝ (fun w => G s w) (ρ • z)) - (A s : E →L[ℝ] E)‖
        ≤ ρ * (Cg * (ρ * ‖z - Z₀' s‖) + ε) :=
          mul_le_mul_of_nonneg_left hstep hρ.le
      _ = ρ ^ 2 * Cg * ‖z - Z₀' s‖ + ρ * ε := by ring
      _ ≤ ρ ^ 2 * Cg * ‖z - Z₀' s‖ + ε := by
          have : ρ * ε ≤ ε := by nlinarith [hρ, hρ1, hε]
          linarith
  have hEE : EE = Real.exp (lam * (b - a)) := by
    rw [hEE_def, hlamdef, hB'def, hL'def]
    congr 1
    field_simp
  have hε2eq : 1 / (2 * B' * M * EE) = ρ / (2 * B * M * EE) := by
    rw [hB'def]; field_simp
  have hε2' : ε < 1 / (2 * B' * M * EE) := by
    rw [hε2eq]; exact hε2
  have hε3eq : 1 / (4 * B' * (2 * B' * Cg' * M * EE + 1))
      = ρ / (4 * B * (2 * ρ * B * Cg * M * EE + 1)) := by
    rw [hB'def, hCg'def]; field_simp
  have hε3' : ε < 1 / (4 * B' * (2 * B' * Cg' * M * EE + 1)) := by
    rw [hε3eq]; exact hε3
  obtain ⟨Z', hZ'cont, hZ'sol, hZ'close⟩ :=
    Work.VolterraLong.volterra_long_exists_eps hab A' G0' G' Θ0' Θ' Ξ0 Ξ Z₀'
      hB'pos hL'nonneg hCg'nonneg hA_spec' hA_cont' hAb' hG_cont' hΘ_cont' hΞ_cont hZ₀_cont'
      hΘ0_cont' hbase' hΘ_lip' hdiff' lam M EE hlamdef hM_def hEE hε hε1 hε2' hε3'
      hΞc hGc' hΘc' hder'
  have hcont_Z : ContinuousOn (fun s => ρ • Z' s) (Set.Icc a b) := hZ'cont.const_smul ρ
  refine ⟨fun s => ρ • Z' s, hcont_Z, ?_, ?_⟩
  · intro s hs
    have := hZ'sol s hs
    simpa only [Work.VolterraLong.SolvesOn, hG'def, hΘ'def] using this
  · intro s hs
    have h1 := hZ'close s hs
    have h2 : dist (ρ • Z' s) (Z₀ s) = ρ * dist (Z' s) (Z₀' s) := by
      rw [hZ₀_eq s, dist_smul_smul ρ hρ.le]
    rw [h2]
    calc ρ * dist (Z' s) (Z₀' s) ≤ ρ * (2 * B' * M * EE * ε) :=
          mul_le_mul_of_nonneg_left h1 hρ.le
      _ = 2 * B * M * EE * ε := by
          rw [hB'def]; field_simp

end

end Work.OddCurveB.Engine
