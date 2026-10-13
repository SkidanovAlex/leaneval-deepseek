import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.PertShear
import Submission.Work.WilE3.Taylor.CaseII.contDiffOn_shear_data
import Submission.Work.WilE3.Taylor.CaseII.fderiv_pertMinor_eq_smul_fderiv_shear
import Submission.Work.WilE3.Taylor.CaseII.det_ne_zero_of_mulVec_shear
import Submission.Work.WilE3.API.hasFDerivAt_eaEval

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

/-- The Fréchet derivative of a scalar EA function, evaluated on a vector `ξ`, is the pairing of
`ξ` with the symbolic gradient: `(fderiv (eaEval c Q) x) ξ = ∑ j, ∂_j Q(x) · ξ_j`. -/
lemma fderiv_eaEval_apply {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    (x ξ : Fin k → ℝ) :
    (fderiv ℝ (fun z : Fin k → ℝ => eaEval c Q z) x) ξ
      = ∑ j : Fin k, eaEval c (eaD c j Q) x * ξ j := by
  rw [(Work.WilE3.API.hasFDerivAt_eaEval c Q x).fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- **The determinant bridge.**  If `x` is a point of the shear locus (`Ush`) at which the shear
equations hold and the shear Jacobian `M` (pivot row `∇Φ`, rows `∇(aShᵢ + bShᵢ · v_{i₀})` for
`i ≠ i₀`) is injective, then the Jacobian determinant `sysDet` of the square perturbed system
`pertSys c Φ v i₀` does not vanish at `x`.

Why: on `Ush` one has the identity `pertMinor(v)ᵢ = G·∂_{i₀}Φ · (aᵢ + bᵢ·v_{i₀} + vᵢ)` (lemma
`aSh_add_bSh_mul_add`), so at `x` the shear equations give `pertMinor(v)ᵢ x = 0`; differentiating
`(G ∂_{i₀}Φ)·(Rᵢ + vᵢ) = pertMinor(v)ᵢ` (valid on the neighbourhood `Ush` of `x`) and using
`Rᵢ x + vᵢ = 0` gives `∂ⱼ pertMinor(v)ᵢ (x) = (G ∂_{i₀}Φ)(x) · ∂ⱼ Rᵢ (x)`.  So the top rows of the
matrix of the system are the rows of `M` with the rows `i ≠ i₀` rescaled by the nonzero constant
`(G ∂_{i₀}Φ)(x)` (row `i₀` is `∇Φ` in both), and a row rescaling by nonzero constants preserves
injectivity of the associated (square) linear map; hence the determinant `sysDet` is nonzero. -/
theorem sysDet_pertSys_ne_zero_of_shearInj {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (i₀ : Fin k) (v : Fin k → ℝ) (x : Fin k → ℝ)
    (hx : x ∈ Work.WilE3.Taylor.CaseII.Ush c Φ i₀)
    (ha : ContDiffOn ℝ 1 (Work.WilE3.Taylor.CaseII.aSh c Φ i₀) (Work.WilE3.Taylor.CaseII.Ush c Φ i₀))
    (hb : ContDiffOn ℝ 1 (Work.WilE3.Taylor.CaseII.bSh c Φ i₀) (Work.WilE3.Taylor.CaseII.Ush c Φ i₀))
    (hcon : ∀ i : Fin k, i ≠ i₀ →
      Work.WilE3.Taylor.CaseII.aSh c Φ i₀ x i + Work.WilE3.Taylor.CaseII.bSh c Φ i₀ x i * v i₀
        + v i = 0)
    (hinj : Function.Injective (LinearMap.pi (fun i : Fin k =>
        if i = i₀ then
          (fderiv ℝ (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z) x).toLinearMap
        else (fderiv ℝ (fun z : Fin k → ℝ =>
          Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i + Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i * v i₀)
            x).toLinearMap))) :
    Work.WilE3.Taylor.CaseII.sysDet c (Work.WilE3.Taylor.CaseII.pertSys c Φ v i₀) x ≠ 0 := by
  -- The common denominator `D = G · ∂_{i₀}Φ` at `x`, nonzero because `x ∈ Ush`.
  set D := eaEval c (denP c Φ i₀) x with hDdef
  have hDne : D ≠ 0 := hx
  -- The shear Jacobian `M` of the hypothesis, as a family of linear functionals.
  set F : Fin k → ((Fin k → ℝ) →ₗ[ℝ] ℝ) := (fun i : Fin k =>
        if i = i₀ then (fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) x).toLinearMap
        else (fderiv ℝ (fun z : Fin k → ℝ =>
          aSh c Φ i₀ z i + bSh c Φ i₀ z i * v i₀) x).toLinearMap) with hF
  have hFi₀ : F i₀ = (fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) x).toLinearMap := by
    simp only [hF, if_pos rfl]
  have hFi : ∀ i, i ≠ i₀ → F i =
      (fderiv ℝ (fun z : Fin k → ℝ =>
        aSh c Φ i₀ z i + bSh c Φ i₀ z i * v i₀) x).toLinearMap := by
    intro i hi
    simp only [hF, if_neg hi]
  have hMinj : Function.Injective (LinearMap.pi F) := by rw [hF]; exact hinj
  rw [sysDet]
  -- Row `i` of the system is the row of `M` at `i₀`, and `D` times the row of `M` otherwise.
  refine det_ne_zero_of_mulVec_shear
    (Matrix.of fun i j => eaEval c (eaD c j (pertSys c Φ v i₀ i)) x) (LinearMap.pi F)
    i₀ D hDne hMinj ?_
  intro ξ
  funext i
  rw [Matrix.mulVec_apply]
  simp only [Matrix.row, dotProduct, Matrix.of_apply]
  rw [← fderiv_eaEval_apply c (pertSys c Φ v i₀ i) x ξ]
  by_cases hi : i = i₀
  · -- Pivot row: `pertSys … i₀ = Φ`, and the `i₀`-th component of `M` is `∇Φ`.
    rw [hi]
    simp only [pertSys, if_pos rfl, LinearMap.pi_apply]
    rw [hFi₀]
    rfl
  · -- Minor rows: rescale by `D = eaEval c (denP c Φ i₀) x` and use the chain rule.
    simp only [pertSys, if_neg hi, LinearMap.pi_apply]
    rw [fderiv_pertMinor_eq_smul_fderiv_shear c Φ i₀ v x hx i hi (hcon i hi), hFi i hi]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hDdef]
    rfl

end Work.WilE3.Taylor.CaseII
