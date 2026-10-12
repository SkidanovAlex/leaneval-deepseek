import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB6Est.Defs
import Submission.Work.BoseBogFS.meshNormComponent
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.meshInj_norm_gain`

The **norm gain** of the mesh injection `meshInj` (`Submission/Work/BoseBogFS/meshInj.lean`).

`meshInj` provides an injection `e` of the box labels into the Bogoliubov mode lattice whose
components separate the box label from the lattice centre,
`|(e k) i − gridD n/2| ≥ |labVec N k i|/σ + 1/2` (the form in which the hypothesis `h` below
appears).  This lemma is its consumer: at FS's mesh relation
`(n:ℝ)+1 = ℓ√(ρ_z a)/σ` the *momentum* of the box label, `kmomLab ℓ N k = (2π/ℓ)·labVec N k`,
together with the half-mesh safety margin `πσ/ℓ`, is dominated by
`√(ρ_z a)` times the norm of the assigned mode position.

The mathematical content is the mesh relation together with the elementary inequality
`‖u‖ + 1/2 ≤ ‖u + (1/2)1‖` on the orthant (`Work.BoseBogFS.sqrt_norm_add_half`): the additive
`1/2` in the hypothesis is exactly the `πσ/ℓ` margin of the conclusion.

Contents (all `sorry`-free):

* `Work.BoseBogFS.eucNorm3_eq` — `eucNorm3` unfolded;
* `Work.BoseBogFS.normCompBound` — the componentwise separation passes to `eucNorm3`;
* `Work.BoseBogFS.eucNorm3_kmomLab` — `‖kmomLab ℓ N k‖ = |ℓ⁻¹|·2π·‖labVec N k‖`;
* `Work.BoseBogFS.meshInj_norm_gain` — the target.
-/

open scoped Real BigOperators

-- The hypothesis `σ ≤ 1` of the target is not needed for this arithmetic fact (it belongs to
-- the mesh construction `meshInj`); it is kept because the statement is fixed.
set_option linter.unusedVariables false

namespace Work.BoseBogFS

open Submission.BoseGases

/-- `eucNorm3` is by definition the `ℝ³`-norm of the coordinate vector. -/
lemma eucNorm3_eq (u : Fin 3 → ℝ) :
    eucNorm3 u = Real.sqrt (∑ i, u i ^ 2) := rfl

/-- The componentwise mesh separation passes to the Euclidean norm: the additive `1/2` of the
hypothesis is preserved (it is exactly the `sqrt_norm_add_half` gain). -/
lemma normCompBound {σ c : ℝ} (hσ : 0 < σ) (hc : 0 < c) {M p : Fin 3 → ℝ}
    (h : ∀ i, c * (|M i| / σ + 1 / 2) ≤ |p i|) :
    c * (eucNorm3 M / σ + 1 / 2) ≤ eucNorm3 p := by
  rw [eucNorm3_eq, eucNorm3_eq]
  exact meshNormComponent hσ hc h

/-- The norm of the box momentum `kmomLab ℓ N k = ℓ⁻¹ • vec (labVec N k)`, with
`Work.BoseB4.vec m = 2π m`. -/
lemma eucNorm3_kmomLab (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) :
    eucNorm3 (Work.BoseBoxFock.kmomLab ℓ N k)
      = |ℓ⁻¹| * (2 * π) * eucNorm3 (fun i => ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) := by
  rw [Work.BoseBoxFock.kmomLab]
  rw [show (ℓ⁻¹ • Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)).ofLp
        = ℓ⁻¹ • (Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)).ofLp from rfl]
  rw [eucNorm3_smul]
  rw [show (Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)).ofLp
        = (2 * π) • (fun i : Fin 3 => ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) from rfl]
  rw [eucNorm3_smul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π)]
  ring

theorem meshInj_norm_gain {N n : ℕ} {ℓ ρz a σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hrel : (n : ℝ) + 1 = ℓ * Real.sqrt (ρz * a) / σ)
    {e : Work.BoseBoxFock.Lab N → Work.BoseB6Est.modeIdx n}
    (h : ∀ k : Work.BoseBoxFock.Lab N, ∀ i : Fin 3,
        (Work.BoseB6.meshD n)
            * (|((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| / σ + 1 / 2)
          ≤ |(Work.BoseB6Est.modePos n (e k)) i|) :
    ∀ k : Work.BoseBoxFock.Lab N,
      Submission.BoseGases.eucNorm3 (Work.BoseBoxFock.kmomLab ℓ N k) + π * σ / ℓ
        ≤ Real.sqrt (ρz * a)
            * Submission.BoseGases.eucNorm3 (Work.BoseB6Est.modePos n (e k)) := by
  -- FS's mesh relation `(n:ℝ)+1 = ℓ√(ρ_z a)/σ`, cleared of denominators:
  have hℓsa : ℓ * Real.sqrt (ρz * a) = σ * ((n : ℝ) + 1) := by
    have h' := congrArg (fun x : ℝ => x * σ) hrel
    rw [div_mul_cancel₀ _ (ne_of_gt hσ0)] at h'
    linarith [h']
  have hsnn : 0 ≤ Real.sqrt (ρz * a) := Real.sqrt_nonneg _
  have hprod : 0 < ℓ * Real.sqrt (ρz * a) := by rw [hℓsa]; positivity
  have hℓ : 0 < ℓ := pos_of_mul_pos_left hprod hsnn
  have hsa : 0 ≤ Real.sqrt (ρz * a) := hsnn
  have hmeshD : 0 < Work.BoseB6.meshD n := by
    unfold Work.BoseB6.meshD; positivity
  -- the mesh relation in the form `meshD n · √(ρ_z a) = 2πσ/ℓ`
  have hmesh : Work.BoseB6.meshD n * Real.sqrt (ρz * a) = 2 * π * σ / ℓ := by
    have hsqrt : Real.sqrt (ρz * a) = σ * ((n : ℝ) + 1) / ℓ := by
      rw [eq_div_iff (ne_of_gt hℓ), mul_comm]
      exact hℓsa
    rw [hsqrt, Work.BoseB6.meshD]
    field_simp
  intro k
  -- the componentwise separation, passed through the Euclidean norm
  have hbound : Work.BoseB6.meshD n
      * (eucNorm3 (fun i => ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) / σ + 1 / 2)
      ≤ eucNorm3 (Work.BoseB6Est.modePos n (e k)) :=
    normCompBound hσ0 hmeshD (fun i => h k i)
  have hkm := eucNorm3_kmomLab ℓ N k
  have hmain : Work.BoseB6.meshD n * Real.sqrt (ρz * a)
      * (eucNorm3 (fun i => ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) / σ + 1 / 2)
      ≤ Real.sqrt (ρz * a) * eucNorm3 (Work.BoseB6Est.modePos n (e k)) := by
    have h1 : Work.BoseB6.meshD n * Real.sqrt (ρz * a)
        * (eucNorm3 (fun i => ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) / σ + 1 / 2)
        = Real.sqrt (ρz * a) * (Work.BoseB6.meshD n
          * (eucNorm3 (fun i => ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) / σ + 1 / 2)) := by
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hbound hsa
  calc eucNorm3 (Work.BoseBoxFock.kmomLab ℓ N k) + π * σ / ℓ
      = (2 * π * σ / ℓ)
          * (eucNorm3 (fun i => ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) / σ + 1 / 2) := by
        rw [hkm, abs_of_pos (inv_pos.mpr hℓ)]
        field_simp
    _ = (Work.BoseB6.meshD n * Real.sqrt (ρz * a))
          * (eucNorm3 (fun i => ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) / σ + 1 / 2) := by
        rw [hmesh]
    _ ≤ Real.sqrt (ρz * a) * eucNorm3 (Work.BoseB6Est.modePos n (e k)) := hmain

end Work.BoseBogFS
