import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.LatGreen.CellDefs
import Submission.Work.BoseFixR.LatGreen.HeatIntegral
import Submission.Work.BoseFixR.LatGreen.LGFormAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.LatGreenParsevalBDefs` — shared vocabulary of the `(B)`-carrying
cell-Parseval identity `LatGreenParsevalB`

The target identity (`Submission/Work/BoseFixR/LatGreen/LatGreenParsevalB.lean`) is

`Σ'_{k∈ℤ³∖0} (chat W q_k)²/‖q_k‖² = ∬_{cell ℓ × cell ℓ} P(x)P(y)·ℓ²·latGreen(ℓ⁻¹•(x−y))`,

with the torus lattice momenta `q_k = ℓ⁻¹ • vec k` (`vec k = 2πk`), `P = period W ℓ`.

* `qmom ℓ k = ℓ⁻¹ • vec k` is that momentum; its square length `qlam ℓ k = ‖qmom ℓ k‖²`
  satisfies `ℓ²·qlam ℓ k = ‖vec k‖²`, the exponent of the Poisson/θ series of the periodised
  heat kernel.
* `latBox` is the finite set of lattice labels `{-4,…,4}³`: for every `u` with `|u i| ≤ 2`
  it contains the nearest lattice point of `u`.  It indexes the finite part of the domination
  bound `∫₀^ε |heatPeriod s u − 1| ds ≤ C(1 + Σ_{n∈latBox} 1/‖u − latVec n‖)` used by the
  Fubini step of the identity.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-- The torus momentum `q_k = ℓ⁻¹ • vec k = ℓ⁻¹ • (2πk)` of the `ℓ`-periodic cell. -/
noncomputable def qmom (ℓ : ℝ) (k : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  ℓ⁻¹ • Work.BoseB4.vec k

/-- `‖q_k‖²`, the denominator of the lattice row. -/
noncomputable def qlam (ℓ : ℝ) (k : Fin 3 → ℤ) : ℝ := ‖qmom ℓ k‖ ^ 2

/-- `ℓ²‖q_k‖² = ‖vec k‖²`. -/
lemma sq_mul_qlam {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Fin 3 → ℤ) :
    ℓ ^ 2 * qlam ℓ k = ‖Work.BoseB4.vec k‖ ^ 2 := by
  rw [qlam, qmom, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  field_simp

/-- `‖q_k‖²` is positive away from the origin. -/
lemma qlam_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 3 → ℤ} (hk : k ≠ 0) : 0 < qlam ℓ k := by
  rw [qlam]
  refine pow_pos ?_ 2
  rw [qmom, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  exact mul_pos (inv_pos.mpr hℓ) (Work.BoseFixR.LatGreen.norm_vec_pos hk)

/-- `cos⟨q_k, z⟩ = cos⟨vec k, ℓ⁻¹•z⟩`. -/
lemma cos_qmom {ℓ : ℝ} (k : Fin 3 → ℤ) (z : EuclideanSpace ℝ (Fin 3)) :
    Real.cos (inner ℝ (qmom ℓ k) z)
      = Real.cos (inner ℝ (Work.BoseB4.vec k) (ℓ⁻¹ • z)) := by
  rw [qmom, real_inner_smul_left, real_inner_smul_right]

/-- The finite set of lattice labels `{-4,…,4}³`; for every `u` with `|u i| ≤ 2` it contains the
nearest lattice point of `u`. -/
noncomputable def latBox : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-4 : ℤ) 4)

lemma mem_latBox {n : Fin 3 → ℤ} :
    n ∈ latBox ↔ ∀ i : Fin 3, n i ∈ Finset.Icc (-4 : ℤ) 4 := by
  rw [latBox, Fintype.mem_piFinset]

end Work.BoseFixR.LatGreen
