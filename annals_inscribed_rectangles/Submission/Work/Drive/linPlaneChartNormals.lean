import Mathlib
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.linVecC_smul_surjective
import Submission.Work.Drive.hVNormalForm

/-!
# The normal functionals of the linear planes

`linearPlaneChart.lean` defines the linear plane `linSub φ = φ (linStd)` of the level `c` (its chart
presentation `linPlaneChart φ c hc`) and the functional `linFun φ` "whose kernel is the plane
`linSub φ`" — but that last statement is *not proved* there.  It is the dictionary that turns the
*general position* of three linear planes (the hypothesis of `Work.Drive.projective_planes_meet_oddly`
and `Work.Drive.ncard_projLine_inter_eq_one`) into a statement about three linear functionals, which is
the form in which the workspace's `hV` criterion
(`Work.Drive.iInf_ker_eq_bot_iff_linearIndependent`, `hVNormalForm.lean`) consumes it.

This file proves the two dictionary lemmas:

* `Work.Drive.linStd_eq_kerProj` — the standard plane `linStd` *is* the hyperplane `{v : v 3 = 0}` of
  `ℂ² = ℝ⁴` (equivalently `ker (v ↦ v 3)`), so the sphere lift `linVecC` sweeps exactly that hyperplane;
* `Work.Drive.ker_linFun` — `(linFun φ).ker = linSub φ` for every linear equivalence `φ`.

The proof of the first uses the surjectivity of the sphere lift on the closed disk
(`Work.Drive.linVecC_smul_surjective`): every vector with `v 3 = 0` is a real multiple of some
`linVecC z`, while `linVecC z` itself always has fourth coordinate `0`.
-/

namespace Work.Drive

noncomputable section

open scoped Manifold ContDiff

/-- The fourth coordinate of the standard sphere lift vanishes. -/
@[simp] lemma c₂_im (v : Eucl 3) : (c₂ v).im = v 3 := by simp [c₂]

@[simp] lemma linVecC_three_eq_zero (z : ℂ) : linVecC z 3 = 0 := by
  rw [show linVecC z 3 = (c₂ (linVecC z)).im from by simp [c₂], linVecC, c₂_ofComplex]
  exact Complex.ofReal_im _

/-- A vector of `ℂ² = ℝ⁴` with fourth coordinate `0` is determined by its first two complex
coordinates. -/
lemma ofComplex_c₁_c₂_of_apply_three_eq_zero {v : Eucl 3} (hv : v 3 = 0) :
    ofComplex (c₁ v) ((v 2 : ℝ) : ℂ) = v := by
  have h2 : ((v 2 : ℝ) : ℂ) = c₂ v := by rw [c₂]; simp [hv]
  rw [h2, ofComplex_c₁_c₂ v]

/-- **The standard plane is the hyperplane `{v : v 3 = 0}`.** -/
theorem linStd_eq_kerProj :
    linStd = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 3).ker := by
  refine le_antisymm ?_ ?_
  · rw [linStd, Submodule.span_le]
    rintro v ⟨z, rfl⟩
    exact linVecC_three_eq_zero z
  · intro v hv
    have hv3 : v 3 = 0 := hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact Submodule.zero_mem _
    · have hw : c₁ v ≠ 0 ∨ v 2 ≠ 0 := by
        by_contra h
        push Not at h
        refine hv0 ?_
        ext i
        fin_cases i
        · simpa [c₁] using congrArg Complex.re h.1
        · simpa [c₁] using congrArg Complex.im h.1
        · simpa using h.2
        · simpa using hv3
      obtain ⟨z, a, -, -, haz⟩ := linVecC_smul_surjective (w₁ := c₁ v) (t := v 2) hw
      rw [← ofComplex_c₁_c₂_of_apply_three_eq_zero hv3, ← haz]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨z, rfl⟩)

/-- **The kernel of `linFun φ` is the plane `linSub φ`.** -/
theorem ker_linFun (φ : Eucl 3 ≃L[ℝ] Eucl 3) : (linFun φ).ker = linSub φ := by
  ext v
  rw [LinearMap.mem_ker, linFun_apply, linSub, Submodule.mem_map]
  constructor
  · intro hv
    exact ⟨φ.symm v, by rw [linStd_eq_kerProj]; exact hv, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    rw [linStd_eq_kerProj] at hw
    simpa using hw

/-- **General position of three linear planes is the independence of their normal functionals.**
`linSub (Φ k)` are three `3`-dimensional subspaces of `ℝ⁴` (the linear planes of `ℝP³`), and their
intersection is a line (dimension `1 = 4 - 3`) exactly when the normal functionals `linFun (Φ k)` are
linearly independent (`Work.Drive.finrank_iInf_ker_eq_iff_linearIndependent`).  This is the form in
which the counting lane consumes the general position of the end faces; note the planes are the
*projective* planes `projLine (linSub (Φ k))`, which then meet in exactly one point. -/
theorem finrank_iInf_linSub_eq_one_iff_linearIndependent (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) :
    Module.finrank ℝ ↥(⨅ k, linSub (Φ k)) = 1 ↔
      LinearIndependent ℝ (fun k : Fin 3 => linFun (Φ k)) := by
  have h1 : (⨅ k, linSub (Φ k)) = ⨅ k, (linFun (Φ k)).ker := by
    simp only [← ker_linFun]
  rw [h1]
  have hcard : Fintype.card (Fin 3) ≤ Module.finrank ℝ (Eucl 3) := by simp [Eucl]
  simpa using finrank_iInf_ker_eq_iff_linearIndependent (fun k : Fin 3 => linFun (Φ k)) hcard

end

end Work.Drive
