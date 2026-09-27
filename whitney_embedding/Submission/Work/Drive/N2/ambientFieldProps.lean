import Mathlib
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.levelField_spec
import Submission.Work.Drive.N2.gramDetNeZero

/-!
# The two computations on the ambient model field

`modelField A φ β s₁ s₂` is the ambient vector field which, along the embedded surface, is the
push-forward of the model field `b (‖u‖²) • (s₁ u 0, s₂ u 1)` of the chart `φ`.  This file proves
the two computations used by the flow assembly:

* `fderiv_uCoord_modelField` — the chart coordinate `u_j = φ_j ∘ π` varies along `modelField`
  with velocity `chartVel β s₁ s₂ (φ y) j` (the model ODE in the chart);
* `fderiv_piF_modelField` — the ambient function `f ∘ π` varies along `modelField` with velocity
  `2 * ‖φ y‖² * β (‖φ y‖²)`, i.e. at the rate `θ (‖u‖²) = 2 ‖u‖² β (‖u‖²)` at which the model field
  raises `chartQ = s₁ u₀² + s₂ u₁²`.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Drive.N2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

namespace AmbSetup

variable (A : AmbSetup M)

/-- `E = e ∘ π` is a retraction: `E (E z) = E z`. -/
lemma E_idem (z : EuclideanSpace ℝ (Fin 5)) : A.E (A.E z) = A.E z := by
  simp [AmbSetup.E, A.hπe]

lemma E_apply_e (y : M) : A.E (A.e y) = A.e y := by simp [AmbSetup.E, A.hπe]

/-- `E` is `C^∞` near `e y`. -/
lemma contDiffAt_E (y : M) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.E (A.e y) := by
  have hyU : A.e y ∈ A.U := A.hUe ⟨y, rfl⟩
  have hπ : ContMDiffAt (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) A.π (A.e y) :=
    A.hπ.contMDiffAt (A.hU.mem_nhds hyU)
  have he : ContMDiffAt (𝓡 2) (𝓡 5) ((⊤ : ℕ∞) : WithTop ℕ∞) A.e (A.π (A.e y)) :=
    A.he.contMDiffAt
  have h2 : ContMDiffAt (𝓡 5) (𝓡 5) ((⊤ : ℕ∞) : WithTop ℕ∞) A.E (A.e y) :=
    he.comp (A.e y) hπ
  exact (contMDiffAt_iff_contDiffAt).mp h2

/-- The chart coordinate `u_j` is unchanged by `E`: `u_j ∘ E = u_j`. -/
lemma uCoord_comp_E (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (j : Fin 2) :
    (fun z => uCoord A φ j (A.E z)) = uCoord A φ j := by
  funext z
  simp only [uCoord, AmbSetup.E, A.hπe]

end AmbSetup

/-- **The model ODE in the chart.**  Along the ambient model field, the `j`-th chart coordinate
varies with velocity `chartVel β s₁ s₂ (φ y) j`. -/
theorem fderiv_uCoord_modelField {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (A : AmbSetup M) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat)
      (fun y => φ y) φ.source)
    (hφ' : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat)
      (fun u => φ.symm u) φ.target)
    (β : ℝ → ℝ) (s₁ s₂ : ℝ) {y : M} (hy : y ∈ φ.source) (j : Fin 2) :
    (fderiv ℝ (uCoord A φ j) (A.e y))
      (modelField A φ β s₁ s₂ (A.e y))
      = chartVel β s₁ s₂ (φ y) j := by
  have hdet : gramDet A φ (A.e y) ≠ 0 := gramDet_ne_zero_of_mem_source A φ hφ hφ' hy
  have hpair := inner_gram_leastSquares (uGrad A φ 0 (A.e y)) (uGrad A φ 1 (A.e y))
    (chartVel β s₁ s₂ (φ (A.π (A.e y))) 0) (chartVel β s₁ s₂ (φ (A.π (A.e y))) 1)
    (by simpa [gramDet] using hdet)
  have hpairgen : ∀ k : Fin 2, inner ℝ (uGrad A φ k (A.e y)) (modelRaw A φ β s₁ s₂ (A.e y))
      = chartVel β s₁ s₂ (φ y) k := by
    intro k
    have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk with hk | hk
    · rw [hk]
      simpa only [modelRaw, gramDet, A.hπe y] using hpair.1
    · rw [hk]
      simpa only [modelRaw, gramDet, A.hπe y] using hpair.2
  have hproj : (fderiv ℝ (uCoord A φ j) (A.e y)) (modelField A φ β s₁ s₂ (A.e y))
      = (fderiv ℝ (uCoord A φ j) (A.e y)) (modelRaw A φ β s₁ s₂ (A.e y)) := by
    have hE : DifferentiableAt ℝ A.E (A.e y) := (A.contDiffAt_E y).differentiableAt (by simp)
    have hF : DifferentiableAt ℝ (uCoord A φ j) (A.E (A.e y)) := by
      rw [A.E_apply_e y]
      exact (contDiffAt_uCoord A φ hφ hy j).differentiableAt (by simp)
    have hcomp : HasFDerivAt (fun w => uCoord A φ j (A.E w))
        ((fderiv ℝ (uCoord A φ j) (A.E (A.e y))).comp (fderiv ℝ A.E (A.e y))) (A.e y) :=
      hF.hasFDerivAt.comp (A.e y) hE.hasFDerivAt
    have heq : (fun w => uCoord A φ j (A.E w)) = uCoord A φ j := A.uCoord_comp_E φ j
    have hfe : fderiv ℝ (fun w => uCoord A φ j (A.E w)) (A.e y)
        = fderiv ℝ (uCoord A φ j) (A.e y) := by rw [heq]
    have h1 : fderiv ℝ (uCoord A φ j) (A.e y)
        = (fderiv ℝ (uCoord A φ j) (A.e y)).comp (fderiv ℝ A.E (A.e y)) := by
      have h := hcomp.fderiv
      rw [hfe] at h
      rw [A.E_apply_e y] at h
      exact h
    have h2 := congrArg (fun (L : EuclideanSpace ℝ (Fin 5) →L[ℝ] ℝ) =>
      L (modelRaw A φ β s₁ s₂ (A.e y))) h1
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [modelField, ← h2]
  rw [hproj, fderiv_eq_inner_grad]
  exact hpairgen j

/-- **The rate at which the model field raises `f`.**  Along the ambient model field the ambient
function `f ∘ π` varies with velocity `2 * ‖φ y‖² * β (‖φ y‖²)`, i.e. at the rate
`θ (‖u‖²) = 2 ‖u‖² β (‖u‖²)` at which the chart model raises `chartQ = s₁ u₀² + s₂ u₁²`. -/
theorem fderiv_piF_modelField {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (A : AmbSetup M) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat)
      (fun y => φ y) φ.source)
    (hφ' : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat)
      (fun u => φ.symm u) φ.target)
    (f : M → ℝ) (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f)
    (β : ℝ → ℝ) (s₁ s₂ : ℝ)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) (c : ℝ)
    (hval : ∀ z ∈ φ.source, f z = c + chartQ φ s₁ s₂ z)
    {y : M} (hy : y ∈ φ.source) :
    (fderiv ℝ (fun z => f (A.π z)) (A.e y))
      (modelField A φ β s₁ s₂ (A.e y))
      = 2 * ‖φ y‖ ^ 2 * β (‖φ y‖ ^ 2) := by
  have _ := hf
  -- the ambient function is eventually the constant plus the model quadratic form
  have hconv : ∀ᶠ z in 𝓝 (A.e y), A.π z ∈ φ.source := by
    have hπcont : ContinuousAt A.π (A.e y) :=
      (A.hπ.contMDiffAt (A.hU.mem_nhds (A.hUe ⟨y, rfl⟩))).continuousAt
    refine hπcont.preimage_mem_nhds ?_
    rw [A.hπe y]
    exact φ.open_source.mem_nhds hy
  let Q : EuclideanSpace ℝ (Fin 5) → ℝ :=
    (fun z => s₁ * uCoord A φ 0 z ^ 2) + fun z => s₂ * uCoord A φ 1 z ^ 2
  have hev : (fun z => f (A.π z)) =ᶠ[𝓝 (A.e y)] fun z => c + Q z := by
    filter_upwards [hconv] with z hz
    rw [hval (A.π z) hz]
    simp only [chartQ, uCoord, Q, Pi.add_apply]
  -- the derivative of the quadratic form
  have hD0 : HasFDerivAt (uCoord A φ 0) (fderiv ℝ (uCoord A φ 0) (A.e y)) (A.e y) :=
    ((contDiffAt_uCoord A φ hφ hy 0).differentiableAt (by simp)).hasFDerivAt
  have hD1 : HasFDerivAt (uCoord A φ 1) (fderiv ℝ (uCoord A φ 1) (A.e y)) (A.e y) :=
    ((contDiffAt_uCoord A φ hφ hy 1).differentiableAt (by simp)).hasFDerivAt
  have hsum : HasFDerivAt Q
      ((s₁ • (((2 : ℕ) • uCoord A φ 0 (A.e y) ^ (2 - 1)) • fderiv ℝ (uCoord A φ 0) (A.e y)))
        + (s₂ • (((2 : ℕ) • uCoord A φ 1 (A.e y) ^ (2 - 1)) •
            fderiv ℝ (uCoord A φ 1) (A.e y)))) (A.e y) :=
    (hD0.pow 2).const_mul s₁ |>.add ((hD1.pow 2).const_mul s₂)
  have hgoal : (fderiv ℝ Q (A.e y)) (modelField A φ β s₁ s₂ (A.e y))
      = 2 * ‖φ y‖ ^ 2 * β (‖φ y‖ ^ 2) := by
    rw [hsum.fderiv]
    have hy0 : uCoord A φ 0 (A.e y) = (φ y) 0 := by simp [uCoord, A.hπe]
    have hy1 : uCoord A φ 1 (A.e y) = (φ y) 1 := by simp [uCoord, A.hπe]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hy0, hy1, smul_eq_mul]
    rw [fderiv_uCoord_modelField A φ hφ hφ' β s₁ s₂ hy 0,
      fderiv_uCoord_modelField A φ hφ hφ' β s₁ s₂ hy 1]
    rw [← quadForm_chartVel β hs₁ hs₂ (φ y)]
    ring
  rw [hev.fderiv_eq, fderiv_const_add c]
  exact hgoal

end Work.Drive.N2

