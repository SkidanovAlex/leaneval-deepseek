import Mathlib
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.levelField_spec

/-!
# Non-degeneracy of the chart coordinates of the embedded surface

The ambient least-squares construction `modelRaw` inverts the Gram determinant
`gramDet A φ z = ‖∇u₀‖² ‖∇u₁‖² - ⟨∇u₀, ∇u₁⟩²` of the two gradients of the chart coordinates
`u_j = φ_j ∘ π`.  This file proves that at every point `e y` of the embedded surface with
`y ∈ φ.source` this determinant is non-zero: the curve `t ↦ e (φ.symm (φ y + t (a, b)))` has a
velocity whose pairings with `∇u_j` are the prescribed numbers `a`, `b`, so the two gradients are
linearly independent.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Drive.N2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- `uCoord A φ j` is `C^∞` near `e y` whenever `y ∈ φ.source`. -/
lemma contDiffAt_uCoord (A : AmbSetup M) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    {y : M} (hy : y ∈ φ.source) (j : Fin 2) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uCoord A φ j) (A.e y) := by
  have hyU : A.e y ∈ A.U := A.hUe ⟨y, rfl⟩
  have hπ : ContMDiffAt (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) A.π (A.e y) :=
    A.hπ.contMDiffAt (A.hU.mem_nhds hyU)
  have hφy : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z) (A.π (A.e y)) := by
    rw [A.hπe y]; exact hφ.contMDiffAt (φ.open_source.mem_nhds hy)
  have hcomp : ContMDiffAt (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => φ (A.π z)) (A.e y) :=
    hφy.comp (A.e y) hπ
  have h2 : ContMDiffAt (𝓡 5) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => φ (A.π z) j) (A.e y) :=
    ((coordProj j).contMDiffAt.comp (A.e y) hcomp)
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ (A.π z) j) (A.e y) :=
    (contMDiffAt_iff_contDiffAt).mp h2
  show ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ (A.π z) j) (A.e y)
  exact h3

/-- Differentiability of the chart coordinate at `e y`. -/
lemma differentiableAt_uCoord (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    {y : M} (hy : y ∈ φ.source) (j : Fin 2) :
    DifferentiableAt ℝ (uCoord A φ j) (A.e y) :=
  (contDiffAt_uCoord A φ hφ hy j).differentiableAt (by simp)

/-- **The pairing along the model curve.**  The velocity of the curve
`t ↦ e (φ.symm (φ y + t • (a, b)))` at `t = 0` pairs with `∇u_j` to the `j`-th coordinate of
`(a, b)`. -/
lemma fderiv_uCoord_curve (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    (hφ' : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => φ.symm u) φ.target)
    {y : M} (hy : y ∈ φ.source) (a b : ℝ) (j : Fin 2) :
    (fderiv ℝ (uCoord A φ j) (A.e y))
        ((fderiv ℝ (fun s => A.e (φ.symm s)) (φ y)) (vec2 a b)) = vec2 a b j := by
  have hu : φ y ∈ φ.target := φ.map_source hy
  have hcomp : ContMDiffOn (𝓡 2) (𝓡 5) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s => A.e (φ.symm s)) φ.target :=
    ContMDiffOn.comp (t := Set.univ) (f := fun s : EuclideanSpace ℝ (Fin 2) => φ.symm s)
      (g := A.e) (A.he.contMDiffOn (s := Set.univ)) hφ'
      (fun s _ => Set.mem_univ (A.e (φ.symm s)))
  have hcdiff : DifferentiableAt ℝ (fun s => A.e (φ.symm s)) (φ y) := by
    have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => A.e (φ.symm s)) φ.target :=
      (contMDiffOn_iff_contDiffOn).mp hcomp
    exact (hc.differentiableOn (by simp)).differentiableAt (φ.open_target.mem_nhds hu)
  have hγ : HasDerivAt (fun t : ℝ => φ y + t • vec2 a b) (vec2 a b) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const (vec2 a b)
    simpa using h.const_add (φ y)
  have hcurve : HasDerivAt (fun t : ℝ => A.e (φ.symm (φ y + t • vec2 a b)))
      ((fderiv ℝ (fun s => A.e (φ.symm s)) (φ y)) (vec2 a b)) 0 := by
    have hF : HasFDerivAt (fun s => A.e (φ.symm s)) (fderiv ℝ (fun s => A.e (φ.symm s)) (φ y))
        ((fun t : ℝ => φ y + t • vec2 a b) 0) := by
      simpa using hcdiff.hasFDerivAt
    simpa [Function.comp_def] using hF.comp_hasDerivAt (x := (0 : ℝ)) hγ
  have hchain : HasDerivAt (fun t : ℝ => uCoord A φ j (A.e (φ.symm (φ y + t • vec2 a b))))
      ((fderiv ℝ (uCoord A φ j) (A.e y))
        ((fderiv ℝ (fun s => A.e (φ.symm s)) (φ y)) (vec2 a b))) 0 := by
    have hF : HasFDerivAt (uCoord A φ j) (fderiv ℝ (uCoord A φ j) (A.e y))
        ((fun t : ℝ => A.e (φ.symm (φ y + t • vec2 a b))) 0) := by
      have h0 : (fun t : ℝ => A.e (φ.symm (φ y + t • vec2 a b))) 0 = A.e y := by
        simp [φ.left_inv hy]
      rw [h0]
      exact (differentiableAt_uCoord A φ hφ hy j).hasFDerivAt
    simpa [Function.comp_def] using hF.comp_hasDerivAt (x := (0 : ℝ)) hcurve
  have hev : (fun t : ℝ => uCoord A φ j (A.e (φ.symm (φ y + t • vec2 a b))))
      =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => φ y j + t * vec2 a b j) := by
    have hcont : Continuous fun t : ℝ => φ y + t • vec2 a b := by fun_prop
    have hmem : {t : ℝ | φ y + t • vec2 a b ∈ φ.target} ∈ 𝓝 (0 : ℝ) := by
      have h0 : (φ y + (0 : ℝ) • vec2 a b) = φ y := by simp
      refine hcont.continuousAt.preimage_mem_nhds ?_
      rw [h0]
      exact φ.open_target.mem_nhds hu
    filter_upwards [hmem] with t ht
    show φ (A.π (A.e (φ.symm (φ y + t • vec2 a b)))) j = φ y j + t * vec2 a b j
    rw [A.hπe, φ.right_inv ht]
    simp [PiLp.add_apply, PiLp.smul_apply]
  have h2 : HasDerivAt (fun t : ℝ => φ y j + t * vec2 a b j) (vec2 a b j) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).mul_const (vec2 a b j)
    simpa using h.const_add (φ y j)
  exact (hchain.congr_of_eventuallyEq hev.symm).unique h2

/-- **Surjectivity of the chart-coordinate derivative.**  For every pair `(a, b)` there is an
ambient vector `V` whose pairings with the two chart-coordinate derivatives at `e y` are `a` and
`b`. -/
theorem exists_pairing_uCoord (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    (hφ' : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => φ.symm u) φ.target)
    {y : M} (hy : y ∈ φ.source) (a b : ℝ) :
    ∃ V : EuclideanSpace ℝ (Fin 5),
      (fderiv ℝ (uCoord A φ 0) (A.e y)) V = a ∧
      (fderiv ℝ (uCoord A φ 1) (A.e y)) V = b := by
  refine ⟨(fderiv ℝ (fun s => A.e (φ.symm s)) (φ y)) (vec2 a b), ?_, ?_⟩
  · simpa using fderiv_uCoord_curve A φ hφ hφ' hy a b 0
  · simpa using fderiv_uCoord_curve A φ hφ hφ' hy a b 1

/-- If a pair of vectors has vanishing Gram determinant, the pairings with them cannot be
arbitrary. -/
lemma not_surj_of_gramDet_eq_zero {N : ℕ} (x y : EuclideanSpace ℝ (Fin N))
    (h : ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2 = 0) :
    ¬ (∀ a b : ℝ, ∃ V : EuclideanSpace ℝ (Fin N), inner ℝ x V = a ∧ inner ℝ y V = b) := by
  intro hsurj
  by_cases hy : y = 0
  · obtain ⟨V, -, hV⟩ := hsurj 0 1
    rw [hy, inner_zero_left] at hV
    exact one_ne_zero hV.symm
  · set Z : EuclideanSpace ℝ (Fin N) := ‖y‖ ^ 2 • x - inner ℝ x y • y with hZ
    have hfac : ‖x‖ ^ 2 * ‖y‖ ^ 2 = (inner ℝ x y) ^ 2 := by linarith
    have hZx : inner ℝ Z x = 0 := by
      rw [hZ, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, ← real_inner_comm y x]
      rw [mul_comm (‖y‖ ^ 2) (‖x‖ ^ 2), hfac]
      ring
    have hZy : inner ℝ Z y = 0 := by
      rw [hZ, inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm y x,
        real_inner_self_eq_norm_sq]
      ring
    have hZ0 : Z = 0 := by
      have hzz : inner ℝ Z Z = 0 := by
        rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, hZx, hZy, mul_zero, mul_zero,
          sub_zero]
      exact inner_self_eq_zero.mp hzz
    obtain ⟨V, hxV, hyV⟩ := hsurj 1 0
    have hZV : inner ℝ Z V = 0 := by rw [hZ0, inner_zero_left]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hxV, hyV, mul_one, mul_zero,
      sub_zero] at hZV
    have hy2 : ‖y‖ ^ 2 = 0 := by simpa using hZV
    exact hy (norm_eq_zero.mp (by nlinarith [hy2, norm_nonneg y]))

/-- **Non-degeneracy of the Gram determinant at points of the surface.** -/
theorem gramDet_ne_zero_of_mem_source {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (A : AmbSetup M) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    (hφ' : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => φ.symm u) φ.target)
    {y : M} (hy : y ∈ φ.source) :
    gramDet A φ (A.e y) ≠ 0 := by
  intro h0
  have hsurj : ∀ a b : ℝ, ∃ V : EuclideanSpace ℝ (Fin 5),
      inner ℝ (uGrad A φ 0 (A.e y)) V = a ∧ inner ℝ (uGrad A φ 1 (A.e y)) V = b := by
    intro a b
    obtain ⟨V, hV0, hV1⟩ := exists_pairing_uCoord A φ hφ hφ' hy a b
    refine ⟨V, ?_, ?_⟩
    · have hg := fderiv_eq_inner_grad (uCoord A φ 0) (A.e y) V
      simp only [uGrad]
      rw [← hg]
      exact hV0
    · have hg := fderiv_eq_inner_grad (uCoord A φ 1) (A.e y) V
      simp only [uGrad]
      rw [← hg]
      exact hV1
  exact not_surj_of_gramDet_eq_zero _ _ (by simpa [gramDet] using h0) hsurj

end Work.Drive.N2
