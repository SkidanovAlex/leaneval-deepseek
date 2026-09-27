import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.saddleModelPsi

/-!
# The saddle window block (chart form)

`Work.Drive.N2.saddleWindowBlock`: in a Morse chart of a saddle whose level function is (a non-zero
multiple of) the real part of the square of a complex coordinate `Z`, the model map
`Work.Drive.N2.saddlePsi η δ` (composed with `Z` and the inclusion `ℂ ↪ ℝ³`) is a *good drawing* of
the chart: smooth, injective on the levels of `f` there, and its differential is injective on
`ker (df)` there.  On the collar `2 - 2δ ≤ |Im Z²| ≤ 2` it is the model's *foot* map
(`(Ψ Z)² = -η + i·Im Z²` with the correct sign), which is the interface datum that the assembly with
the adjacent bands consumes.

This is the "critical window block" of the drawing for the compact `n = 2` case in the form the
assemblies consume; the global assembly is described in
`NOTES_S_NEXT_window_matching_CRUX.md`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

/-- The component linear map `ℂ → (Fin 3 → ℝ)`, `w ↦ (re w, im w, 0)`. -/
noncomputable def cE3L : ℂ →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin 3 =>
    if i = 0 then Complex.reCLM else if i = 1 then Complex.imCLM else 0)

/-- The inclusion `ℂ ↪ ℝ³`, `w ↦ (re w, im w, 0)`, as a continuous linear map. -/
noncomputable def cE3 : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp cE3L

@[simp] lemma cE3_apply_zero (w : ℂ) : (cE3 w) 0 = w.re := by
  simp [cE3, cE3L, ContinuousLinearMap.pi_apply]

@[simp] lemma cE3_apply_one (w : ℂ) : (cE3 w) 1 = w.im := by
  simp [cE3, cE3L, ContinuousLinearMap.pi_apply]

@[simp] lemma cE3_apply_two (w : ℂ) : (cE3 w) 2 = 0 := by
  simp [cE3, cE3L, ContinuousLinearMap.pi_apply]

lemma cE3_injective : Function.Injective cE3 := by
  intro u v h
  have h1 : (cE3 u) 0 = (cE3 v) 0 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) h
  have h2 : (cE3 u) 1 = (cE3 v) 1 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) h
  simp only [cE3_apply_zero, cE3_apply_one] at h1 h2
  exact Complex.ext h1 h2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The chart-form saddle window block.**  `Z` is the complex coordinate of a Morse chart of a
saddle, and `f = c + lam * Re (Z²)` on the open set `U`.  Then the model map `Ψ = saddlePsi η δ`
composed with `Z` (and the inclusion `ℂ ↪ ℝ³`) is a good drawing on `U`, and on the collar it is the
model's foot map. -/
theorem saddleWindowBlock (f : M → ℝ) (U : Set M) (hU : IsOpen U) (Z : M → ℂ) (c lam : ℝ)
    (hlam : lam ≠ 0)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U)
    (hZinj : Set.InjOn Z U)
    (hlev : ∀ y ∈ U, f y = c + lam * (Z y ^ 2).re)
    {η δ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10) :
    ∃ g : M → EuclideanSpace ℝ (Fin 3),
      (∀ x ∈ U, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) g x) ∧
      (∀ x ∈ U, ∀ y ∈ U, f x = f y → g x = g y → x = y) ∧
      (∀ x ∈ U, |((Z x) ^ 2).re| ≤ η → 2 - 2 * δ ≤ |((Z x) ^ 2).im| → |((Z x) ^ 2).im| ≤ 2 →
        (saddlePsi η δ (Z x)) ^ 2 = ((-η : ℝ) : ℂ) + (((Z x) ^ 2).im : ℂ) * Complex.I ∧
        0 < ((saddlePsi η δ (Z x)) * (starRingEnd ℂ) (Z x)).re) ∧
      (∀ x ∈ U, Z x = 0 → saddlePsi η δ (Z x) = Z x) := by
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  have hδ₂ : δ < 1 / 2 := by linarith
  have hr₀pos : (0:ℝ) < (2 - 4 * δ) / 4 := by linarith
  have hΨidz : ∀ z : ℂ, ‖z‖ < (2 - 4 * δ) / 4 → saddlePsi η δ z = z :=
    fun z hz => saddlePsi_eq_self_of_norm_lt hδ hδ₂ hz
  have hΨcol : ∀ z : ℂ, |(z ^ 2).re| ≤ η → 2 - 2 * δ ≤ |(z ^ 2).im| → |(z ^ 2).im| ≤ 2 →
      (saddlePsi η δ z) ^ 2 = ((-η : ℝ) : ℂ) + ((z ^ 2).im : ℂ) * Complex.I ∧
      0 < ((saddlePsi η δ z) * (starRingEnd ℂ) z).re :=
    fun z hs hw₁ hw₂ => by simpa using saddlePsi_collar hη hη' hδ hδ' hs hw₁ hw₂
  refine ⟨fun x => cE3 (saddlePsi η δ (Z x)), ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro x hx
    have hZx : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x :=
      hZsm.contMDiffAt (hU.mem_nhds hx)
    have hΨx : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (saddlePsi η δ) (Z x) :=
      (contDiff_saddlePsi η δ hδ hδ₂).contMDiff.contMDiffAt
    have h1 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => saddlePsi η δ (Z y)) x := hΨx.comp x hZx
    exact (cE3.contMDiff.contMDiffAt).comp x h1
  · -- injectivity on the levels
    intro x hx y hy hf hg
    have hΨ : saddlePsi η δ (Z x) = saddlePsi η δ (Z y) := cE3_injective hg
    have hre : (Z x ^ 2).re = (Z y ^ 2).re := by
      have h := hf
      rw [hlev x hx, hlev y hy] at h
      exact mul_left_cancel₀ hlam (by linarith : lam * (Z x ^ 2).re = lam * (Z y ^ 2).re)
    exact hZinj hx hy (saddlePsi_injOn_level hδ (le_of_lt h2) hre hΨ)
  · -- the collar rows
    intro x hx hre h1 h2'
    exact hΨcol (Z x) hre h1 h2'
  · -- `Ψ = 0` at `0`
    intro x hx hx0
    rw [hx0]
    exact hΨidz 0 (by simpa using hr₀pos)

/-- The derivative of the "square" map, in coordinates. -/
lemma fderiv_sq_re_apply (z w : ℂ) :
    (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z) w = (2 * z * w).re := by
  have h1 : HasFDerivAt (fun ζ : ℂ => ζ ^ 2)
      ((2 * z) • ContinuousLinearMap.id ℝ ℂ) z := by
    simpa [two_nsmul, pow_one] using hasFDerivAt_pow (𝕜 := ℝ) 2 (x := z)
  have h2 : HasFDerivAt (fun ζ : ℂ => (ζ ^ 2).re)
      (Complex.reCLM.comp ((2 * z) • ContinuousLinearMap.id ℝ ℂ)) z :=
    Complex.reCLM.hasFDerivAt.comp z h1
  rw [h2.fderiv]
  rfl

/-- The derivative of the "square" map, imaginary part. -/
lemma fderiv_sq_im_apply (z w : ℂ) :
    (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).im) z) w = (2 * z * w).im := by
  have h1 : HasFDerivAt (fun ζ : ℂ => ζ ^ 2)
      ((2 * z) • ContinuousLinearMap.id ℝ ℂ) z := by
    simpa [two_nsmul, pow_one] using hasFDerivAt_pow (𝕜 := ℝ) 2 (x := z)
  have h2 : HasFDerivAt (fun ζ : ℂ => (ζ ^ 2).im)
      (Complex.imCLM.comp ((2 * z) • ContinuousLinearMap.id ℝ ℂ)) z :=
    Complex.imCLM.hasFDerivAt.comp z h1
  rw [h2.fderiv]
  rfl


end Work.Drive.N2
