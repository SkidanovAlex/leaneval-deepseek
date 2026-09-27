import Mathlib
import Submission.Work.Drive.Morse

/-!
# Critical points read in a chart (`n = 2`)

For a smooth function `f` on a surface `M` and a point `z` in the source of the extended chart at
`x`, the condition `IsCritical f z` (the manifold derivative of `f` at `z` vanishes) is equivalent
to the vanishing of the ordinary derivative at `(extChartAt x) z` of the chart representative
`y ↦ f ((extChartAt x).symm y)`.

The proof is the chain rule for the manifold derivative applied to the factorization
`f = (f ∘ (extChartAt x).symm) ∘ (extChartAt x)` near `z`, together with the fact that the manifold
derivative of the chart is invertible (hence surjective), and the identification of the manifold
derivative of a map between vector spaces with the ordinary derivative.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

/-- Vanishing of the manifold derivative of `f` at `z` is equivalent to the vanishing of the
derivative of the chart representative `f ∘ (extChartAt x).symm` at the chart point of `z`. -/
lemma mfderiv_eq_zero_iff_chartRep {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x z : M) (hz : z ∈ (extChartAt (𝓡 2) x).source) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f z = 0 ↔
      fderiv ℝ (f ∘ (extChartAt (𝓡 2) x).symm) ((extChartAt (𝓡 2) x) z) = 0 := by
  let e := extChartAt (𝓡 2) x
  let g : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => f (e.symm y)
  show mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f z = 0 ↔ fderiv ℝ g (e z) = 0
  have hf_at' : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (e.symm (e z)) :=
    hf.mdifferentiableAt (by simp)
  have htarget : e z ∈ e.target := e.map_source hz
  have h_symm : MDifferentiableAt (𝓡 2) (𝓡 2) e.symm (e z) := by
    have h1 := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 2) (x := x) (z := e z) htarget
    exact h1.mdifferentiableAt (by rw [ModelWithCorners.range_eq_univ]; exact Filter.univ_mem)
  have hg_diff : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) g (e z) :=
    MDifferentiableAt.comp (e z) (g := f) hf_at' h_symm
  have he_diff : MDifferentiableAt (𝓡 2) (𝓡 2) e z := by
    have h : z ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := by
      rw [← extChartAt_source (𝓡 2)]
      exact hz
    exact mdifferentiableAt_extChartAt h
  have hcongr : (g ∘ e) =ᶠ[nhds z] f := by
    filter_upwards [isOpen_extChartAt_source (I := 𝓡 2) x |>.mem_nhds hz] with y hy
    simp only [Function.comp_apply, g]
    rw [e.left_inv hy]
  have key : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f z
      = (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g (e z)).comp (mfderiv (𝓡 2) (𝓡 2) e z) := by
    have h := hcongr.mfderiv_eq (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ))
    rw [mfderiv_comp z hg_diff he_diff] at h
    rw [h]
    ext v
    rfl
  have hA : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g (e z) = fderiv ℝ g (e z) := mfderiv_eq_fderiv
  have hBC := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := 𝓡 2) (x := x) hz
  -- Restate everything with the tangent spaces unfolded, so that the linear-algebra steps below
  -- are syntactically well typed.
  let F : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f z
  let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g (e z)
  let B : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) := mfderiv (𝓡 2) (𝓡 2) e z
  let C : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderivWithin (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) (extChartAt (𝓡 2) x).symm
      (Set.range (𝓡 2)) ((extChartAt (𝓡 2) x) z)
  change F = 0 ↔ fderiv ℝ g (e z) = 0
  have keyF : F = A.comp B := key
  have hA' : A = fderiv ℝ g (e z) := hA
  have hBC' : B.comp C = ContinuousLinearMap.id ℝ _ := hBC
  have hS : Function.Surjective B := by
    intro w
    exact ⟨C w, by
      have h :=
        congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) => L w) hBC'
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h⟩
  constructor
  · intro h
    have hAB : (fderiv ℝ g (e z)).comp B = 0 := by
      rw [← hA', ← keyF]
      exact h
    ext w
    obtain ⟨v, hv⟩ := hS w
    rw [← hv]
    have h2 : ((fderiv ℝ g (e z)).comp B) v = 0 := by rw [hAB]; rfl
    simpa using h2
  · intro h
    rw [keyF, hA', h]
    simp

theorem isCritical_iff_chartRep {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x : M) :
    ∀ z ∈ (extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x).source,
      Work.Drive.Morse.IsCritical f z ↔
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => f ((extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x).symm y)) ((extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x) z) = 0 := by
  intro z hz
  rw [Work.Drive.Morse.IsCritical]
  exact mfderiv_eq_zero_iff_chartRep f hf x z hz

end Work.Drive.N2
