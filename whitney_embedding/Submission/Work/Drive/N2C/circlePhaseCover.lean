import Mathlib
import Submission.Work.Drive.N2C.circlePhase

/-!
# A finite phase cover of a periodic embedded circle

From the local phase patches (`∀ t₀, ∃ U ∋ γ t₀, ∃ φ` smooth on `U` with `φ (γ t) ≡ t` mod `1` on
`U`) and compactness of the circle, we extract a *finite* family of phase patches covering the
curve: a `CirclePhaseCover`.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- **A finite phase cover from local phase patches.** -/
theorem exists_circlePhaseCover_of_localPhase {γ : ℝ → M} (hγc : Continuous γ)
    (hper : Function.Periodic γ 1)
    (h : ∀ t₀ : ℝ, ∃ (U : Set M) (φ : M → ℝ), IsOpen U ∧ γ t₀ ∈ U ∧
      ContMDiffOn (𝓡 2) (𝓘(ℝ,ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) φ U ∧
      ∀ y ∈ U, ∀ t : ℝ, γ t = y → ∃ k : ℤ, φ y = t + k) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (CirclePhaseCover γ ι) := by
  classical
  choose Ufun φfun hUopen hUt hφ hphase using h
  -- the curve meets the compact parameter interval in a compact set, which the `Ufun` cover
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover (isCompact_Icc.image hγc)
      Ufun hUopen (fun y hy => by
        obtain ⟨t, ht, rfl⟩ := hy
        exact mem_iUnion.mpr ⟨t, hUt t⟩)
  have hmemK : ∀ x : ℝ, γ x ∈ γ '' Set.Icc (0:ℝ) 1 := by
    intro x
    refine ⟨Int.fract x, ⟨Int.fract_nonneg x, le_of_lt (Int.fract_lt_one x)⟩, ?_⟩
    have h1 := (hper.zsmul ⌊x⌋ (Int.fract x)).symm
    simp only [zsmul_one] at h1
    rw [Int.fract_add_floor] at h1
    exact h1
  refine ⟨{t : ℝ // t ∈ F}, inferInstance, ⟨?_⟩⟩
  refine
    { U := fun i => Ufun i.1
      φ := fun i => φfun i.1
      isOpen_U := fun i => hUopen i.1
      contMDiff_φ := fun i => hφ i.1
      cover := ?_
      phase := fun i => hphase i.1 }
  intro x hx
  obtain ⟨x, rfl⟩ := hx
  have hK := hmemK x
  have := hF hK
  simp only [mem_iUnion, exists_prop, Finset.mem_coe] at this
  obtain ⟨t, ht, hxt⟩ := this
  exact mem_iUnion.mpr ⟨⟨t, ht⟩, hxt⟩

end Work.Drive.N2C
