import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ManifoldParity.InterSetDefs
import Submission.Work.Drive.ManifoldParity.Transfer

/-!
# The `BoxThree` form of the loop-vs-chain regularity data

`Work.Drive.BoxThree A D` is the **three-clause form** of the regularity data of a family `A` of loops
(`A : ℝ² → M`, two parameters) against a chain `D : ℝ³ → M`, *relative to the five-box*
`unitBox 4 = [0,1]² × [0,1]³`:

1. at every meet `x ∈ unitBox 4` the two tangent ranges span;
2. no meet in the box lies on **two** faces of the box;
3. at every meet in the box which lies on a face coordinate `i`, there is a common tangent direction
   `(σ, τ)` with `mkPart σ τ i ≠ 0` (the *crossing* condition).

This is verbatim the shape produced by the parametric-Sard assembly of the loop-family data
(`Work.Drive.loopFamData_of_good_family`'s conclusion with `K = unitBox 4`), and it is the form in
which a *producer* can supply the four clauses of `Work.Drive.DiamFamRegBox`: see
`Work.Drive.loopBoxData_of_boxThree`, which converts it to the `(u,x)`-form.

The declarations here are generic in the smooth `4`-manifold `M`, so that they can be used in files
which do not carry the charted-space instances of `CappingSpace`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The three-clause box form of the regularity data** of a two-parameter loop family `A` against a
chain `D` (see the module docstring). -/
def BoxThree (A : EuclideanSpace ℝ (Fin 2) → M) (D : EuclideanSpace ℝ (Fin 3) → M) : Prop :=
  (∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → A (sqPart x) = D (cbPart x) →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) A (sqPart x)).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) D (cbPart x)).toLinearMap = ⊤) ∧
  (∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → A (sqPart x) = D (cbPart x) →
    ¬ (∃ i j : Fin 5, i ≠ j ∧ (x i = 0 ∨ x i = 1) ∧ (x j = 0 ∨ x j = 1))) ∧
  (∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → A (sqPart x) = D (cbPart x) →
    ∀ i : Fin 5, (x i = 0 ∨ x i = 1) → (∀ j : Fin 5, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) →
    ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
      mfderiv (𝓡 2) (𝓡 4) A (sqPart x) σ = mfderiv (𝓡 3) (𝓡 4) D (cbPart x) τ ∧
      mkPart σ τ i ≠ 0)

/-- **The two clauses of `DiamFamRegBox` attached to a single loop family**: the transversality at
every meet in the box, and the face condition at every boundary meet. -/
def LoopBoxData (A : EuclideanSpace ℝ (Fin 2) → M) (D : EuclideanSpace ℝ (Fin 3) → M) : Prop :=
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A u = D x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) A u).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) D x).toLinearMap = ⊤) ∧
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A u = D x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
    (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
          mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ τ j ≠ 0))

/-- **`BoxThree` gives `LoopBoxData`**: the `(u,x)`-form of the three box clauses, with the face
coordinate split into its square and cube blocks. -/
theorem loopBoxData_of_boxThree {A : EuclideanSpace ℝ (Fin 2) → M} {D : EuclideanSpace ℝ (Fin 3) → M}
    (h : BoxThree A D) : LoopBoxData A D := by
  obtain ⟨h1, h2, h3⟩ := h
  constructor
  · intro u x heq hu hx
    have hbox : mkPart u x ∈ Submission.Drive.unitBox 4 :=
      (mem_unitBox_five_iff _).mpr ⟨by rwa [sqPart_mkPart], by rwa [cbPart_mkPart]⟩
    have hsq : sqPart (mkPart u x) = u := sqPart_mkPart u x
    have hcb : cbPart (mkPart u x) = x := cbPart_mkPart u x
    have hmeet : A (sqPart (mkPart u x)) = D (cbPart (mkPart u x)) := by
      rw [hsq, hcb]; exact heq
    have hres := h1 (mkPart u x) hbox hmeet
    rwa [hsq, hcb] at hres
  · intro u x heq hu hx hbd
    have hbox : mkPart u x ∈ Submission.Drive.unitBox 4 :=
      (mem_unitBox_five_iff _).mpr ⟨by rwa [sqPart_mkPart], by rwa [cbPart_mkPart]⟩
    have hsq : sqPart (mkPart u x) = u := sqPart_mkPart u x
    have hcb : cbPart (mkPart u x) = x := cbPart_mkPart u x
    have hmeet : A (sqPart (mkPart u x)) = D (cbPart (mkPart u x)) := by
      rw [hsq, hcb]; exact heq
    -- the values of `mkPart u x` on the two blocks
    have sq_at : ∀ i' : Fin 2, (mkPart u x) (sqIdx i') = u i' := by
      intro i'
      show sqPart (mkPart u x) i' = u i'
      rw [hsq]
    have cb_at : ∀ j' : Fin 3, (mkPart u x) (cbIdx j') = x j' := by
      intro j'
      show cbPart (mkPart u x) j' = x j'
      rw [hcb]
    -- the point is on the boundary of the five-box
    have hbd5 : mkPart u x ∈ Submission.Drive.unitBoxBdry 4 := by
      rw [unitBoxBdry_iff]
      refine ⟨hbox, ?_⟩
      rcases hbd with h | h
      · rw [unitBoxBdry_iff] at h
        obtain ⟨-, i, hi⟩ := h
        exact ⟨sqIdx i, by rw [sq_at i]; exact hi⟩
      · rw [unitBoxBdry_iff] at h
        obtain ⟨-, j, hj⟩ := h
        exact ⟨cbIdx j, by rw [cb_at j]; exact hj⟩
    obtain ⟨-, i, hi⟩ := (unitBoxBdry_iff 4 (mkPart u x)).mp hbd5
    -- clause 2: no other face coordinate
    have hother : ∀ j : Fin 5, j ≠ i → (mkPart u x) j ∈ Set.Ioo (0 : ℝ) 1 := by
      intro j hj
      have hle := hbox j
      rw [Set.mem_Icc] at hle
      have hne0 : (mkPart u x) j ≠ 0 := fun h =>
        h2 (mkPart u x) hbox hmeet ⟨j, i, hj, Or.inl h, hi⟩
      have hne1 : (mkPart u x) j ≠ 1 := fun h =>
        h2 (mkPart u x) hbox hmeet ⟨j, i, hj, Or.inr h, hi⟩
      exact ⟨lt_of_le_of_ne hle.1 (Ne.symm hne0), lt_of_le_of_ne hle.2 hne1⟩
    obtain ⟨σ, τ, hστ0, hne⟩ := h3 (mkPart u x) hbox hmeet i hi hother
    have hστ : mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ := by
      rw [hsq, hcb] at hστ0
      exact hστ0
    -- split the face coordinate into its square and cube blocks
    revert hi hne hother
    refine Fin.addCases (m := 2) (n := 3) (motive := fun i =>
      ((mkPart u x) i = 0 ∨ (mkPart u x) i = 1) →
      (∀ j : Fin 5, j ≠ i → (mkPart u x) j ∈ Set.Ioo (0 : ℝ) 1) → (mkPart σ τ) i ≠ 0 → _) ?_ ?_ i
    · intro i' hi' hother' hne'
      left
      have hi2 : u i' = 0 ∨ u i' = 1 := by
        have hh : (mkPart u x) (sqIdx i') = 0 ∨ (mkPart u x) (sqIdx i') = 1 := hi'
        rwa [sq_at i'] at hh
      have hne2 : σ i' ≠ 0 := by
        have hh : (mkPart σ τ) (sqIdx i') ≠ 0 := hne'
        rwa [mkPart_sqIdx] at hh
      refine ⟨i', hi2, ?_, ?_, σ, τ, hστ, hne2⟩
      · intro j hj
        have hji : sqIdx j ≠ sqIdx i' := by
          intro h
          exact hj (Fin.ext (by have := congrArg Fin.val h; simpa using this))
        have hh : (mkPart u x) (sqIdx j) ∈ Set.Ioo (0 : ℝ) 1 := hother' (sqIdx j) hji
        rwa [sq_at j] at hh
      · intro j
        have hji : cbIdx j ≠ sqIdx i' := (sqIdx_ne_cbIdx i' j).symm
        have hh : (mkPart u x) (cbIdx j) ∈ Set.Ioo (0 : ℝ) 1 := hother' (cbIdx j) hji
        rwa [cb_at j] at hh
    · intro j' hj' hother' hne'
      right
      have hj2 : x j' = 0 ∨ x j' = 1 := by
        have hh : (mkPart u x) (cbIdx j') = 0 ∨ (mkPart u x) (cbIdx j') = 1 := hj'
        rwa [cb_at j'] at hh
      have hne2 : τ j' ≠ 0 := by
        have hh : (mkPart σ τ) (cbIdx j') ≠ 0 := hne'
        rwa [mkPart_cbIdx] at hh
      refine ⟨j', hj2, ?_, ?_, σ, τ, hστ, hne2⟩
      · intro k hk
        have hkj : cbIdx k ≠ cbIdx j' := by
          intro h
          exact hk (Fin.ext (by have := congrArg Fin.val h; simpa using this))
        have hh : (mkPart u x) (cbIdx k) ∈ Set.Ioo (0 : ℝ) 1 := hother' (cbIdx k) hkj
        rwa [cb_at k] at hh
      · intro i'
        have hij : sqIdx i' ≠ cbIdx j' := sqIdx_ne_cbIdx i' j'
        have hh : (mkPart u x) (sqIdx i') ∈ Set.Ioo (0 : ℝ) 1 := hother' (sqIdx i') hij
        rwa [sq_at i'] at hh

end

end Work.Drive
