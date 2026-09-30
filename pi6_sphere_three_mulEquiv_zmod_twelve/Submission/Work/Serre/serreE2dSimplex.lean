import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Serre.E0SimplexDefs
import Submission.Work.Cohomology.relChainsHomeomorphCompat
import Submission.Work.Serre.serreE2d
import Submission.Work.StemsB.EucCubeAffine
import Submission.Work.StemsB.cohomology_collar_iso
import Submission.Work.Serre.stdSimplexBdryHomology

set_option synthInstance.maxHeartbeats 400000

/-!
# E2(d) for the standard simplex pair `(Δᵖ, ∂Δᵖ)`

`Work.Serre.serreE2dSimplex` is the simplex form of the E2(d) statement: for a Serre fibration
`q : X → B`, a map `τ : Δᵖ → B` and a point `d₀ : Δᵖ`, the relative homology of the pullback over
the pair `(Δᵖ, ∂Δᵖ)` in degree `k + p` is the homology of the fibre `q⁻¹(τ d₀)` in degree `k`.

The proof transports the cube form `Work.Serre.serreE2d` along a homeomorphism of pairs
`(Δᵖ, ∂Δᵖ) ≅ (Iᵖ, ∂Iᵖ)`, which is assembled here from two pieces:

* `Work.Serre.stdSimplexPairHomeo` (the simplex is, as a pair, the closed ball with its sphere);
* `Work.StemsB.eucCube_closedBall_homeomorph` (the Euclidean cube is the ball, boundary ↦ sphere),
  and `Work.StemsB.eucToCubeP`/`cubePToEuc` (the Euclidean cube is `Iᵖ`, boundary ↦ `∂Iᵖ`).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-! ## The pair `(Δᵖ, ∂Δᵖ)` is homeomorphic to the pair `(Iᵖ, ∂Iᵖ)` -/

/-- A homeomorphism, regarded as a continuous map. -/
def homeoToCM_e2d {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) : C(α, β) where
  toFun := fun x => e x
  continuous_toFun := e.continuous

@[simp]
theorem homeoToCM_e2d_apply {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (x : α) : homeoToCM_e2d e x = e x := rfl

/-- The standard simplex `Δᵖ` is homeomorphic to the Euclidean cube `eucCube p`, by a
homeomorphism carrying `simplexBdry p` onto `eucBdry p`. -/
theorem exists_pairHomeo_simplex_eucCube (p : ℕ) :
    ∃ e : ↥(stdSimplex ℝ (Fin (p + 1))) ≃ₜ ↥(Work.StemsB.eucCube p),
      ∀ z, z ∈ simplexBdry p ↔
        (e z : EuclideanSpace ℝ (Fin p)) ∈ Work.StemsB.eucBdry p := by
  obtain ⟨e₁, he₁⟩ := stdSimplexPairHomeo p
  obtain ⟨e₂, he₂⟩ := Work.StemsB.eucCube_closedBall_homeomorph p
  refine ⟨e₁.trans e₂.symm, fun z => ?_⟩
  have h2 : (e₂ (e₁.trans e₂.symm z) : EuclideanSpace ℝ (Fin p)) =
      (e₁ z : EuclideanSpace ℝ (Fin p)) := by simp
  rw [he₂ (e₁.trans e₂.symm z), h2]
  exact he₁ z

/-- The affine homeomorphism `eucCube p ≃ₜ Iᵖ` (`x ↦ (x+1)/2`). -/
def eucCubeHomeoIC (p : ℕ) : ↥(Work.StemsB.eucCube p) ≃ₜ Work.Stems.Cubical.IC p :=
  { toFun := Work.StemsB.eucToCubeP p
    invFun := Work.StemsB.cubePToEuc p
    left_inv := Work.StemsB.cubePToEuc_eucToCubeP p
    right_inv := Work.StemsB.eucToCubeP_cubePToEuc p
    continuous_toFun := Work.StemsB.continuous_eucToCubeP p
    continuous_invFun := Work.StemsB.continuous_cubePToEuc p }

@[simp]
theorem eucCubeHomeoIC_apply (p : ℕ) (v : ↥(Work.StemsB.eucCube p)) :
    eucCubeHomeoIC p v = Work.StemsB.eucToCubeP p v := rfl

@[simp]
theorem eucCubeHomeoIC_symm_apply (p : ℕ) (x : Work.Stems.Cubical.IC p) :
    (eucCubeHomeoIC p).symm x = Work.StemsB.cubePToEuc p x := rfl

/-- The Euclidean cube `eucCube p` is the standard cube `Iᵖ`, by a homeomorphism carrying
`eucBdry p` onto `Cube.boundary (Fin p)`. -/
theorem exists_pairHomeo_eucCube_cube (p : ℕ) :
    ∃ e : ↥(Work.StemsB.eucCube p) ≃ₜ Work.Stems.Cubical.IC p,
      ∀ v : ↥(Work.StemsB.eucCube p),
        (v : EuclideanSpace ℝ (Fin p)) ∈ Work.StemsB.eucBdry p ↔
          e v ∈ Cube.boundary (Fin p) := by
  refine ⟨eucCubeHomeoIC p, fun v => ?_⟩
  constructor
  · intro hv
    rw [eucCubeHomeoIC_apply]
    exact Work.StemsB.eucToCubeP_mem_boundary p hv
  · intro hv
    rw [eucCubeHomeoIC_apply] at hv
    have h := Work.StemsB.cubePToEuc_mem_eucBdry p hv
    rwa [Work.StemsB.cubePToEuc_eucToCubeP p] at h

/-- **The pair `(Iᵖ, ∂Iᵖ)` is homeomorphic to the pair `(Δᵖ, ∂Δᵖ)`**: there is a homeomorphism
`Iᵖ ≃ₜ Δᵖ` carrying `∂Iᵖ = Cube.boundary (Fin p)` onto `simplexBdry p`. -/
theorem exists_pairHomeo_IC_simplex (p : ℕ) :
    ∃ e : Work.Stems.Cubical.IC p ≃ₜ ↥(stdSimplex ℝ (Fin (p + 1))),
      ∀ t, t ∈ Cube.boundary (Fin p) ↔ e t ∈ simplexBdry p := by
  obtain ⟨e₁, he₁⟩ := exists_pairHomeo_eucCube_cube p
  obtain ⟨e₂, he₂⟩ := exists_pairHomeo_simplex_eucCube p
  refine ⟨e₁.symm.trans e₂.symm, fun t => ?_⟩
  have hA : ((e₁.symm t : ↥(Work.StemsB.eucCube p)) : EuclideanSpace ℝ (Fin p)) ∈
      Work.StemsB.eucBdry p ↔ t ∈ Cube.boundary (Fin p) := by
    have h := he₁ (e₁.symm t)
    rw [Homeomorph.apply_symm_apply e₁ t] at h
    exact h
  have hB : (e₁.symm.trans e₂.symm) t ∈ simplexBdry p ↔
      ((e₁.symm t : ↥(Work.StemsB.eucCube p)) : EuclideanSpace ℝ (Fin p)) ∈
        Work.StemsB.eucBdry p := by
    have h := he₂ (e₂.symm (e₁.symm t))
    rw [Homeomorph.apply_symm_apply e₂ (e₁.symm t)] at h
    exact h
  exact hA.symm.trans hB.symm

/-! ## The homeomorphism of pullbacks over a homeomorphism of the base -/

/-- The homeomorphism of pullbacks induced by a homeomorphism of the base:
`(x, t) ↦ (x, e t)`. -/
def pullbackHomeo {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    {p : ℕ} (q : C(X, B)) (τ : C(↥(stdSimplex ℝ (Fin (p + 1))), B))
    (e : Work.Stems.Cubical.IC p ≃ₜ ↥(stdSimplex ℝ (Fin (p + 1)))) :
    Work.StemsB.Pullback q (τ.comp (homeoToCM_e2d e)) ≃ₜ Work.StemsB.Pullback q τ where
  toFun x := ⟨(x.1.1, e x.1.2), by
    have h := x.2
    simp only [ContinuousMap.comp_apply] at h
    exact h⟩
  invFun y := ⟨(y.1.1, e.symm y.1.2), by
    have h := y.2
    rw [ContinuousMap.comp_apply]
    have h2 : (homeoToCM_e2d e) (e.symm y.1.2) = y.1.2 := by
      rw [homeoToCM_e2d_apply]
      exact Homeomorph.apply_symm_apply e y.1.2
    rw [h2]
    exact h⟩
  left_inv x := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact Homeomorph.symm_apply_apply e x.1.2
  right_inv y := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact Homeomorph.apply_symm_apply e y.1.2
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ ?_
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp continuous_subtype_val
    · exact e.continuous.comp (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ ?_
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp continuous_subtype_val
    · exact e.symm.continuous.comp (continuous_snd.comp continuous_subtype_val)

@[simp]
theorem pullbackHomeo_val {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    {p : ℕ} (q : C(X, B)) (τ : C(↥(stdSimplex ℝ (Fin (p + 1))), B))
    (e : Work.Stems.Cubical.IC p ≃ₜ ↥(stdSimplex ℝ (Fin (p + 1))))
    (x : Work.StemsB.Pullback q (τ.comp (homeoToCM_e2d e))) :
    Subtype.val (pullbackHomeo q τ e x) = (x.1.1, e x.1.2) := rfl

@[simp]
theorem pullbackHomeo_snd {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    {p : ℕ} (q : C(X, B)) (τ : C(↥(stdSimplex ℝ (Fin (p + 1))), B))
    (e : Work.Stems.Cubical.IC p ≃ₜ ↥(stdSimplex ℝ (Fin (p + 1))))
    (x : Work.StemsB.Pullback q (τ.comp (homeoToCM_e2d e))) :
    Work.StemsB.pullbackSnd q τ (pullbackHomeo q τ e x) =
      e (Work.StemsB.pullbackSnd q (τ.comp (homeoToCM_e2d e)) x) := rfl

/-! ## The simplex form of E2(d) -/

theorem serreE2dSimplex {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (p : ℕ)
    (τ : C(↥(stdSimplex ℝ (Fin (p + 1))), B)) (d₀ : ↥(stdSimplex ℝ (Fin (p + 1)))) (k : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback q τ))
        {x : Work.StemsB.Pullback q τ | Work.StemsB.pullbackSnd q τ x ∈ Work.Serre.simplexBdry p}).homology (k + p)) ≅
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q (τ d₀)))).homology k)) := by
  obtain ⟨e, he⟩ := exists_pairHomeo_IC_simplex p
  obtain ⟨iso⟩ := serreE2d X B q p hq (τ.comp (homeoToCM_e2d e)) (e.symm d₀) k
  have hbd : ∀ x : Work.StemsB.Pullback q (τ.comp (homeoToCM_e2d e)),
      x ∈ ({x : Work.StemsB.Pullback q (τ.comp (homeoToCM_e2d e)) |
        Work.StemsB.pullbackSnd q (τ.comp (homeoToCM_e2d e)) x ∈ Cube.boundary (Fin p)} : Set _) ↔
      pullbackHomeo q τ e x ∈ ({x : Work.StemsB.Pullback q τ |
        Work.StemsB.pullbackSnd q τ x ∈ simplexBdry p} : Set _) := by
    intro x
    show Work.StemsB.pullbackSnd q (τ.comp (homeoToCM_e2d e)) x ∈ Cube.boundary (Fin p) ↔
      Work.StemsB.pullbackSnd q τ (pullbackHomeo q τ e x) ∈ simplexBdry p
    rw [pullbackHomeo_snd]
    exact he _
  obtain ⟨tr⟩ := Work.Cohomology.relChainsHomeomorphCompat
    (Work.StemsB.Pullback q (τ.comp (homeoToCM_e2d e))) (Work.StemsB.Pullback q τ)
    {x : Work.StemsB.Pullback q (τ.comp (homeoToCM_e2d e)) |
      Work.StemsB.pullbackSnd q (τ.comp (homeoToCM_e2d e)) x ∈ Cube.boundary (Fin p)}
    {x : Work.StemsB.Pullback q τ | Work.StemsB.pullbackSnd q τ x ∈ simplexBdry p}
    (pullbackHomeo q τ e) hbd (k + p)
  have hpt : (τ.comp (homeoToCM_e2d e)) (e.symm d₀) = τ d₀ := by
    rw [ContinuousMap.comp_apply, homeoToCM_e2d_apply, Homeomorph.apply_symm_apply e d₀]
  have hiso : (Work.Cohomology.singularChains ℤ (TopCat.of
        (Work.StemsB.fibre q ((τ.comp (homeoToCM_e2d e)) (e.symm d₀))))).homology k =
      (Work.Cohomology.singularChains ℤ (TopCat.of
        (Work.StemsB.fibre q (τ d₀)))).homology k :=
    congrArg (fun b : B =>
      (Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q b))).homology k) hpt
  exact ⟨tr.symm ≪≫ iso ≪≫ eqToIso hiso⟩

end

end Work.Serre
