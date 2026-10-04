import Mathlib
import Submission.Work.Diff.Dim2.Ambient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The ambient map reindexed to `Fin (Module.finrank ℝ E + 1)`

The map `sphereAmb : ℝ × ℝ² → ℝ³` of `Ambient.lean` targets `EuclideanSpace ℝ (Fin 3)`, while the
target of the `d = 2` construction is `SphereD E = sphere (0 : ℝ^{finrank ℝ E + 1}) 1`.  In this
file the two are related by the reindexing linear isometry `reindexLI` (which exists as soon as
`finrank ℝ E + 1 = 3`), and `ambD` is the ambient map reindexed so that its target matches
`SphereD E` definitionally.

Nothing here is hard: `ambD = (reindexLI h).symm ∘ sphereAmb`, so `reindexLI h (ambD p) = sphereAmb p`
and `‖ambD p‖ = ‖sphereAmb p‖` are immediate.
-/

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

noncomputable section

/-- The reindexing linear isometry `ℝ^{n+1} ≃ ℝ³` attached to an identification `n + 1 = 3`. -/
def reindexLI {n : ℕ} (h : n + 1 = 3) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h)

@[simp] lemma reindexLI_apply {n : ℕ} (h : n + 1 = 3) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    reindexLI h v = LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h) v := rfl

/-- **The ambient map of the sphere parametrisation, reindexed to `Fin (finrank ℝ E + 1)`.** -/
def ambD (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h : Module.finrank ℝ E + 1 = 3) :
    ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)) :=
  (reindexLI h).symm ∘ sphereAmb

@[simp] lemma ambD_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (h : Module.finrank ℝ E + 1 = 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    ambD E h p = (reindexLI h).symm (sphereAmb p) := rfl

/-- The defining property: `reindexLI h` carries `ambD` back to `sphereAmb`. -/
lemma reindexLI_ambD (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (h : Module.finrank ℝ E + 1 = 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    reindexLI h (ambD E h p) = sphereAmb p :=
  (reindexLI h).apply_symm_apply (sphereAmb p)

/-- The reindexing is an isometry, so it does not change norms. -/
lemma norm_ambD (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h : Module.finrank ℝ E + 1 = 3) (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    ‖ambD E h p‖ = ‖sphereAmb p‖ :=
  (reindexLI h).symm.norm_map (sphereAmb p)

/-- Smoothness of `ambD` from smoothness of `sphereAmb`. -/
lemma contDiff_ambD (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (h : Module.finrank ℝ E + 1 = 3)
    (hsphere : ContDiff ℝ (⊤ : ℕ∞) sphereAmb) :
    ContDiff ℝ (⊤ : ℕ∞) (ambD E h) :=
  ((reindexLI h).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ
      (Fin (Module.finrank ℝ E + 1))).contDiff.comp hsphere

section SphereAmbComponents

@[simp] lemma proj_sphereAmb_c (i : Fin 3) (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    (EuclideanSpace.proj i) (sphereAmb p) = sphereAmbComp i p := by
  rw [sphereAmb]
  simp [EuclideanSpace.proj, PiLp.proj_apply]

@[simp] lemma ofLp_sphereAmb (i : Fin 3) (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    (sphereAmb p).ofLp i = sphereAmbComp i p := by
  simpa only [PiLp.proj_apply] using proj_sphereAmb_c i p

@[simp] lemma sphereAmbComp_zero_ (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (0 : Fin 3) p = Real.sin p.1 * p.2.ofLp 0 := by
  rw [sphereAmbComp, Fin.cases_zero]

@[simp] lemma sphereAmbComp_one_ (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (1 : Fin 3) p = Real.sin p.1 * p.2.ofLp 1 := by
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl, sphereAmbComp, Fin.cases_succ,
    Fin.cases_zero]

@[simp] lemma sphereAmbComp_two_ (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (2 : Fin 3) p = Real.cos p.1 := by
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, sphereAmbComp, Fin.cases_succ,
    show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, Fin.cases_succ]

end SphereAmbComponents

end

end Work.Diff.Dim2
