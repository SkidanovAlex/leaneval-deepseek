import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.LDG.Defs
import Submission.Work.Diff.C.LDG.Kit
import Submission.Work.Diff.C.LDG.Gram
import Submission.Work.Diff.C.LDG.Normalize
import Submission.Work.Diff.C.LDG.Key

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology EuclideanSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric

-- ROUTE.  Write `aᵢ := rgrad (F i) x` (so `⟪aᵢ, v⟫ = mfderiv (F i) x v`), `fᵢ := F i x`,
-- and `Aᵢⱼ := gp (F i) (F j) x = ⟪aᵢ, aⱼ⟫ + fᵢ fⱼ`.  For `T : (Fin (n+1) → ℝ) → TₓM × ℝ`,
-- `T c := (∑ cᵢ aᵢ, ∑ cᵢ fᵢ)` one has `‖T c‖² = ∑ᵢⱼ cᵢ cⱼ Aᵢⱼ`, so `hgram` says
-- `‖T c‖² ≥ (1-ε₂)‖c‖²`: `T` is INJECTIVE, and since `finrank ℝ (TₓM × ℝ) = n+1 = finrank ℝ
-- (Fin (n+1) → ℝ)` it is a linear iso.  This injectivity is what an entrywise form of `hgram`
-- does NOT give (an earlier review rejected the entrywise version with a counterexample), and it
-- is the heart of the proof.
-- Let `G₀ : M → EuclideanSpace ℝ (Fin (n+1))`, `G₀ x = (Real.sqrt (∑ Fᵢ x ^ 2))⁻¹ • (F · x)`, and
-- `G x = ⟨G₀ x, ‖G₀ x‖ = 1⟩ : SphereD E`.  For `v : TₓM`, `mfderiv G x v = 0` iff
-- `mfderiv F x v = μ • F x` for some `μ`.  In that case `mfderiv F x v = μ • F x` reads
-- `⟪aᵢ, v⟫ = μ fᵢ` for all i, hence `⟪T c, (v, -μ)⟫ = ∑ cᵢ (⟪aᵢ,v⟫ - μ fᵢ) = 0` for all c, so
-- `(v,-μ) = 0` (T onto) and `v = 0`: `mfderiv G x` is injective between spaces of dimension `n`,
-- hence `(mfderiv G x).IsInvertible`.
-- Then finish with the workspace's inverse function theorem
-- `Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible`
-- (`Submission/Commons/Geometry/Manifold/LocalDiffeomorph/...`; it wants `I.IsInteriorPoint x`,
-- which `[I.Boundaryless]` supplies) together with `ContMDiff` of `G`.
-- `G` smooth: `Mathlib.Geometry.Manifold.Instances.Sphere`'s `contMDiff.codRestrict_sphere`
-- (and `contMDiff_coe_sphere` for the coercion).  `Σ Fᵢ x ^ 2 ≥ 1 - ε₂ > 0` from `hunit`.
-- `[I.Boundaryless]` is REQUIRED and must not be dropped: `IsLocalDiffeomorphAt.isInteriorPoint_iff`
-- forces every point of `M` to be interior, since the target `SphereD E` is boundaryless.
theorem local_diffeo_of_gram
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    {F : Fin (Module.finrank ℝ E + 1) → M → ℝ} (hFsm : ∀ i, CMDiff ∞ (F i))
    {ε₂ : ℝ} (hε₂ : 0 ≤ ε₂) (hε₂1 : ε₂ < 1)
    (hunit : ∀ x : M, |(∑ i, F i x ^ 2) - 1| ≤ ε₂)
    (hgram : ∀ (x : M) (c : Fin (Module.finrank ℝ E + 1) → ℝ),
        |(∑ i, ∑ j, c i * c j * gp (I := I) (M := M) (F i) (F j) x) - (∑ i, c i ^ 2)|
          ≤ ε₂ * (∑ i, c i ^ 2)) :
    ∃ G : M → SphereD E, IsLocalDiffeomorph I (𝓡 (Module.finrank ℝ E)) ∞ G ∧
      ∀ x : M, ∃ b : ℝ, 0 < b ∧
        ((G x : SphereD E) : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
          = b • (fun i => F i x) := by
    classical
  have hpos : ∀ x : M, 0 < sq F x := fun x => by
    have h := abs_le.mp (hunit x)
    rw [sq_def]
    linarith [h.1]
  have hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) ∞ (U F) := LDG.contMDiff_U hFsm
  have hGsm : ContMDiff I (𝓡 (Module.finrank ℝ E)) ∞ (G F hpos) := LDG.contMDiff_G hFsm hpos
  -- The differential of `G₀ F` vanishes only on the zero vector.
  have hkey : ∀ (x : M) (v : TangentSpace I x),
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (G₀ F) x v = 0 → v = 0 := by
    intro x v hv
    obtain ⟨μ, hμ⟩ := LDG.exists_smul_of_mfderiv_G0_eq_zero (I := I) (M := M) (F := F) hU (hpos x) hv
    refine LDG.eq_zero_of_gram (I := I) (M := M) (F := F) (v := v) (μ := μ) hε₂ hε₂1
      hgram x ?_
    intro i
    have h2 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x v).ofLp i = μ * F i x := by
      rw [hμ, WithLp.ofLp_smul]
      simp [ofLp_U, smul_eq_mul]
    rw [inner_rgrad (F i) x v, ← LDG.ofLp_mfderiv_U (I := I) (M := M) (F := F) hU x v i]
    exact h2
  -- Chain rule with the inclusion of the sphere.
  have hchain : ∀ x : M, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (G₀ F) x
      = mfderiv (𝓡 (Module.finrank ℝ E)) 𝓘(ℝ, EuclideanSpace ℝ (Idx E))
          (fun y : SphereD E => (y : EuclideanSpace ℝ (Idx E))) ((G F hpos) x)
        ∘SL mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x := by
    intro x
    have hf : MDifferentiableAt I (𝓡 (Module.finrank ℝ E)) (G F hpos) x :=
      (hGsm x).mdifferentiableAt (by simp)
    have hg : MDifferentiableAt (𝓡 (Module.finrank ℝ E)) 𝓘(ℝ, EuclideanSpace ℝ (Idx E))
        (fun y : SphereD E => (y : EuclideanSpace ℝ (Idx E))) ((G F hpos) x) :=
      (contMDiff_coe_sphere (E := EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        (n := Module.finrank ℝ E) (m := ∞)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp (x := x) (f := G F hpos)
      (g := fun y : SphereD E => (y : EuclideanSpace ℝ (Idx E))) hg hf
    rwa [show (fun y : SphereD E => (y : EuclideanSpace ℝ (Idx E))) ∘ (G F hpos) = G₀ F
      from funext fun y => rfl] at hcomp
  have hinj : ∀ x : M, Function.Injective (mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x) := by
    intro x v w hvw
    have hvw' : mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    have h0 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (G₀ F) x (v - w) = 0 := by
      have h1 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (G₀ F) x (v - w)
          = (mfderiv (𝓡 (Module.finrank ℝ E)) 𝓘(ℝ, EuclideanSpace ℝ (Idx E))
              (fun y : SphereD E => (y : EuclideanSpace ℝ (Idx E))) ((G F hpos) x))
            ((mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x) (v - w)) := by
        rw [hchain x]
        rfl
      rw [h1, hvw', map_zero]
      try rfl
    exact sub_eq_zero.mp (hkey x (v - w) h0)
  have hinv : ∀ x : M, (mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x).IsInvertible := by
    intro x
    have hrank : Module.finrank ℝ (TangentSpace I x)
        = Module.finrank ℝ (TangentSpace (𝓡 (Module.finrank ℝ E)) ((G F hpos) x)) := by
      rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from
            (tangentSpaceCastModel I x).toLinearEquiv.finrank_eq,
          show Module.finrank ℝ (TangentSpace (𝓡 (Module.finrank ℝ E)) ((G F hpos) x))
            = Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) from
            (tangentSpaceCastModel (𝓡 (Module.finrank ℝ E))
              ((G F hpos) x)).toLinearEquiv.finrank_eq]
      exact finrank_euclideanSpace_fin.symm
    have hsurj : Function.Surjective (mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ)
        (V := TangentSpace I x)
        (V₂ := TangentSpace (𝓡 (Module.finrank ℝ E)) ((G F hpos) x)) hrank
        (f := (mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x :
          TangentSpace I x →ₗ[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) ((G F hpos) x)))).mp (hinj x)
    have hbij : Function.Bijective
        ((mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x :
          TangentSpace I x →ₗ[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) ((G F hpos) x))) :=
      ⟨hinj x, hsurj⟩
    let e : TangentSpace I x ≃ₗ[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) ((G F hpos) x) :=
      LinearEquiv.ofBijective _ hbij
    let eC : TangentSpace I x ≃L[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) ((G F hpos) x) :=
      e.toContinuousLinearEquiv
    have heC : (eC : TangentSpace I x →L[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) ((G F hpos) x))
        = mfderiv I (𝓡 (Module.finrank ℝ E)) (G F hpos) x := by
      ext v
      rfl
    exact ⟨eC, heC⟩
  refine ⟨G F hpos, fun x => ?_, fun x => ?_⟩
  · exact Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible
      (I := I) (I' := 𝓡 (Module.finrank ℝ E)) (f := G F hpos) (x := x) (U := Set.univ)
      Filter.univ_mem (hGsm.contMDiffOn) (BoundarylessManifold.isInteriorPoint' x) (hinv x)
  · exact ⟨(rad F x)⁻¹, inv_pos.mpr (rad_pos F (hpos x)), coe_G_eq F hpos x⟩


end Work.Diff.C
