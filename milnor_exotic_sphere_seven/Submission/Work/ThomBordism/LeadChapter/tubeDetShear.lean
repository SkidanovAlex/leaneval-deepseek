import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.LeadChapter.tubeDetShear`

The **shear invariance of the block determinant**.  `blockDet k B N` is the determinant of the
endomorphism `ModN k →ₗ ModN k` obtained by reading the frame `[B | N]` (level directions `B`,
normal directions `N`) through the fixed reference splitting `CofAtlas.sigma k`.  If the two normal
maps `N`, `N'` differ by a map taking values in the image of `B`, then — the level part `B` being
the `coprod`'s first block — the two frames differ by a *shear* of the first block along the
second, and a shear has determinant `1`.  Hence `blockDet k B N = blockDet k B N'`.

The point of the hypothesis `∀ v, ∃ x, B x = N v - N' v` is only that it makes the difference
`N - N'` land in `range B`; linearity upgrades the pointwise statement to a factorization
`N - N' = B ∘ f` for a genuine linear map `f` (`B` is applied to a *basis* of the source and the
result is extended linearly, `Module.Basis.constr`).

No `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open CategoryTheory

namespace Work.ThomBordism.LeadChapter

noncomputable section

/-- **The shear `(x, v) ↦ (x - f v, v)` has determinant `1`.**  It is `1 - b` where
`b = inl ∘ f ∘ snd` is a square-zero map (`snd ∘ inl = 0`), and the matrix of the shear in the
product basis `bV.prod bW` is `fromBlocks 1 B 0 1`, which is block triangular with unit diagonal
blocks. -/
theorem det_one_sub_inl_snd {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [Module.Finite ℝ V] [Module.Free ℝ V] [Module.Finite ℝ W] [Module.Free ℝ W]
    (f : W →ₗ[ℝ] V) :
    LinearMap.det (LinearMap.id - LinearMap.inl ℝ V W ∘ₗ f ∘ₗ LinearMap.snd ℝ V W) = 1 := by
  classical
  let bV := Module.Free.chooseBasis ℝ V
  let bW := Module.Free.chooseBasis ℝ W
  rw [← LinearMap.det_toMatrix (bV.prod bW)]
  have hmat : LinearMap.toMatrix (bV.prod bW) (bV.prod bW)
      (LinearMap.id - LinearMap.inl ℝ V W ∘ₗ f ∘ₗ LinearMap.snd ℝ V W)
      = Matrix.fromBlocks 1 (LinearMap.toMatrix bW bV (-f)) 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.snd_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂]
    all_goals exact if_congr eq_comm rfl rfl
  rw [hmat, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- **`det (D ∘ σ⁻¹) = det (σ⁻¹ ∘ D)`**: the two composites are conjugate (`LinearMap.det_conj`),
one being `↑σ ∘ (↑σ.symm ∘ D) ∘ ↑σ.symm` and the other `D ∘ ↑σ.symm`. -/
theorem det_comp_linearEquiv_symm {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (D : N →ₗ[ℝ] M) (e : N ≃ₗ[ℝ] M) :
    LinearMap.det (D ∘ₗ (e.symm : M →ₗ[ℝ] N)) = LinearMap.det ((e.symm : M →ₗ[ℝ] N) ∘ₗ D) := by
  have h := LinearMap.det_conj ((e.symm : M →ₗ[ℝ] N) ∘ₗ D) e
  rw [← h]
  congr 1
  ext x
  simp

/-- **The block determinant is invariant under shearing the normal directions by the level
directions.**  If every value of `N - N'` lies in the image of `B`, then `N - N'` factorizes
linearly through `B`, the two blocks `B.coprod N` and `B.coprod N'` differ by composition with the
unit-determinant shear `(x, v) ↦ (x - f v, v)`, and `blockDet` — a determinant read through the
fixed splitting `sigma k` — is unchanged. -/
theorem tubeDetShear {k : ℕ} (B : Work.ThomBordism.CofAtlas.E9 →L[ℝ] Work.ThomBordism.CofAtlas.ModN k)
    (N N' : EuclideanSpace ℝ (Fin k) →L[ℝ] Work.ThomBordism.CofAtlas.ModN k)
    (h : ∀ v, ∃ x : Work.ThomBordism.CofAtlas.E9, B x = N v - N' v) :
    Work.ThomBordism.LeadChapter.blockDet k B N = Work.ThomBordism.LeadChapter.blockDet k B N' := by
  classical
  -- choose preimages of `N - N'` on a basis of the normal direction and extend linearly
  let bW := Module.Free.chooseBasis ℝ (EuclideanSpace ℝ (Fin k))
  let x : Module.Free.ChooseBasisIndex ℝ (EuclideanSpace ℝ (Fin k)) →
      Work.ThomBordism.CofAtlas.E9 := fun j => Classical.choose (h (bW j))
  have hx : ∀ j, B.toLinearMap (x j) = N.toLinearMap (bW j) - N'.toLinearMap (bW j) :=
    fun j => Classical.choose_spec (h (bW j))
  let f : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] Work.ThomBordism.CofAtlas.E9 := bW.constr ℝ x
  have hfe : ∀ v : EuclideanSpace ℝ (Fin k), B (f v) = N v - N' v := by
    have hf : B.toLinearMap ∘ₗ f = N.toLinearMap - N'.toLinearMap :=
      bW.ext (fun j => by
        rw [LinearMap.comp_apply, Module.Basis.constr_basis, hx j, LinearMap.sub_apply])
    intro v
    have hv := congrArg
      (fun g : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] Work.ThomBordism.CofAtlas.ModN k => g v) hf
    simpa [LinearMap.sub_apply] using hv
  -- the block maps and the shear relating them
  let D : Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k) →ₗ[ℝ]
      Work.ThomBordism.CofAtlas.ModN k := B.coprod N
  let D' : Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k) →ₗ[ℝ]
      Work.ThomBordism.CofAtlas.ModN k := B.coprod N'
  let S : Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k) →ₗ[ℝ]
      Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k) :=
    LinearMap.id - LinearMap.inl ℝ Work.ThomBordism.CofAtlas.E9 (EuclideanSpace ℝ (Fin k)) ∘ₗ f ∘ₗ
      LinearMap.snd ℝ Work.ThomBordism.CofAtlas.E9 (EuclideanSpace ℝ (Fin k))
  have hD : D' = D ∘ₗ S := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨x, v⟩ := p
    change (B.coprod N') (x, v) = (B.coprod N) ((x, v) - (f v, 0))
    rw [Prod.mk_sub_mk, sub_zero, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.coprod_apply, map_sub, hfe v]
    abel
  refine calc blockDet k B N
      = LinearMap.det (D ∘ₗ ((Work.ThomBordism.CofAtlas.sigma k).symm :
          Work.ThomBordism.CofAtlas.ModN k →ₗ[ℝ]
            Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k))) := rfl
    _ = LinearMap.det (((Work.ThomBordism.CofAtlas.sigma k).symm :
          Work.ThomBordism.CofAtlas.ModN k →ₗ[ℝ]
            Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k)) ∘ₗ D) :=
          det_comp_linearEquiv_symm D (Work.ThomBordism.CofAtlas.sigma k)
    _ = LinearMap.det ((((Work.ThomBordism.CofAtlas.sigma k).symm :
          Work.ThomBordism.CofAtlas.ModN k →ₗ[ℝ]
            Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k)) ∘ₗ D) ∘ₗ S) := by
          rw [LinearMap.det_comp, det_one_sub_inl_snd, mul_one]
    _ = LinearMap.det (((Work.ThomBordism.CofAtlas.sigma k).symm :
          Work.ThomBordism.CofAtlas.ModN k →ₗ[ℝ]
            Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k)) ∘ₗ D') := by
          rw [hD, LinearMap.comp_assoc]
    _ = LinearMap.det (D' ∘ₗ ((Work.ThomBordism.CofAtlas.sigma k).symm :
          Work.ThomBordism.CofAtlas.ModN k →ₗ[ℝ]
            Work.ThomBordism.CofAtlas.E9 × EuclideanSpace ℝ (Fin k))) :=
          (det_comp_linearEquiv_symm D' (Work.ThomBordism.CofAtlas.sigma k)).symm
    _ = blockDet k B N' := rfl

end

end Work.ThomBordism.LeadChapter
