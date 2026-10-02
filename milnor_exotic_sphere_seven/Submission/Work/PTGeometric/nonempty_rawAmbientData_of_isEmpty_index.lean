import Mathlib
import Submission.Work.PTGeometric.RawAmbientData
import Submission.Work.PTGeometric.WeakRegion.Properties
import Submission.Work.PTGeometric.trace_starProjection
import Submission.Work.SignatureBordism.BallBoundary
import Submission.Work.PTGeometric.PadAmb

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the degenerate case of the raw-data producer (an empty index type)

`Work.PTGeometric.RawAmbientData k (Fin m × ι) (fun a => Fam a.2)` asks for a compact `T2` smooth
manifold with boundary `M` (of dimension `8 + k + 1`), ambient coordinates `(P, v)` of the
null-homotopy, a collapse end `S`, and a homeomorphism
`↥(S ∩ {v = 0}) ≃ₜ Σ a : Fin m × ι, (Fam a.2).pt`.

When `ι` is *empty* the index type `Fin m × ι` is empty, so the right-hand side of the collapse-end
homeomorphism is empty; the conclusion is then index-free and is realised by the crudest possible
data: the closed ball `D^{8+k+1}` (the workspace's `Work.SignatureBordism.Ball`), the constant rank-`k`
coordinate projection `stdProj k` with the constant basis vector `stdVec k` in its range (so `v` is
nowhere zero, the collapse end is `S = ∅` and its zero set is empty), the collar `V = univ`, the
sub-collar `S0 = ∅`, and the empty family of prescribed charts (`mE = 0`).

This is the degenerate branch of `Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

set_option maxHeartbeats 3200000

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-! ## Auxiliary constructions -/

/-- A homeomorphism between two empty topological spaces. -/
def homeoOfIsEmpty {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (hα : IsEmpty α) (hβ : IsEmpty β) : α ≃ₜ β where
  toFun := fun a => hα.elim a
  invFun := fun b => hβ.elim b
  left_inv := fun a => hα.elim a
  right_inv := fun b => hβ.elim b
  continuous_toFun := continuous_iff_continuousAt.mpr fun a => hα.elim a
  continuous_invFun := continuous_iff_continuousAt.mpr fun b => hβ.elim b

/-- The standard inclusion `Fin k ↪ Fin (8 + k)`. -/
def stdIdx (k : ℕ) (i : Fin k) : Fin (8 + k) := ⟨i.1, by omega⟩

theorem stdIdx_injective (k : ℕ) : Function.Injective (stdIdx k) := by
  intro i j h
  have h' : (i : ℕ) = (j : ℕ) := congrArg (fun x : Fin (8 + k) => (x : ℕ)) h
  exact Fin.ext h'

/-- The `k`-plane of `ℝ^{8+k}` spanned by the first `k` standard basis vectors. -/
def stdPlane (k : ℕ) : Submodule ℝ (Amb (8 + k)) :=
  Submodule.span ℝ
    (Set.range fun i : Fin k => EuclideanSpace.basisFun (Fin (8 + k)) ℝ (stdIdx k i))

theorem linearIndependent_stdBasis (k : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin k => EuclideanSpace.basisFun (Fin (8 + k)) ℝ (stdIdx k i)) :=
  ((EuclideanSpace.basisFun (Fin (8 + k)) ℝ).orthonormal.linearIndependent).comp (stdIdx k)
    (stdIdx_injective k)

theorem finrank_stdPlane (k : ℕ) : Module.finrank ℝ (stdPlane k) = k := by
  rw [stdPlane, finrank_span_eq_card (linearIndependent_stdBasis k), Fintype.card_fin]

/-- The orthogonal projection onto `stdPlane k`: a point of the Grassmannian `Gr (8+k) k`. -/
def stdProj (k : ℕ) : EndOp (8 + k) := (stdPlane k).starProjection

theorem stdProj_mem_Gr (k : ℕ) : stdProj k ∈ Gr (8 + k) k := by
  haveI : (stdPlane k).HasOrthogonalProjection := inferInstance
  rw [Gr, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [stdProj]
    show ContinuousLinearMap.adjoint
        ((stdPlane k).subtypeL.comp (stdPlane k).orthogonalProjectionOnto) =
      (stdPlane k).subtypeL.comp (stdPlane k).orthogonalProjectionOnto
    rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjectionOnto,
      Submodule.adjoint_subtypeL]
  · rw [stdProj]
    exact Submodule.isIdempotentElem_starProjection (stdPlane k)
  · rw [stdProj]
    show LinearMap.trace ℝ (Amb (8 + k))
        ((stdPlane k).subtypeL.comp (stdPlane k).orthogonalProjectionOnto) = (k : ℝ)
    rw [trace_starProjection, finrank_stdPlane]

/-- A standard basis vector of `ℝ^{8+k}` lying in `stdPlane k` (for `k > 0`). -/
def stdVec (k : ℕ) (hk : 0 < k) : Amb (8 + k) :=
  EuclideanSpace.basisFun (Fin (8 + k)) ℝ (stdIdx k ⟨0, hk⟩)

theorem stdVec_mem_stdPlane (k : ℕ) (hk : 0 < k) : stdVec k hk ∈ stdPlane k :=
  Submodule.subset_span ⟨⟨0, hk⟩, rfl⟩

theorem norm_stdVec (k : ℕ) (hk : 0 < k) : ‖stdVec k hk‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (8 + k)) ℝ).norm_eq_one _

theorem stdVec_ne_zero (k : ℕ) (hk : 0 < k) : stdVec k hk ≠ 0 := by
  intro h
  have h1 : ‖stdVec k hk‖ = 1 := norm_stdVec k hk
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

theorem stdProj_apply_stdVec (k : ℕ) (hk : 0 < k) : stdProj k (stdVec k hk) = stdVec k hk :=
  (Submodule.starProjection_eq_self_iff).mpr (stdVec_mem_stdPlane k hk)

/-! ## The theorem -/

theorem nonempty_rawAmbientData_of_isEmpty_index
    {k : ℕ} {ι : Type} [Fintype ι] [IsEmpty ι] {Fam : ι → Work.ThomBordism.Man8}
    (hk : 11 ≤ k) (mU : ℕ) (hmU : 8 ≤ mU) (m : ℕ) :
    Nonempty (Work.PTGeometric.RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2)) := by
  classical
  have hk0 : 0 < k := by omega
  -- the compact `T2` smooth manifold with boundary: the closed ball `D^{8+k+1}`
  haveI hMan : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ (Work.SignatureBordism.Ball (8 + k)) :=
    Work.SignatureBordism.instIsManifoldBall (8 + k)
  haveI : CompactSpace (Work.SignatureBordism.Ball (8 + k)) :=
    Work.SignatureBordism.instCompactSpaceBall (8 + k)
  haveI : T2Space (Work.SignatureBordism.Ball (8 + k)) := inferInstance
  haveI : Nonempty (Work.SignatureBordism.Ball (8 + k)) :=
    ⟨0, by simp [Work.SignatureBordism.Ball]⟩
  -- the index type is empty, and so is the collapse end `S ∩ {v = 0}` (with `S = ∅`)
  haveI hRight : IsEmpty (Σ a : Fin m × ι, (Fam a.2).pt) :=
    ⟨fun y => isEmptyElim y.1.2⟩
  have hLeft : IsEmpty ↥((∅ : Set (Work.SignatureBordism.Ball (8 + k))) ∩
      {x : Work.SignatureBordism.Ball (8 + k) |
        (fun _ : Work.SignatureBordism.Ball (8 + k) => padEuc k mU hmU (stdVec k hk0)) x = 0}) :=
    ⟨fun x => Set.notMem_empty x.1 x.2.1⟩
  exact ⟨
    { M := Work.SignatureBordism.Ball (8 + k)
      P := fun _ => padEndEuc k mU hmU (stdProj k)
      v := fun _ => padEuc k mU hmU (stdVec k hk0)
      hPc := continuous_const
      hvc := continuous_const
      hProj := fun _ => padEndEuc_mem_Gr hmU (stdProj_mem_Gr k)
      hMem := fun _ => by
        rw [padEndEuc_apply_padEuc, stdProj_apply_stdVec k hk0]
      V := Set.univ
      hVopen := isOpen_univ
      S0 := ∅
      hS0cl := isClosed_empty
      hS0V := Set.empty_subset _
      hPsmV := contMDiff_const.contMDiffOn
      hvsmV := contMDiff_const.contMDiffOn
      S := ∅
      hScl := isClosed_empty
      hSsub := Set.empty_subset _
      hSS0 := Set.empty_subset _
      hend := homeoOfIsEmpty hLeft hRight
      hzero_sub := by
        intro x _ hx0
        exact absurd (padEuc_injective k mU hmU (by
          rw [hx0, map_zero])) (stdVec_ne_zero k hk0)
      δ := 1
      hδpos := one_pos
      hδ := by
        intro x _ _
        simp [norm_padEuc, norm_stdVec k hk0]
      mE := 0
      ellE := fun j => isEmptyElim j
      UE := fun _ => ∅
      isOpen_UE := fun _ => isOpen_empty
      UE_int := fun _ => Set.empty_subset _
      ellE_inj := fun j => isEmptyElim j
      ellE_inj_cl := fun j => isEmptyElim j
      bndZero_cov := by
        intro x _ hx0
        exact absurd (padEuc_injective k mU hmU (by rw [hx0, map_zero]))
          (stdVec_ne_zero k hk0)
      bndZero_trans := fun j => isEmptyElim j }⟩

end

end Work.PTGeometric
