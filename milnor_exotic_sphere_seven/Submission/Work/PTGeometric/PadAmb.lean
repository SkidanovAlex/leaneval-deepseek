import Mathlib
import Submission.Work.PTGeometric.exists_padAmb
import Submission.Work.PTGeometric.RieszProj.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGEOMETRIC: the ambient padding `ℝ^{k+8} ↪ ℝ^{k+m}` as a fixed definition, and its action on
endomorphisms

`Work.PTGeometric.exists_padAmb` provides, for `8 ≤ m`, an isometric linear inclusion
`pad : ℝ^{k+8} → ℝ^{k+m}` (the *coordinate* inclusion, keeping the first `k+8` coordinates) together
with its adjoint projection `proj`.  It is an *existential*, so statements mentioning it must fix a
single syntactic form of the witness once and for all: that is what this file does.

* `padAmb k m hm`, `padAmbProj k m hm` — the chosen inclusion and projection, with
  `padAmbProj_padAmb`, `norm_padAmb`, `padAmb_adjoint`, `padAmbProj_adjoint`,
  `padAmb_apply_ofLp` (the coordinate clause);
* `padEnd` — the induced map on endomorphisms, `A ↦ pad ∘ A ∘ proj`, with `padEndCLM` its
  continuous-linear form (so that `padEnd` is smooth in `A`), `padEnd_apply`,
  `padEnd_apply_padAmb`, `range_padEnd`, `padEnd_fixes`.

This is the ambient dimension repair (`NOTE_COORD_DIMENSION_FIX.md`): the ambient coordinates of the
universal Thom space `Th(γ_{k,m})` are `Amb (k+m)`-valued, while TUBULAR's tube data live in
`Euc (8+k) = Amb (k+8)`; every statement comparing the two goes through these maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Topology ContDiff

namespace Work.PTGeometric

noncomputable section

/-- **The coordinate inclusion `ℝ^{k+8} ↪ ℝ^{k+m}`** (`8 ≤ m`), as the *fixed* witness of
`Work.PTGeometric.exists_padAmb`. -/
def padAmb (k m : ℕ) (hm : 8 ≤ m) : Amb (k + 8) →L[ℝ] Amb (k + m) :=
  Classical.choose (exists_padAmb k m hm)

/-- **The coordinate projection `ℝ^{k+m} → ℝ^{k+8}`**, the adjoint of `padAmb`. -/
def padAmbProj (k m : ℕ) (hm : 8 ≤ m) : Amb (k + m) →L[ℝ] Amb (k + 8) :=
  Classical.choose (Classical.choose_spec (exists_padAmb k m hm))

/-- **The properties of the chosen padding**, taken from `exists_padAmb`. -/
theorem padAmb_spec (k m : ℕ) (hm : 8 ≤ m) :
    (padAmbProj k m hm).comp (padAmb k m hm) = ContinuousLinearMap.id ℝ (Amb (k + 8)) ∧
    (padAmb k m hm).adjoint = padAmbProj k m hm ∧
    (padAmbProj k m hm).adjoint = padAmb k m hm ∧
    (∀ x : Amb (k + 8), ‖padAmb k m hm x‖ = ‖x‖) ∧
    (∀ (x : Amb (k + 8)) (j : Fin (k + 8)),
      (padAmb k m hm x).ofLp (Fin.castLE (by omega) j) = x.ofLp j) :=
  Classical.choose_spec (Classical.choose_spec (exists_padAmb k m hm))

/-- The projection is a left inverse of the inclusion. -/
theorem padAmbProj_padAmb (k m : ℕ) (hm : 8 ≤ m) (x : Amb (k + 8)) :
    padAmbProj k m hm (padAmb k m hm x) = x :=
  congrFun (congrArg DFunLike.coe (padAmb_spec k m hm).1) x

theorem padAmb_adjoint (k m : ℕ) (hm : 8 ≤ m) :
    (padAmb k m hm).adjoint = padAmbProj k m hm := (padAmb_spec k m hm).2.1

theorem padAmbProj_adjoint (k m : ℕ) (hm : 8 ≤ m) :
    (padAmbProj k m hm).adjoint = padAmb k m hm := (padAmb_spec k m hm).2.2.1

theorem norm_padAmb (k m : ℕ) (hm : 8 ≤ m) (x : Amb (k + 8)) :
    ‖padAmb k m hm x‖ = ‖x‖ := (padAmb_spec k m hm).2.2.2.1 x

theorem padAmb_apply_ofLp (k m : ℕ) (hm : 8 ≤ m) (x : Amb (k + 8)) (j : Fin (k + 8)) :
    (padAmb k m hm x).ofLp (Fin.castLE (by omega) j) = x.ofLp j :=
  (padAmb_spec k m hm).2.2.2.2 x j

theorem padAmb_injective (k m : ℕ) (hm : 8 ≤ m) : Function.Injective (padAmb k m hm) :=
  fun x y h => by
    have h' := congrArg (padAmbProj k m hm) h
    rwa [padAmbProj_padAmb, padAmbProj_padAmb] at h'

/-- The inclusion followed by the projection is a projection of the ambient space onto the image. -/
theorem padAmb_comp_proj_apply (k m : ℕ) (hm : 8 ≤ m) (z : Amb (k + m)) :
    padAmb k m hm (padAmbProj k m hm z) = padAmb k m hm (padAmbProj k m hm z) := rfl

/-- **The padding of endomorphisms**: `A ↦ pad ∘ A ∘ proj`.  As a *continuous linear* map in `A`
(`padEndCLM`), so that `padEnd` is smooth wherever `A` is. -/
def padEndCLM (k m : ℕ) (hm : 8 ≤ m) : EndOp (k + 8) →L[ℝ] EndOp (k + m) :=
  ((ContinuousLinearMap.compL ℝ (Amb (k + m)) (Amb (k + 8)) (Amb (k + m))).flip
      (padAmbProj k m hm)).comp
    (ContinuousLinearMap.compL ℝ (Amb (k + 8)) (Amb (k + 8)) (Amb (k + m)) (padAmb k m hm))

/-- **The padding of endomorphisms**: `A ↦ pad ∘ A ∘ proj`. -/
def padEnd (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (k + 8)) : EndOp (k + m) :=
  padEndCLM k m hm A

theorem padEnd_apply (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (k + 8)) (z : Amb (k + m)) :
    padEnd k m hm A z = padAmb k m hm (A (padAmbProj k m hm z)) := by
  simp [padEnd, padEndCLM]

theorem contDiff_padEndCLM (k m : ℕ) (hm : 8 ≤ m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (padEndCLM k m hm) :=
  (padEndCLM k m hm).contDiff

/-- **`padEnd` fixes the image of `pad` when `A` fixes the point.** -/
theorem padEnd_apply_padAmb (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (k + 8)) (y : Amb (k + 8)) :
    padEnd k m hm A (padAmb k m hm y) = padAmb k m hm (A y) := by
  rw [padEnd_apply, padAmbProj_padAmb]

/-- The range of `padEnd A` is the image under `pad` of the range of `A`. -/
theorem range_padEnd (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (k + 8)) :
    Set.range (padEnd k m hm A) = padAmb k m hm '' Set.range A := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨A (padAmbProj k m hm u), ⟨padAmbProj k m hm u, rfl⟩, (padEnd_apply k m hm A u).trans rfl⟩
  · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
    exact ⟨padAmb k m hm y, padEnd_apply_padAmb k m hm A y⟩

/-- A vector fixed by `A` is fixed by `padEnd A` after padding. -/
theorem padEnd_fixes (k m : ℕ) (hm : 8 ≤ m) {A : EndOp (k + 8)} {y : Amb (k + 8)}
    (hy : A y = y) : padEnd k m hm A (padAmb k m hm y) = padAmb k m hm y := by
  rw [padEnd_apply_padAmb, hy]

/-- `padEnd` as a composition of continuous linear maps. -/
theorem padEnd_apply_comp (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (k + 8)) :
    (padEnd k m hm A : EndOp (k + m))
      = (padAmb k m hm).comp (A.comp (padAmbProj k m hm)) := by
  ext z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, padEnd_apply]

/-- **The padding of an orthogonal projection of rank `k` is again one.**  This is what lets the
universal (`k+m`-ambient) reading of a member's Gauss data be a point of the Grassmannian, and it is
used by the degenerate (empty-index) source construction. -/
theorem padEnd_mem_Gr {k m : ℕ} (hm : 8 ≤ m) {S : EndOp (k + 8)} (hS : S ∈ Gr (k + 8) k) :
    padEnd k m hm S ∈ Gr (k + m) k := by
  obtain ⟨hadj, hidem, htr⟩ := hS
  have hidem_pt : ∀ y : Amb (k + 8), S (S y) = S y := by
    intro y
    have h := congrFun (congrArg DFunLike.coe hidem) y
    simpa only [ContinuousLinearMap.mul_apply] using h
  refine ⟨?_, ?_, ?_⟩
  · rw [padEnd_apply_comp k m hm S, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, padAmbProj_adjoint, padAmb_adjoint, hadj,
      ContinuousLinearMap.comp_assoc]
  · show (padEnd k m hm S) * (padEnd k m hm S) = padEnd k m hm S
    ext z
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, padEnd_apply, padAmbProj_padAmb, hidem_pt]
  · rw [← htr]
    have hcomp_lin : (padEnd k m hm S : Amb (k + m) →ₗ[ℝ] Amb (k + m))
        = ((padAmb k m hm : Amb (k + 8) →L[ℝ] Amb (k + m)) : Amb (k + 8) →ₗ[ℝ] Amb (k + m)) ∘ₗ
          (((S.comp (padAmbProj k m hm)) : Amb (k + m) →L[ℝ] Amb (k + 8)) :
            Amb (k + m) →ₗ[ℝ] Amb (k + 8)) := by
      ext z
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.comp_apply, padEnd_apply]
    have hgf : (((S.comp (padAmbProj k m hm)) : Amb (k + m) →L[ℝ] Amb (k + 8)) :
          Amb (k + m) →ₗ[ℝ] Amb (k + 8))
        ∘ₗ ((padAmb k m hm : Amb (k + 8) →L[ℝ] Amb (k + m)) : Amb (k + 8) →ₗ[ℝ] Amb (k + m))
        = (S : Amb (k + 8) →ₗ[ℝ] Amb (k + 8)) := by
      ext x
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.comp_apply, padAmbProj_padAmb]
    rw [hcomp_lin, ← LinearMap.trace_comp_comm' (R := ℝ) (M := Amb (k + 8)) (N := Amb (k + m))
      ((padAmb k m hm : Amb (k + 8) →L[ℝ] Amb (k + m)) : Amb (k + 8) →ₗ[ℝ] Amb (k + m))
      (((S.comp (padAmbProj k m hm)) : Amb (k + m) →L[ℝ] Amb (k + 8)) :
        Amb (k + m) →ₗ[ℝ] Amb (k + 8)), hgf]


/-! ## The same padding with the index written `8 + k`

The member's ambient space is written `Euc (8+k) = EuclideanSpace ℝ (Fin (8+k))` throughout
`Submission/Work/PTGeometric`, while the universal Grassmannian's ambient space is
`Amb (k+m) = EuclideanSpace ℝ (Fin (k+m))`.  The two index types have the same elements but are not
definitely equal, so the statements that compare the two go through the coordinate reindexing
`reIdxEuc` and the padding built on top of it.  Everything below is the `8+k`-indexed mirror of the
`k+8`-indexed material above. -/

/-- The coordinate reindexing `Euc (8+k) ≃ₗᵢ Amb (k+8)` (value-preserving: it only changes the
syntactic index of the index type). -/
noncomputable def reIdxEuc (k : ℕ) :
    EuclideanSpace ℝ (Fin (8 + k)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (Nat.add_comm 8 k))

theorem reIdxEuc_apply_ofLp (k : ℕ) (x : EuclideanSpace ℝ (Fin (8 + k))) (j : Fin (k + 8)) :
    ((reIdxEuc k) x).ofLp j = x.ofLp ((finCongr (Nat.add_comm 8 k)).symm j) := by
  rw [reIdxEuc, LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

theorem reIdxEuc_symm_apply_ofLp (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 8)))
    (j : Fin (8 + k)) :
    ((reIdxEuc k).symm y).ofLp j = y.ofLp ((finCongr (Nat.add_comm 8 k)) j) := by
  have hsymm : (reIdxEuc k).symm = LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr (Nat.add_comm 8 k)).symm := by
    rw [reIdxEuc, LinearIsometryEquiv.piLpCongrLeft_symm]
  rw [hsymm, LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

/-- **The padding in the `8+k` index**, obtained from `exists_padAmb` by the coordinate
reindexing `reIdxEuc`.  The coordinate formula is stated in terms of the coordinate inclusion. -/
theorem exists_padAmbE (k m : ℕ) (hm : 8 ≤ m) :
    ∃ (pad : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + m)))
      (proj : EuclideanSpace ℝ (Fin (k + m)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))),
      proj.comp pad = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (8 + k))) ∧
      pad.adjoint = proj ∧ proj.adjoint = pad ∧
      (∀ x : EuclideanSpace ℝ (Fin (8 + k)), ‖pad x‖ = ‖x‖) ∧
      (∀ (x : EuclideanSpace ℝ (Fin (8 + k))) (j : Fin (8 + k)),
        (pad x).ofLp (Fin.castLE (by omega) j) = x.ofLp j) := by
  obtain ⟨pad, proj, h1, h2, h3, h4, h5⟩ := exists_padAmb k m hm
  refine ⟨pad.comp ((reIdxEuc k).toContinuousLinearEquiv :
        EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))),
    ((reIdxEuc k).symm.toContinuousLinearEquiv :
        EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))).comp proj,
    ?_, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    show ((reIdxEuc k).symm) (proj (pad ((reIdxEuc k) x))) = x
    have h1x := congrFun (congrArg DFunLike.coe h1) ((reIdxEuc k) x)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1x
    rw [h1x]
    exact (reIdxEuc k).symm_apply_apply x
  · rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm, h2]
  · rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm, h3,
      LinearIsometryEquiv.symm_symm]
  · intro x
    show ‖pad ((reIdxEuc k) x)‖ = ‖x‖
    rw [h4]
    exact (reIdxEuc k).norm_map x
  · intro x j
    show (pad ((reIdxEuc k) x)).ofLp (Fin.castLE (by omega) j) = x.ofLp j
    have h6 := h5 ((reIdxEuc k) x) ((finCongr (Nat.add_comm 8 k)) j)
    have hidx : (Fin.castLE (by omega : 8 + k ≤ k + m) j : Fin (k + m))
        = Fin.castLE (by omega : k + 8 ≤ k + m) ((finCongr (Nat.add_comm 8 k)) j) := Fin.ext rfl
    calc (pad ((reIdxEuc k) x)).ofLp (Fin.castLE (by omega) j)
        = (pad ((reIdxEuc k) x)).ofLp
            (Fin.castLE (by omega) ((finCongr (Nat.add_comm 8 k)) j)) := by rw [hidx]
      _ = ((reIdxEuc k) x).ofLp ((finCongr (Nat.add_comm 8 k)) j) := h6
      _ = x.ofLp ((finCongr (Nat.add_comm 8 k)).symm ((finCongr (Nat.add_comm 8 k)) j)) :=
            reIdxEuc_apply_ofLp k x _
      _ = x.ofLp j := by rw [Equiv.symm_apply_apply]

/-- **The padding `ℝ^{8+k} ↪ ℝ^{k+m}`** (`8 ≤ m`), in the `8+k` index. -/
def padEuc (k m : ℕ) (hm : 8 ≤ m) :
    EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + m)) :=
  Classical.choose (exists_padAmbE k m hm)

/-- **The projection `ℝ^{k+m} → ℝ^{8+k}`**, the adjoint of `padEuc`. -/
def projEuc (k m : ℕ) (hm : 8 ≤ m) :
    EuclideanSpace ℝ (Fin (k + m)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  Classical.choose (Classical.choose_spec (exists_padAmbE k m hm))

theorem padEuc_spec (k m : ℕ) (hm : 8 ≤ m) :
    (projEuc k m hm).comp (padEuc k m hm)
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (8 + k))) ∧
    (padEuc k m hm).adjoint = projEuc k m hm ∧
    (projEuc k m hm).adjoint = padEuc k m hm ∧
    (∀ x : EuclideanSpace ℝ (Fin (8 + k)), ‖padEuc k m hm x‖ = ‖x‖) ∧
    (∀ (x : EuclideanSpace ℝ (Fin (8 + k))) (j : Fin (8 + k)),
      (padEuc k m hm x).ofLp (Fin.castLE (by omega) j) = x.ofLp j) :=
  Classical.choose_spec (Classical.choose_spec (exists_padAmbE k m hm))

theorem projEuc_padEuc (k m : ℕ) (hm : 8 ≤ m) (x : EuclideanSpace ℝ (Fin (8 + k))) :
    projEuc k m hm (padEuc k m hm x) = x :=
  congrFun (congrArg DFunLike.coe (padEuc_spec k m hm).1) x

theorem padEuc_adjoint (k m : ℕ) (hm : 8 ≤ m) :
    (padEuc k m hm).adjoint = projEuc k m hm := (padEuc_spec k m hm).2.1

theorem projEuc_adjoint (k m : ℕ) (hm : 8 ≤ m) :
    (projEuc k m hm).adjoint = padEuc k m hm := (padEuc_spec k m hm).2.2.1

theorem norm_padEuc (k m : ℕ) (hm : 8 ≤ m) (x : EuclideanSpace ℝ (Fin (8 + k))) :
    ‖padEuc k m hm x‖ = ‖x‖ := (padEuc_spec k m hm).2.2.2.1 x

theorem padEuc_apply_ofLp (k m : ℕ) (hm : 8 ≤ m) (x : EuclideanSpace ℝ (Fin (8 + k)))
    (j : Fin (8 + k)) :
    (padEuc k m hm x).ofLp (Fin.castLE (by omega) j) = x.ofLp j :=
  (padEuc_spec k m hm).2.2.2.2 x j

theorem padEuc_injective (k m : ℕ) (hm : 8 ≤ m) : Function.Injective (padEuc k m hm) :=
  fun x y h => by
    have h' := congrArg (projEuc k m hm) h
    rwa [projEuc_padEuc, projEuc_padEuc] at h'

/-- **The padding of endomorphisms**, in the `8+k` index: `A ↦ pad ∘ A ∘ proj`. -/
def padEndEucCLM (k m : ℕ) (hm : 8 ≤ m) :
    EndOp (8 + k) →L[ℝ] EndOp (k + m) :=
  ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (k + m)))
      (EuclideanSpace ℝ (Fin (8 + k))) (EuclideanSpace ℝ (Fin (k + m)))).flip (projEuc k m hm)).comp
    (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (8 + k)))
      (EuclideanSpace ℝ (Fin (8 + k))) (EuclideanSpace ℝ (Fin (k + m))) (padEuc k m hm))

/-- **The padding of endomorphisms**: `A ↦ pad ∘ A ∘ proj`. -/
def padEndEuc (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (8 + k)) : EndOp (k + m) :=
  padEndEucCLM k m hm A

theorem padEndEuc_apply (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (8 + k))
    (z : EuclideanSpace ℝ (Fin (k + m))) :
    padEndEuc k m hm A z = padEuc k m hm (A (projEuc k m hm z)) := by
  simp [padEndEuc, padEndEucCLM]

theorem contDiff_padEndEucCLM (k m : ℕ) (hm : 8 ≤ m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (padEndEucCLM k m hm) :=
  (padEndEucCLM k m hm).contDiff

theorem padEndEuc_apply_padEuc (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (8 + k))
    (y : EuclideanSpace ℝ (Fin (8 + k))) :
    padEndEuc k m hm A (padEuc k m hm y) = padEuc k m hm (A y) := by
  rw [padEndEuc_apply, projEuc_padEuc]

theorem padEndEuc_apply_comp (k m : ℕ) (hm : 8 ≤ m) (A : EndOp (8 + k)) :
    (padEndEuc k m hm A : EndOp (k + m))
      = (padEuc k m hm).comp (A.comp (projEuc k m hm)) := by
  ext z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, padEndEuc_apply]

theorem padEndEuc_mem_Gr {k m : ℕ} (hm : 8 ≤ m) {S : EndOp (8 + k)} (hS : S ∈ Gr (8 + k) k) :
    padEndEuc k m hm S ∈ Gr (k + m) k := by
  obtain ⟨hadj, hidem, htr⟩ := hS
  have hidem_pt : ∀ y : EuclideanSpace ℝ (Fin (8 + k)), S (S y) = S y := by
    intro y
    have h := congrFun (congrArg DFunLike.coe hidem) y
    simpa only [ContinuousLinearMap.mul_apply] using h
  refine ⟨?_, ?_, ?_⟩
  · rw [padEndEuc_apply_comp k m hm S, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, projEuc_adjoint, padEuc_adjoint, hadj,
      ContinuousLinearMap.comp_assoc]
  · show (padEndEuc k m hm S) * (padEndEuc k m hm S) = padEndEuc k m hm S
    ext z
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, padEndEuc_apply, projEuc_padEuc, hidem_pt]
  · rw [← htr]
    have hcomp_lin : (padEndEuc k m hm S : EuclideanSpace ℝ (Fin (k + m)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (k + m)))
        = ((padEuc k m hm : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ]
              EuclideanSpace ℝ (Fin (k + m))) :
            EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + m))) ∘ₗ
          (((S.comp (projEuc k m hm)) : EuclideanSpace ℝ (Fin (k + m)) →L[ℝ]
              EuclideanSpace ℝ (Fin (8 + k))) :
            EuclideanSpace ℝ (Fin (k + m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k))) := by
      ext z
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.comp_apply, padEndEuc_apply]
    have hgf : (((S.comp (projEuc k m hm)) : EuclideanSpace ℝ (Fin (k + m)) →L[ℝ]
          EuclideanSpace ℝ (Fin (8 + k))) :
            EuclideanSpace ℝ (Fin (k + m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
        ∘ₗ ((padEuc k m hm : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ]
              EuclideanSpace ℝ (Fin (k + m))) :
            EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + m)))
        = (S : EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k))) := by
      ext x
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.comp_apply, projEuc_padEuc]
    rw [hcomp_lin, ← LinearMap.trace_comp_comm' (R := ℝ)
      (M := EuclideanSpace ℝ (Fin (8 + k))) (N := EuclideanSpace ℝ (Fin (k + m)))
      ((padEuc k m hm : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ]
          EuclideanSpace ℝ (Fin (k + m))) : EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin (k + m)))
      (((S.comp (projEuc k m hm)) : EuclideanSpace ℝ (Fin (k + m)) →L[ℝ]
          EuclideanSpace ℝ (Fin (8 + k))) : EuclideanSpace ℝ (Fin (k + m)) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin (8 + k))), hgf]

end

end Work.PTGeometric
