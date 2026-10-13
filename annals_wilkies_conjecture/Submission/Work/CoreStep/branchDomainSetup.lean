/-
  `Work.CoreStep.branchDomainSetup`: the linear algebra of the two halves of the pair coordinates,
  used by `Work.CoreStep.branchDomain_open`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.DimAPI.ProjRankAux

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
namespace Work.CoreStep

open Work.WilE7 Work.WilE7.CoreStep
/-! ## §1. Linear algebra of the pair coordinates -/

/-- `projFirst` bundled as a linear map. -/
def linProjFirst (a b : ℕ) : (Fin (a + b) → ℝ) →ₗ[ℝ] (Fin a → ℝ) where
  toFun := projFirst a b
  map_add' := fun x y => by funext i; rfl
  map_smul' := fun c x => by funext i; rfl

/-- `projSnd` bundled as a linear map. -/
def linProjSnd (a b : ℕ) : (Fin (a + b) → ℝ) →ₗ[ℝ] (Fin b → ℝ) where
  toFun := projSnd a b
  map_add' := fun x y => by funext i; rfl
  map_smul' := fun c x => by funext i; rfl

/-- `MainDesign.absPt` bundled as a linear map. -/
def linAbsPt (N : ℕ) : (Fin (0 + N) → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun := MainDesign.absPt
  map_add' := fun x y => by funext i; rfl
  map_smul' := fun c x => by funext i; rfl

/-- The inverse reindexing `ℝ^N → ℝ^{0+N}`, which is `Work.WilE7.CoreStep.absPtUp`. -/
def linAbsPtUp (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin (0 + N) → ℝ) where
  toFun := Work.WilE7.DimAPI.absPtInv N
  map_add' := fun x y => by funext i; rfl
  map_smul' := fun c x => by funext i; rfl

@[simp] theorem linAbsPt_apply {N : ℕ} (z : Fin (0 + N) → ℝ) :
    linAbsPt N z = MainDesign.absPt z := rfl

@[simp] theorem linAbsPtUp_apply {N : ℕ} (w : Fin N → ℝ) :
    linAbsPtUp N w = Work.WilE7.DimAPI.absPtInv N w := rfl

@[simp] theorem linProjFirst_apply {a b : ℕ} (z : Fin (a + b) → ℝ) :
    linProjFirst a b z = projFirst a b z := rfl

@[simp] theorem linProjSnd_apply {a b : ℕ} (z : Fin (a + b) → ℝ) :
    linProjSnd a b z = projSnd a b z := rfl

/-- `absPt` of a lifted pair point is the pair point. -/
@[simp] theorem absPt_pairPtUp {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    MainDesign.absPt (pairPtUp u v) = pairPt u v := by
  funext i
  show pairPtUp u v (Fin.cast (Nat.zero_add (pPair n m)).symm i) = pairPt u v i
  show pairPt u v (Fin.cast (Nat.zero_add (pPair n m))
    (Fin.cast (Nat.zero_add (pPair n m)).symm i)) = pairPt u v i
  congr 1

/-- The second half of the pair point of `u, v` is the lifted point `absPtInv v`. -/
@[simp] theorem snd_half_pairPt {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt (pairPtUp u v)) = absPtInv v := by
  rw [absPt_pairPtUp, projSnd_pairPt]

/-- The first half of the pair point of `u, v` is the lifted point `absPtInv u`. -/
@[simp] theorem fst_half_pairPt {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt (pairPtUp u v)) = absPtInv u := by
  rw [absPt_pairPtUp, projFirst_pairPt]

/-- `absPtUp` is `absPtInv` (`DimAPI`), i.e. `absPt^-1`. -/
theorem absPtUp_eq_absPtInv {n m : ℕ} (w : Fin (n + (m + 1)) → ℝ) :
    absPtUp (n := n) (m := m) w = Work.WilE7.DimAPI.absPtInv (n + (m + 1)) w := rfl

/-- The lifted `absPtInv` of a point of `ℝ^N` is its `absPtUp`. -/
theorem absPtInv_eq_absPt {n m : ℕ} (u : Fin (pDim n m) → ℝ) :
    absPtInv (n := n) (m := m) u = MainDesign.absPt u := rfl

/-- `absPt` of the origin is the origin. -/
@[simp] theorem absPt_zero (N : ℕ) :
    MainDesign.absPt (0 : Fin (0 + N) → ℝ) = 0 := by
  funext i; rfl

/-- The lifted second half of a pair point:
`z ↦ absPtUp (projSnd (n+(m+1)) (n+(m+1)) (absPt z))`. -/
def pairSndLift {n m : ℕ} :
    (Fin (0 + pPair n m) → ℝ) →ₗ[ℝ] (Fin (0 + (n + (m + 1))) → ℝ) :=
  (linAbsPtUp (n + (m + 1))).comp
    ((linProjSnd (n + (m + 1)) (n + (m + 1))).comp (linAbsPt (pPair n m)))

/-- The lifted first half of a pair point. -/
def pairFstLift {n m : ℕ} :
    (Fin (0 + pPair n m) → ℝ) →ₗ[ℝ] (Fin (0 + (n + (m + 1))) → ℝ) :=
  (linAbsPtUp (n + (m + 1))).comp
    ((linProjFirst (n + (m + 1)) (n + (m + 1))).comp (linAbsPt (pPair n m)))

@[simp] theorem pairSndLift_apply {n m : ℕ} (y : Fin (0 + pPair n m) → ℝ) :
    pairSndLift (n := n) (m := m) y =
      absPtUp (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y)) := rfl

@[simp] theorem pairFstLift_apply {n m : ℕ} (y : Fin (0 + pPair n m) → ℝ) :
    pairFstLift (n := n) (m := m) y =
      absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y)) := rfl

/-- The second-half lift is `absPt` of the second half, in the `absPt` bookkeeping. -/
theorem absPt_pairSndLift {n m : ℕ} (y : Fin (0 + pPair n m) → ℝ) :
    MainDesign.absPt (pairSndLift (n := n) (m := m) y) =
      projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y) := by
  rw [pairSndLift_apply, absPtUp_eq_absPtInv]
  exact Work.WilE7.DimAPI.absPt_absPtInv (n + (m + 1)) _

/-- The first-half lift is `absPt` of the first half. -/
theorem absPt_pairFstLift {n m : ℕ} (y : Fin (0 + pPair n m) → ℝ) :
    MainDesign.absPt (pairFstLift (n := n) (m := m) y) =
      projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y) := by
  rw [pairFstLift_apply, absPtUp_eq_absPtInv]
  exact Work.WilE7.DimAPI.absPt_absPtInv (n + (m + 1)) _

end Work.CoreStep
