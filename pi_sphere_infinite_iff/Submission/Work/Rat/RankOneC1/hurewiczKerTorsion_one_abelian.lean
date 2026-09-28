import Mathlib
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.RatHurewicz.degenCycleReduction
import Submission.Work.RatHurewicz.collapseClassOne

/-!
# The Hurewicz kernel in degree one is torsion when `π₁` is abelian

For a path-connected space `X` with abelian fundamental group at `x₀`, every class `a` in the
kernel of the Hurewicz map `π₁(X,x₀) → H₁(X;ℤ)` has finite order (in fact is trivial).

The proof is the degree-one case of the cubical proof of the Hurewicz theorem
(`Work.RatHurewicz.cubicalBridgeDeg`, `Work.RatHurewicz.Deg`): the bridge turns the vanishing of the
Hurewicz image of a based `1`-cube `p` into a relation `∂c = ±p + (degenerate)` in the cubical
`1`-chains, and the map `Ψ` that assigns to a `1`-cube the class of the loop obtained from it by
conjugation with chosen paths from `x₀` kills boundaries (`Ψ(∂τ) = 0` for a square `τ`, the
*cancellation half of the homotopy addition theorem*, which uses the commutativity of `π₁`) and
takes the trivial value on constant cubes.  Hence `Ψ(p) = 0`, i.e. `p = 1`.
-/

namespace Work.Rat.RankOneC1

open scoped Topology Topology.Homotopy unitInterval
open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-! ## Chosen paths from the base point -/

/-- A chosen path from the base point `x₀` to `y`. -/
def basePath (x₀ : X) [PathConnectedSpace X] (y : X) : Path x₀ y :=
  Classical.choice (PathConnectedSpace.joined x₀ y)

/-! ## The `1`-cube (interval model) of a path -/

/-- The path associated with a `1`-cube: `u ↦ s (fun _ => u)`. -/
def cubePath {Y : Type} [TopologicalSpace Y] (s : C(IC 1, Y)) : Path (s 0) (s 1) where
  toFun u := s (fun _ => u)
  continuous_toFun := s.continuous.comp (continuous_pi (fun _ => continuous_id))
  source' := rfl
  target' := rfl

@[simp] theorem cubePath_apply {Y : Type} [TopologicalSpace Y] (s : C(IC 1, Y))
    (u : unitInterval) : cubePath s u = s (fun _ => u) := rfl

/-! ## The square and its four edges -/

/-- The corner `(a,b)` of the square `I²`. -/
def sqPt (a b : unitInterval) : IC 2 := fun i => if i = 0 then a else b

theorem continuous_sqPt_fst (b : unitInterval) : Continuous (fun a : unitInterval => sqPt a b) := by
  apply continuous_pi; intro i
  by_cases h : i = 0
  · rw [show (fun a : unitInterval => sqPt a b i) = fun a => a from by
      funext a; simp [sqPt, h]]
    exact continuous_id
  · rw [show (fun a : unitInterval => sqPt a b i) = fun _ => b from by
      funext a; simp [sqPt, h]]
    exact continuous_const

theorem continuous_sqPt_snd (a : unitInterval) : Continuous (fun b : unitInterval => sqPt a b) := by
  apply continuous_pi; intro i
  by_cases h : i = 0
  · rw [show (fun b : unitInterval => sqPt a b i) = fun _ => a from by
      funext b; simp [sqPt, h]]
    exact continuous_const
  · rw [show (fun b : unitInterval => sqPt a b i) = fun b => b from by
      funext b; simp [sqPt, h]]
    exact continuous_id

/-- The four corners as they appear in the `faceCM`-faces of the square. -/
theorem faceCM_zero (b u : unitInterval) :
    faceCM (0 : Fin 2) b (fun _ => u) = sqPt b u := by
  funext i
  fin_cases i <;> simp [sqPt, faceCM_apply, faceFun]

theorem faceCM_one (b u : unitInterval) :
    faceCM (1 : Fin 2) b (fun _ => u) = sqPt u b := by
  funext i
  fin_cases i
  · show (@Fin.insertNth 1 (fun _ => unitInterval) (1 : Fin 2) b (fun _ : Fin 1 => u)) 0 = u
    rw [show (0 : Fin 2) = (1 : Fin 2).succAbove (0 : Fin 1) from rfl,
      Fin.insertNth_apply_succAbove]
  · show (@Fin.insertNth 1 (fun _ => unitInterval) (1 : Fin 2) b (fun _ : Fin 1 => u)) 1 = b
    rw [Fin.insertNth_apply_same]

/-- The lower-left to upper-left edge `(0,0) → (0,1)` of a square map. -/
def edgeAB {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    Path (sq (sqPt 0 0)) (sq (sqPt 0 1)) where
  toFun u := sq (sqPt 0 u)
  continuous_toFun := sq.continuous.comp (continuous_sqPt_snd 0)
  source' := rfl
  target' := rfl

/-- The upper-left to upper-right edge `(0,1) → (1,1)` of a square map. -/
def edgeBD {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    Path (sq (sqPt 0 1)) (sq (sqPt 1 1)) where
  toFun u := sq (sqPt u 1)
  continuous_toFun := sq.continuous.comp (continuous_sqPt_fst 1)
  source' := rfl
  target' := rfl

/-- The lower-left to lower-right edge `(0,0) → (1,0)` of a square map. -/
def edgeAC {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    Path (sq (sqPt 0 0)) (sq (sqPt 1 0)) where
  toFun u := sq (sqPt u 0)
  continuous_toFun := sq.continuous.comp (continuous_sqPt_fst 0)
  source' := rfl
  target' := rfl

/-- The lower-right to upper-right edge `(1,0) → (1,1)` of a square map. -/
def edgeCD {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    Path (sq (sqPt 1 0)) (sq (sqPt 1 1)) where
  toFun u := sq (sqPt 1 u)
  continuous_toFun := sq.continuous.comp (continuous_sqPt_snd 1)
  source' := rfl
  target' := rfl

/-- The path of the `(0,0)`-face of a square is the lower-left edge. -/
theorem cubePath_face_00 (sq : C(IC 2, X)) :
    cubePath (sq.comp (faceCM (0 : Fin 2) 0))
      = (edgeAB sq).cast (congrArg sq (faceCM_zero 0 0)) (congrArg sq (faceCM_zero 0 1)) := by
  apply Path.ext; funext u
  show sq ((faceCM (0 : Fin 2) 0) (fun _ => u)) = sq (sqPt 0 u)
  rw [faceCM_zero]

/-- The path of the `(0,1)`-face of a square is the lower-right edge. -/
theorem cubePath_face_01 (sq : C(IC 2, X)) :
    cubePath (sq.comp (faceCM (0 : Fin 2) 1))
      = (edgeCD sq).cast (congrArg sq (faceCM_zero 1 0)) (congrArg sq (faceCM_zero 1 1)) := by
  apply Path.ext; funext u
  show sq ((faceCM (0 : Fin 2) 1) (fun _ => u)) = sq (sqPt 1 u)
  rw [faceCM_zero]

/-- The path of the `(1,0)`-face of a square is the lower edge. -/
theorem cubePath_face_10 (sq : C(IC 2, X)) :
    cubePath (sq.comp (faceCM (1 : Fin 2) 0))
      = (edgeAC sq).cast (congrArg sq (faceCM_one 0 0)) (congrArg sq (faceCM_one 0 1)) := by
  apply Path.ext; funext u
  show sq ((faceCM (1 : Fin 2) 0) (fun _ => u)) = sq (sqPt u 0)
  rw [faceCM_one]

/-- The path of the `(1,1)`-face of a square is the upper edge. -/
theorem cubePath_face_11 (sq : C(IC 2, X)) :
    cubePath (sq.comp (faceCM (1 : Fin 2) 1))
      = (edgeBD sq).cast (congrArg sq (faceCM_one 1 0)) (congrArg sq (faceCM_one 1 1)) := by
  apply Path.ext; funext u
  show sq ((faceCM (1 : Fin 2) 1) (fun _ => u)) = sq (sqPt u 1)
  rw [faceCM_one]

namespace SquareAux

/-! ## The two boundary paths of a square are homotopic

For a continuous map `sq : I² → Y`, the two vertices of the square `I²` can be joined along the
boundary in two ways; the corresponding paths are homotopic because `I²` is contractible. -/

/-- The lower-left to upper-left edge `(0,0) → (0,1)` of the square. -/
def sqUp : Path (sqPt 0 0) (sqPt 0 1) where
  toFun u := sqPt 0 u
  continuous_toFun := continuous_sqPt_snd 0
  source' := rfl
  target' := rfl

/-- The upper-left to upper-right edge `(0,1) → (1,1)` of the square. -/
def sqRight : Path (sqPt 0 1) (sqPt 1 1) where
  toFun u := sqPt u 1
  continuous_toFun := continuous_sqPt_fst 1
  source' := rfl
  target' := rfl

/-- The lower-left to lower-right edge `(0,0) → (1,0)` of the square. -/
def sqBottom : Path (sqPt 0 0) (sqPt 1 0) where
  toFun u := sqPt u 0
  continuous_toFun := continuous_sqPt_fst 0
  source' := rfl
  target' := rfl

/-- The lower-right to upper-right edge `(1,0) → (1,1)` of the square. -/
def sqRightUp : Path (sqPt 1 0) (sqPt 1 1) where
  toFun u := sqPt 1 u
  continuous_toFun := continuous_sqPt_snd 1
  source' := rfl
  target' := rfl

/-- The square `I²` is contractible. -/
theorem contractibleSpace_IC2 : ContractibleSpace (IC 2) := by
  haveI : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  haveI : ContractibleSpace (unitInterval × unitInterval) := inferInstance
  exact ((Homeomorph.piFinTwo (fun _ : Fin 2 => unitInterval)).contractibleSpace_iff).mpr
    inferInstance

/-- The left edge of a square map is the image of the left edge of `I²`. -/
theorem map_sqUp {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    sqUp.map sq.continuous = edgeAB sq := by
  ext u
  simp [sqUp, edgeAB]

/-- The top edge of a square map is the image of the top edge of `I²`. -/
theorem map_sqRight {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    sqRight.map sq.continuous = edgeBD sq := by
  ext u
  simp [sqRight, edgeBD]

/-- The bottom edge of a square map is the image of the bottom edge of `I²`. -/
theorem map_sqBottom {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    sqBottom.map sq.continuous = edgeAC sq := by
  ext u
  simp [sqBottom, edgeAC]

/-- The right edge of a square map is the image of the right edge of `I²`. -/
theorem map_sqRightUp {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    sqRightUp.map sq.continuous = edgeCD sq := by
  ext u
  simp [sqRightUp, edgeCD]

/-- **The two boundary paths of a square are homotopic.** -/
theorem square_boundary_homotopic {Y : Type} [TopologicalSpace Y] (sq : C(IC 2, Y)) :
    Path.Homotopic ((edgeAB sq).trans (edgeBD sq)) ((edgeAC sq).trans (edgeCD sq)) := by
  haveI : ContractibleSpace (IC 2) := contractibleSpace_IC2
  haveI : SimplyConnectedSpace (IC 2) := inferInstance
  have hp : (sqUp.trans sqRight).Homotopic (sqBottom.trans sqRightUp) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hm := Path.Homotopic.map hp sq
  rw [Path.map_trans, Path.map_trans] at hm
  rw [map_sqUp sq, map_sqRight sq, map_sqBottom sq, map_sqRightUp sq] at hm
  exact hm

end SquareAux

variable [PathConnectedSpace X]

/-- **The conjugation of a path class `y → z` into a loop class at `x₀`**, by pre- and
post-composing with the chosen paths `x₀ → y` and `x₀ → z`. -/
def conjClass (x₀ : X) {y z : X} (Q : Path.Homotopic.Quotient y z) :
    Path.Homotopic.Quotient x₀ x₀ :=
  (Path.Homotopic.Quotient.mk (basePath x₀ y)).trans
    (Q.trans ((Path.Homotopic.Quotient.mk (basePath x₀ z)).symm))

/-- **`conjClass` is multiplicative.** -/
theorem conjClass_trans (x₀ : X) {y z w : X} (Q : Path.Homotopic.Quotient y z)
    (Q' : Path.Homotopic.Quotient z w) :
    conjClass x₀ (Q.trans Q') = (conjClass x₀ Q).trans (conjClass x₀ Q') := by
  have hkey : (Q.trans (Path.Homotopic.Quotient.mk (basePath x₀ z)).symm).trans
        ((Path.Homotopic.Quotient.mk (basePath x₀ z)).trans
          (Q'.trans (Path.Homotopic.Quotient.mk (basePath x₀ w)).symm))
      = Q.trans (Q'.trans (Path.Homotopic.Quotient.mk (basePath x₀ w)).symm) := by
    rw [Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (basePath x₀ z)).symm
      (Path.Homotopic.Quotient.mk (basePath x₀ z))
      (Q'.trans (Path.Homotopic.Quotient.mk (basePath x₀ w)).symm)]
    rw [Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  simp only [conjClass]
  rw [Path.Homotopic.Quotient.trans_assoc Q Q' _]
  rw [← hkey]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (basePath x₀ y))
    (Q.trans (Path.Homotopic.Quotient.mk (basePath x₀ z)).symm)
    ((Path.Homotopic.Quotient.mk (basePath x₀ z)).trans
      (Q'.trans (Path.Homotopic.Quotient.mk (basePath x₀ w)).symm))]

/-- **`conjClass` is invariant under casting the endpoints.** -/
theorem conjClass_cast (x₀ : X) {y z y' z' : X} (Q : Path.Homotopic.Quotient y z)
    (hy : y' = y) (hz : z' = z) :
    conjClass x₀ (Q.cast hy hz) = conjClass x₀ Q := by
  subst hy; subst hz
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]

/-- The loop of a based `1`-cube, as a path at `x₀` (this is `genLoopEquivOfUnique (Fin 1)`). -/
def loopOfCube (x₀ : X) (p : Ω^ (Fin 1) X x₀) : Path x₀ x₀ where
  toFun t := p.1 (fun _ => t)
  continuous_toFun := p.1.continuous.comp (continuous_pi (fun _ => continuous_id))
  source' := GenLoop.boundary p (fun _ => 0) ⟨default, Or.inl rfl⟩
  target' := GenLoop.boundary p (fun _ => 1) ⟨default, Or.inr rfl⟩

@[simp] theorem loopOfCube_apply (x₀ : X) (p : Ω^ (Fin 1) X x₀) (t : unitInterval) :
    loopOfCube x₀ p t = p.1 (fun _ => t) := rfl

/-- The class in `π₁(X,x₀)` of a based `1`-cube is the class of its loop, in the path model. -/
theorem pi1_eq_mk_loopOfCube (x₀ : X) (p : Ω^ (Fin 1) X x₀) :
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)) ⟦p⟧
      = Path.Homotopic.Quotient.mk (loopOfCube x₀ p) := by
  rfl

/-- The class of a `1`-cube in `π₁(X,x₀)`, in the group model: the conjugating loop of the
cube (the multiplicative version of `psiCube`). -/
def cubeClass (x₀ : X) (s : C(IC 1, X)) : HomotopyGroup (Fin 1) X x₀ :=
  (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
    (FundamentalGroup.fromPath
      (conjClass x₀ (Path.Homotopic.Quotient.mk (cubePath s))))

/-- **The `Ψ`-value of a `1`-cube**, in the abelianisation of `π₁(X,x₀)`: the class of the loop
obtained from the cube by conjugation with the chosen paths to its endpoints. -/
def psiCube (x₀ : X) (s : C(IC 1, X)) :
    Additive (Abelianization (HomotopyGroup (Fin 1) X x₀)) :=
  Additive.ofMul (Abelianization.of (cubeClass x₀ s))

theorem psiCube_eq (x₀ : X) (s : C(IC 1, X)) :
    psiCube x₀ s = Additive.ofMul (Abelianization.of (cubeClass x₀ s)) := rfl

/-- The identification of the conjugating loop of the `(0,0)`-face with the lower-left edge. -/
theorem cubeClass_face_00 (x₀ : X) (sq : C(IC 2, X)) :
    cubeClass x₀ (faceCube (0 : Fin 2) 0 sq)
      = (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
          (FundamentalGroup.fromPath
            (conjClass x₀ (Path.Homotopic.Quotient.mk (edgeAB sq)))) := by
  unfold cubeClass
  rw [show faceCube (0 : Fin 2) 0 sq = sq.comp (faceCM (0 : Fin 2) 0) from rfl]
  rw [cubePath_face_00, Path.Homotopic.Quotient.mk_cast, conjClass_cast]

/-- The identification of the conjugating loop of the `(0,1)`-face with the lower-right edge. -/
theorem cubeClass_face_01 (x₀ : X) (sq : C(IC 2, X)) :
    cubeClass x₀ (faceCube (0 : Fin 2) 1 sq)
      = (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
          (FundamentalGroup.fromPath
            (conjClass x₀ (Path.Homotopic.Quotient.mk (edgeCD sq)))) := by
  unfold cubeClass
  rw [show faceCube (0 : Fin 2) 1 sq = sq.comp (faceCM (0 : Fin 2) 1) from rfl]
  rw [cubePath_face_01, Path.Homotopic.Quotient.mk_cast, conjClass_cast]

/-- The identification of the conjugating loop of the `(1,0)`-face with the lower edge. -/
theorem cubeClass_face_10 (x₀ : X) (sq : C(IC 2, X)) :
    cubeClass x₀ (faceCube (1 : Fin 2) 0 sq)
      = (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
          (FundamentalGroup.fromPath
            (conjClass x₀ (Path.Homotopic.Quotient.mk (edgeAC sq)))) := by
  unfold cubeClass
  rw [show faceCube (1 : Fin 2) 0 sq = sq.comp (faceCM (1 : Fin 2) 0) from rfl]
  rw [cubePath_face_10, Path.Homotopic.Quotient.mk_cast, conjClass_cast]

/-- The identification of the conjugating loop of the `(1,1)`-face with the upper edge. -/
theorem cubeClass_face_11 (x₀ : X) (sq : C(IC 2, X)) :
    cubeClass x₀ (faceCube (1 : Fin 2) 1 sq)
      = (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
          (FundamentalGroup.fromPath
            (conjClass x₀ (Path.Homotopic.Quotient.mk (edgeBD sq)))) := by
  unfold cubeClass
  rw [show faceCube (1 : Fin 2) 1 sq = sq.comp (faceCM (1 : Fin 2) 1) from rfl]
  rw [cubePath_face_11, Path.Homotopic.Quotient.mk_cast, conjClass_cast]

/-- **The cancellation half of the homotopy addition theorem, in the reversed order.**  For
composable paths `Q` and `Q'`, the conjugating classes of `Q'` and `Q` multiply (in the group
model) to the conjugating class of the composite `Q ⋆ Q'`. -/
theorem e_symm_conjClass_mul (x₀ : X) {y z w : X} (Q : Path.Homotopic.Quotient y z)
    (Q' : Path.Homotopic.Quotient z w) :
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
        (FundamentalGroup.fromPath (conjClass x₀ Q'))
      * (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
          (FundamentalGroup.fromPath (conjClass x₀ Q))
      = (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
          (FundamentalGroup.fromPath (conjClass x₀ (Q.trans Q'))) := by
  rw [← map_mul]
  congr 1
  calc FundamentalGroup.fromPath (conjClass x₀ Q') * FundamentalGroup.fromPath (conjClass x₀ Q)
      = (FundamentalGroup.fromPath (conjClass x₀ Q)).trans
          (FundamentalGroup.fromPath (conjClass x₀ Q')) :=
        FundamentalGroup.mul_def (p := FundamentalGroup.fromPath (conjClass x₀ Q'))
          (q := FundamentalGroup.fromPath (conjClass x₀ Q))
    _ = FundamentalGroup.fromPath (conjClass x₀ (Q.trans Q')) :=
        (congrArg FundamentalGroup.fromPath (conjClass_trans x₀ Q Q')).symm

section Main

variable (x₀ : X)

/-- **The chain-level map `Ψ`** on the cubical `1`-chains, with values in the abelianisation of
`π₁(X,x₀)`. -/
def PsiLin : Cub 1 X →ₗ[ℤ] Additive (Abelianization (HomotopyGroup (Fin 1) X x₀)) :=
  Finsupp.linearCombination ℤ (psiCube x₀)

@[simp] theorem PsiLin_single (s : C(IC 1, X)) :
    PsiLin x₀ (Finsupp.single s 1) = psiCube x₀ s := by
  simp [PsiLin]

/-- **`Ψ` kills the boundary of a square.**  This is the degree-one case of the chain identity
`Ψ(∂τ) = 0`; it uses the commutativity of the target (the abelianisation) through the geometric
fact that the two boundary paths of a square are path-homotopic. -/
theorem PsiLin_cubD_single (sq : C(IC 2, X)) :
    PsiLin x₀ (cubD 1 X (Finsupp.single sq 1)) = 0 := by
  have hgeo : Path.Homotopic.Quotient.mk ((edgeAB sq).trans (edgeBD sq))
      = Path.Homotopic.Quotient.mk ((edgeAC sq).trans (edgeCD sq)) :=
    (Path.Homotopic.Quotient.eq).mpr (SquareAux.square_boundary_homotopic sq)
  have h1 : Abelianization.of (cubeClass x₀ (faceCube (0 : Fin 2) 0 sq))
        * Abelianization.of (cubeClass x₀ (faceCube (1 : Fin 2) 1 sq))
      = Abelianization.of
          ((HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
            (FundamentalGroup.fromPath
              (conjClass x₀ (Path.Homotopic.Quotient.mk ((edgeAB sq).trans (edgeBD sq))))) ) := by
    rw [cubeClass_face_00, cubeClass_face_11, mul_comm, ← map_mul,
      e_symm_conjClass_mul (x₀ := x₀) (Q := Path.Homotopic.Quotient.mk (edgeAB sq))
        (Q' := Path.Homotopic.Quotient.mk (edgeBD sq)),
      ← Path.Homotopic.Quotient.mk_trans]
  have h2 : Abelianization.of (cubeClass x₀ (faceCube (1 : Fin 2) 0 sq))
        * Abelianization.of (cubeClass x₀ (faceCube (0 : Fin 2) 1 sq))
      = Abelianization.of
          ((HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
            (FundamentalGroup.fromPath
              (conjClass x₀ (Path.Homotopic.Quotient.mk ((edgeAC sq).trans (edgeCD sq)))))) := by
    rw [cubeClass_face_10, cubeClass_face_01, mul_comm, ← map_mul,
      e_symm_conjClass_mul (x₀ := x₀) (Q := Path.Homotopic.Quotient.mk (edgeAC sq))
        (Q' := Path.Homotopic.Quotient.mk (edgeCD sq)),
      ← Path.Homotopic.Quotient.mk_trans]
  have hmult : Abelianization.of (cubeClass x₀ (faceCube (0 : Fin 2) 0 sq))
        * Abelianization.of (cubeClass x₀ (faceCube (1 : Fin 2) 1 sq))
      = Abelianization.of (cubeClass x₀ (faceCube (1 : Fin 2) 0 sq))
        * Abelianization.of (cubeClass x₀ (faceCube (0 : Fin 2) 1 sq)) := by
    rw [h1, h2, hgeo]
  have hadd : psiCube x₀ (faceCube (0 : Fin 2) 0 sq) + psiCube x₀ (faceCube (1 : Fin 2) 1 sq)
      = psiCube x₀ (faceCube (1 : Fin 2) 0 sq) + psiCube x₀ (faceCube (0 : Fin 2) 1 sq) := by
    rw [psiCube_eq, psiCube_eq, psiCube_eq, psiCube_eq, ← ofMul_mul, ← ofMul_mul, hmult]
  have hbd : cubD 1 X (Finsupp.single sq 1)
      = (Finsupp.single (faceCube (0 : Fin 2) 0 sq) 1
            - Finsupp.single (faceCube (0 : Fin 2) 1 sq) 1)
        + -(Finsupp.single (faceCube (1 : Fin 2) 0 sq) 1
            - Finsupp.single (faceCube (1 : Fin 2) 1 sq) 1) := by
    rw [cubD_single, Fin.sum_univ_two]
    simp [neg_smul]
  have hY : PsiLin x₀ (cubD 1 X (Finsupp.single sq 1))
      = (psiCube x₀ (faceCube (0 : Fin 2) 0 sq) - psiCube x₀ (faceCube (0 : Fin 2) 1 sq))
        - (psiCube x₀ (faceCube (1 : Fin 2) 0 sq) - psiCube x₀ (faceCube (1 : Fin 2) 1 sq)) := by
    rw [hbd, map_add, map_neg, map_sub, map_sub, PsiLin_single, PsiLin_single, PsiLin_single,
      PsiLin_single]
    abel
  rw [hY]
  have key : psiCube x₀ (faceCube (0 : Fin 2) 0 sq) - psiCube x₀ (faceCube (0 : Fin 2) 1 sq)
        - (psiCube x₀ (faceCube (1 : Fin 2) 0 sq) - psiCube x₀ (faceCube (1 : Fin 2) 1 sq))
      = (psiCube x₀ (faceCube (0 : Fin 2) 0 sq) + psiCube x₀ (faceCube (1 : Fin 2) 1 sq))
        - (psiCube x₀ (faceCube (0 : Fin 2) 1 sq) + psiCube x₀ (faceCube (1 : Fin 2) 0 sq)) := by
    abel
  rw [key, hadd, add_comm, sub_self]

/-- In a commutative group, conjugation is trivial. -/
theorem inv_mul_mul_cancel {M : Type} [CommGroup M] (a b : M) : a⁻¹ * b * a = b := by
  rw [mul_comm a⁻¹ b, mul_assoc, inv_mul_cancel, mul_one]

/-- The `Ψ`-value of a constant `1`-cube is trivial. -/
theorem PsiLin_cconst (v : X) :
    PsiLin x₀ (Finsupp.single (Work.RatHurewicz.cconst 1 v) 1) = 0 := by
  rw [PsiLin_single, psiCube_eq]
  have h0 : (Work.RatHurewicz.cconst 1 v) 0 = v := rfl
  have h1 : (Work.RatHurewicz.cconst 1 v) 1 = v := rfl
  have hpath : cubePath (Work.RatHurewicz.cconst 1 v) = (Path.refl v).cast h0 h1 := by
    ext t
    rw [Path.cast_coe]
    rfl
  have hq : Path.Homotopic.Quotient.mk (cubePath (Work.RatHurewicz.cconst 1 v))
      = (Path.Homotopic.Quotient.mk (Path.refl v)).cast h0 h1 := by
    rw [hpath]
    exact Path.Homotopic.Quotient.mk_cast (Path.refl v) h0 h1
  have hc : FundamentalGroup.fromPath
      (conjClass x₀ (Path.Homotopic.Quotient.mk (Path.refl v)))
      = Path.Homotopic.Quotient.refl x₀ := by
    have hdef : (conjClass x₀ (Path.Homotopic.Quotient.mk (Path.refl v)) : FundamentalGroup X x₀)
        = (Path.Homotopic.Quotient.mk (basePath x₀ v)).trans
            ((Path.Homotopic.Quotient.mk (Path.refl v)).trans
              (Path.Homotopic.Quotient.mk (basePath x₀ v)).symm) := rfl
    rw [hdef, Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans,
      Path.Homotopic.Quotient.trans_symm]
  have hcube : cubeClass x₀ (Work.RatHurewicz.cconst 1 v) = 1 := by
    unfold cubeClass
    rw [hq, conjClass_cast, hc]
    exact map_one (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
  rw [hcube, map_one]
  rfl

/-- **`Ψ` kills the degenerate `1`-chains.** -/
theorem PsiLin_deg {z : Cub 1 X} (hz : z ∈ Work.RatHurewicz.Deg 1 X) : PsiLin x₀ z = 0 := by
  refine Submodule.iSup_induction (motive := fun w => PsiLin x₀ w = 0) _ hz ?_ ?_ ?_
  · intro i y hy
    refine Submodule.span_induction (p := fun w _ => PsiLin x₀ w = 0) ?_ ?_ ?_ ?_ hy
    · rintro w ⟨f, hf, rfl⟩
      have hfc : f = Work.RatHurewicz.cconst 1 (f 0) := by
        ext t
        exact hf t (0 : IC 1) (fun j hj => absurd (Subsingleton.elim j i) hj)
      rw [hfc]
      exact PsiLin_cconst x₀ _
    · simp
    · intro a b ha hb ha' hb'
      rw [map_add, ha', hb', add_zero]
    · intro a b hb hb'
      rw [map_smul, hb', smul_zero]
  · simp
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

/-- **`Ψ` kills cubical boundaries.** -/
theorem PsiLin_cubD (c : Cub 2 X) : PsiLin x₀ (cubD 1 X c) = 0 := by
  refine Finsupp.induction c (motive := fun c => PsiLin x₀ (cubD 1 X c) = 0) ?_ ?_
  · simp
  · intro a b f ha hb ih
    have hsingle : Finsupp.single a b = b • Finsupp.single a (1 : ℤ) := by
      rw [Finsupp.smul_single]
      simp
    rw [hsingle, map_add (cubD 1 X), map_add (PsiLin x₀), map_smul (cubD 1 X),
      map_smul (PsiLin x₀), PsiLin_cubD_single, ih, smul_zero, add_zero]

/-- **The conjugation is invisible in the abelianisation**: the class of a based `1`-cube is the
abelianised class of the cube, read in the path model. -/
theorem cubeClass_based (p : Ω^ (Fin 1) X x₀) :
    Abelianization.of (cubeClass x₀ p.1)
      = Abelianization.of (show HomotopyGroup (Fin 1) X x₀ from ⟦p⟧) := by
  have h0 : p.1 (0 : IC 1) = x₀ := p.2 0 ⟨0, Or.inl rfl⟩
  have h1 : p.1 (1 : IC 1) = x₀ := p.2 1 ⟨0, Or.inr rfl⟩
  have hpath : cubePath p.1 = (loopOfCube x₀ p).cast h0 h1 := by
    ext u
    rw [Path.cast_coe]
    rfl
  have hcast : Path.Homotopic.Quotient.mk (cubePath p.1)
      = (Path.Homotopic.Quotient.mk (loopOfCube x₀ p)).cast h0 h1 := by
    rw [hpath]
    exact Path.Homotopic.Quotient.mk_cast (loopOfCube x₀ p) h0 h1
  have hconj : (conjClass x₀ (Path.Homotopic.Quotient.mk (loopOfCube x₀ p)) :
        FundamentalGroup X x₀)
      = (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basePath x₀ x₀)))⁻¹
        * FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopOfCube x₀ p))
        * FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basePath x₀ x₀)) := rfl
  have hkey : (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopOfCube x₀ p)))
      = (show HomotopyGroup (Fin 1) X x₀ from ⟦p⟧) := by
    rw [← pi1_eq_mk_loopOfCube x₀ p]
    exact MulEquiv.symm_apply_apply _ _
  show Abelianization.of
      ((HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x₀)).symm
        (FundamentalGroup.fromPath
          (conjClass x₀ (Path.Homotopic.Quotient.mk (cubePath p.1)))))
      = Abelianization.of (show HomotopyGroup (Fin 1) X x₀ from ⟦p⟧)
  rw [hcast, conjClass_cast, hconj]
  simp only [map_mul, map_inv]
  rw [hkey]
  exact inv_mul_mul_cancel _ _

/-- **`Ψ` of a based `1`-cube is the abelianised class of the cube.** -/
theorem PsiLin_single_based (p : Ω^ (Fin 1) X x₀) :
    PsiLin x₀ (Finsupp.single p.1 1)
      = Additive.ofMul (Abelianization.of (show HomotopyGroup (Fin 1) X x₀ from ⟦p⟧)) := by
  rw [PsiLin_single, psiCube_eq, cubeClass_based]

end Main

theorem hurewiczKerTorsion_one_abelian {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x₀ : X)
    (hcomm : ∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a) :
    letI hGr : Group (HomotopyGroup (Fin 1) X x₀) := HomotopyGroup.group (Fin 1)
    ∀ a : HomotopyGroup (Fin 1) X x₀,
      Work.Stems.hurewiczMapN 1 (le_refl 1) x₀ a = 0 → ∃ N : ℕ, 0 < N ∧ a ^ N = 1 := by
  intro a ha
  set p : Ω^ (Fin 1) X x₀ := Quotient.out a with hp
  have hpa : (show HomotopyGroup (Fin 1) X x₀ from (⟦p⟧ : HomotopyGroup (Fin 1) X x₀)) = a :=
    Quotient.out_eq a
  have hp0 : Work.Stems.hurewiczMapN 1 (le_refl 1) x₀
      (show HomotopyGroup (Fin 1) X x₀ from (⟦p⟧ : HomotopyGroup (Fin 1) X x₀)) = 0 := by
    rw [hpa]; exact ha
  have hker : ∀ x : HomotopyGroup (Fin 1) X x₀, Abelianization.of x = 1 → x = 1 := by
    intro x hx
    have hx1 : x ∈ commutator (HomotopyGroup (Fin 1) X x₀) := by
      rw [← Abelianization.ker_of]
      exact MonoidHom.mem_ker.mpr hx
    have hle : commutator (HomotopyGroup (Fin 1) X x₀) ≤ ⊥ := by
      rw [commutator_eq_closure, Subgroup.closure_le]
      rintro z ⟨u, v, rfl⟩
      exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hcomm u v))
    exact Subgroup.mem_bot.mp (hle hx1)
  have key : (show HomotopyGroup (Fin 1) X x₀ from (⟦p⟧ : HomotopyGroup (Fin 1) X x₀)) = 1 := by
    apply hker
    have hz : PsiLin x₀ (Finsupp.single p.1 1) = 0 := by
      obtain ⟨c, hc | hc⟩ := Work.RatHurewicz.cubicalBridgeDeg 1 (le_refl 1) x₀ p hp0
      · have hdeg : PsiLin x₀ (cubD 1 X c - Finsupp.single p.1 1) = 0 := PsiLin_deg x₀ hc
        have h2 : PsiLin x₀ (cubD 1 X c) - PsiLin x₀ (Finsupp.single p.1 1) = 0 := by
          rw [← map_sub]; exact hdeg
        rw [PsiLin_cubD, zero_sub] at h2
        exact neg_eq_zero.mp h2
      · have hdeg : PsiLin x₀ (cubD 1 X c + Finsupp.single p.1 1) = 0 := PsiLin_deg x₀ hc
        have h2 : PsiLin x₀ (cubD 1 X c) + PsiLin x₀ (Finsupp.single p.1 1) = 0 := by
          rw [← map_add]; exact hdeg
        rw [PsiLin_cubD, zero_add] at h2
        exact h2
    have hZ := PsiLin_single_based x₀ p
    rw [hZ] at hz
    exact Additive.ofMul.injective (by rw [hz]; rfl)
  have ha1 : a = 1 := by rw [← hpa]; exact key
  exact ⟨1, one_pos, by rw [ha1, one_pow]⟩

end

end Work.Rat.RankOneC1
