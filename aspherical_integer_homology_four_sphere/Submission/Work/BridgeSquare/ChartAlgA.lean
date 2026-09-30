/-
# `BridgeSquare/ChartAlgA.lean` — chart simplices in the cusp coordinates, and their chain algebra

A *chart simplex* is the image under the ceiling map `mbarPtC v` of an affine simplex of the cusp
coordinate space `E3 = ℝ³` with a given vertex family `p`:

  `cSimp v p : Δ^k → M̄,   z ↦ mbarPtC v (∑ i, zᵢ • pᵢ)`.

Its faces are the chart simplices of the face families (`cSimp_face`), hence the alternating-sum
formula for its boundary (`cChain_d`), from which all the formal chain identities of this file
follow: the three-vertex shape of the boundary, the collinear subdivision, the reversal, the
degeneracy and the prism identity.  These are the combinatorial skeleton of the fibre identities
`fibreLoopIdentA/B`: everything there reduces to linear combinations of chart chains.

This file is self-contained (it does not import the in-progress `Chart.lean`), so that it is
independent of concurrent edits in the area.
-/
import Mathlib
import Submission.Work.Cohomology.linSimplex_boundary
import Submission.Work.RTOwed.cuspChartGlue
import Submission.Work.RTOwed.cuspCeilingData_exists
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.BridgeSquare.FibreData

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology
open Convexity

attribute [local instance] Convexity.ConvexSpace.ofModule

namespace Work.BridgeSquare

noncomputable section

/-- `M̄`, as a topological space. -/
abbrev cMtop : TopCat := TopCat.of Work.FoldInst.Mbar

/-- The cusp coordinate space. -/
abbrev cE3 : Type := Work.Cusp.E3

/-! ## §0  The boundary of a singular generator -/

/-- The `i`-th coface of the standard simplex, as a continuous map `Δ^k → Δ^{k+1}`. -/
def cFace {k : ℕ} (i : Fin (k + 2)) :
    C(StdSimplex ℝ (Fin (k + 1)), StdSimplex ℝ (Fin (k + 2))) :=
  ⟨StdSimplex.map (Fin.succAbove i),
    Convexity.StdSimplex.continuous_map (R := ℝ) (Fin.succAbove i)⟩

/-- **The boundary of a singular simplex**, evaluated on its basis element. -/
theorem singGen_d {X : TopCat} {k : ℕ} (u : C(StdSimplex ℝ (Fin (k + 2)), X)) :
    (singCxFun.obj X).d (k + 1) k (singGen u)
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • singGen (u.comp (cFace i)) := by
  have key : ∀ i : Fin (k + 2),
      ((TopCat.toSSet.obj X).ιChainComplex (R := Work.Homology.ZMod)
        ((TopCat.toSSet.obj X).δ i
          ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk (k + 1)))).symm u))).hom 1
        = singGen (u.comp (cFace i)) := by
    intro i
    simp only [singGen]
    congr 2
  have h := Work.Cohomology.chainComplex_d_ι_apply ℤ (X := TopCat.toSSet.obj X) (n := k)
    ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk (k + 1)))).symm u)
  exact h.trans (Finset.sum_congr rfl fun i _ =>
    congrArg (fun y => ((-1 : ℤ) ^ (i : ℕ)) • y) (key i))

/-! ## §1  The chart simplex and its faces -/

/-- The affine point of the vertex family `p`. -/
def cPt {k : ℕ} (p : Fin (k + 1) → cE3) (z : StdSimplex ℝ (Fin (k + 1))) : cE3 :=
  z.iConvexComb p

theorem cPt_eq_sum {k : ℕ} (p : Fin (k + 1) → cE3) (z : StdSimplex ℝ (Fin (k + 1))) :
    cPt p z = ∑ i, z.weights i • p i := by
  show z.iConvexComb p = ∑ i, z.weights i • p i
  rw [Convexity.iConvexComb_eq_sum, Finsupp.sum_fintype]
  simp

theorem continuous_cPt {k : ℕ} (p : Fin (k + 1) → cE3) : Continuous (cPt p) := by
  rw [show cPt p = fun z => ∑ i, z.weights i • p i from funext fun z => cPt_eq_sum p z]
  fun_prop

/-- **The affine point commutes with reindexing the standard simplex.** -/
theorem cPt_map {k l : ℕ} (p : Fin (k + 1) → cE3) (f : Fin (l + 1) → Fin (k + 1))
    (z : StdSimplex ℝ (Fin (l + 1))) :
    cPt p (StdSimplex.map f z) = cPt (fun j => p (f j)) z := by
  show (StdSimplex.map f z).iConvexComb p = z.iConvexComb (fun j => p (f j))
  rw [Convexity.iConvexComb_map]

/-- **The chart simplex** of the `v`-th cusp with the vertex family `p`. -/
def cSimp (v : Fin 5) {k : ℕ} (p : Fin (k + 1) → cE3) : C(StdSimplex ℝ (Fin (k + 1)), cMtop) :=
  ⟨fun z => Work.RTOwed.mbarPtC v (cPt p z),
    (Work.RTOwed.mbarPtC_continuous v).comp (continuous_cPt p)⟩

@[simp] theorem cSimp_apply (v : Fin 5) {k : ℕ} (p : Fin (k + 1) → cE3)
    (z : StdSimplex ℝ (Fin (k + 1))) :
    cSimp v p z = Work.RTOwed.mbarPtC v (cPt p z) := rfl

/-- **The `i`-th face of a chart simplex is the chart simplex of the face family.** -/
theorem cSimp_face (v : Fin 5) {k : ℕ} (p : Fin (k + 2) → cE3) (i : Fin (k + 2)) :
    (cSimp v p).comp (cFace i) = cSimp v (fun j => p (Fin.succAbove i j)) := by
  ext z
  simp only [ContinuousMap.comp_apply, cFace, ContinuousMap.coe_mk]
  exact congrArg (fun w => Work.RTOwed.mbarPtC v w) (cPt_map p (Fin.succAbove i) z)

/-- **The chart chain** of the vertex family `p`. -/
def cChain (v : Fin 5) {k : ℕ} (p : Fin (k + 1) → cE3) : ↥((singCxFun.obj cMtop).X k) :=
  singGen (cSimp v p)

/-- **The boundary of a chart simplex**: the alternating sum of the chart simplices of its faces. -/
theorem cChain_d (v : Fin 5) {k : ℕ} (p : Fin (k + 2) → cE3) :
    (singCxFun.obj cMtop).d (k + 1) k (cChain (v := v) p)
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          cChain (v := v) (fun j => p (Fin.succAbove i j)) := by
  rw [cChain, singGen_d]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [cSimp_face]
  rfl

/-! ## §2  The small chart chains and their formal identities -/

/-- The chart `0`-chain of a point. -/
abbrev c0 (v : Fin 5) (a : cE3) : ↥((singCxFun.obj cMtop).X 0) := cChain (v := v) ![a]

/-- The chart `1`-chain with the two vertices `a`, `b`. -/
abbrev c1 (v : Fin 5) (a b : cE3) : ↥((singCxFun.obj cMtop).X 1) := cChain (v := v) ![a, b]

/-- The chart `2`-chain with the three vertices `a`, `b`, `c`. -/
abbrev c2 (v : Fin 5) (a b c : cE3) : ↥((singCxFun.obj cMtop).X 2) := cChain (v := v) ![a, b, c]

/-- The boundary of the chart `1`-simplex `[a,b]`. -/
theorem c1_d (v : Fin 5) (a b : cE3) :
    (singCxFun.obj cMtop).d 1 0 (c1 v a b) = c0 v b - c0 v a := by
  have h := cChain_d (v := v) (k := 0) (p := ![a, b])
  rw [Fin.sum_univ_two] at h
  have e0 : (fun j : Fin 1 => (![a, b] : Fin 2 → cE3) (Fin.succAbove 0 j)) = ![b] := by
    funext j; fin_cases j; rfl
  have e1 : (fun j : Fin 1 => (![a, b] : Fin 2 → cE3) (Fin.succAbove 1 j)) = ![a] := by
    funext j; fin_cases j; rfl
  rw [e0, e1] at h
  norm_num at h
  simpa only [c1, c0, sub_eq_add_neg] using h

/-- The boundary of the chart `2`-simplex `[a,b,c]`. -/
theorem c2_d (v : Fin 5) (a b c : cE3) :
    (singCxFun.obj cMtop).d 2 1 (c2 v a b c) = c1 v b c - c1 v a c + c1 v a b := by
  have h := cChain_d (v := v) (k := 1) (p := ![a, b, c])
  rw [Fin.sum_univ_three] at h
  have e0 : (fun j : Fin 2 => (![a, b, c] : Fin 3 → cE3) (Fin.succAbove 0 j)) = ![b, c] := by
    funext j; fin_cases j <;> rfl
  have e1 : (fun j : Fin 2 => (![a, b, c] : Fin 3 → cE3) (Fin.succAbove 1 j)) = ![a, c] := by
    funext j; fin_cases j <;> rfl
  have e2 : (fun j : Fin 2 => (![a, b, c] : Fin 3 → cE3) (Fin.succAbove 2 j)) = ![a, b] := by
    funext j; fin_cases j <;> rfl
  rw [e0, e1, e2] at h
  norm_num at h
  simpa only [c2, c1, sub_eq_add_neg] using h

/-- **Collinear subdivision**: `[a,b] + [b,c] = [a,c] + ∂[a,b,c]`. -/
theorem c1_sub (v : Fin 5) (a b c : cE3) :
    c1 v a b + c1 v b c = c1 v a c + (singCxFun.obj cMtop).d 2 1 (c2 v a b c) := by
  rw [c2_d]; abel

/-- **Reversal**: `[a,b] + [b,a] = ∂[a,b,a] + [a,a]`. -/
theorem c1_rev (v : Fin 5) (a b : cE3) :
    c1 v a b + c1 v b a = (singCxFun.obj cMtop).d 2 1 (c2 v a b a) + c1 v a a := by
  rw [c2_d]; abel

/-- The degenerate chart `1`-simplex `[a,a]` is a boundary. -/
theorem c1_deg (v : Fin 5) (a : cE3) :
    c1 v a a = (singCxFun.obj cMtop).d 2 1 (c2 v a a a) := by
  rw [c2_d]; abel

/-- **The prism identity**: the boundary of the two triangles `[A,B,C]`, `[B,D,C]` of the
quadrilateral with the vertices `A,B,D,C` is `- [A,C] + [A,B] + [D,C] + [B,D]`. -/
theorem c1_prism (v : Fin 5) (A B C D : cE3) :
    c1 v A C = c1 v B D + c1 v A B + c1 v D C
      - (singCxFun.obj cMtop).d 2 1 (c2 v A B C + c2 v B D C) := by
  rw [map_add, c2_d, c2_d]; abel

/-- **The subdivision identity**: the sum of the consecutive chart edges `[x i, x (i+1)]` over
`i < n` equals `[x 0, x n]` up to the boundary of the cone over the base point `x 0`. -/
theorem c1_subdiv (v : Fin 5) (x : ℕ → cE3) (n : ℕ) :
    (∑ i ∈ Finset.range n, c1 v (x i) (x (i + 1)))
      = c1 v (x 0) (x n)
        + (singCxFun.obj cMtop).d 2 1 (∑ i ∈ Finset.range n, c2 v (x 0) (x i) (x (i + 1)))
        - c1 v (x 0) (x 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, map_add]
      have h2 : c1 v (x 0) (x n) + c1 v (x n) (x (n + 1))
          = c1 v (x 0) (x (n + 1))
            + (singCxFun.obj cMtop).d 2 1 (c2 v (x 0) (x n) (x (n + 1))) :=
        c1_sub v (x 0) (x n) (x (n + 1))
      have h3 : c1 v (x n) (x (n + 1))
          = c1 v (x 0) (x (n + 1))
            + (singCxFun.obj cMtop).d 2 1 (c2 v (x 0) (x n) (x (n + 1)))
            - c1 v (x 0) (x n) := by
        rw [← h2]; abel
      rw [h3]; abel

end

end Work.BridgeSquare
