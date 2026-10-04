import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.EXT.curvNormK_frame_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tensoriality of `∇^k Rm`: the value at a point depends only on the values of the fields

`Work.Diff.EXT.covKRmExt g k v A B C D x` is the `k`-th covariant derivative `(∇^k Rm)` of the
curvature of `g`, evaluated in `k` differentiation slots `v` and the four curvature slots
`A B C D` at the point `x`.  It is defined in `Submission/Work/Diff/EXT/local_ext_of_bounded_curv.lean`
by the Leibniz recursion

`(∇_{v₀} ∇^k Rm)(v₁,…,v_k;a,b,c,d) = ∂_{v₀} (∇^k Rm)(v₁,…,v_k;a,b,c,d) − ∑_slots (∇^k Rm)(… ∇_{v₀}(slot) …)`,

which is exactly the covariant derivative of the `(0,k+4)`-tensor `∇^k Rm`.  Consequently
`∇^k Rm` is `C^∞(M)`-multilinear in the `k+4` fields, i.e. its value at `x` depends only on the
values of those fields at `x`.  That is the statement proved here.

## Proof

The recursion is the `Ext`-pattern iteration `Work.Diff.EXT.ckt` of
`Submission/Work/Diff/EXT/curvNormK_frame_indep.lean`, which computes `covKRmExt` on the
corresponding `Fin (k+4)`-tuple of fields (`Work.Diff.EXT.ckt_mkT_eq`).  That file also proves the
single-slot value dependence `Work.Diff.EXT.ckt_val_dep` of the iteration: changing one slot of the
tuple to another field with the same value at `x` does not change the value at `x`.  Chaining this
over the `k+4` slots (`Work.Diff.EXT.ckt_val_dep_all` below) gives the statement.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- The four curvature slots `A B C D` of `∇^k Rm`, as a `Fin 4`-tuple of fields. -/
def quad (A B C D : (Π y : M, TangentSpace I y)) : Fin 4 → (Π y : M, TangentSpace I y) :=
  ![A, B, C, D]

@[simp] theorem quad_zero (A B C D : (Π y : M, TangentSpace I y)) : quad A B C D 0 = A := rfl

@[simp] theorem quad_one (A B C D : (Π y : M, TangentSpace I y)) : quad A B C D 1 = B := rfl

@[simp] theorem quad_two (A B C D : (Π y : M, TangentSpace I y)) : quad A B C D 2 = C := rfl

@[simp] theorem quad_three (A B C D : (Π y : M, TangentSpace I y)) : quad A B C D 3 = D := rfl

/-- **Value dependence of the iteration in all slots at once.**  If two `(k+4)`-tuples of smooth
fields have the same values at `x`, then the values of the `k`-th iterate `ckt` at `x` agree.
(Each slot is replaced in turn using the single-slot value dependence
`Work.Diff.EXT.ckt_val_dep`, the hybrid tuple being tracked by the finset of already replaced
slots.) -/
theorem ckt_val_dep_all (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (k : ℕ) (x : M) {F F' : Fin (k + 4) → (Π y : M, TangentSpace I y)}
    (hF : ∀ s, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F s))
    (hF' : ∀ s, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F' s))
    (h : ∀ s, F s x = F' s x) :
    Work.Diff.EXT.ckt g k F x = Work.Diff.EXT.ckt g k F' x := by
  -- the hybrid tuple: the slots in `t` are taken from `F'`, the others from `F`
  set H : Finset (Fin (k + 4)) → (Fin (k + 4) → (Π y : M, TangentSpace I y)) :=
    fun t s => if s ∈ t then F' s else F s with hHdef
  have hH : ∀ t s, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (H t s) := by
    intro t s
    rw [hHdef]
    by_cases hs : s ∈ t
    · simp only [if_pos hs]
      exact hF' s
    · simp only [if_neg hs]
      exact hF s
  have hHself : ∀ t s, s ∉ t → H t s = F s := by
    intro t s hs
    rw [hHdef]
    simp only [if_neg hs]
  -- replacing one more slot of the hybrid tuple does not change the value at `x`
  have hstep : ∀ (t : Finset (Fin (k + 4))) (s : Fin (k + 4)), s ∉ t →
      Work.Diff.EXT.ckt g k (H t) x = Work.Diff.EXT.ckt g k (H (insert s t)) x := by
    intro t s hs
    have hupd : H (insert s t) = Function.update (H t) s (F' s) := by
      funext u
      simp only [hHdef, Function.update_apply]
      by_cases hu : u = s
      · subst hu
        simp
      · rw [if_neg hu]
        simp only [Finset.mem_insert, hu, false_or]
    rw [hupd]
    have hsd := ckt_val_dep hLC g k x (hH t) s (hF s) (hF' s) (h s)
    have hsame : Function.update (H t) s (F s) = H t := by
      funext u
      by_cases hu : u = s
      · rw [hu, Function.update_self, hHself t s hs]
      · rw [Function.update_of_ne hu]
    rwa [hsame] at hsd
  have hchain : Work.Diff.EXT.ckt g k (H ∅) x = Work.Diff.EXT.ckt g k (H Finset.univ) x :=
    Finset.induction_on (motive := fun t =>
        Work.Diff.EXT.ckt g k (H ∅) x = Work.Diff.EXT.ckt g k (H t) x)
      (Finset.univ : Finset (Fin (k + 4))) rfl
      (fun a t ha ih => by rw [ih, hstep t a ha])
  have h0 : H ∅ = F := by
    funext s
    simp [hHdef]
  have h1 : H Finset.univ = F' := by
    funext s
    simp [hHdef]
  rwa [h0, h1] at hchain

theorem covKRmExt_tensorial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (g : Submission.Diff.SMet I M) (x : M)
    (v v' : Fin k → (Π y : M, TangentSpace I y))
    (A A' B B' C C' D D' : Π y : M, TangentSpace I y)
    (hv : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (v i))
    (hv' : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (v' i))
    (hA : Work.Diff.GE.SmoothFieldT (I := I) (M := M) A)
    (hA' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) A')
    (hB : Work.Diff.GE.SmoothFieldT (I := I) (M := M) B)
    (hB' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) B')
    (hC : Work.Diff.GE.SmoothFieldT (I := I) (M := M) C)
    (hC' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) C')
    (hD : Work.Diff.GE.SmoothFieldT (I := I) (M := M) D)
    (hD' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) D')
    (hvv : ∀ i, v i x = v' i x) (hAA : A x = A' x) (hBB : B x = B' x)
    (hCC : C x = C' x) (hDD : D x = D' x) :
    Work.Diff.EXT.covKRmExt g k v A B C D x = Work.Diff.EXT.covKRmExt g k v' A' B' C' D' x := by
  -- smoothness of the two packed tuples
  have hFs : ∀ s, Work.Diff.GE.SmoothFieldT (I := I) (M := M) ((mkT v (quad A B C D)) s) := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT_castAdd]
      exact hv i
    · intro p
      rw [mkT_natAdd]
      fin_cases p
      · exact hA
      · exact hB
      · exact hC
      · exact hD
  have hFs' : ∀ s, Work.Diff.GE.SmoothFieldT (I := I) (M := M) ((mkT v' (quad A' B' C' D')) s) := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT_castAdd]
      exact hv' i
    · intro p
      rw [mkT_natAdd]
      fin_cases p
      · exact hA'
      · exact hB'
      · exact hC'
      · exact hD'
  -- the two packed tuples have the same values at `x`
  have hvals : ∀ s, (mkT v (quad A B C D)) s x = (mkT v' (quad A' B' C' D')) s x := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT_castAdd, mkT_castAdd]
      exact hvv i
    · intro p
      rw [mkT_natAdd, mkT_natAdd]
      fin_cases p
      · exact hAA
      · exact hBB
      · exact hCC
      · exact hDD
  have e1 : Work.Diff.EXT.covKRmExt g k v A B C D x
      = Work.Diff.EXT.ckt g k (mkT v (quad A B C D)) x := by
    rw [ckt_mkT_eq]
    simp only [quad_zero, quad_one, quad_two, quad_three]
  have e2 : Work.Diff.EXT.covKRmExt g k v' A' B' C' D' x
      = Work.Diff.EXT.ckt g k (mkT v' (quad A' B' C' D')) x := by
    rw [ckt_mkT_eq]
    simp only [quad_zero, quad_one, quad_two, quad_three]
  rw [e1, e2]
  exact ckt_val_dep_all hLC g k x hFs hFs' hvals

end Work.Diff.EXT
