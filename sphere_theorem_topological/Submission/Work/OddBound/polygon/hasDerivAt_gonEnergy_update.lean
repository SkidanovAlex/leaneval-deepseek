import Mathlib
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.polygon.hasDerivAt_riemannianDist_sq_along
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal

namespace Work.OddBound.polygon

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The derivative of the polygon energy in one vertex

`gonEnergy p w = (N/2) · Σ_{j<N} d(v_j, v_{j+1})²` is a function of the interior vertices
`w : Fin (N-1) → M`; moving the `i`-th vertex along a curve `γ` changes exactly the two sides
adjacent to it (side `i` and side `i+1`), and the first variation of the squared distance
(`hasDerivAt_riemannianDist_sq_along`) gives

  `d/dt|_{t=0} gonEnergy p (w with w i := γ t) = -N · ⟨uplus + uminus, γ'(0)⟩`,

where `uplus` (resp. `uminus`) is the tangent vector at `w i` whose exponential is the next
(resp. previous) vertex.  This is the vertex-wise first-variation formula used to identify the
critical points of `gonEnergy` with the closed geodesics.

## Contents

* `gonVert_update_succ`, `gonVert_update_ne`: how the vertex list `gonVert` reacts to
  `Function.update` of one interior vertex (pure bookkeeping, no geometry);
* `riemannianDist_comm`: the Riemannian distance is symmetric;
* `hasDerivAt_gonEnergy_update`: the requested formula.
-/

/-! ## 1. Vertex bookkeeping for `gonVert` -/

section VertexBookkeeping

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]

/-- **Updating the `i`-th interior vertex moves vertex `i+1`.**  The vertex `i+1` of the polygon
is the `i`-th interior vertex `w i`, so replacing `w i` by `x` replaces the vertex `i+1` by `x`. -/
lemma gonVert_update_succ (p : M) {N : ℕ} (w : Fin (N-1) → M) (i : Fin (N-1)) (x : M) :
    Work.OddBound.gonVert p (Function.update w i x) ((i:ℕ) + 1) = x := by
  have hi : (i:ℕ) < N - 1 := i.2
  rw [Work.OddBound.gonVert_succ (i := (i:ℕ)) (hi := hi)]
  have hfin : (⟨(i:ℕ), hi⟩ : Fin (N-1)) = i := rfl
  rw [hfin, Function.update_self]

/-- **Updating the `i`-th interior vertex keeps every other vertex.**  If `j ≠ i+1` then the
vertex `j` of the polygon does not involve the interior vertex `w i`. -/
lemma gonVert_update_ne (p : M) {N : ℕ} (w : Fin (N-1) → M) (i : Fin (N-1)) (x : M)
    {j : ℕ} (hj : j ≠ (i:ℕ) + 1) :
    Work.OddBound.gonVert p (Function.update w i x) j = Work.OddBound.gonVert p w j := by
  by_cases h0 : j = 0
  · subst h0
    rw [Work.OddBound.gonVert_zero, Work.OddBound.gonVert_zero]
  · by_cases hN : N ≤ j
    · rw [Work.OddBound.gonVert_of_le (p := p) (w := Function.update w i x) hN,
        Work.OddBound.gonVert_of_le (p := p) (w := w) hN]
    · have hj1 : j - 1 < N - 1 := by omega
      have hj' : j = (j - 1) + 1 := by omega
      have hL : Work.OddBound.gonVert p (Function.update w i x) j
          = Function.update w i x ⟨j - 1, hj1⟩ := by
        conv_lhs => rw [hj']
        exact Work.OddBound.gonVert_succ (p := p) (w := Function.update w i x)
          (i := j - 1) (hi := hj1)
      have hR : Work.OddBound.gonVert p w j = w ⟨j - 1, hj1⟩ := by
        conv_lhs => rw [hj']
        exact Work.OddBound.gonVert_succ (p := p) (w := w) (i := j - 1) (hi := hj1)
      rw [hL, hR]
      have hne : (⟨j - 1, hj1⟩ : Fin (N-1)) ≠ i := by
        intro h
        have hval : j - 1 = (i : ℕ) := congrArg Fin.val h
        have hjge : 1 ≤ j := by omega
        exact hj (by rw [← Nat.sub_add_cancel hjge, hval])
      rw [Function.update_of_ne hne]

end VertexBookkeeping

/-! ## 2. Symmetry of the Riemannian distance -/

section DistanceComm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  [PathConnectedSpace M] [RegularSpace M]

/-- **The Riemannian distance is symmetric**, being the `toReal` of the symmetric extended
Riemannian distance (`riemannianDist_eq_toReal`, `Manifold.riemannianEDist_comm`). -/
lemma riemannianDist_comm (x y : M) :
    Submission.Distance.riemannianDist (I := I) x y
      = Submission.Distance.riemannianDist (I := I) y x := by
  rw [riemannianDist_eq_toReal (I := I) x y, riemannianDist_eq_toReal (I := I) y x,
    Manifold.riemannianEDist_comm]

end DistanceComm

/-! ## 3. The first variation of the polygon energy in one vertex -/

theorem hasDerivAt_gonEnergy_update
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {N : ℕ} (hN : 2 ≤ N) {p : M} {w : Fin (N - 1) → M}
    {R : ℝ} (hR : 0 < R)
    (hinj : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x R)
    (hsmall : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p w i < R)
    (i : Fin (N - 1)) {uplus uminus : TangentSpace I (w i)}
    (hup : Submission.GlobalExp.GExp (cov := cov) hmet (w i) uplus
      = Work.OddBound.gonVert p w ((i : ℕ) + 2))
    (hupn : ‖uplus‖ = Submission.Distance.riemannianDist (I := I) (w i)
      (Work.OddBound.gonVert p w ((i : ℕ) + 2)))
    (hum : Submission.GlobalExp.GExp (cov := cov) hmet (w i) uminus
      = Work.OddBound.gonVert p w (i : ℕ))
    (humn : ‖uminus‖ = Submission.Distance.riemannianDist (I := I) (w i)
      (Work.OddBound.gonVert p w (i : ℕ)))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hγ0 : γ 0 = w i) :
    HasDerivAt (fun t : ℝ => Work.OddBound.gonEnergy (I := I) p (Function.update w i (γ t)))
      (-(N : ℝ) * inner ℝ (uplus + uminus) (Submission.Geodesic.curveVelocity (I := I) γ 0)) 0 := by
  classical
  -- ### index bounds
  have hkN : (i:ℕ) < N := by have := i.isLt; omega
  have hk1N : (i:ℕ) + 1 < N := by have := i.isLt; omega
  -- ### the two sides adjacent to the moving vertex are shorter than the injectivity radius
  have hd_prev : Submission.Distance.riemannianDist (I := I) (w i)
      (Work.OddBound.gonVert p w ((i:ℕ))) < R := by
    have hs : Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p w ((i:ℕ)))
        (w i) < R := by
      have hv : Work.OddBound.gonVert p w ((i:ℕ)+1) = w i := by
        rw [Work.OddBound.gonVert_succ (i := (i:ℕ)) (hi := i.isLt)]
      rw [← hv]
      exact hsmall ⟨(i:ℕ), hkN⟩
    rw [riemannianDist_comm]
    exact hs
  have hd_next : Submission.Distance.riemannianDist (I := I) (w i)
      (Work.OddBound.gonVert p w ((i:ℕ)+2)) < R := by
    have hv : Work.OddBound.gonVert p w ((i:ℕ)+1) = w i := by
      rw [Work.OddBound.gonVert_succ (i := (i:ℕ)) (hi := i.isLt)]
    have h : Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p w ((i:ℕ)+1))
        (Work.OddBound.gonVert p w ((i:ℕ)+1+1)) < R := hsmall ⟨(i:ℕ)+1, hk1N⟩
    rw [hv] at h
    exact h
  -- ### first variation of the squared distance to the two neighbouring vertices
  have hprev := hasDerivAt_riemannianDist_sq_along (I := I) (cov := cov) hmet htor hR
    (hinj (w i)) hd_prev hum humn hγ hγ0
  have hnext := hasDerivAt_riemannianDist_sq_along (I := I) (cov := cov) hmet htor hR
    (hinj (w i)) hd_next hup hupn hγ hγ0
  -- ### the side lengths of the updated polygon
  have hside_prev : ∀ t : ℝ,
      Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) ((i:ℕ))
      = Submission.Distance.riemannianDist (I := I) (γ t) (Work.OddBound.gonVert p w ((i:ℕ))) := by
    intro t
    show Submission.Distance.riemannianDist (I := I)
        (Work.OddBound.gonVert p (Function.update w i (γ t)) ((i:ℕ)))
        (Work.OddBound.gonVert p (Function.update w i (γ t)) ((i:ℕ)+1))
      = Submission.Distance.riemannianDist (I := I) (γ t) (Work.OddBound.gonVert p w ((i:ℕ)))
    rw [gonVert_update_succ p w i (γ t),
      gonVert_update_ne p w i (γ t) (j := (i:ℕ)) (by omega), riemannianDist_comm]
  have hside_next : ∀ t : ℝ,
      Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) ((i:ℕ)+1)
      = Submission.Distance.riemannianDist (I := I) (γ t) (Work.OddBound.gonVert p w ((i:ℕ)+2)) := by
    intro t
    show Submission.Distance.riemannianDist (I := I)
        (Work.OddBound.gonVert p (Function.update w i (γ t)) ((i:ℕ)+1))
        (Work.OddBound.gonVert p (Function.update w i (γ t)) ((i:ℕ)+1+1))
      = Submission.Distance.riemannianDist (I := I) (γ t) (Work.OddBound.gonVert p w ((i:ℕ)+2))
    rw [gonVert_update_succ p w i (γ t),
      gonVert_update_ne p w i (γ t) (j := (i:ℕ)+2) (by omega)]
  have hside_other : ∀ (j : ℕ), j ≠ (i:ℕ) → j ≠ (i:ℕ)+1 → ∀ t : ℝ,
      Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j
      = Work.OddBound.gonSideLen (I := I) p w j := by
    intro j hj hj' t
    show Submission.Distance.riemannianDist (I := I)
        (Work.OddBound.gonVert p (Function.update w i (γ t)) j)
        (Work.OddBound.gonVert p (Function.update w i (γ t)) (j+1))
      = Submission.Distance.riemannianDist (I := I)
        (Work.OddBound.gonVert p w j) (Work.OddBound.gonVert p w (j+1))
    rw [gonVert_update_ne p w i (γ t) (j := j) hj',
      gonVert_update_ne p w i (γ t) (j := j+1) (by omega)]
  -- ### first variation of the (finite) sum of squared side lengths
  have hsum : HasDerivAt (fun t : ℝ => ∑ j : Fin N,
        (Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j) ^ 2)
      (∑ j : Fin N, ((if (j:ℕ) = (i:ℕ) then
            (-2 : ℝ) * inner ℝ uminus (Submission.Geodesic.curveVelocity (I := I) γ 0) else 0)
          + (if (j:ℕ) = (i:ℕ)+1 then
            (-2 : ℝ) * inner ℝ uplus (Submission.Geodesic.curveVelocity (I := I) γ 0) else 0))) 0 := by
    have key := HasDerivAt.sum (x := 0) (u := (Finset.univ : Finset (Fin N)))
      (A := fun (j : Fin N) (t : ℝ) =>
        (Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j) ^ 2)
      (A' := fun j : Fin N => ((if (j:ℕ) = (i:ℕ) then
            (-2 : ℝ) * inner ℝ uminus (Submission.Geodesic.curveVelocity (I := I) γ 0) else 0)
          + (if (j:ℕ) = (i:ℕ)+1 then
            (-2 : ℝ) * inner ℝ uplus (Submission.Geodesic.curveVelocity (I := I) γ 0) else 0))) ?_
    · have hfun_eq : (∑ j : Fin N,
          fun t : ℝ => (Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j) ^ 2)
          = fun t : ℝ => ∑ j : Fin N,
            (Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j) ^ 2 := by
        funext t
        rw [Finset.sum_apply]
      simpa only [← hfun_eq] using key
    · intro j _
      rcases eq_or_ne ((j:ℕ)) ((i:ℕ)) with hj | hj
      · -- `j = i`: the derivative comes from the *previous* vertex
        have hfun : (fun t : ℝ =>
              (Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j) ^ 2)
            = fun t : ℝ => (Submission.Distance.riemannianDist (I := I) (γ t)
                (Work.OddBound.gonVert p w ((i:ℕ)))) ^ 2 := by
          funext t
          rw [hj, hside_prev t]
        have hne : ¬((j:ℕ) = (i:ℕ)+1) := by omega
        rw [hfun, if_pos hj, if_neg hne, add_zero]
        exact hprev
      · rcases eq_or_ne ((j:ℕ)) ((i:ℕ)+1) with hj2 | hj2
        · -- `j = i+1`: the derivative comes from the *next* vertex
          have hfun : (fun t : ℝ =>
                (Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j) ^ 2)
              = fun t : ℝ => (Submission.Distance.riemannianDist (I := I) (γ t)
                  (Work.OddBound.gonVert p w ((i:ℕ)+2))) ^ 2 := by
            funext t
            rw [hj2, hside_next t]
          rw [hfun, if_neg hj, if_pos hj2, zero_add]
          exact hnext
        · -- all other sides are constant in `t`
          have hfun : (fun t : ℝ =>
                (Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j) ^ 2)
              = fun _ : ℝ => (Work.OddBound.gonSideLen (I := I) p w j) ^ 2 := by
            funext t
            rw [hside_other (j:ℕ) hj hj2 t]
          rw [hfun, if_neg hj, if_neg hj2, add_zero]
          exact hasDerivAt_const 0 _
  -- ### evaluation of the two-index sum
  have hA : (∑ j : Fin N, (if (j:ℕ) = (i:ℕ) then
        (-2 : ℝ) * inner ℝ uminus (Submission.Geodesic.curveVelocity (I := I) γ 0) else 0))
      = (-2 : ℝ) * inner ℝ uminus (Submission.Geodesic.curveVelocity (I := I) γ 0) := by
    refine (Finset.sum_eq_single_of_mem (⟨(i:ℕ), hkN⟩ : Fin N) (Finset.mem_univ _) ?_).trans ?_
    · intro b _ hb
      have hbn : (b:ℕ) ≠ (i:ℕ) := fun h => hb (Fin.ext h)
      simp [hbn]
    · simp
  have hB : (∑ j : Fin N, (if (j:ℕ) = (i:ℕ)+1 then
        (-2 : ℝ) * inner ℝ uplus (Submission.Geodesic.curveVelocity (I := I) γ 0) else 0))
      = (-2 : ℝ) * inner ℝ uplus (Submission.Geodesic.curveVelocity (I := I) γ 0) := by
    refine (Finset.sum_eq_single_of_mem (⟨(i:ℕ)+1, hk1N⟩ : Fin N) (Finset.mem_univ _) ?_).trans ?_
    · intro b _ hb
      have hbn : (b:ℕ) ≠ (i:ℕ)+1 := fun h => hb (Fin.ext h)
      simp [hbn]
    · simp
  -- ### the energy is `(N/2)` times the sum
  have hfun : (fun t : ℝ => Work.OddBound.gonEnergy (I := I) p (Function.update w i (γ t)))
      = fun t : ℝ => (N:ℝ)/2 * ∑ j : Fin N,
          (Work.OddBound.gonSideLen (I := I) p (Function.update w i (γ t)) j) ^ 2 := rfl
  -- ### the scalar identity
  have hT : -(N:ℝ) * inner ℝ (uplus + uminus) (Submission.Geodesic.curveVelocity (I := I) γ 0)
      = (N:ℝ)/2 * ((-2 : ℝ) * inner ℝ uminus (Submission.Geodesic.curveVelocity (I := I) γ 0)
          + (-2 : ℝ) * inner ℝ uplus (Submission.Geodesic.curveVelocity (I := I) γ 0)) := by
    have h2 : (2:ℝ) * ((N:ℝ)/2) = (N:ℝ) := by ring_nf
    have hIA := inner_add_left (𝕜 := ℝ) (E := TangentSpace I (w i)) uplus uminus
      (Submission.Geodesic.curveVelocity (I := I) γ 0)
    rw [hIA, add_comm (inner ℝ uplus (Submission.Geodesic.curveVelocity (I := I) γ 0))
      (inner ℝ uminus (Submission.Geodesic.curveVelocity (I := I) γ 0))]
    linear_combination (inner ℝ uminus (Submission.Geodesic.curveVelocity (I := I) γ 0)
      + inner ℝ uplus (Submission.Geodesic.curveVelocity (I := I) γ 0)) * h2
  rw [Finset.sum_add_distrib, hA, hB] at hsum
  rw [hfun, hT]
  exact hsum.const_mul ((N:ℝ)/2)

end Work.OddBound.polygon
