/-
  WilG4c — the base case of the induction step.

  BNZ §5.5 ends the reduction with the case where the family is `1`-Lipschitz and `C^r` with
  all operator norms `≤ 1` on the open cube.  There the single identity chart already works:
  its graph is a coordinate hyperplane, hence `Ω`-definite of degree `1`, and the `ε`-cover of
  the image is trivial.  This is `FLemP S p (n+1) (PSmooth p n)`, the bottom of the chain

    FLemP PSmooth → FLemP PYLipDef → FLemP PYLip → FLemP PY → FLem (dim `n+1`).
-/
import Submission.Work.WilG4c.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The chart tuple of the identity self-map of the cube (the parameter is ignored). -/
def identityChart (p m : ℕ) : ChartTuple p m := fun j _ t => t j

theorem identityChart_apply {p m : ℕ} (j : Fin m) (l : Fin p → ℝ) (t : Fin m → ℝ) :
    identityChart p m j l t = t j := rfl

/-- The graph of the `j`-th coordinate of the identity chart is the coordinate hyperplane
`z_{p+m} = z_{p+j}`, hence an `Ω`-set of format `p+m+1` and degree `1`. -/
theorem identityChart_graph_mem (S : SOMin) (p m : ℕ) (j : Fin m) :
    famGraph (fun l t => identityChart p m j l t) ∈ S.Ω (p + m + 1) 1 (p + m + 1) := by
  have h := S.hyp (p + m + 1)
    (MvPolynomial.X (Fin.last (p + m)) - MvPolynomial.X ((Fin.natAdd p j).castSucc) :
      MvPolynomial (Fin (p + m + 1)) ℝ)
  have hdeg : (MvPolynomial.X (Fin.last (p + m)) -
      MvPolynomial.X ((Fin.natAdd p j).castSucc) :
        MvPolynomial (Fin (p + m + 1)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X, max_self]
  have hset : famGraph (fun l t => identityChart p m j l t) =
      {x : Fin (p + m + 1) → ℝ |
        MvPolynomial.eval x (MvPolynomial.X (Fin.last (p + m)) -
          MvPolynomial.X ((Fin.natAdd p j).castSucc)) = 0} := by
    ext z
    simp [famGraph, graphOf, identityChart, MvPolynomial.eval_sub, sub_eq_zero, Fin.init]
  rw [hset]
  exact Omega_mono_D_le S hdeg h

/-- **The base case of the induction step (BNZ §5.5, the `V = ∅` case).**  A family that is
`1`-Lipschitz and `C^r` with all derivative norms `≤ 1` on the open cube is covered, within
`ε`, by pulling back along the identity chart. -/
theorem StepBase (S : SOMin) (n p : ℕ) : FLemP S p (n + 1) (PSmooth p n) := by
  intro F0
  refine ⟨p + (n + 1) + 1, 1, 1, ?_⟩
  intro D r k ε hε hε1 Λ F hP hΩ hval
  refine ⟨{identityChart p (n + 1)}, by simp, ?_, ?_⟩
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    subst hφ
    refine ⟨?_, ?_⟩
    · intro j
      simpa using identityChart_graph_mem S p (n + 1) j
    · intro l hl
      refine ⟨?_, ?_⟩
      · intro t ht
        simpa [identityChart, openCube] using ht
      · intro i
        exact hP.2 i l
  · intro l hl x hx
    refine ⟨identityChart p (n + 1), Finset.mem_singleton_self _, x, hx, ?_⟩
    intro i
    have hx' : F i l (fun j : Fin (n + 1) => identityChart p (n + 1) j l x) = F i l x := rfl
    rw [hx', sub_self, abs_zero]
    exact hε

end Work.WilkG4c
