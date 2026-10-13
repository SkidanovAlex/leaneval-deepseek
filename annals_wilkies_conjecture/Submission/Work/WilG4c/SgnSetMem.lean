import Mathlib
import Submission.Work.WilG4c.StepBadLoc
import Submission.Work.WilG1.Basic

noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## The closed half-space is `Ω`-bounded

The `hyp` axiom of `SOMin` only produces *zero sets* of polynomials, so a closed half-space
like `{z | 0 ≤ z i}` is not available directly.  The standard encoding is the parabola over
the `i`-th coordinate: let `P = X (last n)^2 - X (castSucc i)` be the equation
`(last coordinate)^2 = i`-th coordinate in `ℝ^{n+1}`.  Then

`projLast {w : Fin (n+1) → ℝ | P w = 0} = {z : Fin n → ℝ | 0 ≤ z i}`

because over `ℝ`, `∃ t, t ^ 2 = z i ↔ 0 ≤ z i` (use `Real.sqrt` one way and `sq_nonneg` the
other).  The cost is one extra variable (`hyp` runs in dimension `n+1`) and one projection
(`SOMin.proj`), i.e. format `n+2`, and the degree is `2`.

This is exactly the shape needed to intersect the derivative-graph set of `dgSet` with a sign
condition before projecting. -/
theorem halfspaceMemOmega (S : SOMin) {n : ℕ} (i : Fin n) :
    {z : Fin n → ℝ | 0 ≤ z i} ∈ S.Ω (n + 2) 2 n := by
  let P : MvPolynomial (Fin (n + 1)) ℝ :=
    MvPolynomial.X (Fin.last n) ^ 2 - MvPolynomial.X (Fin.castSucc i)
  have htd : P.totalDegree ≤ 2 := by
    dsimp only [P]
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · have h := MvPolynomial.totalDegree_pow
        (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℝ) 2
      simpa using h
    · simp
  have h1 : {w : Fin (n + 1) → ℝ | MvPolynomial.eval w P = 0} ∈ S.Ω (n + 1) 2 (n + 1) :=
    Work.WilG1.Omega.mono (S := S) (S.hyp (n + 1) P) le_rfl htd
  have hproj := S.proj h1
  have hset : projLast {w : Fin (n + 1) → ℝ | MvPolynomial.eval w P = 0}
      = {z : Fin n → ℝ | 0 ≤ z i} := by
    ext z
    simp only [projLast, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, ht⟩
      simp only [P, MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X,
        Fin.snoc_last, Fin.snoc_castSucc, sub_eq_zero] at ht
      rw [← ht]
      exact sq_nonneg t
    · intro hz
      refine ⟨Real.sqrt (z i), ?_⟩
      simp only [P, MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X,
        Fin.snoc_last, Fin.snoc_castSucc, sub_eq_zero]
      exact Real.sq_sqrt hz
  rw [hset] at hproj
  exact hproj

/-- **Sign sets of derivative graphs are `Ω`-bounded.**  If the derivative graph
`dgSet f 1 (fun _ => Fin.last N)` of a function `f : ℝ^{N+1} → ℝ` (the graph of the derivative
along the last coordinate, over the `C^1` locus) is `Ω`-bounded with format `a` and degree
`eval ![F,1] b`, then so is the projection of the part of it lying over the sign condition
`0 ≤ (derivative value)`: intersect with the closed half-space given by `halfspaceMemOmega`
(format `N+4`, degree `2`) and project out the value coordinate.  The format grows by the
constant `K = N + 6`, and the degree grows by exactly the degree of the parabola, `2`. -/
theorem SgnSetMem (S : WilkiesDesign.SOMin) (N : ℕ) :
    ∃ K : ℕ, ∀ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (F : ℕ) (f : (Fin (N + 1) → ℝ) → ℝ),
      Work.WilG4c.dgSet f 1 (fun _ : Fin 1 => Fin.last N) ∈
        S.Ω a (MvPolynomial.eval ![F, 1] b) (N + 2) →
      WilkiesDesign.projLast (Work.WilG4c.dgSet f 1 (fun _ : Fin 1 => Fin.last N) ∩
          {z : Fin (N + 2) → ℝ | 0 ≤ z (Fin.last (N + 1))}) ∈
        S.Ω (a + K) (MvPolynomial.eval ![F, 1] (b + 2)) (N + 1) := by
  refine ⟨N + 6, ?_⟩
  intro a b F f hf
  -- The closed half-space `0 ≤ z (last (N+1))`, in format `N+4` and degree `2`.
  have hH : ({z : Fin (N + 2) → ℝ | 0 ≤ z (Fin.last (N + 1))} : Set (Fin (N + 2) → ℝ)) ∈
      S.Ω (N + 4) 2 (N + 2) :=
    halfspaceMemOmega (S := S) (n := N + 2) (i := Fin.last (N + 1))
  -- Match the formats of the two sets at `a + (N+4)`.
  have hG : dgSet f 1 (fun _ : Fin 1 => Fin.last N) ∈
      S.Ω (a + (N + 4)) (MvPolynomial.eval ![F, 1] b) (N + 2) :=
    Work.WilG1.Omega.mono (S := S) hf (by omega) le_rfl
  have hH' : ({z : Fin (N + 2) → ℝ | 0 ≤ z (Fin.last (N + 1))} : Set (Fin (N + 2) → ℝ)) ∈
      S.Ω (a + (N + 4)) 2 (N + 2) :=
    Work.WilG1.Omega.mono (S := S) hH (by omega) le_rfl
  -- Intersect: format `+1`, degrees add.
  have hinter : (⋂ i : Fin 2, (if i = 0 then dgSet f 1 (fun _ : Fin 1 => Fin.last N)
        else ({z : Fin (N + 2) → ℝ | 0 ≤ z (Fin.last (N + 1))} : Set (Fin (N + 2) → ℝ)))) ∈
      S.Ω (a + (N + 4) + 1) (MvPolynomial.eval ![F, 1] b + 2) (N + 2) := by
    have h := S.inter (F := a + (N + 4)) (n := N + 2) (k := 2)
      (fun i : Fin 2 => if i = 0 then MvPolynomial.eval ![F, 1] b else 2)
      (fun i : Fin 2 => if i = 0 then dgSet f 1 (fun _ : Fin 1 => Fin.last N)
        else {z : Fin (N + 2) → ℝ | 0 ≤ z (Fin.last (N + 1))})
      (by intro i
          fin_cases i
          · simpa using hG
          · simpa using hH')
    have hsum : (∑ i : Fin 2, (if i = 0 then MvPolynomial.eval ![F, 1] b else 2))
        = MvPolynomial.eval ![F, 1] b + 2 := by
      rw [Fin.sum_univ_two]
      simp
    simpa [hsum] using h
  have hinter2 : (dgSet f 1 (fun _ : Fin 1 => Fin.last N) ∩
      {z : Fin (N + 2) → ℝ | 0 ≤ z (Fin.last (N + 1))}) ∈
      S.Ω (a + (N + 4) + 1) (MvPolynomial.eval ![F, 1] b + 2) (N + 2) := by
    simpa [Work.WilG1.Omega.iInter_fin_two] using hinter
  -- Project out the value coordinate: format `+1`.
  have heval : MvPolynomial.eval ![F, 1] (b + 2) = MvPolynomial.eval ![F, 1] b + 2 := by simp
  exact Work.WilG1.Omega.mono (S := S) (S.proj hinter2) le_rfl (le_of_eq heval.symm)

end Work.WilG4c
