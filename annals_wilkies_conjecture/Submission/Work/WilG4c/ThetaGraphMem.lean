import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Basic

/-!
  `ThetaGraphMem` — the "θ-graph" of a `p`-tuple of graphs is an `Ω`-set.

  Let `θ : ℝ^q → ℝ^p` be a map all of whose coordinate functions have their graph in
  `S.Ω F2 D (q+1)` (as a subset of `ℝ^{q+1}`, last coordinate = value).  Then the graph of
  `θ`, namely

    `{z : Fin (p+q) → ℝ | ∀ j : Fin p, z (Fin.castAdd q j) = θ (fun i => z (Fin.natAdd p i)) j}`

  (first `p` coordinates = values, last `q` = arguments), is again an `Ω`-set, with format and
  degree uniform in `D` (the degree a fixed linear polynomial in `D`).

  The proof is the `Ω`-calculus of area `G5`: each coordinate condition is the preimage
  `coordPre ιⱼ (graphOf θⱼ)` of one graph under the *coordinate insertion*

    `ιⱼ : Fin (q+1) → Fin (p+q)`, `ιⱼ (castSucc i) = Fin.natAdd p i`, `ιⱼ (last q) = Fin.castAdd q j`

  (`coordPre_mem`, module `Work.WilG5.Reindex3`), and the graph is the intersection of the `p`
  conditions (`SOMin.inter`).  Only the degree bookkeeping — the intersection sums the `p`
  degrees `D + 32·((p+q)+(q+1)) + 32`, a linear polynomial in `D` — is left to be done.
-/

namespace Work.WilG4c

open WilkiesDesign

/-- The coordinate insertion taking a `(q+1)`-tuple `(u_0,…,u_{q-1}, t)` of coordinates of
`ℝ^{p+q}` (arguments followed by the value) to the corresponding coordinates of `ℝ^{p+q}`:
the `i`-th coordinate of `ℝ^{q+1}` is the `i`-th argument `Fin.natAdd p i` for `i < q`, and the
last one is the `j`-th coordinate `Fin.castAdd q j`. -/
def thetaIdx (p q : ℕ) (j : Fin p) : Fin (q + 1) → Fin (p + q) :=
  fun i => if h : (i : ℕ) < q then ⟨p + i, by omega⟩ else ⟨j, by omega⟩

theorem thetaIdx_castSucc (p q : ℕ) (j : Fin p) (i : Fin q) :
    thetaIdx p q j (Fin.castSucc i) = Fin.natAdd p i := by
  simp only [thetaIdx]
  split_ifs with h
  · exact Fin.ext rfl
  · exact absurd i.isLt h

theorem thetaIdx_last (p q : ℕ) (j : Fin p) :
    thetaIdx p q j (Fin.last q) = Fin.castAdd q j := by
  simp only [thetaIdx]
  split_ifs with h
  · exact absurd h (by simp)
  · exact Fin.ext rfl

/-- The arguments of the inserted tuple: `Fin.init (z ∘ ιⱼ)` is the `q`-tuple of the last `q`
coordinates of `z`. -/
theorem thetaIdx_init (p q : ℕ) (j : Fin p) (z : Fin (p + q) → ℝ) :
    Fin.init (z ∘ thetaIdx p q j) = fun i : Fin q => z (Fin.natAdd p i) := by
  funext i
  rw [show Fin.init (z ∘ thetaIdx p q j) i = (z ∘ thetaIdx p q j) (Fin.castSucc i) from rfl,
    Function.comp_apply, thetaIdx_castSucc]

/-- The θ-graph is the intersection of the `p` coordinate conditions, each of which is the
preimage of one graph under the coordinate insertion `thetaIdx`. -/
theorem thetaGraph_eq (p q : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)) :
    {z : Fin (p + q) → ℝ | ∀ j : Fin p,
        z (Fin.castAdd q j) = θ (fun i : Fin q => z (Fin.natAdd p i)) j}
      = ⋂ j : Fin p, Work.WilG5.coordPre (thetaIdx p q j)
          (graphOf (fun μ : Fin q → ℝ => θ μ j)) := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Work.WilG5.coordPre, Function.comp_apply,
    graphOf]
  constructor
  · intro h j
    rw [thetaIdx_last, thetaIdx_init]
    exact h j
  · intro h j
    have := h j
    rw [thetaIdx_last, thetaIdx_init] at this
    exact this

theorem ThetaGraphMem (S : WilkiesDesign.SOMin) (p q F2 : ℕ) :
    ∃ (F : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)),
        (∀ j : Fin p, WilkiesDesign.graphOf (fun μ : Fin q → ℝ => θ μ j) ∈ S.Ω F2 D (q + 1)) →
        {z : Fin (p + q) → ℝ | ∀ j : Fin p,
            z (Fin.castAdd q j) = θ (fun i : Fin q => z (Fin.natAdd p i)) j}
          ∈ S.Ω F (b.eval D) (p + q) := by
  refine ⟨(F2 + 64 * ((p + q) + (q + 1)) + 64) + 1,
    Polynomial.C (p * (32 * ((p + q) + (q + 1)) + 32)) + Polynomial.C p * Polynomial.X, ?_⟩
  intro D θ hθ
  -- each coordinate condition: `coordPre_mem` applied to the corresponding graph
  have hC : ∀ j : Fin p, Work.WilG5.coordPre (thetaIdx p q j)
        (graphOf (fun μ : Fin q → ℝ => θ μ j))
      ∈ S.Ω (F2 + 64 * ((p + q) + (q + 1)) + 64)
          (D + 32 * ((p + q) + (q + 1)) + 32) (p + q) :=
    fun j => Work.WilG5.coordPre_mem (S := S) (ι := thetaIdx p q j) (hθ j)
  -- the intersection of the `p` conditions
  have hmain := S.inter (fun _ : Fin p => D + 32 * ((p + q) + (q + 1)) + 32)
    (fun j : Fin p => Work.WilG5.coordPre (thetaIdx p q j)
      (graphOf (fun μ : Fin q → ℝ => θ μ j))) hC
  -- the degree of the intersection is the linear polynomial `p·(D + 32·((p+q)+(q+1)) + 32)`
  have hb : (Polynomial.C (p * (32 * ((p + q) + (q + 1)) + 32))
        + Polynomial.C p * Polynomial.X).eval D
      = ∑ _ : Fin p, (D + 32 * ((p + q) + (q + 1)) + 32) := by
    simp [Finset.sum_const, Finset.card_univ]
    ring
  rw [hb, thetaGraph_eq]
  exact hmain

end Work.WilG4c
