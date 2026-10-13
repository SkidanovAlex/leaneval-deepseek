import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-!
## Coordinate graph membership

Given an `Ω`-set `G ⊆ ℝ^{p+q}` that is the *coordinate graph* of a function
`f : ℝ^p → ℝ^q` (the first `p` coordinates form the input, the last `q` the output), we show
that each single coordinate graph `graphOf (fun l => f l j) ⊆ ℝ^{p+1}` is again an `Ω`-set,
with format and degree only additively larger.

The mechanism is `Work.WilG5.coordImage_mem`: the graph of `f · j` is the image of `G` under
the coordinate selection `ι : Fin (p+1) → Fin (p+q)` that keeps the first `p` coordinates and
the `j`-th output coordinate, and images under coordinate selections preserve `Ω`-membership
with explicit bounds `(F + 64*(N+m) + 64, D + 32*(N+m) + 32)`.
-/

/-- Selection of `p + 1` coordinates out of `p + q`: the first `p` coordinates, together with
the `j`-th of the last `q`. -/
def coordSel {p q : ℕ} (j : Fin q) : Fin (p + 1) → Fin (p + q) :=
  fun i => if h : (i : ℕ) < p then Fin.castAdd q ⟨i, h⟩ else Fin.natAdd p j

@[simp] theorem coordSel_castSucc {p q : ℕ} (j : Fin q) (i : Fin p) :
    coordSel j (Fin.castSucc i) = Fin.castAdd q i := by
  unfold coordSel
  rw [dite_eq_left (by simp)]
  congr 1

@[simp] theorem coordSel_last {p q : ℕ} (j : Fin q) :
    coordSel j (Fin.last p) = Fin.natAdd p j := by
  unfold coordSel
  rw [dite_eq_right (by simp)]

/-- The image of the coordinate graph of `f` under the coordinate selection is the graph of
the `j`-th coordinate function `f · j`. -/
theorem coordImage_coordSel (p q : ℕ) (f : (Fin p → ℝ) → (Fin q → ℝ)) (j : Fin q) :
    Work.WilG5.coordImage (coordSel j)
      {z : Fin (p + q) → ℝ | ∀ j : Fin q,
          z (Fin.natAdd p j) = f (fun i : Fin p => z (Fin.castAdd q i)) j}
      = WilkiesDesign.graphOf (fun l : Fin p → ℝ => f l j) := by
  ext u
  constructor
  · rintro ⟨z, hz, hzu⟩
    show u (Fin.last p) = f (Fin.init u) j
    rw [← hzu]
    rw [Function.comp_apply, coordSel_last]
    have hinit : Fin.init (z ∘ coordSel j) = fun i : Fin p => z (Fin.castAdd q i) := by
      funext i
      show (z ∘ coordSel j) (Fin.castSucc i) = z (Fin.castAdd q i)
      rw [Function.comp_apply, coordSel_castSucc]
    rw [hinit]
    exact hz j
  · intro hu
    refine ⟨Fin.append (Fin.init u) (fun j' : Fin q => f (Fin.init u) j'), ?_, ?_⟩
    · intro j'
      show Fin.append (Fin.init u) (fun j' : Fin q => f (Fin.init u) j') (Fin.natAdd p j')
        = f (fun i : Fin p =>
            Fin.append (Fin.init u) (fun j' : Fin q => f (Fin.init u) j') (Fin.castAdd q i)) j'
      simp only [Fin.append_right, Fin.append_left]
    · funext i
      show Fin.append (Fin.init u) (fun j' : Fin q => f (Fin.init u) j') (coordSel j i) = u i
      refine Fin.lastCases ?_ ?_ i
      · rw [coordSel_last]
        simp only [Fin.append_right]
        exact hu.symm
      · intro i0
        rw [coordSel_castSucc]
        simp only [Fin.append_left]
        rfl

/-- **Coordinate graphs of a coordinate graph.** If the coordinate graph of
`f : ℝ^p → ℝ^q` is `Ω`-definable with format `a'` and degree `b'.eval D`, then for every
output coordinate `j` the graph of `l ↦ f l j` is `Ω`-definable with format `a' + A` and
degree `(b' + B).eval D`, where `A` and `B` depend only on `p` and `q`. -/
theorem CoordGraphMem (S : WilkiesDesign.SOMin) (p q : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (D a' : ℕ) (b' : Polynomial ℕ) (f : (Fin p → ℝ) → (Fin q → ℝ)),
        {z : Fin (p + q) → ℝ | ∀ j : Fin q,
            z (Fin.natAdd p j) = f (fun i : Fin p => z (Fin.castAdd q i)) j} ∈ S.Ω a' (b'.eval D) (p + q) →
        ∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => f l j) ∈
          S.Ω (a' + A) ((b' + B).eval D) (p + 1) := by
  refine ⟨64 * ((p + q) + (p + 1)) + 64,
    Polynomial.C (32 * ((p + q) + (p + 1)) + 32), ?_⟩
  intro D a' b' f hG j
  have hmem := Work.WilG5.coordImage_mem (S := S) (ι := coordSel j) hG
  rw [coordImage_coordSel p q f j] at hmem
  rw [show a' + (64 * ((p + q) + (p + 1)) + 64)
        = a' + 64 * ((p + q) + (p + 1)) + 64 from by omega,
      show (b' + Polynomial.C (32 * ((p + q) + (p + 1)) + 32)).eval D
        = b'.eval D + 32 * ((p + q) + (p + 1)) + 32 from by
          rw [Polynomial.eval_add, Polynomial.eval_C]
          omega]
  exact hmem

end Work.WilG4c
