import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.GraphOfComp

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0

/-- The coordinate substitution `σ : Fin (p+n+1) → Fin (p+(n+1)+1)` that skips the
*second-to-last* coordinate: it is the identity on the first `p+n` coordinates and sends the
last one to the very last one.  Composing with `σ` forgets the dummy coordinate sitting
between the `p+n` "input" coordinates and the value coordinate. -/
def padSig (p n : ℕ) : Fin (p + n + 1) → Fin (p + (n + 1) + 1) :=
  Fin.snoc (fun k : Fin (p + n) => Fin.castLE (by omega) k) (Fin.last (p + (n + 1)))

@[simp] theorem padSig_castSucc (p n : ℕ) (i : Fin (p + n)) :
    padSig p n (Fin.castSucc i) = Fin.castLE (by omega) i := by
  simp [padSig, Fin.snoc_castSucc]

@[simp] theorem padSig_last (p n : ℕ) :
    padSig p n (Fin.last (p + n)) = Fin.last (p + (n + 1)) := by
  simp [padSig, Fin.snoc_last]

/-- The graph of `(l, t) ↦ g l (Fin.init t)` is the pullback, along `padSig`, of the graph of
`g`: the only difference is that the `(n+1)`-st fibre coordinate is a dummy (the value
coordinate moves from position `p+n` to position `p+n+1`). -/
theorem famGraph_padSig_eq (p n : ℕ) (g : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) :
    famGraph (fun l (t : Fin (n + 1) → ℝ) => g l (Fin.init t)) =
      {x : Fin (p + (n + 1) + 1) → ℝ | x ∘ padSig p n ∈ famGraph g} := by
  ext w
  simp only [Set.mem_ofPred_eq, Function.comp_apply, famGraph, graphOf, Fin.init_def]
  simp only [padSig_castSucc, padSig_last]
  constructor <;> intro h <;> rw [h] <;> congr 1

/-- **Padding a family graph by a dummy trailing coordinate.**  If the graph of a family
`g : ℝ^p × ℝ^n → ℝ` (i.e. `famGraph g ⊆ ℝ^{p+n+1}`) is `Ω`-definable at format `F` and degree
`eval ![D,1] b`, then the graph of `(l, t) ↦ g l (Fin.init t)` (the same family on `n+1`
coordinates, ignoring the last one) is `Ω`-definable at format `F + a` and degree
`eval ![D,1] (b + C c)`, with `a, c` independent of `F`, `D`, `b` and of the family. -/
theorem FamGraphPad (S : SOMin) (p n : ℕ) :
    ∃ (a c : ℕ), ∀ (F D : ℕ) (b : MvPolynomial (Fin 2) ℕ)
      (g : (Fin p → ℝ) → (Fin n → ℝ) → ℝ),
      famGraph g ∈ S.Ω F (MvPolynomial.eval ![D, 1] b) (p + n + 1) →
      famGraph (fun l (t : Fin (n + 1) → ℝ) => g l (Fin.init t)) ∈
        S.Ω (F + a) (MvPolynomial.eval ![D, 1] (b + MvPolynomial.C c)) (p + (n + 1) + 1) := by
  refine ⟨2 * ((p + (n + 1) + 1) + (p + n + 1)) + 1, 2, ?_⟩
  intro F D b g hg
  have hmem := GraphComp.subst_mem S (padSig p n) hg
  rw [← famGraph_padSig_eq p n g] at hmem
  have hdeg : MvPolynomial.eval ![D, 1] b + 2
      = MvPolynomial.eval ![D, 1] (b + MvPolynomial.C 2) := by
    rw [map_add, MvPolynomial.eval_C]
  have hfmt : F + 2 * ((p + (n + 1) + 1) + (p + n + 1)) + 1
      = F + (2 * ((p + (n + 1) + 1) + (p + n + 1)) + 1) := by ring
  exact Omega_mono_FD (le_of_eq hfmt) (le_of_eq hdeg) hmem

end Work.WilG4c
