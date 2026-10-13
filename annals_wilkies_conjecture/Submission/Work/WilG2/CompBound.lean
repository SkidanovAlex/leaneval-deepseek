/-
  WilG2 : the Faa di Bruno bound for the jet norm, in the `OrderedFinpartition` form.

  `iteratedFDeriv_comp` (Mathlib) writes the `n`-th derivative of a composition as the
  Taylor composition `(ftaylorSeries g (F x)).taylorComp (ftaylorSeries F x) n`, which is a
  sum over ordered set partitions of `Fin n`.  Mathlib bounds the norm of each term; summing
  gives the bound used to prove subcompositionality.
-/
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG2.Tnorm
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

set_option autoImplicit false
noncomputable section
open Classical Finset
namespace WilkiesDesign.CG
open WilkiesConjecture WilkiesDesign FirstOrder Language

/-- Norm bound on one Taylor composition coefficient, in terms of the coefficient norms. -/
theorem norm_taylorComp_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (q : FormalMultilinearSeries ℝ V ℝ) (p : FormalMultilinearSeries ℝ E V) (n : ℕ) :
    ‖(q.taylorComp p) n‖ ≤
      ∑ c : OrderedFinpartition n, ‖q c.length‖ * ∏ i : Fin c.length, ‖p (c.partSize i)‖ := by
  rw [FormalMultilinearSeries.taylorComp]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have h := OrderedFinpartition.norm_compAlongOrderedFinpartition_le c (q c.length)
    (fun i => p (c.partSize i))
  simpa [FormalMultilinearSeries.compAlongOrderedFinpartition] using h

/-- **The Faa di Bruno bound (BNZ Lemma 4.2(ii), local form).**
The `n`-th derivative of `g ∘ F` at `x` is bounded by the sum over ordered set partitions
of `Fin n` of the corresponding products of coefficient norms. -/
theorem norm_iteratedFDeriv_comp_le_ofp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (r n : ℕ) (hn : n ≤ r) (F : E → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (x : E)
    (hF : ContDiffAt ℝ r F x) (hg : ContDiffAt ℝ r g (F x)) :
    ‖iteratedFDeriv ℝ n (g ∘ F) x‖ ≤
      ∑ c : OrderedFinpartition n, ‖iteratedFDeriv ℝ c.length g (F x)‖ *
        ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) F x‖ := by
  have hcomp := iteratedFDeriv_comp (𝕜 := ℝ) (f := F) (g := g) (x := x)
    (n := (r : WithTop ℕ∞)) hg hF (i := n) (by exact_mod_cast hn)
  rw [hcomp]
  exact norm_taylorComp_le (ftaylorSeries ℝ g (F x)) (ftaylorSeries ℝ F x) n

end WilkiesDesign.CG
