import Mathlib
import Submission.Work.Diff.EXT.evolX.compLadderDefs
import Submission.Work.Diff.EXT.evolX.ladderAtoms
import Submission.Work.Diff.EXT.evolX.atomZf_pair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pairing identity of the frame-expanded curvature vector `Zsk`

`Work.Diff.EXT.evolX.Zsk g W k s Ψ` is the level-`k` curvature vector expanded in the frame field
`W`, with the insertion of the extra slot at the position `s`:

`Zsk g W k s Ψ = ∑ m, (ckt g k (insert (W m) at slot s into Ψ ∘ skipMap k s)) • W m`.

This module proves its defining property (`ZskPair`):

`⟪Zsk g W k s Ψ, D⟫ x = ckt g k (insert D at slot s into Ψ ∘ skipMap k s) x`

whenever `W` is `g`-orthonormal near `x`.  This is the general-slot version of the last-slot
identity `Work.Diff.EXT.evolX.atomZf_pair` (which treats `Zf`, the insertion at the last slot).

The proof is a verbatim replay of the proof of `atomZf_pair`: `ckt` at a point depends only on the
*values* of its tuple at that point (`Work.Diff.EXT.ckt_val_dep_all`), and `Kpt` (the evaluation of
`∇^k Rm`) is ℝ-linear in each slot (`Work.Diff.EXT.Kpt_add`, `Work.Diff.EXT.Kpt_smul`), so
expanding `D x` in the orthonormal frame turns the frame sum `∑ i cᵢ • Wᵢ x` into the single
evaluation on `D x`.  Nothing depends on which slot is the inserted one.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

theorem ZskPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (hON : Work.Diff.EXT.evolX.ONFrameAt (I := I) (M := M) g x W)
    (k : ℕ) (s : Fin (k + 4))
    (Ψ : Fin (k + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hΨ : ∀ r, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (Ψ r))
    (D : Work.Diff.EXT.TField (I := I) (M := M))
    (hD : Work.Diff.EXT.evolX.SmTf (I := I) (M := M) D) :
    g.inner x (Work.Diff.EXT.evolX.Zsk (I := I) (M := M) g W k s Ψ x) (D x)
      = Work.Diff.EXT.ckt g k
          (Function.update (fun i : Fin (k + 4) =>
            Ψ (Work.Diff.EXT.evolX.skipMap k s i)) s D) x := by
  classical
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have hONx : Submission.Diff.IsONFrame g x (fun i => W i x) := hON.self_of_nhds
  -- smoothness of every slot of the tuple with `X` inserted at the slot `s`
  have hsupd : ∀ (X : Work.Diff.EXT.TField (I := I) (M := M)), SmTf X →
      ∀ q : Fin (k + 4), SmTf
        ((Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s X) q) := by
    intro X hX q
    by_cases hq : q = s
    · subst hq; rw [Function.update_self]; exact hX
    · rw [Function.update_of_ne hq]; exact hΨ (skipMap k s q)
  -- the tuple of *values* at `x` of the tuple with `D` inserted at the slot `s`
  set w : Fin (k + 4) → TangentSpace I x :=
    fun q => (Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s D) q x with hw
  have hws : w s = D x := by rw [hw]; simp
  -- expansion of `D x` in the orthonormal frame
  have hDexp : D x = ∑ i, g.inner x (D x) (W i x) • W i x :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x (fun i => W i x) hONx (D x)).symm
  -- the four rewrites of the computation
  have hR1 : Work.Diff.EXT.ckt g k
      (Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s D) x
      = Work.Diff.EXT.Kpt g x k w := by
    rw [ckt_eq_KptE hLC g k x (hsupd D hD), hw]
  have hR2 : Work.Diff.EXT.Kpt g x k w
      = Work.Diff.EXT.Kpt g x k (Function.update w s (∑ i, g.inner x (D x) (W i x) • W i x)) := by
    have h : Function.update w s (∑ i, g.inner x (D x) (W i x) • W i x) = w := by
      funext q
      by_cases hq : q = s
      · subst hq; rw [Function.update_self]; exact (hws.trans hDexp).symm
      · rw [Function.update_of_ne hq]
    rw [h]
  have hR3 : Work.Diff.EXT.Kpt g x k (Function.update w s (∑ i, g.inner x (D x) (W i x) • W i x))
      = ∑ i : Fin (Module.finrank ℝ E),
          g.inner x (D x) (W i x) * Work.Diff.EXT.Kpt g x k (Function.update w s (W i x)) := by
    simpa only [smul_eq_mul] using
      kpt_sum_slotE hLC g x k w s (fun i => g.inner x (D x) (W i x)) (fun i => W i x)
  have hR4 : ∀ i : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.Kpt g x k (Function.update w s (W i x))
      = Work.Diff.EXT.ckt g k
          (Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s (W i)) x := by
    intro i
    rw [ckt_eq_KptE hLC g k x (hsupd (W i) (hW i))]
    congr 1
    funext q
    by_cases hq : q = s
    · subst hq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hq]; simp only [hw, Function.update_of_ne hq]
  have hLHS : g.inner x (Work.Diff.EXT.evolX.Zsk (I := I) (M := M) g W k s Ψ x) (D x)
      = ∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g k
              (Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s (W i)) x)
            * (g.inner x (W i x) (D x)) := by
    simp only [Work.Diff.EXT.evolX.Zsk, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  have hsym : ∀ i : Fin (Module.finrank ℝ E),
      g.inner x (D x) (W i x) = g.inner x (W i x) (D x) :=
    fun i => g.symm x (D x) (W i x)
  calc g.inner x (Work.Diff.EXT.evolX.Zsk (I := I) (M := M) g W k s Ψ x) (D x)
      = ∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g k
              (Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s (W i)) x)
            * (g.inner x (W i x) (D x)) := hLHS
    _ = ∑ i : Fin (Module.finrank ℝ E),
          (g.inner x (W i x) (D x)) *
            (Work.Diff.EXT.ckt g k
              (Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s (W i)) x) := by
          refine Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ i : Fin (Module.finrank ℝ E),
          (g.inner x (D x) (W i x)) *
            (Work.Diff.EXT.ckt g k
              (Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s (W i)) x) := by
          refine Finset.sum_congr rfl (fun i _ => by rw [hsym i])
    _ = ∑ i : Fin (Module.finrank ℝ E),
          (g.inner x (D x) (W i x)) *
            (Work.Diff.EXT.Kpt g x k (Function.update w s (W i x))) := by
          refine Finset.sum_congr rfl (fun i _ => by rw [← hR4 i])
    _ = Work.Diff.EXT.Kpt g x k (Function.update w s (∑ i, g.inner x (D x) (W i x) • W i x)) :=
          hR3.symm
    _ = Work.Diff.EXT.Kpt g x k w := hR2.symm
    _ = Work.Diff.EXT.ckt g k
          (Function.update (fun j : Fin (k + 4) => Ψ (skipMap k s j)) s D) x := hR1.symm

end Work.Diff.EXT.evolX
