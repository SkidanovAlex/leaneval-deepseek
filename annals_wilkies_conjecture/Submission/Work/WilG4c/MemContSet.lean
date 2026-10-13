/-
  WilG4c / `MemContSet` — the value condition (C0) of the punctured-limit criterion.

  `contSet p n f = projLast (LimeqP p n (famGraph f) ∩ famGraph f)` is the set of points
  `w = (l,u)` of `ℝ^{p + (n+1)}` for which the `F`-values along the *punctured* cube over the
  parameter `l` tend to `F w`, and `(w, F w)` lies on the graph of `famFunHat f`.  The lemma
  says that this is exactly continuity of the fibre `y ↦ f l y` at the cube point `u`: the
  punctured limit is the full limit (which exists and equals the value), and the graph
  condition is satisfied at the last coordinate `s := f l u`.

  `LimeqP` is stated with the punctured condition `x ≠ cubePt ...`, which is *weaker* than
  continuity, so the content is that continuity of the fibre together with the graph
  membership (at the correct value!) is enough.
-/
import Mathlib
import Submission.Work.WilG4c.AlSliceBase

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

open WilkiesDesign

/-- `famFunHat f` composed with the affine inclusion `Fin.append l` of the cube coordinates is
the fibre `f l`. -/
private lemma famFunHat_append_local {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (v : Fin (n + 1) → ℝ) :
    Work.WilkG4c.famFunHat f (Fin.append l v) = f l v := by
  simp only [Work.WilkG4c.famFunHat, Fin.append_left, Fin.append_right]

theorem MemContSet {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (w : Fin (p + (n + 1)) → ℝ)
    (h : ContinuousAt (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt w) y)
      (Work.WilkG4c.cubePt w)) :
    w ∈ Work.WilkG4c.contSet p n f := by
  unfold Work.WilkG4c.contSet WilkiesDesign.projLast
  simp only [Set.mem_ofPred_eq]
  -- The witness for the value coordinate: the value of the fibre at the cube point.
  set s : ℝ := f (Work.WilkG4c.parPt w) (Work.WilkG4c.cubePt w) with hs
  refine ⟨s, ?_, ?_⟩
  · -- `Fin.snoc w s ∈ LimeqP p n (famGraph f)`: the punctured limit condition.
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.continuousAt_iff.mp h) ε hε
    refine ⟨δ, hδ, fun x hx hd v hv => ?_⟩
    -- Strip the `snoc`/`init` bookkeeping.
    simp only [Fin.init_snoc, Fin.snoc_last] at hx hd hv ⊢
    -- Membership in the graph of `famFunHat f` forces `v` to be the fibre value at `x`.
    rw [Work.WilkG4c.famGraph_eq_graphOf_famFunHat] at hv
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hv
    rw [famFunHat_append_local f (Work.WilkG4c.parPt w) x] at hv
    rw [hv]
    -- The strict box condition is the sup-metric ball, so continuity applies.
    have hdist : dist x (Work.WilkG4c.cubePt w) < δ := by
      rw [dist_pi_lt_iff hδ]
      intro j
      rw [Real.dist_eq]
      exact hd j
    exact le_of_lt (by simpa [hs, Real.dist_eq] using hδ' hdist)
  · -- `Fin.snoc w s ∈ famGraph f`: the value indeed is `famFunHat f w`.
    rw [Work.WilkG4c.famGraph_eq_graphOf_famFunHat]
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    rw [hs]
    exact (Work.WilkG4c.famFunHat_eq_parPt_cubePt f w).symm

end Work.WilG4c
