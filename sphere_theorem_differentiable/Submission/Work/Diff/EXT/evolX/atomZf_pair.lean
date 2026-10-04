import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pairing identity of the frame-expanded curvature vector `Zf`

`Work.Diff.EXT.evolX.Zf g W l Ψ` is the level-`l` curvature vector expanded in the frame field `W`.
This module proves its defining property (`atomZf_pair`):

`⟪Zf g W l Ψ, D⟫ x = ckt g l (snoc Ψ D) x`

whenever `W` is `g`-orthonormal near `x`: the pairing of the frame expansion with a smooth field `D`
is the level-`l` tower `∇^l Rm` evaluated on the tuple `Ψ` extended by `D` in the last slot.

The proof is value-level.  `ckt` at a point depends only on the *values* of its tuple at that point
(`Work.Diff.EXT.ckt_val_dep_all`), so the identity is reduced to the evaluation
`Kpt g x l = ckt g l (smoothExt x ·) x`, which is ℝ-linear in each slot
(`Work.Diff.EXT.Kpt_add`, `Work.Diff.EXT.Kpt_smul`): expanding `D x` in the orthonormal frame
(`Work.EXT.sum_inner_smul_eq_self_of_isONFrame`) turns the frame sum `∑ i cᵢ • Wᵢ x` into the single
evaluation on `D x`.

`LCSmooth I M` — needed by the induction statements of `ckt` and unavailable from
`Work.Diff.T.lc_smooth` in the absence of `[I.Boundaryless]` — is supplied here by the boundary-free
`Work.EXT.lcSmooth_noBoundary`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **Value-level linearity of `Kpt` in one slot, as a finite sum.**  This is the boundary-free copy
of `Work.Diff.EXT.Kpt_sum_slot` (which carries `[I.Boundaryless] [CompactSpace M]` hypotheses that
are not needed for the statement). -/
lemma kpt_sum_slotE (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (w : Fin (k + 4) → TangentSpace I x)
    (s : Fin (k + 4)) (c : ι → ℝ) (Y : ι → TangentSpace I x) :
    Work.Diff.EXT.Kpt g x k (Function.update w s (∑ i, c i • Y i))
      = ∑ i, c i • Work.Diff.EXT.Kpt g x k (Function.update w s (Y i)) := by
  classical
  have key : ∀ t : Finset ι, Work.Diff.EXT.Kpt g x k (Function.update w s (∑ i ∈ t, c i • Y i))
      = ∑ i ∈ t, c i • Work.Diff.EXT.Kpt g x k (Function.update w s (Y i)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have h := Work.Diff.EXT.Kpt_smul hLC g x k w s (0 : ℝ) (w s)
      simpa using h
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Work.Diff.EXT.Kpt_add hLC g x k w s (c a • Y a) (∑ i ∈ t, c i • Y i),
        Work.Diff.EXT.Kpt_smul hLC g x k w s (c a) (Y a), ih]
  simpa using key Finset.univ

/-- **Value-level evaluation of the tower.**  Boundary-free copy of `Work.Diff.EXT.ckt_eq_Kpt`: at a
point, `ckt` only depends on the values of its tuple, i.e. it is the evaluation of `Kpt`. -/
lemma ckt_eq_KptE (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (k : ℕ) (x : M)
    {T : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hT : ∀ s, Work.Diff.EXT.evolX.SmTf (T s)) :
    Work.Diff.EXT.ckt g k T x = Work.Diff.EXT.Kpt g x k (fun s => T s x) := by
  simpa only [Work.Diff.EXT.Kpt] using
    (Work.Diff.EXT.ckt_val_dep_all hLC g k x hT
      (fun s => Work.Diff.GE.smoothExt_cmdiff x (T s x))
      (fun s => by rw [Work.Diff.GE.smoothExt_apply]))

theorem atomZf_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (hON : Work.Diff.EXT.evolX.ONFrameAt (I := I) (M := M) g x W)
    (l : ℕ) (Ψ : Fin (l + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hΨ : ∀ r, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (Ψ r))
    (D : Work.Diff.EXT.TField (I := I) (M := M))
    (hD : Work.Diff.EXT.evolX.SmTf (I := I) (M := M) D) :
    g.inner x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x) (D x)
      = Work.Diff.EXT.ckt g l (Fin.snoc Ψ D) x := by
  classical
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have hONx : Submission.Diff.IsONFrame g x (fun i => W i x) := hON.self_of_nhds
  -- every slot of `Fin.snoc Ψ X` is a smooth field whenever `X` is
  have hsnoc : ∀ (X : Work.Diff.EXT.TField (I := I) (M := M)), Work.Diff.EXT.evolX.SmTf X →
      ∀ s : Fin (l + 4), Work.Diff.EXT.evolX.SmTf
        ((Fin.snoc Ψ X : Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M)) s) := by
    intro X hX s
    by_cases hs : s = Fin.last (l + 3)
    · subst hs; rw [Fin.snoc_last]; exact hX
    · obtain ⟨t, rfl⟩ := Fin.eq_castSucc_of_ne_last hs
      rw [Fin.snoc_castSucc]; exact hΨ t
  -- the tuple of *values* at `x` of `Fin.snoc Ψ D`
  set w : Fin (l + 4) → TangentSpace I x :=
    fun s => (Fin.snoc Ψ D : Fin (l + 4) → Work.Diff.EXT.TField (I := I) (M := M)) s x with hw
  -- expansion of `D x` in the orthonormal frame
  have hDexp : D x = ∑ i, g.inner x (D x) (W i x) • W i x :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x (fun i => W i x) hONx (D x)).symm
  have hlast : w (Fin.last (l + 3)) = ∑ i, g.inner x (D x) (W i x) • W i x := by
    rw [hw]; simp only [Fin.snoc_last]; exact hDexp
  have hR1 : Work.Diff.EXT.ckt g l (Fin.snoc Ψ D) x = Work.Diff.EXT.Kpt g x l w := by
    rw [ckt_eq_KptE hLC g l x (hsnoc D hD), hw]
  have hR2 : Work.Diff.EXT.Kpt g x l w
      = Work.Diff.EXT.Kpt g x l (Function.update w (Fin.last (l + 3))
          (∑ i, g.inner x (D x) (W i x) • W i x)) := by
    rw [← hlast, Function.update_eq_self]
  have hR3 : Work.Diff.EXT.Kpt g x l (Function.update w (Fin.last (l + 3))
        (∑ i, g.inner x (D x) (W i x) • W i x))
      = ∑ i, g.inner x (D x) (W i x) * Work.Diff.EXT.Kpt g x l
          (Function.update w (Fin.last (l + 3)) (W i x)) := by
    simpa only [smul_eq_mul] using kpt_sum_slotE hLC g x l w (Fin.last (l + 3))
      (fun i => g.inner x (D x) (W i x)) (fun i => W i x)
  have hR4 : ∀ i, Work.Diff.EXT.Kpt g x l (Function.update w (Fin.last (l + 3)) (W i x))
      = Work.Diff.EXT.ckt g l (Fin.snoc Ψ (W i)) x := by
    intro i
    rw [ckt_eq_KptE hLC g l x (hsnoc (W i) (hW i))]
    congr 1
    funext s
    by_cases hs : s = Fin.last (l + 3)
    · subst hs; rw [Function.update_self, Fin.snoc_last]
    · obtain ⟨t, ht⟩ := Fin.eq_castSucc_of_ne_last hs
      rw [← ht, Function.update_of_ne (by rw [ht]; exact hs), Fin.snoc_castSucc, hw]
      simp only [Fin.snoc_castSucc]
  have hLHS : g.inner x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x) (D x)
      = ∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g l (Fin.snoc Ψ (W i)) x) * (g.inner x (W i x) (D x)) := by
    simp only [Work.Diff.EXT.evolX.Zf, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  have hsym : ∀ i : Fin (Module.finrank ℝ E), g.inner x (D x) (W i x) = g.inner x (W i x) (D x) :=
    fun i => g.symm x (D x) (W i x)
  calc g.inner x (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ x) (D x)
      = ∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g l (Fin.snoc Ψ (W i)) x) * (g.inner x (W i x) (D x)) := hLHS
    _ = ∑ i : Fin (Module.finrank ℝ E),
          (g.inner x (W i x) (D x)) * (Work.Diff.EXT.ckt g l (Fin.snoc Ψ (W i)) x) := by
          refine Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ i : Fin (Module.finrank ℝ E),
          (g.inner x (D x) (W i x)) * (Work.Diff.EXT.ckt g l (Fin.snoc Ψ (W i)) x) := by
          refine Finset.sum_congr rfl (fun i _ => by rw [hsym i])
    _ = ∑ i : Fin (Module.finrank ℝ E),
          (g.inner x (D x) (W i x)) *
            (Work.Diff.EXT.Kpt g x l (Function.update w (Fin.last (l + 3)) (W i x))) := by
          refine Finset.sum_congr rfl (fun i _ => by rw [← hR4 i])
    _ = Work.Diff.EXT.Kpt g x l (Function.update w (Fin.last (l + 3))
          (∑ i, g.inner x (D x) (W i x) • W i x)) := hR3.symm
    _ = Work.Diff.EXT.Kpt g x l w := hR2.symm
    _ = Work.Diff.EXT.ckt g l (Fin.snoc Ψ D) x := hR1.symm

end Work.Diff.EXT.evolX
