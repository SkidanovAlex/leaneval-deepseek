import Submission.Work.Diff.EXT.ConnCov.moving_honest_ric_tower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `k`-th order Shi-type bound for the *honest* tower of the Ricci tensor

This module proves `Work.Diff.EXT.ConnCov.RicTr.honestRicTowerH`, the uniform bound on the honest
towers `∇^{G t, j}Ric` (`j ≤ k+1`) along a Ricci flow on the collapsed slab `[T/2, T)`, with the
`∏ᵢ(1+√⟨vᵢ,vᵢ⟩)` shape in the direction slots.

## Route

The whole analytic and linear-algebraic content is in
`Work.Diff.EXT.ConnCov.moving_honest_ric_tower_aux` (proved, sorry-free, axiom-clean), which takes
exactly two inputs:

* `hcan : FrameCorrZero` — the frame-derivative cancellation
  `Σ_m ∇^jRm(v, ∇_{v₀}e_m, a, e_m, b) + Σ_m ∇^jRm(v, e_m, a, ∇_{v₀}e_m, b) = 0`
  for a `g`-orthonormal frame field `e` near the base point (used for the trace identity
  `∇^{g,j}Ric(v,a,b) = Σ_m ∇^{g,j}Rm(v, e_m, a, e_m, b)`);
* `hbridge` — the identification of the honest `Op3`-tower of `baseRic g` (two value slots plus a
  dummy third one, recursion `hstep = step + drop`) with the honest `(0,2)`-tower
  `tower2 (lcOf g) (baseRic2 g)` of the Ricci tensor.

Here `hcan` is *hypotheses* of the target (the requester's input), and `hbridge` is provided by the
short induction `htower_baseRic_eq_tower2` below: the dummy third value slot makes `baseRic g`
third-slot independent (`cIndep_baseRic`), so in the honest recursion formula `hstep_apply` the
third-slot correction is exactly the `drop` shift, and the two recursions coincide.

The estimate itself (the evaluation bound `covKRmExt_eval_bound` on the orthonormal frame
`onFrame (G t) x`, together with Shi's estimate `hShi`) is then the body of
`moving_honest_ric_tower_aux`.
-/

namespace Work.Diff.EXT.ConnCov.RicTr

/-- **The honest `Op3`-tower of `baseRic g` is the honest `(0,2)`-tower of `baseRic2 g`.**

`baseRic g` ignores its third value slot (`cIndep_baseRic`), and on third-slot-independent objects
the honest recursion `hstep = step + drop` (`hstep_apply`) coincides with the `(0,2)`-recursion
`step2`.  Induction on the level. -/
theorem htower_baseRic_eq_tower2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) :
    ∀ (k : ℕ) (v : Fin k → (Π y : M, TangentSpace I y))
      (A B C : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) k v A B C x
      = Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) k v A B x := by
  intro k
  induction k with
  | zero =>
    intro v A B C x
    rfl
  | succ k ih =>
    intro v A B C x
    rw [Work.Diff.EXT.ConnCov.htower_succ,
      Work.Diff.EXT.ConnCov.hstep_apply (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.cIndep_htower (Submission.Diff.lcOf g)
          (Work.Diff.EXT.ConnCov.cIndep_baseRic g) k) v A B C x,
      Work.Diff.EXT.ConnCov.tower2_succ, Work.Diff.EXT.ConnCov.step2_apply]
    have hfun : (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf g)
          (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) k
          (fun i : Fin k => v i.succ) A B C)
        = (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf g)
          (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) k
          (fun i : Fin k => v i.succ) A B) :=
      funext (fun y => ih (fun i : Fin k => v i.succ) A B C y)
    rw [hfun]
    simp only [ih]

theorem honestRicTowerH
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hcan : ∀ (g : Submission.Diff.SMet I M) (x : M) (j : ℕ)
      (v : Fin j → (Π y : M, TangentSpace I y)) (v0 A B : Π y : M, TangentSpace I y)
      (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M v0 →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      (∀ m, Work.Diff.EXT.ATower.SmE I M (W m)) →
      (∀ᶠ y in nhds x, Submission.Diff.IsONFrame g y (fun m => W m y)) →
      (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (Work.Diff.EXT.dirF g (W m) v0) A (W m) B x))
        + (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (W m) A (Work.Diff.EXT.dirF g (W m) v0) B x)) = 0)
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) (k : ℕ) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ j : ℕ, j ≤ k + 1 → ∀ x : M,
      ∀ (v : Fin j → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G t))
              (Work.Diff.EXT.ConnCov.baseRic (G t)) j) x v a b c|
          ≤ Ck * (Finset.univ.prod (fun i : Fin j => (1 + Real.sqrt ((G t).inner x (v i) (v i)))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
  exact Work.Diff.EXT.ConnCov.moving_honest_ric_tower_aux (I := I) (M := M)
    (hcan := hcan)
    (hbridge := fun g j v A B Cc x => htower_baseRic_eq_tower2 g j v A B Cc x)
    hLC G T C hT hC hflow hbound hmet hShi k

end Work.Diff.EXT.ConnCov.RicTr
