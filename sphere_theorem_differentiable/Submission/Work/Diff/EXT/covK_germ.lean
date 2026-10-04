import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Germ-locality of the Levi-Civita connection

The value of `lcOf g X x` depends only on the germ of `X` at `x` — with *no* differentiability
hypothesis on `X`: `lvOf g` is Mathlib's `leviCivitaConnection`, which is
`if MDiffAt (T% X) x then (Koszul) else 0`, and both branches are germ-determined at `x`. -/

/-- An eventual equality near `x` is an eventual equality near every nearby point. -/
lemma germ_nhds_eventually {α : Type*} [TopologicalSpace α] {x : α} {p q : α → M}
    (h : p =ᶠ[𝓝 x] q) : ∀ᶠ y in 𝓝 x, p =ᶠ[𝓝 y] q := by
  obtain ⟨U, hU, hUU⟩ := Filter.eventually_iff_exists_mem.mp h
  have hx : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact Filter.eventually_iff_exists_mem.mpr
    ⟨interior U, isOpen_interior.mem_nhds hy, fun z hz => hUU z (interior_subset hz)⟩

/-- `lcOf g X x = 0` for a field which is not differentiable at `x` (the "junk" branch of
Mathlib's `leviCivitaAux`). -/
lemma lcOf_eq_zero_of_not_mdiffAt (g : SMet I M) {X : TField (I := I) (M := M)} {x : M}
    (hX : ¬ MDiffAt (T% X) x) : lcOf g X x = 0 := by
  rw [Submission.Diff.lcOf]
  simp only [CovariantDerivative.leviCivitaConnection]
  exact dite_eq_right hX

/-- **Germ-locality of the Levi-Civita connection in the field.** -/
lemma lcOf_congr_germ (g : SMet I M) {X X' : TField (I := I) (M := M)} {x : M}
    (h : X =ᶠ[𝓝 x] X') : lcOf g X x = lcOf g X' x := by
  have hT : T% X =ᶠ[𝓝 x] T% X' := by
    filter_upwards [h] with y hy
    rw [hy]
  by_cases hX : MDiffAt (T% X) x
  · exact Work.Diff.GE.Kato3.lcOf_congr_eventuallyEq g hX (hT.mdifferentiableAt_iff.mp hX) h
  · rw [lcOf_eq_zero_of_not_mdiffAt g hX,
      lcOf_eq_zero_of_not_mdiffAt g (fun hh => hX (hT.mdifferentiableAt_iff.mpr hh))]

/-- **Germ-locality of the corrected field `y ↦ lcOf g X y (Z y)`.** -/
lemma dirF_congr_germ (g : SMet I M) {X X' Z Z' : TField (I := I) (M := M)} {x : M}
    (hX : X =ᶠ[𝓝 x] X') (hZ : Z =ᶠ[𝓝 x] Z') :
    (fun y => lcOf g X y (Z y)) =ᶠ[𝓝 x] (fun y => lcOf g X' y (Z' y)) := by
  filter_upwards [germ_nhds_eventually hX, germ_nhds_eventually hZ] with y hyX hyZ
  rw [lcOf_congr_germ g hyX, hyZ.eq_of_nhds]

/-- Germ-locality of the family obtained by updating one slot of a family of fields. -/
lemma update_congr_germ {ι : Type*} [DecidableEq ι]
    {F G : ι → TField (I := I) (M := M)} {W W' : TField (I := I) (M := M)} {x : M} {i : ι}
    (h : ∀ j, F j =ᶠ[𝓝 x] G j) (hi : W =ᶠ[𝓝 x] W') :
    ∀ j, Function.update F i W j =ᶠ[𝓝 x] Function.update G i W' j := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self, Function.update_self]; exact hi
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact h j

/-! ## Germ-locality of the tower `∇^k Rm` -/

/-- **Germ-locality of `∇^k Rm`, strong form**: the value of `covKRmExt g k V A B C D` at `x`
depends only on the germs at `x` of the `k + 4` fields — with no differentiability hypothesis.

The proof is the induction on `k` following the recursion defining `covKRmExt`.  Both the
`mvfderiv` term and the correction terms are handled by the induction hypothesis applied at the
nearby points `y` (germ hypotheses are hereditary), together with `lcOf_congr_germ`. -/
theorem covKRmExt_congr_germ (g : SMet I M) (k : ℕ) :
    ∀ (V V' : Fin k → TField (I := I) (M := M))
      (A A' B B' C C' D D' : TField (I := I) (M := M)) (x : M),
      (∀ j, V j =ᶠ[𝓝 x] V' j) → A =ᶠ[𝓝 x] A' → B =ᶠ[𝓝 x] B' → C =ᶠ[𝓝 x] C' →
      D =ᶠ[𝓝 x] D' → covKRmExt g k V A B C D x = covKRmExt g k V' A' B' C' D' x := by
  induction k with
  | zero =>
      intro V V' A A' B B' C C' D D' x _ hA hB hC hD
      simp only [covKRmExt]
      rw [hA.eq_of_nhds, hB.eq_of_nhds, hC.eq_of_nhds, hD.eq_of_nhds]
  | succ k ih =>
      intro V V' A A' B B' C C' D D' x hV hA hB hC hD
      -- the germ equalities of the `succ`-shifted families, at `x` and near `x`
      have hVs : ∀ i : Fin k, (fun j : Fin k => V j.succ) i =ᶠ[𝓝 x] (fun j : Fin k => V' j.succ) i :=
        fun i => hV i.succ
      have hVs' : ∀ᶠ y in 𝓝 x,
          ∀ i : Fin k, (fun j : Fin k => V j.succ) i =ᶠ[𝓝 y] (fun j : Fin k => V' j.succ) i :=
        Filter.eventually_all.mpr (fun i => germ_nhds_eventually (hVs i))
      -- the level-`k` functional is germ-determined
      have hF : covKRmExt g k (fun i : Fin k => V i.succ) A B C D
          =ᶠ[𝓝 x] covKRmExt g k (fun i : Fin k => V' i.succ) A' B' C' D' := by
        filter_upwards [hVs', germ_nhds_eventually hA, germ_nhds_eventually hB,
          germ_nhds_eventually hC, germ_nhds_eventually hD] with y hyV hyA hyB hyC hyD
        exact ih (fun i : Fin k => V i.succ) (fun i : Fin k => V' i.succ) A A' B B' C C' D D'
          y hyV hyA hyB hyC hyD
      -- the six terms of the recursion
      have hter : (mvfderiv I (covKRmExt g k (fun i : Fin k => V i.succ) A B C D) x) (V 0 x)
          = (mvfderiv I (covKRmExt g k (fun i : Fin k => V' i.succ) A' B' C' D') x) (V' 0 x) := by
        rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hF, (hV 0).eq_of_nhds]
      have hsum : (∑ i : Fin k, covKRmExt g k
            (Function.update (fun j : Fin k => V j.succ) i
              (fun y => lcOf g (V i.succ) y (V 0 y))) A B C D x)
          = (∑ i : Fin k, covKRmExt g k
            (Function.update (fun j : Fin k => V' j.succ) i
              (fun y => lcOf g (V' i.succ) y (V' 0 y))) A' B' C' D' x) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact ih (Function.update (fun j : Fin k => V j.succ) i
            (fun y => lcOf g (V i.succ) y (V 0 y)))
          (Function.update (fun j : Fin k => V' j.succ) i
            (fun y => lcOf g (V' i.succ) y (V' 0 y)))
          A A' B B' C C' D D' x
          (update_congr_germ hVs (dirF_congr_germ g (hVs i) (hV 0))) hA hB hC hD
      have hcA : covKRmExt g k (fun i : Fin k => V i.succ)
            (fun y => lcOf g A y (V 0 y)) B C D x
          = covKRmExt g k (fun i : Fin k => V' i.succ)
            (fun y => lcOf g A' y (V' 0 y)) B' C' D' x :=
        ih (fun j : Fin k => V j.succ) (fun j : Fin k => V' j.succ)
          (fun y => lcOf g A y (V 0 y)) (fun y => lcOf g A' y (V' 0 y)) B B' C C' D D' x
          hVs (dirF_congr_germ g hA (hV 0)) hB hC hD
      have hcB : covKRmExt g k (fun i : Fin k => V i.succ) A
            (fun y => lcOf g B y (V 0 y)) C D x
          = covKRmExt g k (fun i : Fin k => V' i.succ) A'
            (fun y => lcOf g B' y (V' 0 y)) C' D' x :=
        ih (fun j : Fin k => V j.succ) (fun j : Fin k => V' j.succ) A A'
          (fun y => lcOf g B y (V 0 y)) (fun y => lcOf g B' y (V' 0 y)) C C' D D' x
          hVs hA (dirF_congr_germ g hB (hV 0)) hC hD
      have hcC : covKRmExt g k (fun i : Fin k => V i.succ) A B
            (fun y => lcOf g C y (V 0 y)) D x
          = covKRmExt g k (fun i : Fin k => V' i.succ) A' B'
            (fun y => lcOf g C' y (V' 0 y)) D' x :=
        ih (fun j : Fin k => V j.succ) (fun j : Fin k => V' j.succ) A A' B B'
          (fun y => lcOf g C y (V 0 y)) (fun y => lcOf g C' y (V' 0 y)) D D' x
          hVs hA hB (dirF_congr_germ g hC (hV 0)) hD
      have hcD : covKRmExt g k (fun i : Fin k => V i.succ) A B C
            (fun y => lcOf g D y (V 0 y)) x
          = covKRmExt g k (fun i : Fin k => V' i.succ) A' B' C'
            (fun y => lcOf g D' y (V' 0 y)) x :=
        ih (fun j : Fin k => V j.succ) (fun j : Fin k => V' j.succ) A A' B B' C C'
          (fun y => lcOf g D y (V 0 y)) (fun y => lcOf g D' y (V' 0 y)) x
          hVs hA hB hC (dirF_congr_germ g hD (hV 0))
      simp only [covKRmExt]
      rw [hter, hsum, hcA, hcB, hcC, hcD]

/-- **Germ-locality of `∇^k Rm`** (`KrGerm`, see `Submission/Work/Diff/EXT/curvDefs.lean`): the value
of `covKRmExt g k V A B C D` at `x` depends only on the germs at `x` of the `k + 4` fields (assumed
smooth at `x`).

PROOF: induction on `k` using the recursion defining `covKRmExt` (it unfolds definitionally).
* `k = 0`: `rmP g x (A x) (B x) (C x) (D x)` depends on the *values* at `x` only.
* `k + 1`: use `mvfderiv_congr_of_eventuallyEq` (module `Submission.ChartCurv`) for the `mvfderiv`
  term and germ-locality of `lcOf g X x` in the field `X` for the correction terms.  NOTE: the
  cleanest route is the *stronger* statement "the value at `x` depends only on the germs, with no
  smoothness hypothesis at all", which follows from Mathlib's `leviCitaAux` being
  `if MDiffAt (T% Y) x then … else 0` (both branches germ-determined; Mathlib has
  `leviCivitaAux_congr_of_eventuallyEq`); the version stated here follows immediately. -/
theorem covK_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (k : ℕ) :
    KrGerm (I := I) (M := M) g k := by
  intro V V' A A' B B' C C' D D' x _ _ _ _ _ _ _ _ _ _ hV hA hB hC hD
  exact covKRmExt_congr_germ g k V V' A A' B B' C C' D D' x hV hA hB hC hD

end Work.Diff.EXT
