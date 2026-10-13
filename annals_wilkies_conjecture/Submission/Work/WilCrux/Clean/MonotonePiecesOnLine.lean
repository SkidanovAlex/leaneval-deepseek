import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilCrux.UnifMonotonePieces
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG5.Reindex
import Submission.Work.WilCrux.Clean.LineSliceDefs
import Submission.Work.WilCrux.Clean.sliceLineSet_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux.Clean

open WilkiesDesign

/-!
## `Work.WilCrux.Clean.MonotonePiecesOnLine`

**Uniformly many monotonicity pieces along a coordinate line.**

`Work.WilCrux.UnifMonotonePieces` proves the one-variable statement: for a sharply o-minimal `S`
and a format/degree pair `(F,D)` there is a single bound `K` such that *every* `Ω F D 2`-definable
`h : ℝ → ℝ` is differentiable off, and monotone or antitone between, at most `K` break points.

To transfer it to a line `t ↦ w₁ + t • eᵢ` in `ℝⁿ` (with `H : ℝⁿ → ℝ` of format `F`, degree `D`,
so `graphOf H ∈ S.Ω F D (n+1)`) the only thing to check is that the one-variable function
`t ↦ H (w₁ + t • eᵢ)` is again `Ω`-definable **at a format and degree that do not see `H` or
`w₁`**; then the bound `K` of `UnifMonotonePieces` is uniform in both.

This is what `LineSliceDefs` sets up and what the two lemmas below provide:

* `sliceLineSet_mem` (module `Submission.Work.WilCrux.Clean.sliceLineSet_mem`): the affine set
  `x = w₁ + t • eᵢ` inside `ℝ^{n+2}` is `Ω (n+3) n (n+2)`, by `S.hyp` on the `n` degree-one
  equations (the coefficients `w₁` enter only as multiplicative constants, so the *degree* bound
  is `1` per equation and the format is the number of variables) and `S.inter`;
* `sliceGraph_eq_line` (below): the graph of the restriction is the coordinate image of
  `liftFirst 1 (graphOf H) ∩ sliceLineSet n i w₁` under the selection `sliceCoord n` of the two
  coordinates `(t, y)`.

`Work.WilG5.coordImage_mem` then prices the coordinate image at format
`(max (F+1) (n+3) + 1) + 64 * ((n+2)+2) + 64` and degree `(D+n) + 32 * ((n+2)+2) + 32`, both of
which are functions of `n, F, D` alone.
-/

/-- **The graph of the restriction of `H` to the line `w₁ + t • eᵢ` is a coordinate image.**

A point `z` of `ℝ^{n+2}` is in `liftFirst 1 (graphOf H)` exactly when its first `n+1`
coordinates `(z (sxIdx n ·), z (sYIdx n))` lie on the graph of `H`, and in `sliceLineSet n i w₁`
exactly when `z (sxIdx n j) = w₁ j + z (sTIdx n) · (if j = i then 1 else 0)`, i.e. the `x`-block
is `w₁ + t • eᵢ` with `t = z (sTIdx n)`.  Selecting the coordinates `(t, y)` therefore produces
exactly the graph of `t ↦ H (w₁ + t • eᵢ)`.

Forward: with `p := fun m => z (Fin.castAdd 1 m)` the `graphOf` condition is
`z (sYIdx n) = H (Fin.init p)`, and `Fin.init p = fun j => z (sxIdx n j) = w₁ + u 0 • eᵢ` because
`u 0 = z (sTIdx n)` and by the line equations.

Backward: given `u` with `u 1 = H (w₁ + u 0 • eᵢ)`, take `z := Fin.snoc (Fin.snoc x (u 1)) (u 0)`
with `x := w₁ + u 0 • eᵢ`; then `z (sxIdx n j) = x j`, `z (sYIdx n) = u 1` and `z (sTIdx n) = u 0`,
and the two conjuncts follow. -/
theorem sliceGraph_eq_line {n : ℕ} (H : (Fin n → ℝ) → ℝ) (i : Fin n) (w₁ : Fin n → ℝ) :
    Work.WilG5.coordImage (sliceCoord n)
        (Work.WilG5.liftFirst 1 (graphOf H) ∩ sliceLineSet n i w₁)
      = graphOf (fun x : Fin 1 → ℝ => H (w₁ + x 0 • Pi.single i (1 : ℝ))) := by
  ext u
  constructor
  · rintro ⟨z, hz, hzu⟩
    rw [Set.mem_inter_iff] at hz
    obtain ⟨hzG, hzL⟩ := hz
    have hval : z (sYIdx n) = H (fun j : Fin n => z (sxIdx n j)) := by
      have h := hzG
      simp only [Work.WilG5.liftFirst, Set.mem_ofPred_eq] at h
      simp only [graphOf, Set.mem_ofPred_eq] at h
      have hR : Fin.init (fun m : Fin (n + 1) => z (Fin.castAdd 1 m)) =
          (fun j : Fin n => z (sxIdx n j)) := by
        funext j
        exact congrArg z (Fin.ext rfl)
      rw [hR] at h
      exact h
    have h0 : u 0 = z (sTIdx n) := ((comp_sliceCoord_eq z u).mp hzu).1
    have h1 : u 1 = z (sYIdx n) := ((comp_sliceCoord_eq z u).mp hzu).2
    have hline : (fun j : Fin n => z (sxIdx n j)) = w₁ + u 0 • Pi.single i (1 : ℝ) := by
      funext j
      rw [add_smul_single_apply, h0]
      exact hzL j
    show u (Fin.last 1) = H (w₁ + (Fin.init u) 0 • Pi.single i (1 : ℝ))
    rw [show (Fin.last 1 : Fin 2) = 1 from rfl, show (Fin.init u) 0 = u 0 from rfl, h1, hval,
      hline]
  · intro hu
    have hu' : u 1 = H (w₁ + u 0 • Pi.single i (1 : ℝ)) := hu
    refine ⟨(Fin.snoc (Fin.snoc (w₁ + u 0 • Pi.single i (1 : ℝ)) (u 1)) (u 0) :
      Fin (n + 2) → ℝ), ?_, ?_⟩
    · rw [Set.mem_inter_iff]
      refine ⟨?_, ?_⟩
      · show (fun m : Fin (n + 1) =>
            (Fin.snoc (Fin.snoc (w₁ + u 0 • Pi.single i (1 : ℝ)) (u 1)) (u 0) :
              Fin (n + 2) → ℝ) (Fin.castAdd 1 m)) ∈ graphOf H
        have hblock : (fun m : Fin (n + 1) =>
            (Fin.snoc (Fin.snoc (w₁ + u 0 • Pi.single i (1 : ℝ)) (u 1)) (u 0) :
              Fin (n + 2) → ℝ) (Fin.castAdd 1 m))
            = (Fin.snoc (w₁ + u 0 • Pi.single i (1 : ℝ)) (u 1) : Fin (n + 1) → ℝ) := by
          funext m
          rw [show (Fin.castAdd 1 m : Fin (n + 2)) = m.castSucc from Fin.ext rfl]
          simp
        rw [hblock]
        simp only [graphOf, Set.mem_ofPred_eq]
        rw [Fin.snoc_last, Fin.init_snoc]
        exact hu'
      · intro j
        show (Fin.snoc (Fin.snoc (w₁ + u 0 • Pi.single i (1 : ℝ)) (u 1)) (u 0) :
              Fin (n + 2) → ℝ) (sxIdx n j) = w₁ j +
          (Fin.snoc (Fin.snoc (w₁ + u 0 • Pi.single i (1 : ℝ)) (u 1)) (u 0) :
              Fin (n + 2) → ℝ) (sTIdx n) * (if j = i then 1 else 0)
        rw [show sxIdx n j = ((Fin.castSucc j).castSucc : Fin (n + 2)) from Fin.ext rfl,
          show sTIdx n = Fin.last (n + 1) from rfl]
        simp
        rw [Pi.single_apply]
        by_cases h : j = i <;> simp [h]
    · refine (comp_sliceCoord_eq _ u).mpr ⟨?_, ?_⟩
      · rw [show sTIdx n = Fin.last (n + 1) from rfl, Fin.snoc_last]
      · rw [show sYIdx n = ((Fin.last n).castSucc : Fin (n + 2)) from Fin.ext rfl,
          Fin.snoc_castSucc, Fin.snoc_last]

/-- **Uniformly many monotonicity pieces of a definable function on a coordinate line.**

For a sharply o-minimal `S` satisfying sharp cell decomposition and sharp derivatives, a format
`F`, a degree `D` and a direction `i : Fin n` there is one bound `K` such that for every
`Ω F D (n+1)`-definable `H : ℝⁿ → ℝ` and every base point `w₁`, the restriction
`t ↦ H (w₁ + t • Pi.single i 1)` is differentiable off, and monotone or antitone between, at
most `K` break points.

Proof.  Write `x := w₁ + t • eᵢ` for the line.  In `ℝ^{n+2}` (coordinates `(x, y, t)`) the set
`liftFirst 1 (graphOf H) ∩ sliceLineSet n i w₁` is `Ω` with format `≤ max (F+1) (n+3) + 1` and
degree `≤ D + n` (`liftFirst_mem`, `sliceLineSet_mem`, `S.inter`), so by
`Work.WilG5.coordImage_mem` the coordinate image along `sliceCoord n` of it — which is the graph
of the restriction, by `sliceGraph_eq_line` — is `Ω Fbig Dbig 2` for the explicit constants

`Fbig = (max (F+1) (n+3) + 1) + 64 * ((n+2) + 2) + 64`,
`Dbig = (D+n) + 32 * ((n+2) + 2) + 32`,

depending only on `n`, `F`, `D`.  `Work.WilCrux.UnifMonotonePieces S hcd hder Fbig Dbig` now
supplies a single `K` for all such one-variable functions, and it is independent of `H` and of
`w₁` because `Fbig`, `Dbig` are. -/
theorem MonotonePiecesOnLine (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    {n F D : ℕ} (i : Fin n) :
    ∃ K : ℕ, ∀ (H : (Fin n → ℝ) → ℝ), WilkiesDesign.graphOf H ∈ S.Ω F D (n + 1) →
      ∀ (w₁ : Fin n → ℝ), ∃ brk : Finset ℝ, brk.card ≤ K ∧
        (∀ s : ℝ, s ∉ brk → DifferentiableAt ℝ (fun t : ℝ => H (w₁ + t • Pi.single i 1)) s) ∧
        ∀ s t : ℝ, s < t → (∀ u ∈ Set.Ioo s t, u ∉ brk) →
          MonotoneOn (fun t : ℝ => H (w₁ + t • Pi.single i 1)) (Set.Ioo s t) ∨
          AntitoneOn (fun t : ℝ => H (w₁ + t • Pi.single i 1)) (Set.Ioo s t) := by
  let Fbig : ℕ := (max (F + 1) (n + 3) + 1) + 64 * ((n + 2) + 2) + 64
  let Dbig : ℕ := (D + n) + 32 * ((n + 2) + 2) + 32
  obtain ⟨K, hK⟩ := Work.WilCrux.UnifMonotonePieces S hcd hder Fbig Dbig
  refine ⟨K, ?_⟩
  intro H hg w₁
  have hA : Work.WilG5.liftFirst 1 (WilkiesDesign.graphOf H) ∈ S.Ω (F + 1) D (n + 2) :=
    Work.WilG5.liftFirst_mem (S := S) 1 F D hg
  have hL : sliceLineSet n i w₁ ∈ S.Ω (n + 3) n (n + 2) := sliceLineSet_mem S i w₁
  have h1 : Work.WilG5.liftFirst 1 (WilkiesDesign.graphOf H) ∈
      S.Ω (max (F + 1) (n + 3)) D (n + 2) :=
    Work.WilG5.mem_mono hA _ _ (le_max_left _ _) le_rfl
  have h2 : sliceLineSet n i w₁ ∈ S.Ω (max (F + 1) (n + 3)) n (n + 2) :=
    Work.WilG5.mem_mono hL _ _ (le_max_right _ _) le_rfl
  have hB : (Work.WilG5.liftFirst 1 (WilkiesDesign.graphOf H) ∩ sliceLineSet n i w₁) ∈
      S.Ω (max (F + 1) (n + 3) + 1) (D + n) (n + 2) := by
    have h := S.inter (fun l : Fin 2 => if l = 0 then D else n)
      (fun l : Fin 2 => if l = 0 then Work.WilG5.liftFirst 1 (WilkiesDesign.graphOf H)
        else sliceLineSet n i w₁)
      (by intro l; fin_cases l
          · simpa using h1
          · simpa using h2)
    rw [show (∑ l : Fin 2, (if l = 0 then D else n)) = D + n from by
      rw [Fin.sum_univ_two]; norm_num] at h
    rw [show (⋂ l : Fin 2, (if l = 0 then Work.WilG5.liftFirst 1 (WilkiesDesign.graphOf H)
        else sliceLineSet n i w₁))
        = Work.WilG5.liftFirst 1 (WilkiesDesign.graphOf H) ∩ sliceLineSet n i w₁ from by
      ext z; simp [Fin.forall_fin_two]] at h
    exact Work.WilG5.mem_mono h _ _ (by omega) (le_refl _)
  have hC : Work.WilG5.coordImage (sliceCoord n)
      (Work.WilG5.liftFirst 1 (WilkiesDesign.graphOf H) ∩ sliceLineSet n i w₁) ∈
      S.Ω Fbig Dbig 2 :=
    Work.WilG5.coordImage_mem (S := S) (m := 2) (N := n + 2)
      (F := max (F + 1) (n + 3) + 1) (D := D + n) hB
  have hslice : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => H (w₁ + x 0 • Pi.single i (1 : ℝ)))
      ∈ S.Ω Fbig Dbig 2 := by
    rw [← sliceGraph_eq_line H i w₁]
    exact hC
  exact hK (fun t : ℝ => H (w₁ + t • Pi.single i (1 : ℝ))) hslice

end Work.WilCrux.Clean
