/-
  WilG4c / YPullbackGraph — the `Ω`-bookkeeping of the `y`-pullback.

  The `y`-pullback `yPullback F φ` of the family `F` along a chart tuple `φ` is the composite
  `(l, z) ↦ F i l (pullbackMap φ l z)`; the reparametrisation `pullbackMap φ` keeps the
  distinguished coordinate `z 0` and feeds the remaining coordinates through `φ`.

  This file records the `Ω`-filtration bookkeeping for the two families appearing in the §5.2
  reduction: the graph of every coordinate of `pullbackMap φ` (the regrouping lemma
  `Work.WilG4c.phiPtCoordGraph`), and the graph of `yPullback F φ` (composition of graphs,
  `famGraph_comp_single`).  Both constants are *additive* in the data, which is what the
  downstream uniformity in `F0, D, a₁, Dg₁` needs.
-/
import Mathlib
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.phiPtCoordGraph

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- `pullbackMap` in the `Fin.cases` spelling used by the coordinate regrouping lemmas: the
value at `j` is `z 0` for `j = 0` and the chart value `φ i (Fin.snoc l (z 0)) (Fin.tail z)`
otherwise. -/
theorem pullbackMap_eq_cases {p n : ℕ} (φ : ChartTuple (p+1) n) (l : Fin p → ℝ)
    (z : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    pullbackMap φ l z j =
      Fin.cases (z 0) (fun i : Fin n => φ i (Fin.snoc l (z 0)) (Fin.tail z)) j := by
  induction j using Fin.cases with
  | zero => simp [pullbackMap]
  | succ i => simp [pullbackMap]

theorem YPullbackGraph (S : WilkiesDesign.SOMin) {k p n : ℕ} (F : Work.WilkG4c.Family k p (n+1))
    (φ : Work.WilkG4c.ChartTuple (p+1) n) (F0 D a₁ Dg₁ : ℕ)
    (hF : ∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n+1) + 1))
    (hφ : ∀ j, WilkiesDesign.CG.famGraph (φ j) ∈ S.Ω a₁ Dg₁ ((p+1) + n + 1)) :
    ∃ (a : ℕ) (c : ℕ),
      (∀ j : Fin (n+1), WilkiesDesign.CG.famGraph (fun l z => Work.WilkG4c.pullbackMap φ l z j) ∈
        S.Ω (a₁ + a) (Dg₁ + c) (p + (n+1) + 1)) ∧
      ∀ i, WilkiesDesign.CG.famGraph (Work.WilkG4c.yPullback F φ i) ∈
        S.Ω (F0 + a₁ + a) (D + (p + (n+1)) * (Dg₁ + c) + c) (p + (n+1) + 1) := by
  obtain ⟨aphi, cphi, hphi⟩ := Work.WilG4c.phiPtCoordGraph S p n
  obtain ⟨acomp, ccomp, hcomp⟩ := famGraph_comp_single S p (n+1)
  -- the coordinate graphs of the reparametrisation, at the "unshifted" level
  have hχ : ∀ j : Fin (n+1),
      WilkiesDesign.CG.famGraph (fun l z => Work.WilkG4c.pullbackMap φ l z j) ∈
        S.Ω (a₁ + aphi) (Dg₁ + cphi) (p + (n+1) + 1) := by
    intro j
    have h := hphi a₁ Dg₁ φ hφ j
    have hfun : (fun (l : Fin p → ℝ) (z : Fin (n+1) → ℝ) => Work.WilkG4c.pullbackMap φ l z j)
        = (fun (l : Fin p → ℝ) (z : Fin (n+1) → ℝ) =>
            Fin.cases (z 0) (fun i : Fin n => φ i (Fin.snoc l (z 0)) (Fin.tail z)) j) := by
      funext l z
      exact pullbackMap_eq_cases φ l z j
    rw [hfun]
    exact h
  refine ⟨aphi + acomp, max cphi ccomp, ?_, ?_⟩
  · intro j
    exact Omega_mono_le S (by omega) (by omega) (hχ j)
  · intro i
    have hmain := hcomp F0 (a₁ + aphi) D (Dg₁ + cphi) (F i)
      (fun j l z => Work.WilkG4c.pullbackMap φ l z j) (hF i) hχ
    rw [show (fun (l : Fin p → ℝ) (z : Fin (n+1) → ℝ) =>
          F i l (fun j => Work.WilkG4c.pullbackMap φ l z j))
        = Work.WilkG4c.yPullback F φ i from rfl] at hmain
    refine Omega_mono_le S (by omega) ?_ hmain
    have h1 : Dg₁ + cphi ≤ Dg₁ + max cphi ccomp := by omega
    have h3 := Nat.mul_le_mul_left (p + (n+1)) h1
    omega

end Work.WilkG4c
