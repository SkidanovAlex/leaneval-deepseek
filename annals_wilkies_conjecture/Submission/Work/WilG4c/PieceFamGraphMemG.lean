import Mathlib
import Submission.Work.WilG4c.StepLipPieces
import Submission.Work.WilG4c.ExactChartDeriv
import Submission.Work.WilG4c.PieceChartsToF
import Submission.Work.WilkG4c.YPullbackBound
import Submission.Work.WilkG4c.YPullbackGraph
import Submission.Work.WilG4c.YbddAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The `Ω`-bound of the piece family's graph.**  The piece
`pieceFam (yPullback F ψ) (chartFun χ)` is the composition of `F` with the reparametrisation
`z ↦ pullbackMap ψ (Fin.cons (chartFun χ (z 0)) (Fin.tail z))`, whose coordinates are the
coordinates of the combined chart `selPieceChart ψ χ idChart`.  Their graphs are `Ω`-bounded by
`selPieceChart_zero_mem` / `selPieceChart_succ_mem`, so `famGraph_comp_single` gives the bound. -/
theorem PieceFamGraphMem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (A T : ℕ), ∀ {k : ℕ} (F0 D aψ Dgψ a01 Dg01 : ℕ)
      (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
      (χ : Work.WilkG4c.ChartTuple p 1),
      (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
      (∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1)) →
      (∀ j : Fin 1, WilkiesDesign.CG.famGraph (χ j) ∈ S.Ω a01 Dg01 (p + 1 + 1)) →
      ∀ i, WilkiesDesign.CG.famGraph
          (Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i) ∈
        S.Ω (F0 + aψ + a01 + A)
            (D + (p + (n + 1)) * (Dgψ + ((p + 1) + n) * (Dg01 + (p + 1) + T) + T + 1) + T)
            (p + (n + 1) + 1) := by
  obtain ⟨A0, C0, hz0⟩ := Work.WilG4c.selPieceChart_zero_mem S p n
  obtain ⟨A1, C1, hs1⟩ := Work.WilG4c.selPieceChart_succ_mem S p n
  obtain ⟨acs, ccs, hCS⟩ := Work.WilkG4c.famGraph_comp_single S p (n + 1)
  refine ⟨2 * (p + (n + 1) + 1) + A0 + A1 + acs + 2, C0 + C1 + ccs + 1, ?_⟩
  intro k F0 D aψ Dgψ a01 Dg01 F ψ χ hF hψ hχ i
  -- the coordinate graphs of the identity chart
  have hproj : ∀ kk : Fin (n + 1), WilkiesDesign.CG.famGraph
      (fun (_ : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => t kk) ∈
      S.Ω (p + (n + 1) + 1) 1 (p + (n + 1) + 1) := by
    intro kk
    have h := Work.WilkG4c.graphOf_coord_mem S (Fin.natAdd p kk)
    have hfun : (fun x : Fin (p + (n + 1)) → ℝ => x (Fin.natAdd p kk))
        = Work.WilkG4c.flatFun (fun (_ : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => t kk) := by
      funext x
      simp [Work.WilkG4c.flatFun]
    rw [hfun, ← Work.WilkG4c.famGraph_eq_graphOf_flatFun] at h
    exact h
  -- the two candidate coordinate bounds of the reparametrisation
  have hz0' : WilkiesDesign.CG.famGraph
      (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => χ 0 l (fun _ : Fin 1 => t 0)) ∈
      S.Ω (a01 + (p + (n + 1) + 1) + A0) (Dg01 + (p + 1) + C0) (p + (n + 1) + 1) := by
    have h := hz0 a01 Dg01 (p + (n + 1) + 1) 1 χ
      (fun (_ : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => t 0) (hχ 0) (hproj 0)
    simpa using h
  have hs1' : ∀ j : Fin n, WilkiesDesign.CG.famGraph
      (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) =>
        ψ j (Fin.snoc l (χ 0 l (fun _ : Fin 1 => t 0))) (Fin.tail t)) ∈
      S.Ω (aψ + (a01 + (p + (n + 1) + 1) + A1))
          (Dgψ + ((p + 1) + n) * (Dg01 + (p + 1) + C1) + C1) (p + (n + 1) + 1) := by
    intro j
    have h := hs1 aψ Dgψ a01 Dg01 (p + (n + 1) + 1) 1 ψ χ
      (fun (i : Fin (n + 1)) (_ : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => t i) j hψ (hχ 0)
      (fun i => hproj i)
    simpa using h
  -- the piece is the composition of `F i` with the coordinates of `selPieceChart`
  have hpiece : WilkiesDesign.CG.famGraph
      (Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i)
      = WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
          F i l (fun j => selPieceChart ψ χ
            (fun (i : Fin (n + 1)) (_ : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => t i) j l z)) := by
    congr 1
    funext l z
    rw [selPieceChart_toPt]
    simp only [Work.WilkG4c.pieceFam_apply, Work.WilkG4c.yPullback_apply,
      Work.WilkG4c.pullbackMap_apply, Work.WilG4c.chartFun_apply, Fin.cons_zero,
      Fin.tail_cons]
  -- the coordinate bounds at a common format and degree
  have hcoord : ∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph
      (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
        selPieceChart ψ χ (fun (i : Fin (n + 1)) (_ : Fin p → ℝ)
          (t : Fin (n + 1) → ℝ) => t i) j l z) ∈
      S.Ω (max (a01 + (p + (n + 1) + 1) + A0) (aψ + (a01 + (p + (n + 1) + 1) + A1)))
          (Dgψ + ((p + 1) + n) * (Dg01 + (p + 1) + (C0 + C1 + ccs + 1))
            + (C0 + C1 + ccs + 1) + 1)
          (p + (n + 1) + 1) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · rw [selPieceChart_zero]
      refine Work.WilkG4c.Omega_mono_le S (le_max_left _ _) ?_ hz0'
      have ha : Dg01 + (p + 1) + C0
          ≤ ((p + 1) + n) * (Dg01 + (p + 1) + (C0 + C1 + ccs + 1)) := by
        have h1 : (1 : ℕ) * (Dg01 + (p + 1) + C0)
            ≤ ((p + 1) + n) * (Dg01 + (p + 1) + (C0 + C1 + ccs + 1)) :=
          Nat.mul_le_mul (by omega) (by omega)
        simpa using h1
      omega
    · intro kk
      rw [selPieceChart_succ]
      refine Work.WilkG4c.Omega_mono_le S (le_max_right _ _) ?_ (hs1' kk)
      have hb : ((p + 1) + n) * (Dg01 + (p + 1) + C1)
          ≤ ((p + 1) + n) * (Dg01 + (p + 1) + (C0 + C1 + ccs + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  have hmain := hCS F0 (max (a01 + (p + (n + 1) + 1) + A0)
        (aψ + (a01 + (p + (n + 1) + 1) + A1)))
      D (Dgψ + ((p + 1) + n) * (Dg01 + (p + 1) + (C0 + C1 + ccs + 1))
        + (C0 + C1 + ccs + 1) + 1)
      (F i) (fun j l z => selPieceChart ψ χ (fun (i : Fin (n + 1)) (_ : Fin p → ℝ)
        (t : Fin (n + 1) → ℝ) => t i) j l z) (hF i) hcoord
  rw [← hpiece] at hmain
  refine Work.WilkG4c.Omega_mono_le S ?_ ?_ hmain
  · -- the format
    have hle : max (a01 + (p + (n + 1) + 1) + A0)
          (aψ + (a01 + (p + (n + 1) + 1) + A1)) + acs
        ≤ aψ + a01 + (2 * (p + (n + 1) + 1) + A0 + A1 + acs + 2) := by
      rcases le_total (a01 + (p + (n + 1) + 1) + A0)
        (aψ + (a01 + (p + (n + 1) + 1) + A1)) with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    omega
  · -- the degree
    omega

end Work.WilG4c
