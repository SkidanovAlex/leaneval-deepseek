/-
  WilG4c / `StepLipHighPsiPack` — the packaging of the §5.3 union (the last step of
  `StepLipHighPsiCond`), kept in its own module for the per-file build limit.
-/
import Mathlib
import Submission.Work.WilG4c.StepLipHighPsiCell
import Submission.Work.WilG4c.StepLipHighPsiAux3
import Submission.Work.WilG4a.F1AffineW

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The packaging of the §5.3 union**: from the per-cell chart families (with their count
bounds and conditional covers for the clamped family `Fc`) and the three polynomial identities
of the count, produce the single chart family for `(Λ, F)` with the `FLemP` conclusion.

The hypotheses `hMidEq`, `hcFin`, `hbFinal`, `hFc_eq` are the interface to the polynomial
bookkeeping of `StepLipHighPsiCond`; `hA` is the bound on the number of cells. -/
theorem psiCellPack
    (S : WilkiesDesign.SOMin) {p n k : ℕ} (C : Finset (Set (Fin (p + 1) → ℝ)))
    (hCdec : WilkiesDesign.IsCylDecomp (p + 1) C)
    (Fc F : Work.WilkG4c.Family k p (n + 1)) (Λ : Set (Fin p → ℝ))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (ε : ℝ) (D Dc r : ℕ)
    (aFin : ℕ) (bFin bFinal : MvPolynomial (Fin 2) ℕ)
    (cMerge cA cMid cFin : MvPolynomial (Fin 4) ℝ)
    (hcellκ : ∀ κ ∈ C, ∃ Φκ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
        (Φκ.card : ℝ) ≤
            MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMerge ∧
        Work.WilkG4c.ChartsOK S aFin (MvPolynomial.eval ![Dc, r] bFin) r Λ Fc Φκ ∧
        (∀ l ∈ Λ, ∀ x' ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x' 0) ∈ κ →
          (∃ t ∈ WilkiesDesign.openCube n, ∀ i,
            |Fc i l (Fin.cons (x' 0) (fun j => ψ j (Fin.snoc l (x' 0)) t)) - Fc i l x'|
              < ε / 2) →
          ∃ φ ∈ Φκ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
            ∀ i, |Fc i l (fun j => φ j l t) - Fc i l x'| < ε))
    (hA : (C.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA)
    (hMidEq : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMid
        = MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMerge)
    (hcFin : cFin = (cA * cA + cMid * cMid) + (cA + cMid) + 1)
    (hbFinal : MvPolynomial.eval ![D, r] bFinal = MvPolynomial.eval ![Dc, r] bFin)
    (hFc_eq : ∀ (i : Fin k) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ), l ∈ Λ →
      Fc i l t = F i l t) :
    ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
      (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cFin ∧
      Work.WilkG4c.ChartsOK S aFin (MvPolynomial.eval ![D, r] bFinal) r Λ F Φ ∧
      (∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
        (∃ t ∈ WilkiesDesign.openCube n, ∀ i,
          |F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) - F i l (Fin.cons x y)|
            < ε / 2) →
        ∃ t ∈ WilkiesDesign.openCube (n + 1), ∃ φ ∈ Φ, ∀ i,
          |F i l (fun j => φ j l t) - F i l (Fin.cons x y)| < ε) := by
  refine ⟨C.attach.biUnion (fun κ : {s // s ∈ C} => (hcellκ κ.1 κ.2).choose), ?_, ?_, ?_⟩
  · -- ## the cardinality of the union
    have hcard1 : (((C.attach.biUnion (fun κ : {s // s ∈ C} =>
          (hcellκ κ.1 κ.2).choose)).card : ℕ) : ℝ)
        ≤ (C.card : ℝ) *
          MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMerge :=
      Work.WilG4c.card_attach_biUnion_le C
        (fun κ : {s // s ∈ C} => (hcellκ κ.1 κ.2).choose) _
        (fun κ _ => (hcellκ κ.1 κ.2).choose_spec.1)
    obtain ⟨κ₀, hκ₀C, -⟩ := Work.WilG1.Cell.exists_mem_of_cylDecomp hCdec
      (0 : Fin (p + 1) → ℝ)
    have hXm0 : 0 ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMid := by
      rw [hMidEq]
      exact le_trans (Nat.cast_nonneg _) (hcellκ κ₀ hκ₀C).choose_spec.1
    have hXa0 : 0 ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA :=
      le_trans (Nat.cast_nonneg _) hA
    have hMul : (C.card : ℝ) *
          MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMid
        ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA *
          MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMid :=
      mul_le_mul_of_nonneg_right hA hXm0
    have hFin : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA *
          MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMid
        ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cFin := by
      rw [hcFin]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, map_one]
      exact Work.WilG4c.mul_le_merge_sq _ _ hXa0 hXm0
    calc (((C.attach.biUnion (fun κ : {s // s ∈ C} => (hcellκ κ.1 κ.2).choose)).card : ℕ) : ℝ)
        ≤ (C.card : ℝ) *
            MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMerge := hcard1
      _ = (C.card : ℝ) *
            MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMid :=
          congrArg (fun z => (C.card : ℝ) * z) hMidEq.symm
      _ ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA *
            MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMid := hMul
      _ ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cFin := hFin
  · -- ## the per-chart conditions
    have hOKbiU : Work.WilkG4c.ChartsOK S aFin (MvPolynomial.eval ![Dc, r] bFin) r Λ Fc
        (C.attach.biUnion (fun κ : {s // s ∈ C} => (hcellκ κ.1 κ.2).choose)) :=
      fun φ hφ => by
        obtain ⟨i, -, hφi⟩ := Finset.mem_biUnion.mp hφ
        exact (hcellκ i.1 i.2).choose_spec.2.1 φ hφi
    have hOK1 : Work.WilkG4c.ChartsOK S aFin (MvPolynomial.eval ![D, r] bFinal) r Λ Fc
        (C.attach.biUnion (fun κ : {s // s ∈ C} => (hcellκ κ.1 κ.2).choose)) := by
      refine Work.WilkG4c.ChartsOK_mono hOKbiU le_rfl ?_
      exact le_of_eq hbFinal.symm
    exact Work.WilkG4c.ChartsOK_congr (Λ := Λ) (F := F) (G := Fc)
      (fun i l t hl _ => (hFc_eq i l t hl).symm) hOK1
  · -- ## the cover
    intro l hl x hx y hy hhyp
    obtain ⟨κ, hκC, hmem⟩ := Work.WilG1.Cell.exists_mem_of_cylDecomp hCdec (Fin.snoc l x)
    have hxcube : Fin.cons x y ∈ WilkiesDesign.openCube (n + 1) := by
      intro j
      rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
      · rw [h, Fin.cons_zero]; exact hx
      · rw [Fin.cons_succ]; exact hy j'
    have hhyp' : ∃ t ∈ WilkiesDesign.openCube n, ∀ i,
        |Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) - Fc i l (Fin.cons x y)|
          < ε / 2 := by
      obtain ⟨t, ht, hlt⟩ := hhyp
      refine ⟨t, ht, fun i => ?_⟩
      have e1 : Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))
          = F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) := hFc_eq i l _ hl
      have e2 : Fc i l (Fin.cons x y) = F i l (Fin.cons x y) := hFc_eq i l _ hl
      rw [e1, e2]
      exact hlt i
    obtain ⟨φ, hφ, t, ht, hlt⟩ :=
      (hcellκ κ hκC).choose_spec.2.2 l hl (Fin.cons x y) hxcube
        (by simpa only [Fin.cons_zero] using hmem)
        (by simpa only [Fin.cons_zero] using hhyp')
    refine ⟨t, ht, φ,
      Finset.mem_biUnion.mpr ⟨⟨κ, hκC⟩, Finset.mem_attach C ⟨κ, hκC⟩, hφ⟩, fun i => ?_⟩
    have e1 : Fc i l (fun j => φ j l t) = F i l (fun j => φ j l t) := hFc_eq i l _ hl
    have e2 : Fc i l (Fin.cons x y) = F i l (Fin.cons x y) := hFc_eq i l _ hl
    rw [← e1, ← e2]
    exact hlt i


end Work.WilG4c
