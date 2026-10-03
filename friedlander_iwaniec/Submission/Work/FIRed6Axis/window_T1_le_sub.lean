import Mathlib
import Submission.Work.FITop4.Red5.window_T1_le

namespace Work.FIRed6Axis

/-- Copy of `Work.FITop4.Red5.window_T1_le` (`Submission/Work/FITop4/Red5/window_T1_le.lean`)
with the `k`-sum restricted to a subfamily `S` of the angular cells.  The proof transplants
verbatim: swap the `m`-sum inward (`Finset.sum_comm`, once per `i`), then `Finset.sum_le_sum` over
`i` and over `k ∈ S`, and for each fixed `(i,k)` run the existing per-`(i,k)` argument
(`sum_primAnn_eq_sum_boxN`, `fiber_sum_annM`, `Work.FITop4.Red4.sum_norm_inner_le`,
`Real.sqrt_le_sqrt`); no step uses the index type of `k`. -/
theorem window_T1_le_sub
    (x N Pz Mn : ℕ) (C τ θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (f : Fin K → Fin K' → ℤ → ℝ) (S : Finset (Fin K'))
    (hN : 1 ≤ N) (hMn : 1 ≤ Mn)
    (hPaM : ∀ i k, (Pa i k).M = (Mn : ℝ)) (hPaN : ∀ i k, (Pa i k).N = a i)
    (ha : ∀ i, (N : ℝ) ≤ a i)
    (hsup : ∀ i u, p i u ≠ 0 → u ≤ 2 * (N : ℝ))
    (hMaj : ∀ i k, Work.FITop3.IsMajorant (Pa i k) (f i k)) :
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn),
        ∑ i, ∑ k ∈ S, ∑ w ∈ Work.FITop4.Red5.wSph m,
          ‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      ≤ ∑ i, ∑ k ∈ S, Real.sqrt (100 * (Pa i k).M
          * Work.FITop3.Dform (Pa i k) (f i k)
              (Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i))) := by
  -- move the `m`-sum inwards (past `i`, then past `k`)
  have hswap :
      (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn),
        ∑ i, ∑ k ∈ S, ∑ w ∈ Work.FITop4.Red5.wSph m,
          ‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      = ∑ i, ∑ k ∈ S, ∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn),
          ∑ w ∈ Work.FITop4.Red5.wSph m,
          ‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hNle : (N : ℝ) ≤ (Pa i k).N := by rw [hPaN i k]; exact ha i
  have hsup' : ∀ u : ℝ, p i u ≠ 0 → u ≤ 2 * (N : ℝ) := fun u hu => hsup i u hu
  -- the two inner sums are the same
  have hinner : ∀ w : GaussianInt,
      (∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
          Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z)
        = ∑ z ∈ Work.FITop.boxN (Pa i k),
            Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z :=
    fun w => Work.FITop4.Red5.sum_primAnn_eq_sum_boxN hN hNle hsup' w
  -- reindex the `m`-window as the annulus
  have hstep :
      (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph m,
          ‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      = ∑ w ∈ Work.FITop3.annM (Pa i k),
          ‖∑ z ∈ Work.FITop.boxN (Pa i k),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
    have hfun : ∀ w : GaussianInt,
        ‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
          = ‖∑ z ∈ Work.FITop.boxN (Pa i k),
            Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ :=
      fun w => by rw [hinner w]
    rw [show (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph m,
          ‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        = ∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph m,
          ‖∑ z ∈ Work.FITop.boxN (Pa i k),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ from by
      apply Finset.sum_congr rfl
      intro m _
      exact Finset.sum_congr rfl (fun w _ => hfun w)]
    exact (Work.FITop4.Red5.fiber_sum_annM (Pa := Pa i k) (A := Mn) (hPaM i k) hMn
      (fun w => ‖∑ z ∈ Work.FITop.boxN (Pa i k),
             Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)).symm
  rw [hstep]
  -- Cauchy–Schwarz over the annulus, with `f ≥ 1` there and `card (annM) ≤ 100 M`
  have hCS := Work.FITop4.Red4.sum_norm_inner_le (Pa i k) (f i k)
    (Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i)) (hMaj i k)
  have hnn : 0 ≤ ∑ w ∈ Work.FITop3.annM (Pa i k),
      ‖∑ z ∈ Work.FITop.boxN (Pa i k),
          Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ :=
    Finset.sum_nonneg fun w _ => norm_nonneg _
  calc ∑ w ∈ Work.FITop3.annM (Pa i k),
        ‖∑ z ∈ Work.FITop.boxN (Pa i k),
            Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
      = Real.sqrt ((∑ w ∈ Work.FITop3.annM (Pa i k),
          ‖∑ z ∈ Work.FITop.boxN (Pa i k),
              Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (100 * (Pa i k).M
          * Work.FITop3.Dform (Pa i k) (f i k)
              (Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i))) :=
        Real.sqrt_le_sqrt hCS

end Work.FIRed6Axis
