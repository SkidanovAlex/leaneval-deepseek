import Mathlib
import Submission.Work.FITop4.Red5.window_setup
import Submission.Work.FITop4.Red5.sieve_inner_le_pieces_act
import Submission.Work.FITop4.Red5.window_T1_le
import Submission.Work.FITop4.Red5.window_T3_le

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Reindexing the active-cell filter from the outer `m`-sum to the inner `i`-sum: for a finite
window `s ⊆ ℕ` and weights `F`, the sum over `m ∈ s` of the sums over the *active* cells
`{i : (m:ℝ) * a i < x}` equals the sum over `i` of the sums over the `m ∈ s` that are active for
`i`.  This is the elementary rearrangement that lets the "active-`i`" error terms of
`sieve_inner_le_pieces_act`, summed over the window, be recognised as the single right-hand side
that the `T2`/`T3` estimates are stated against. -/
lemma sum_filter_swap_univ {K : ℕ}
    (s : Finset ℕ) (a : Fin K → ℝ) (x : ℝ) (F : ℕ → Fin K → ℝ) :
    (∑ m ∈ s, ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < x), F m i)
      = ∑ i, ∑ m ∈ s.filter (fun m : ℕ => (m : ℝ) * a i < x), F m i := by
  have h1 : ∀ m : ℕ, (∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < x), F m i)
      = ∑ i, if (m : ℝ) * a i < x then F m i else 0 := by
    intro m
    rw [Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Finset.sum_filter (s := s) (p := fun m : ℕ => (m : ℝ) * a i < x) (f := fun m => F m i)).symm

noncomputable section

theorem window_bound_act
    (x N Pz Mn : ℕ) (C τ θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (f : Fin K → Fin K' → ℤ → ℝ)
    (c2 c3 : ℝ)
    (hMn : 1 ≤ Mn) (hN : 1 ≤ N) (hP2 : 2 ≤ Pz)
    (ha : ∀ i, (N : ℝ) ≤ a i)
    (hPaM : ∀ i k, (Pa i k).M = (Mn : ℝ))
    (hPaN : ∀ i k, (Pa i k).N = a i)
    (hPaC : ∀ i k, (Pa i k).C = C)
    (hPaPz : ∀ i k, (Pa i k).Pz = Pz)
    (hPaθ : ∀ i k, (Pa i k).θ = θ)
    (hPaτ : ∀ i k, (Pa i k).τ = τ)
    (hp0 : ∀ i u, 0 ≤ p i u) (hp1 : ∀ i u, p i u ≤ 1)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i)
    (hsup2 : ∀ i u, p i u ≠ 0 → u ≤ 2 * (N : ℝ))
    (hq0 : ∀ k α, 0 ≤ q k α) (hq0z : ∀ k, q k 0 = 0)
    (hqsup : ∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hang : ∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1)
    (hpsum : ∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1)
    (hMaj : ∀ i k, Work.FITop3.IsMajorant (Pa i k) (f i k))
    (hT2 : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
                (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
              ∑ w ∈ Work.FITop4.Red5.wSph mm, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
                2 * Work.FITop4.Red5.badInd mm x τ (Work.FIPlan.gnorm z)
                  * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
            ≤ c2 * Work.FITop4.Red5.T2RHS x N Mn Pz θ)
    (hT3 : (∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph mm,
              ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
              Work.FITop4.Red5.cGInd mm N x Pz τ (Work.FIPlan.gnorm z)
                * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
                * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
            ≤ c3 * Work.FITop4.Red5.T3RHS x N Mn θ) :
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), Work.FITop4.Red5.Iterm x N Pz C τ m)
      ≤ (∑ i, ∑ k, Real.sqrt (100 * (Pa i k).M
            * Work.FITop3.Dform (Pa i k) (f i k)
              (Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i))))
        + c2 * Work.FITop4.Red5.T2RHS x N Mn Pz θ + c3 * Work.FITop4.Red5.T3RHS x N Mn θ := by
  classical
  set IccW : Finset ℕ := Finset.Icc (Mn + 1) (2 * Mn) with hIccW
  -- the `T1`-piece of a single `m`
  let G : ℕ → Fin K → ℝ := fun m i =>
    ∑ k, ∑ w ∈ wSph m, ‖∑ z ∈ primAnn (2 * N),
      pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
  -- the `T2`-piece of a single `m`
  let Hh : ℕ → Fin K → ℝ := fun m i =>
    ∑ k, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
      2 * badInd m x τ (Work.FIPlan.gnorm z)
        * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
  -- the `T3`-piece of a single `m`
  let S3 : ℕ → ℝ := fun m =>
    ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
      cGInd m N x Pz τ (Work.FIPlan.gnorm z)
        * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
  -- the `τ`-truncation transfer
  have hPatau : ∀ (i : Fin K) (k : Fin K') n, n ≤ 2 * N →
      (((n.divisors.card : ℕ) : ℝ) ≤ τ) → (((n.divisors.card : ℕ) : ℝ) ≤ (Pa i k).τ) :=
    fun i k n _ h => by rw [hPaτ i k]; exact h
  -- the per-`m` sieve bound
  have hper : ∀ m ∈ IccW, Iterm x N Pz C τ m ≤
      (∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)), G m i)
      + (∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)), Hh m i)
      + S3 m := by
    intro m hm
    have hm' : m ∈ Finset.Icc (Mn + 1) (2 * Mn) := by rwa [hIccW] at hm
    have hm1 : 1 ≤ m := le_trans (by omega) (Finset.mem_Icc.mp hm').1
    have h := sieve_inner_le_pieces_act m x N Pz C τ θ K K' a p φ q Pa hm1 hN hP2 ha
      hPaN hPaC hPaPz hPaθ hPatau hp0 hp1 hpsup hq0 hq0z hqsup hang hpsum
    simpa only [Iterm, G, Hh, S3] using h
  -- sum the per-`m` bound over the window and split the right-hand side
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  -- bound the accumulated `T1`-piece by `window_T1_le` (the active filter is a sub-sum)
  have hGnonneg : ∀ m i, 0 ≤ G m i := by
    intro m i
    simp only [G]
    exact Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun w _ => norm_nonneg _))
  have hT1b : (∑ m ∈ IccW,
        ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)), G m i)
      ≤ ∑ i, ∑ k, Real.sqrt (100 * (Pa i k).M
          * Work.FITop3.Dform (Pa i k) (f i k) (pieceCoeff (Pa i k) (φ k) (q k) (p i))) := by
    have hstep : (∑ m ∈ IccW,
          ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)), G m i)
        ≤ ∑ m ∈ IccW, ∑ i, G m i := by
      apply Finset.sum_le_sum
      intro m hm
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hGnonneg m i)
    refine le_trans hstep ?_
    rw [hIccW]
    simp only [G]
    exact window_T1_le x N Pz Mn C τ θ K K' a p φ q Pa f hN hMn hPaM hPaN ha hsup2 hMaj
  -- bound the accumulated `T2`-piece by the hypothesis `hT2` (reindexing the active filter)
  have hT2b : (∑ m ∈ IccW,
        ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)), Hh m i)
      ≤ c2 * T2RHS x N Mn Pz θ := by
    rw [hIccW]
    rw [sum_filter_swap_univ (Finset.Icc (Mn + 1) (2 * Mn)) a (x : ℝ) Hh]
    have hkey : ∀ i : Fin K,
        (∑ m ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
            (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)), Hh m i)
        = ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
              (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
            ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              2 * badInd mm x τ (Work.FIPlan.gnorm z)
                * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
      intro i
      simp only [Hh]
      rw [Finset.sum_comm]
    simp_rw [hkey]
    exact hT2
  -- the accumulated `T3`-piece is exactly the hypothesis `hT3`
  have hT3b : (∑ m ∈ IccW, S3 m) ≤ c3 * T3RHS x N Mn θ := by
    rw [hIccW]
    simpa only [S3] using hT3
  linarith [hsum, hT1b, hT2b, hT3b]

end

end Work.FITop4.Red5
