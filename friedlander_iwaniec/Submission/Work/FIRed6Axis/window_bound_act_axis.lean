import Mathlib
import Submission.Work.FIRed6Axis.Statement
import Submission.Work.FITop4.Red5.window_bound_act
import Submission.Work.FITop4.Red5.sieve_inner_le_pieces_act
import Submission.Work.FITop4.Red5.assembly_helpers

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators
open Work.FITop4.Red5

attribute [local instance] Classical.propDecidable

/-- **The per-window far/near split** (`Work.FIRed6Axis.WindowAxisBound`, unfold it), from the
restricted `T1` Cauchy step (`FarT1Bound`) and the (5.16) near bound (`NearAxisBound`).  This is
`Work.FITop4.Red5.window_bound_act` (`Submission/Work/FITop4/Red5/window_bound_act.lean`) with one
change: the per-`m` sieve bound `sieve_inner_le_pieces_act` is split at the angular index `k` before
the Cauchy step.  Concretely, for each `m ∈ (Mn, 2Mn]`:
`Iterm ≤ (T1 restricted to k ∉ S) + (T1 restricted to k ∈ S) + (T2 restricted to k ∉ S)
+ (T2 restricted to k ∈ S) + T3`; sum over the window, bound the `k ∉ S` parts by `hT1` (the `T1`
part) and by `hT2` (the `T2` part: its summand is nonnegative, so the restricted sum is at most the
full one, which `hT2` bounds), the `k ∈ S` parts by `hNear` (after moving the `m`-sum inside, using
that the LHS of `NearAxisBound` has no "active-`i`" filter), and the `T3` term by `hT3`.  The near
term `Cnear·(Mn)^{3/4}N^{-1/4}(ϑN+√N+N^{5/6}+N^{2/3}+1)(log(2+N))^{20}` is exactly `NearAxisBound`'s
right-hand side. -/
theorem window_bound_act_axis (hT1 : Work.FIRed6Axis.FarT1Bound)
    (hNear : Work.FIRed6Axis.NearAxisBound) : Work.FIRed6Axis.WindowAxisBound := by
  classical
  unfold Work.FIRed6Axis.WindowAxisBound
  obtain ⟨Cnear, hCnear_pos, hNearBound⟩ := hNear
  refine ⟨Cnear, hCnear_pos, ?_⟩
  intro x N Pz Mn C τ θ ϑ K K' a p φ q Pa f S c2 c3
    hMn hN hP2 hθpos hθle hϑpos hϑle h4pic hNM ha_le hPaM hPaN hPaC hPaPz hPaθ hPaτ
    hp0 hp1 hpsup hsup2 hq0 hq0z hqsup hang hpsum hMaj hT2 hT3 hnear
  set IccW : Finset ℕ := Finset.Icc (Mn + 1) (2 * Mn) with hIccW
  set FarS : Finset (Fin K') := (Finset.univ : Finset (Fin K')).filter (fun k => k ∉ S) with hFarS
  -- the split of a `k`-sum into its far and near parts
  have ks : ∀ g : Fin K' → ℝ, (∑ k, g k) = (∑ k ∈ FarS, g k) + ∑ k ∈ S, g k := by
    intro g
    rw [hFarS]
    rw [show (Finset.univ : Finset (Fin K')).filter (fun k => k ∉ S) = Finset.univ \ S from by
      rw [Finset.sdiff_eq_filter]]
    exact (Finset.sum_sdiff (Finset.subset_univ S)).symm
  -- the `τ`-transfer used by `sieve_inner_le_pieces_act`
  have hPatau : ∀ (i : Fin K) (k : Fin K') n, n ≤ 2 * N →
      (((n.divisors.card : ℕ) : ℝ) ≤ τ) → (((n.divisors.card : ℕ) : ℝ) ≤ (Pa i k).τ) :=
    fun i k n _ h => by rw [hPaτ i k]; exact h
  -- the five pieces of the per-`m` right-hand side
  let P1f : ℕ → ℝ := fun m =>
    ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
      ∑ k ∈ FarS, ∑ w ∈ wSph m,
        ‖∑ z ∈ primAnn (2 * N),
          pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
  let P1n : ℕ → ℝ := fun m =>
    ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
      ∑ k ∈ S, ∑ w ∈ wSph m,
        ‖∑ z ∈ primAnn (2 * N),
          pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
  let P2f : ℕ → ℝ := fun m =>
    ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
      ∑ k ∈ FarS, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
        2 * badInd m x τ (Work.FIPlan.gnorm z)
          * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
  let P2n : ℕ → ℝ := fun m =>
    ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
      ∑ k ∈ S, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
        2 * badInd m x τ (Work.FIPlan.gnorm z)
          * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
  let S3 : ℕ → ℝ := fun m =>
    ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
      cGInd m N x Pz τ (Work.FIPlan.gnorm z)
        * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
  -- (1) the per-`m` sieve bound, split at the angular index
  have hper : ∀ m ∈ IccW, Iterm x N Pz C τ m ≤ ((P1f m + P1n m) + (P2f m + P2n m)) + S3 m := by
    intro m hm
    have hmI : m ∈ Finset.Icc (Mn + 1) (2 * Mn) := by rwa [hIccW] at hm
    have hm1 : 1 ≤ m := le_trans (by omega) (Finset.mem_Icc.mp hmI).1
    have h := sieve_inner_le_pieces_act m x N Pz C τ θ K K' a p φ q Pa hm1 hN hP2 ha_le
      hPaN hPaC hPaPz hPaθ hPatau hp0 hp1 hpsup hq0 hq0z hqsup hang hpsum
    have eT1 : (∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
          ∑ k, ∑ w ∈ wSph m,
            ‖∑ z ∈ primAnn (2 * N),
              pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        = P1f m + P1n m := by
      simp only [P1f, P1n]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact ks (fun k => ∑ w ∈ wSph m,
        ‖∑ z ∈ primAnn (2 * N),
          pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
    have eT2 : (∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
          ∑ k, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
            2 * badInd m x τ (Work.FIPlan.gnorm z)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        = P2f m + P2n m := by
      simp only [P2f, P2n]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact ks (fun k => ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
        2 * badInd m x τ (Work.FIPlan.gnorm z)
          * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
    have eT3 : (∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
          cGInd m N x Pz τ (Work.FIPlan.gnorm z)
            * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) = S3 m := rfl
    rw [eT1, eT2, eT3] at h
    simpa only [Iterm] using h
  -- (2) the far `T1` part, via the restricted Cauchy step
  have hT1f : (∑ m ∈ IccW, P1f m)
      ≤ ∑ i, ∑ k ∈ FarS, Real.sqrt (100 * (Pa i k).M
          * Work.FITop3.Dform (Pa i k) (f i k)
              (pieceCoeff (Pa i k) (φ k) (q k) (p i))) := by
    have hstep : (∑ m ∈ IccW, P1f m)
        ≤ ∑ m ∈ IccW, ∑ i, ∑ k ∈ FarS, ∑ w ∈ wSph m,
            ‖∑ z ∈ primAnn (2 * N),
              pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
      apply Finset.sum_le_sum
      intro m hm
      simp only [P1f]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun w _ => norm_nonneg _)))
    refine le_trans hstep ?_
    rw [hIccW]
    exact hT1 x N Pz Mn C τ θ K K' a p φ q Pa f FarS hN hMn hPaM hPaN ha_le hsup2 hMaj
  -- (3) the far `T2` part, via the full-family `T2` hypothesis and monotonicity in `k`
  have hT2f : (∑ m ∈ IccW, P2f m) ≤ c2 * T2RHS x N Mn Pz θ := by
    have hQ : (∑ m ∈ IccW, P2f m)
        ≤ ∑ m ∈ IccW, ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
            ∑ k, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
              2 * badInd m x τ (Work.FIPlan.gnorm z)
                * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
      apply Finset.sum_le_sum
      intro m hm
      simp only [P2f]
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun k _ _ => Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun z _ =>
          mul_nonneg (mul_nonneg (by norm_num) (badInd_nonneg m x τ _)) (norm_nonneg _))))
    refine le_trans hQ ?_
    rw [hIccW]
    rw [sum_filter_swap_univ (Finset.Icc (Mn + 1) (2 * Mn)) a (x : ℝ) (fun m i =>
        ∑ k, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
          2 * badInd m x τ (Work.FIPlan.gnorm z)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)]
    have hkey : ∀ i : Fin K,
        (∑ m ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
            ∑ k, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
              2 * badInd m x τ (Work.FIPlan.gnorm z)
                * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
          = ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
              ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
                2 * badInd mm x τ (Work.FIPlan.gnorm z)
                  * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
      intro i
      rw [Finset.sum_comm]
    simp_rw [hkey]
    exact hT2
  -- (4) the near part, via the (5.16) near bound (the active-`i` filter is dropped)
  have hNearLe : (∑ m ∈ IccW, P1n m) + (∑ m ∈ IccW, P2n m)
      ≤ Cnear * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
          * (ϑ * (N : ℝ) + Real.sqrt (N : ℝ) + (N : ℝ) ^ ((5 : ℝ) / 6)
              + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ) := by
    have hNearApp := hNearBound x N Pz Mn C τ θ ϑ K K' a p φ q Pa S
      hMn hN hθpos hθle hϑpos hϑle h4pic hNM ha_le hPaN hp0 hpsup hpsum hq0 hqsup hang hnear
    refine le_trans ?_ hNearApp
    rw [← Finset.sum_add_distrib]
    rw [hIccW]
    apply Finset.sum_le_sum
    intro m hm
    have eN : P1n m + P2n m
        = ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
            ∑ k ∈ S, ∑ w ∈ wSph m,
              (‖∑ z ∈ primAnn (2 * N),
                  pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
                + ∑ z ∈ primAnn (2 * N),
                    2 * badInd m x τ (Work.FIPlan.gnorm z)
                      * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) := by
      simp only [P1n, P2n, Finset.sum_add_distrib]
    rw [eN]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun w _ =>
        add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun z _ =>
          mul_nonneg (mul_nonneg (by norm_num) (badInd_nonneg m x τ _)) (norm_nonneg _))))))
  -- (5) the `T3` part is exactly the hypothesis
  have hT3f : (∑ m ∈ IccW, S3 m) ≤ c3 * T3RHS x N Mn θ := by
    rw [hIccW]
    simpa only [S3] using hT3
  -- (6) sum the per-`m` bound and assemble
  have hsum := Finset.sum_le_sum hper
  simp only [Finset.sum_add_distrib] at hsum
  linarith [hsum, hT1f, hT2f, hNearLe, hT3f]

end Work.FIRed6Axis
