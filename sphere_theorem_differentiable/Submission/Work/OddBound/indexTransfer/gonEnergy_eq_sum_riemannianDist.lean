import Mathlib
import Submission.Work.OddBound.indexTransfer.Infra
import Submission.Work.OddBound.PolygonModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The energy of the sampled-loop polygon as a sum of squared `riemannianDist`

For a loop `Φ : ℝ → M` with `Φ 0 = Φ T = p`, the `Work.OddBound.gonEnergy` of the `N`-gon whose
interior vertices are the samples `Φ (T/N), …, Φ ((N-1)·T/N)` unfolds to
`(N/2) · Σ_{i<N} d(Φ(i·T/N), Φ((i+1)·T/N))²`: the vertex list of that gon is exactly
`Φ(0), Φ(T/N), …, Φ((N-1)·T/N), Φ(T)` (the first and last vertices are the base point `p`).
-/

namespace Work.OddBound.indexTransfer

theorem gonEnergy_eq_sum_riemannianDist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {Φ : ℝ → M} {T : ℝ} (hT : 0 < T) {p : M} (h0 : Φ 0 = p) (hTp : Φ T = p)
    {N : ℕ} (hN : 0 < N) :
    Work.OddBound.gonEnergy (I := I) p (fun i : Fin (N - 1) => Φ ((((i : ℕ) : ℝ) + 1) * T / N))
      = (N : ℝ) / 2 * ∑ i : Fin N,
          (Submission.Distance.riemannianDist (I := I) (Φ (((i : ℕ) : ℝ) * T / N))
            (Φ ((((i : ℕ) : ℝ) + 1) * T / N))) ^ 2 := by
  classical
  -- `((N : ℕ) : ℝ) ≠ 0`, so `↑N * T / ↑N = T`.
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := by positivity
  -- The vertex list of the sampled gon: `gonVert p w k = Φ (k * T / N)` for `k ≤ N`.
  have hvert : ∀ k : ℕ, k ≤ N →
      Work.OddBound.gonVert p
        (fun i : Fin (N - 1) => Φ ((((i : ℕ) : ℝ) + 1) * T / N)) k
        = Φ (((k : ℕ) : ℝ) * T / N) := by
    intro k hk
    rcases Nat.lt_or_ge k N with hk' | hk'
    · rcases Nat.eq_zero_or_pos k with rfl | hk1
      · -- vertex `0` is the base point `p = Φ 0`.
        rw [Work.OddBound.gonVert_zero, Nat.cast_zero, zero_mul, zero_div]
        exact h0.symm
      · -- interior vertex `k` is the sample `Φ (k * T / N)`.
        have h2 : k - 1 + 1 = k := by omega
        rw [← h2, Work.OddBound.gonVert_succ p _ (i := k - 1) (by omega)]
        simp only [Nat.cast_add, Nat.cast_one]
    · -- vertex `N` is the base point `p = Φ T = Φ (N * T / N)`.
      have hkN : k = N := by omega
      rw [hkN, Work.OddBound.gonVert_of_le p _ (Nat.le_refl N),
        mul_div_cancel_left₀ T hNne]
      exact hTp.symm
  rw [Work.OddBound.gonEnergy]
  -- The two sums have the same summands: each side length is the distance between
  -- consecutive samples.
  have hsum : ∑ i : Fin N, (Work.OddBound.gonSideLen (I := I) p
      (fun i : Fin (N - 1) => Φ ((((i : ℕ) : ℝ) + 1) * T / N)) i) ^ 2
      = ∑ i : Fin N,
          (Submission.Distance.riemannianDist (I := I) (Φ (((i : ℕ) : ℝ) * T / N))
            (Φ ((((i : ℕ) : ℝ) + 1) * T / N))) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.OddBound.gonSideLen, hvert (i : ℕ) (by omega),
      hvert ((i : ℕ) + 1) (by omega), Nat.cast_add, Nat.cast_one]
  rw [hsum]

end Work.OddBound.indexTransfer
