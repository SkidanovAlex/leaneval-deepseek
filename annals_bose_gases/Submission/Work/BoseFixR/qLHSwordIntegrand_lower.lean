import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.PerBoxCrudeB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

theorem qLHSwordIntegrand_lower {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) {μ : ℝ} (hμ : 0 ≤ μ) {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ}
    {Cf : ℝ} (hCf : 0 ≤ Cf)
    (hfib : ∀ z : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z|
        ≤ Cf * Submission.BoseGases.chiSmallB M ℓ d u z)
    (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    (Φ x) ^ 2 * (- (μ * Cf) * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)))
      ≤ (Φ x) ^ 2 * (- μ * (∑ i : Fin n,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))) := by
  -- `(Φ x)² ≥ 0`, so it suffices to prove the bracket inequality.
  have hΦ : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
  -- the pair term is a sum of nonnegative kernels.
  have hpair : 0 ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
      Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) :=
    Finset.sum_nonneg fun p _ =>
      Work.BoseFixB1S.wSmallPair_nonneg hv M ℓ d u (x p.1) (x p.2)
  -- the fibre bound summed over the particles.
  have hsum : (∑ i : Fin n,
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      ≤ Cf * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (abs_le.mp (hfib (x i))).2
  have h1 : - (μ * Cf) * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ - μ * (∑ i : Fin n,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)) := by
    have h2 : -μ * (Cf * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)))
        ≤ -μ * (∑ i : Fin n,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)) :=
      mul_le_mul_of_nonpos_left hsum (by linarith)
    calc - (μ * Cf) * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
        = -μ * (Cf * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))) := by ring
      _ ≤ _ := h2
  have h3 : - (μ * Cf) * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ - μ * (∑ i : Fin n,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) := by
    have : 0 ≤ (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) := by linarith
    linarith
  exact mul_le_mul_of_nonneg_left h3 hΦ

end Work.BoseFixR
