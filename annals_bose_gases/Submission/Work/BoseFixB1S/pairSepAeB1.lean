import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.pairVoidAeB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

theorem pairSepAeB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r ⊆ Function.support v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRℓ : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.pairSum v M ℓ d u Φ = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → ∀ i j : Fin n, i ≠ j →
        Submission.BoseGases.chiSmallB M ℓ d u (x i) ≠ 0 →
        Submission.BoseGases.chiSmallB M ℓ d u (x j) ≠ 0 → r ≤ dist (x i) (x j) := by
  -- The pointwise vanishing form of the pairing word (`pairVoidAeB1`) is the whole content:
  -- `pairSum = 0` forces the localised kernel `χ_{B(u)}(xᵢ) v(xᵢ - xⱼ) χ_{B(u)}(xⱼ)` to vanish
  -- a.e.  The hypothesis `hball` (the potential is nonzero on the whole ball of radius `r`) then
  -- turns that into the separation statement: a pair at distance `< r` would have `v ≠ 0`, hence a
  -- nonvanishing kernel.
  filter_upwards [pairVoidAeB1 h hv hv1 hR hv_supp hM hℓ hd hRℓ hRχ hden hΦc hpair] with x hx
  intro hΦne i j hij hxi hxj
  by_contra hcon
  -- `dist (x i) (x j) < r`
  have hlt : dist (x i) (x j) < r := not_le.mp hcon
  -- so `x i - x j` lies in the ball of radius `r`, where `v` does not vanish
  have hvne : v (x i - x j) ≠ 0 := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    rwa [dist_eq_norm] at hlt
  -- but the kernel of the pair `(i, j)` vanishes at `x`
  have h0 := hx hΦne i j hij
  have h1 : Submission.BoseGases.chiSmallB M ℓ d u (x i) * v (x i - x j) = 0 :=
    (mul_eq_zero.mp h0).resolve_right hxj
  exact hvne ((mul_eq_zero.mp h1).resolve_left hxi)

end Work.BoseFixB1S
