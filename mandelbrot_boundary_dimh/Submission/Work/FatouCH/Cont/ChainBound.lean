import Mathlib
import Submission.Work.Motion.koebe_distortion
import Submission.Work.FatouCH.Cont.GeomGrowthChain
import Submission.Work.FatouCH.Cont.TelescopeNormLe

namespace Work.FatouCH.Cont

open scoped Topology
open Set Metric

/-- **Uniform Koebe growth along a chain of balls.**

There is a universal constant `C ≥ 1` such that for an injective holomorphic `f` on an open set
`Ω`, and a chain `p 0, …, p N` whose consecutive steps stay within half the radius of a ball
`ball (p i) (R i) ⊆ Ω`, the derivatives grow at most geometrically,
`‖deriv f (p i)‖ ≤ A * C ^ i`, and the total displacement of `f` from `f (p 0)` is bounded by
`A * C ^ (N+1) * (Σ ‖p (i+1) - p i‖ + R N)` — with `A` any upper bound for `‖deriv f (p 0)‖`.

This is the "Koebe chain" estimate: the distortion of an injective holomorphic map between two
points of a disc is at most a universal factor (`koebe_distortion` with the parameter `σ = 1/2`),
and multiplying the distortions along the chain yields the growth constant. -/
theorem ChainBound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Set ℂ} {f : ℂ → ℂ}, IsOpen Ω → DifferentiableOn ℂ f Ω →
      Set.InjOn f Ω → ∀ {p : ℕ → ℂ} {R : ℕ → ℝ} {N : ℕ} {A : ℝ},
      (∀ i ≤ N, 0 < R i) → (∀ i ≤ N, Metric.ball (p i) (R i) ⊆ Ω) →
      (∀ i < N, ‖p (i + 1) - p i‖ ≤ (1 / 2) * R i) → ‖deriv f (p 0)‖ ≤ A →
      (∀ i ≤ N, ‖deriv f (p i)‖ ≤ A * C ^ i) ∧
      (∀ z ∈ Metric.closedBall (p N) ((1 / 2) * R N),
        ‖f z - f (p 0)‖ ≤ A * C ^ (N + 1) * ((∑ i ∈ Finset.range N, ‖p (i + 1) - p i‖) + R N)) := by
  -- The two-sided Koebe distortion bound at the scale of half a ball.
  obtain ⟨c, C₀, hc, hC₀, hcC₀, H⟩ :=
    Work.Motion.koebe_distortion (1 / 2) (by norm_num) (by norm_num)
  -- The universal growth constant: the Koebe distortion factor, but at least `1`.
  set C : ℝ := max C₀ 1 with hCdef
  have hCge1 : 1 ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hCgeC₀ : C₀ ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hCge1
  refine ⟨C, hCge1, ?_⟩
  intro Ω f hΩ hf hinj p R N A hRpos hball hstep hA0
  have hA : 0 ≤ A := le_trans (norm_nonneg _) hA0
  -- Koebe distortion data at each centre of the chain.
  have hK : ∀ i ≤ N, (∀ z ∈ closedBall (p i) ((1 / 2) * R i),
        ‖deriv f z‖ ≤ C₀ * ‖deriv f (p i)‖) ∧
      (∀ u ∈ closedBall (p i) ((1 / 2) * R i), ∀ v ∈ closedBall (p i) ((1 / 2) * R i),
        ‖f u - f v‖ ≤ C₀ * ‖deriv f (p i)‖ * ‖u - v‖) := by
    intro i hi
    obtain ⟨hup, hlip⟩ := H f (p i) (R i) (hRpos i hi) (hf.mono (hball i hi))
      (hinj.mono (hball i hi))
    exact ⟨fun z hz => (hup z hz).2, fun u hu v hv => (hlip u hu v hv).2⟩
  -- Geometric growth of the derivatives along the chain.
  have hder : ∀ i ≤ N, ‖deriv f (p i)‖ ≤ A * C ^ i := by
    refine GeomGrowthChain (u := fun i => ‖deriv f (p i)‖) (C := C) (A := A) hCge1 hA hA0 ?_
    intro i hi
    have hik : i ≤ N := le_of_lt hi
    have hmem : p (i + 1) ∈ closedBall (p i) ((1 / 2) * R i) := by
      rw [mem_closedBall, dist_eq_norm]
      exact hstep i hi
    exact le_trans ((hK i hik).1 (p (i + 1)) hmem)
      (mul_le_mul_of_nonneg_right hCgeC₀ (norm_nonneg _))
  refine ⟨hder, ?_⟩
  intro z hz
  have hRNpos : 0 < R N := hRpos N le_rfl
  have hRN : 0 ≤ R N := hRNpos.le
  have hCN : 0 ≤ C ^ N := pow_nonneg hCpos.le N
  have hdN : ‖deriv f (p N)‖ ≤ A * C ^ N := hder N le_rfl
  have hzdist : ‖z - p N‖ ≤ (1 / 2) * R N := by
    rw [← dist_eq_norm]; exact mem_closedBall.mp hz
  -- The last leg of the chain: from `p N` to `z`.
  have hlast2 : ‖f z - f (p N)‖ ≤ A * C ^ (N + 1) * R N := by
    have hlast : ‖f z - f (p N)‖ ≤ C₀ * ‖deriv f (p N)‖ * ‖z - p N‖ :=
      (hK N le_rfl).2 z hz (p N) (mem_closedBall_self (mul_nonneg (by norm_num) hRN))
    have h1 : C₀ * ‖deriv f (p N)‖ * ‖z - p N‖
        ≤ C₀ * (A * C ^ N) * ((1 / 2) * R N) := by
      have h2 : C₀ * ‖deriv f (p N)‖ ≤ C₀ * (A * C ^ N) :=
        mul_le_mul_of_nonneg_left hdN hC₀.le
      exact mul_le_mul h2 hzdist (norm_nonneg _) (mul_nonneg hC₀.le (mul_nonneg hA hCN))
    have h3 : C₀ * (A * C ^ N) * ((1 / 2) * R N) ≤ A * C ^ (N + 1) * R N := by
      calc C₀ * (A * C ^ N) * ((1 / 2) * R N)
          ≤ C₀ * (A * C ^ N) * R N := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₀.le (mul_nonneg hA hCN))
            linarith
        _ ≤ C * (A * C ^ N) * R N :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCgeC₀ (mul_nonneg hA hCN)) hRN
        _ = A * C ^ (N + 1) * R N := by rw [pow_succ]; ring
    exact le_trans hlast (le_trans h1 h3)
  -- Telescoping over the chain, using the per-step Koebe bound.
  have hstep_bound : ∀ i < N, ‖f (p (i + 1)) - f (p i)‖ ≤ A * C ^ (N + 1) * ‖p (i + 1) - p i‖ := by
    intro i hi
    have hik : i ≤ N := le_of_lt hi
    have hRi : 0 ≤ (1 / 2) * R i := mul_nonneg (by norm_num) (hRpos i hik).le
    have hmem1 : p (i + 1) ∈ closedBall (p i) ((1 / 2) * R i) := by
      rw [mem_closedBall, dist_eq_norm]; exact hstep i hi
    have h1 : ‖f (p (i + 1)) - f (p i)‖ ≤ C₀ * ‖deriv f (p i)‖ * ‖p (i + 1) - p i‖ :=
      (hK i hik).2 (p (i + 1)) hmem1 (p i) (mem_closedBall_self hRi)
    have hd : ‖deriv f (p i)‖ ≤ A * C ^ i := hder i hik
    have hCNi : C ^ i ≤ C ^ N := pow_le_pow_right₀ hCge1 (le_of_lt hi)
    have h2 : C₀ * ‖deriv f (p i)‖ ≤ A * C ^ (N + 1) := by
      refine le_trans (mul_le_mul_of_nonneg_left hd hC₀.le) ?_
      calc C₀ * (A * C ^ i) ≤ C * (A * C ^ i) :=
            mul_le_mul_of_nonneg_right hCgeC₀ (mul_nonneg hA (pow_nonneg hCpos.le i))
        _ = A * C ^ i * C := by ring
        _ ≤ A * C ^ N * C := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCNi hA) hCpos.le
        _ = A * C ^ (N + 1) := by rw [pow_succ]; ring
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have htel : ‖f (p N) - f (p 0)‖
      ≤ A * C ^ (N + 1) * (∑ i ∈ Finset.range N, ‖p (i + 1) - p i‖) := by
    refine le_trans (TelescopeNormLe (g := fun i => f (p i))
      (b := fun i => A * C ^ (N + 1) * ‖p (i + 1) - p i‖) hstep_bound) ?_
    rw [Finset.mul_sum]
  have htri : ‖f z - f (p 0)‖ ≤ ‖f z - f (p N)‖ + ‖f (p N) - f (p 0)‖ := by
    have h := dist_triangle (f z) (f (p N)) (f (p 0))
    simpa [dist_eq_norm] using h
  calc ‖f z - f (p 0)‖ ≤ ‖f z - f (p N)‖ + ‖f (p N) - f (p 0)‖ := htri
    _ ≤ A * C ^ (N + 1) * R N
          + A * C ^ (N + 1) * (∑ i ∈ Finset.range N, ‖p (i + 1) - p i‖) :=
        add_le_add hlast2 htel
    _ = A * C ^ (N + 1) * ((∑ i ∈ Finset.range N, ‖p (i + 1) - p i‖) + R N) := by ring

end Work.FatouCH.Cont
