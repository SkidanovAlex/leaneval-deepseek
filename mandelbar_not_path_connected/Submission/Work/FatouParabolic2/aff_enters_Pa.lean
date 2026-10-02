import Mathlib
import Submission.Work.FatouParabolic2.AffineConj
import Submission.Work.FatouParabolic2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

noncomputable section

/-- **The `enters` property transports along an affine chart.**  Let `pd` be petal data for the
fixed point `0` of `f` with `pd.Pa ⊆ Metric.ball 0 r`, and let `F` be the affine conjugate of `f`
at `z₀` with scale `lam ≠ 0` on that ball.  Then every `F`-orbit which converges to `z₀` without
ever attaining `z₀` meets the transported petal `aff z₀ lam '' pd.Pa`. -/
theorem aff_enters_Pa {f F : ℂ → ℂ} {z₀ lam : ℂ} {r : ℝ}
    (pd : PetalData f 0) (hlam : lam ≠ 0) (hPa : pd.Pa ⊆ Metric.ball 0 r)
    (hconj : ∀ u : ℂ, u ∈ Metric.ball 0 r → f u = (F (z₀ + lam * u) - z₀) / lam)
    {z : ℂ} (hz : Filter.Tendsto (fun n : ℕ => F^[n] z) Filter.atTop (nhds z₀))
    (hne : ∀ n : ℕ, F^[n] z ≠ z₀) :
    ∃ n : ℕ, F^[n] z ∈ aff z₀ lam '' pd.Pa := by
  -- the petal is nonempty, hence the ball of the chart is nonempty and `r > 0`
  have hr : 0 < r := by
    obtain ⟨x, hx⟩ := pd.nonempty
    have h : dist x 0 < r := Metric.mem_ball.mp (hPa hx)
    rw [dist_zero_right] at h
    exact lt_of_le_of_lt (norm_nonneg x) h
  -- the `u`-coordinates of the `F`-orbit: `u n = (F^[n] z - z₀) / lam`
  set u : ℕ → ℂ := fun n => affInv z₀ lam (F^[n] z) with hu
  have hu_eq : ∀ n : ℕ, u n = affInv z₀ lam (F^[n] z) := fun n => by rw [hu]
  -- `u` tends to `0` because the chart inverse is continuous and fixes `z₀ ↦ 0`
  have hu_tend : Filter.Tendsto u Filter.atTop (nhds (0 : ℂ)) := by
    have h3 : Filter.Tendsto (fun n : ℕ => affInv z₀ lam (F^[n] z)) Filter.atTop
        (nhds (affInv z₀ lam z₀)) :=
      ((continuous_affInv z₀ lam).tendsto z₀).comp hz
    rw [affInv_self, ← hu] at h3
    exact h3
  -- hence eventually the whole `u`-orbit lies in the ball on which `f` and `F` are conjugate
  have hEventually : ∀ᶠ n in Filter.atTop, u n ∈ Metric.ball 0 r :=
    hu_tend.eventually (Metric.ball_mem_nhds 0 hr)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventually
  -- on that tail, the `u`-coordinates follow the `f`-dynamics
  have hstep : ∀ n : ℕ, N ≤ n → f (u n) = u (n + 1) := by
    intro n hn
    have hmem : u n ∈ Metric.ball 0 r := hN n hn
    have h1 : z₀ + lam * u n = F^[n] z := by
      have hh : aff z₀ lam (u n) = F^[n] z := by
        rw [hu_eq n]; exact aff_affInv z₀ lam hlam (F^[n] z)
      exact hh
    rw [hconj (u n) hmem, h1, hu_eq (n + 1)]
    simp only [affInv, Function.iterate_succ_apply']
  -- consequently `f^[k] (u N) = u (N + k)` for all `k`
  have hiter : ∀ k : ℕ, f^[k] (u N) = u (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hstep (N + k) (Nat.le_add_right N k)]
      rfl
  -- the `f`-orbit of `u N` converges to `0` and never attains it
  have hEnters_tend : Filter.Tendsto (fun k : ℕ => f^[k] (u N)) Filter.atTop
      (nhds (0 : ℂ)) := by
    have hshift : Filter.Tendsto (fun k : ℕ => u (N + k)) Filter.atTop (nhds (0 : ℂ)) := by
      have h := (Filter.tendsto_add_atTop_iff_nat (f := u) N).mpr hu_tend
      simpa [Nat.add_comm] using h
    simpa [hiter] using hshift
  have hEnters_ne : ∀ k : ℕ, f^[k] (u N) ≠ 0 := by
    intro k
    rw [hiter k, hu_eq (N + k)]
    simp only [affInv]
    exact div_ne_zero (sub_ne_zero.mpr (hne (N + k))) hlam
  -- so `pd.enters_Pa` produces a `k` with `f^[k] (u N) ∈ pd.Pa`, i.e. its `aff`-image is an
  -- iterate of `z` lying in the transported petal
  obtain ⟨k, hk⟩ := pd.enters_Pa (u N) hEnters_tend hEnters_ne
  refine ⟨N + k, ?_⟩
  refine ⟨f^[k] (u N), hk, ?_⟩
  rw [hiter k]
  have h1 : aff z₀ lam (u (N + k)) = F^[N + k] z := by
    rw [hu_eq (N + k)]; exact aff_affInv z₀ lam hlam (F^[N + k] z)
  exact h1

end

end Work.FatouParabolic2
