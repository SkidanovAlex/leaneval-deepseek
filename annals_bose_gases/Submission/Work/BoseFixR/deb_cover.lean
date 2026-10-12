import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.DebAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open Metric

/-- **The six-ball cover.**  If `u` is within `‖u‖/3` of the lattice `ℓℤ³` and `‖u‖ < 2R < ℓ`,
then `u` lies in one of the six balls of radius `ℓ/2` centred at `±ℓ eᵢ`.

Indeed the nearby lattice point `lat ℓ n` satisfies `‖lat ℓ n‖ ≤ ‖u‖ + ‖u‖/3 < 4ℓ/3`, so its label
`n ≠ 0` has `‖lat1 n‖ < 4/3`, whence `n = ±eᵢ` (`deb_lat1_classify`); and
`dist u (lat ℓ n) < ‖u‖/3 < ℓ/3 < ℓ/2`. -/
theorem deb_cover {ℓ R : ℝ} (hℓ : 0 < ℓ) (h2R : 2 * R < ℓ)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : Metric.infDist u (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) < ‖u‖ / 3)
    (hu2 : ‖u‖ < 2 * R) :
    ∃ i : Fin 3, u ∈ Metric.ball (Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ))) (ℓ / 2)
      ∨ u ∈ Metric.ball (-(Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ)))) (ℓ / 2) := by
  have hne : (Set.range (fun n : Fin 3 → ℤ => lat ℓ n)).Nonempty :=
    ⟨0, 0, lat_zero ℓ⟩
  obtain ⟨y, ⟨n, rfl⟩, hdist⟩ := (Metric.infDist_lt_iff hne).mp hu
  have hdist' : ‖u - lat ℓ n‖ < ‖u‖ / 3 := by rwa [dist_eq_norm] at hdist
  -- `‖u‖ > 0`
  have hu_pos : 0 < ‖u‖ := by
    have h0 : (0 : ℝ) ≤ ‖u - lat ℓ n‖ := norm_nonneg _
    linarith
  -- `‖u‖ < ℓ`
  have huld : ‖u‖ < ℓ := by linarith
  -- the nearby lattice point is nonzero
  have hvnz : lat ℓ n ≠ 0 := by
    intro h0
    have : ‖u‖ < ‖u‖ / 3 := by
      have h := hdist'
      rwa [h0, sub_zero] at h
    linarith
  have hnz : n ≠ 0 := fun h => hvnz (by rw [h, lat_zero])
  -- the nearby lattice point has norm `< 4ℓ/3`
  have hlt : ‖lat ℓ n‖ < 4 * ℓ / 3 := by
    have hb : ‖lat ℓ n‖ ≤ ‖lat ℓ n - u‖ + ‖u‖ := by
      simpa using norm_add_le (lat ℓ n - u) u
    rw [norm_sub_rev] at hb
    linarith
  have hnorm1 : ‖lat1 n‖ < 4 / 3 := by
    rw [deb_norm_lat hℓ.le n] at hlt
    nlinarith [hlt, hℓ]
  -- classify the label
  obtain ⟨i, hi | hi⟩ := deb_lat1_classify hnz hnorm1
  · refine ⟨i, Or.inl ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    rw [hi] at hdist'
    linarith
  · refine ⟨i, Or.inr ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    rw [hi, deb_lat_single_neg] at hdist'
    have hfin := lt_trans hdist' (by linarith : ‖u‖ / 3 < ℓ / 2)
    simpa [debLC] using hfin

end Work.BoseFixR
