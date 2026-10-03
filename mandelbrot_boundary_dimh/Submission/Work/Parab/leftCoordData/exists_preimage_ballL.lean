import Mathlib
import Submission.Work.Transfer.exists_zero_of_norm_lower_bound

namespace Work.Parab.leftCoordData

/-- **Existence of a preimage of `w` under `Φ` inside `L`.**

The function `ζ ↦ Φ ζ` is uniformly `1/32`-close on `L` (away from the origin) to the
"abelian" model `ζ ↦ ζ - a log(-ζ)`.  The point `c` is the model-preimage of `w` up to the
error `a (log(-w) - log(-c))`, which is `≤ 1/32`.  Hence the holomorphic function
`g ζ = Φ ζ - w` satisfies `‖g c‖ < 1/16` at the centre of the disc `B(c, 1/2)` while on its
boundary sphere `‖g‖ > 7/16 > 1/8`: the minimum modulus principle
(`Work.Transfer.exists_zero_of_norm_lower_bound`, i.e. the maximum modulus principle applied
to `g⁻¹`) then produces a zero of `g`. -/
theorem exists_preimage_ballL {Φ : ℂ → ℂ} {L : Set ℂ} {a w c : ℂ} {R : ℝ}
    (hL : Metric.closedBall c 1 ⊆ L)
    (hΦ : DifferentiableOn ℂ Φ L)
    (hc : c = w + a * Complex.log (-w))
    (herror : ∀ ζ ∈ L, R < ‖ζ‖ → ‖Φ ζ - (ζ - a * Complex.log (-ζ))‖ < 1 / 32)
    (hRball : ∀ ζ ∈ Metric.closedBall c (1 / 2), R < ‖ζ‖)
    (hlogb : ‖a * (Complex.log (-w) - Complex.log (-c))‖ ≤ 1 / 32)
    (hlogb' : ∀ ζ ∈ Metric.sphere c (1 / 2), ‖a * (Complex.log (-w) - Complex.log (-ζ))‖ ≤ 1 / 32) :
    ∃ ζ ∈ L, Φ ζ = w := by
  -- The disc `B(c, 1/2)` sits inside `L`.
  have hsub : Metric.closedBall c (1 / 2) ⊆ L :=
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) / 2 ≤ 1)).trans hL
  have hcc : c ∈ Metric.closedBall c (1 / 2) := Metric.mem_closedBall_self (by norm_num)
  -- The function `g ζ = Φ ζ - w` is holomorphic on the disc.
  have hg : DiffContOnCl ℂ (fun ζ => Φ ζ - w) (Metric.closedBall c (1 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact (hΦ.mono hsub).sub_const w
  -- `‖g c‖ < 1/16`: at the centre the model error is at most `1/32` and the log-error at most `1/32`.
  have hcenter : ‖Φ c - w‖ < (1 / 8 : ℝ) / 2 := by
    have hAc : ‖Φ c - (c - a * Complex.log (-c))‖ < 1 / 32 :=
      herror c (hsub hcc) (hRball c hcc)
    have hdec : Φ c - w
        = (Φ c - (c - a * Complex.log (-c))) + a * (Complex.log (-w) - Complex.log (-c)) := by
      rw [hc]; ring
    rw [hdec]
    have h := norm_add_le (Φ c - (c - a * Complex.log (-c)))
      (a * (Complex.log (-w) - Complex.log (-c)))
    have hlt : ‖Φ c - (c - a * Complex.log (-c))‖
        + ‖a * (Complex.log (-w) - Complex.log (-c))‖ < 1 / 32 + 1 / 32 := by linarith
    linarith
  -- On the boundary sphere `‖g‖ ≥ 1/8` (in fact `> 7/16`).
  have hsphere : ∀ z ∈ Metric.sphere c (1 / 2), (1 / 8 : ℝ) ≤ ‖Φ z - w‖ := by
    intro z hz
    have hzball : z ∈ Metric.closedBall c (1 / 2) := Metric.sphere_subset_closedBall hz
    have hAz : ‖Φ z - (z - a * Complex.log (-z))‖ < 1 / 32 :=
      herror z (hsub hzball) (hRball z hzball)
    have hBz : ‖a * (Complex.log (-w) - Complex.log (-z))‖ ≤ 1 / 32 := hlogb' z hz
    have hzc : ‖z - c‖ = 1 / 2 := by
      have h := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm] at h
    have hAeq : (z - a * Complex.log (-z)) - w
        = (z - c) + a * (Complex.log (-w) - Complex.log (-z)) := by
      rw [hc]; ring
    have hAbig : 15 / 32 ≤ ‖(z - a * Complex.log (-z)) - w‖ := by
      rw [hAeq]
      have h := norm_sub_le_norm_add (z - c) (a * (Complex.log (-w) - Complex.log (-z)))
      rw [hzc] at h
      linarith
    have hdec : Φ z - w
        = ((z - a * Complex.log (-z)) - w) + (Φ z - (z - a * Complex.log (-z))) := by ring
    rw [hdec]
    have h := norm_sub_le_norm_add ((z - a * Complex.log (-z)) - w)
      (Φ z - (z - a * Complex.log (-z)))
    linarith
  obtain ⟨z, hzmem, hzw⟩ :=
    Work.Transfer.exists_zero_of_norm_lower_bound (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 8) hg hsphere hcenter
  exact ⟨z, hsub hzmem, sub_eq_zero.mp hzw⟩

end Work.Parab.leftCoordData
