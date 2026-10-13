import Mathlib
import Submission.Work.WilE3.Lib.exists_analyticAt_pow_eq
import Submission.Work.WilE3.Lib.exists_ball_injOn_image_mem_nhds

namespace Work.WilE3.Taylor.Arc

/-- **Fibres of `z ↦ z ^ a * v z` are locally of size at most `a`.**

If `v` is analytic at `0` with `v 0 ≠ 0` and `a ≠ 0`, then there is a neighbourhood of `0`
on which every level set `{z | z ^ a * v z = p}` has at most `a` points.

Indeed, `v` has an analytic `a`-th root `u` near `0` (`Work.WilE3.Lib.exists_analyticAt_pow_eq`),
so `z ^ a * v z = φ z ^ a` for the analytic germ `φ z = z * u z`, which has `φ 0 = 0` and
`φ' (0) = u 0 ≠ 0` and is therefore locally injective.  Hence a fibre of `z ↦ z ^ a * v z`
maps injectively into the `a`-th roots of `p`, of which there are at most `a`. -/
theorem fibre_card_le {a : ℕ} (ha : 0 < a) {v : ℂ → ℂ} (hv : AnalyticAt ℂ v 0) (hv0 : v 0 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℂ, ∀ s : Finset ℂ,
      (∀ z ∈ s, ‖z‖ < δ ∧ z ^ a * v z = p) → s.card ≤ a := by
  classical
  -- An analytic `a`-th root of `v` near `0`.
  obtain ⟨u, hu, hu0, huv⟩ := Work.WilE3.Lib.exists_analyticAt_pow_eq (N := a) hv hv0 ha.ne'
  -- The local biholomorphism `φ z = z * u z`, with `φ ^ a = (· ^ a * v ·)`.
  set φ : ℂ → ℂ := fun z => z * u z with hφdef
  have hφ0 : φ 0 = 0 := by rw [hφdef]; simp
  have hφ_an : AnalyticAt ℂ φ 0 := by
    rw [hφdef]; exact analyticAt_id.mul hu
  have hderiv : deriv φ 0 = u 0 := by
    rw [hφdef, deriv_fun_mul]
    · simp
    · fun_prop
    · exact hu.differentiableAt
  have hφder : HasStrictDerivAt φ (u 0) 0 := by
    rw [← hderiv]; exact hφ_an.hasStrictDerivAt
  obtain ⟨R, hR, hRprop⟩ := Work.WilE3.Lib.exists_ball_injOn_image_mem_nhds hφder hu0 hφ0
  refine ⟨R / 2, by linarith, ?_⟩
  intro p s hs
  have hhalf : (0 : ℝ) < R / 2 := by linarith
  have hlt : R / 2 < R := by linarith
  have hinj : Set.InjOn φ (Metric.ball (0 : ℂ) (R / 2)) := (hRprop (R / 2) hhalf hlt).1
  -- `s` lies in the ball of injectivity.
  have hs_ball : (s : Set ℂ) ⊆ Metric.ball (0 : ℂ) (R / 2) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact (hs z hz).1
  have hinj_s : Set.InjOn φ (↑s : Set ℂ) := hinj.mono hs_ball
  -- Injectivity transfers the count to the image, which lands in the `a`-th roots of `p`.
  have hcard : (s.image φ).card = s.card := Finset.card_image_of_injOn hinj_s
  have hsub : s.image φ ⊆ Polynomial.nthRootsFinset a p := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    rw [Polynomial.mem_nthRootsFinset ha p]
    calc (z * u z) ^ a = z ^ a * u z ^ a := by rw [mul_pow]
      _ = z ^ a * v z := by rw [huv z]
      _ = p := (hs z hz).2
  have hbound : (Polynomial.nthRootsFinset a p).card ≤ a := by
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots a p)
  have := Finset.card_le_card hsub
  omega

end Work.WilE3.Taylor.Arc
