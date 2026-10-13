import Mathlib
import Submission.Work.WilE3.Lib.exists_analyticAt_pow_eq
import Submission.Work.WilE3.Lib.exists_ball_injOn_image_mem_nhds
import Submission.Work.WilE3.Lib.card_nthRootsFinset_complex

namespace Work.WilE3.Lib

set_option autoImplicit false
open Classical Topology

/-! ## The counting step -/

/-- **One-variable counting step of `E3_identity`** (the "multiplicity = number of simple zeros
of a generic perturbation" fact, in the case actually needed: a single holomorphic germ, or
equivalently a Pfaffian function restricted to a curve).  If `g` is holomorphic at `z₀`, `g z₀ = 0`
and `g` has order exactly `N` at `z₀`, then for every sufficiently small `ε ≠ 0` the level set
`{g = ε}` meets a fixed small disc around `z₀` in exactly `N` points (which are automatically
simple, since a local biholomorphism interchanges `g` with `w ↦ w^N`).

Mathlib has neither Rouché nor the argument principle, but this does not need them: from
`AnalyticAt.analyticOrderAt_eq_natCast` one has `g = (· - z₀)^N * u` with `u` analytic and
`u z₀ ≠ 0` on a small disc; an `N`-th root of `u` exists there, and `w := (· - z₀) * u ^ (1/N)`
satisfies `g = w^N` with `HasStrictFDerivAt`-invertible derivative at `z₀`, so the
`N` preimages of `ε` under `z ↦ z^N` pull back biholomorphically.  (The case `N = 0` is vacuous:
`hg` and `h0` force `analyticOrderAt g z₀ ≠ 0`.) -/
theorem exists_card_solutions_eq_analyticOrderAt {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀)
    (h0 : g z₀ = 0) (N : ℕ) (hord : analyticOrderAt g z₀ = N) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ →
      ∃ s : Finset ℂ, s.card = N ∧ (∀ z ∈ s, g z = ε ∧ ‖z - z₀‖ < r) ∧
        (∀ z : ℂ, g z = ε → ‖z - z₀‖ < r → z ∈ s) := by
  classical
  -- `N ≠ 0`: `g z₀ = 0` forces the order to be nonzero.
  have hN0 : N ≠ 0 := by
    intro hN
    exact (hg.analyticOrderAt_ne_zero.mpr h0) (by simp [hord, hN])
  -- Factor `g = (· - z₀)^N * u` with `u` analytic and `u z₀ ≠ 0`.
  obtain ⟨u, hu, hu0, hgu⟩ := (hg.analyticOrderAt_eq_natCast (n := N)).mp hord
  -- An `N`-th root `v` of `u`.
  obtain ⟨v, hv, hv0, hvu⟩ := exists_analyticAt_pow_eq (N := N) hu hu0 hN0
  -- The local biholomorphism `φ z = (z - z₀) * v z`, with `φ^N = g` near `z₀`.
  set φ : ℂ → ℂ := fun z => (z - z₀) * v z with hφdef
  have hφ0 : φ z₀ = 0 := by rw [hφdef]; simp
  have hφder : HasStrictDerivAt φ (v z₀) z₀ := by
    have hφan : AnalyticAt ℂ φ z₀ := by
      rw [hφdef]; exact (analyticAt_id.sub analyticAt_const).mul hv
    have h := hφan.hasStrictDerivAt
    have hd : deriv φ z₀ = v z₀ := by
      rw [hφdef, deriv_fun_mul]
      · simp
      · fun_prop
      · exact hv.differentiableAt
    rwa [hd] at h
  have hpow : ∀ᶠ z in 𝓝 z₀, g z = φ z ^ N := by
    filter_upwards [hgu] with z hz
    rw [hz, hφdef]
    rw [mul_pow, hvu z, smul_eq_mul]
  obtain ⟨r_an, hr_an, h_an⟩ := Metric.mem_nhds_iff.mp hpow
  -- Local injectivity / openness of `φ` at `z₀`.
  obtain ⟨R, hR, hRprop⟩ := exists_ball_injOn_image_mem_nhds hφder hv0 hφ0
  set r : ℝ := min r_an R / 2 with hrdef
  have hr : 0 < r := by
    rw [hrdef]; have := lt_min hr_an hR; linarith
  have hlt_an : r < r_an := by
    rw [hrdef]; linarith [min_le_left r_an R]
  have hlt_R : r < R := by
    rw [hrdef]; linarith [min_le_right r_an R]
  obtain ⟨hinj, himg⟩ := hRprop r hr hlt_R
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp himg
  have hgφ : ∀ z : ℂ, ‖z - z₀‖ < r → g z = φ z ^ N := by
    intro z hz
    exact h_an (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_trans hz hlt_an)
  refine ⟨r, ρ ^ N, hr, pow_pos hρ N, ?_⟩
  intro ε hε0 hεδ
  have hεne : ε ≠ 0 := norm_pos_iff.mp hε0
  -- The `N`-th roots of `ε`, all of which are within the disc of radius `ρ`.
  set T : Finset ℂ := Polynomial.nthRootsFinset N ε with hT
  have hTcard : T.card = N := card_nthRootsFinset_complex hN0 ε hεne
  have hmem : ∀ x : ℂ, x ∈ T ↔ x ^ N = ε := fun x =>
    Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hN0) ε
  have hw_small : ∀ w ∈ T, ‖w‖ < ρ := by
    intro w hw
    have hwN : w ^ N = ε := (hmem w).mp hw
    have hn : ‖w‖ ^ N = ‖ε‖ := by rw [← norm_pow, hwN]
    have hlt : ‖w‖ ^ N < ρ ^ N := by rw [hn]; exact hεδ
    exact (pow_lt_pow_iff_left₀ (norm_nonneg w) hρ.le hN0).mp hlt
  -- Choose a preimage of every root under `φ`, inside the ball of radius `r`.
  have hpre : ∀ w ∈ T, ∃ z : ℂ, ‖z - z₀‖ < r ∧ φ z = w := by
    intro w hw
    have hwball : w ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; simpa using hw_small w hw
    have hwim : w ∈ φ '' Metric.ball z₀ r := hball hwball
    rw [Set.mem_image] at hwim
    obtain ⟨z, hz, hzφ⟩ := hwim
    exact ⟨z, by rwa [Metric.mem_ball, dist_eq_norm] at hz, hzφ⟩
  let zch : ℂ → ℂ := fun w => if hw : w ∈ T then Classical.choose (hpre w hw) else w
  have zch_mem : ∀ w (hw : w ∈ T), ‖zch w - z₀‖ < r := by
    intro w hw
    have heq : zch w = Classical.choose (hpre w hw) := dite_eq_left hw
    rw [heq]
    exact (Classical.choose_spec (hpre w hw)).1
  have zch_φ : ∀ w (hw : w ∈ T), φ (zch w) = w := by
    intro w hw
    have heq : zch w = Classical.choose (hpre w hw) := dite_eq_left hw
    rw [heq]
    exact (Classical.choose_spec (hpre w hw)).2
  have zch_inj : Set.InjOn zch (T : Set ℂ) := by
    intro w hw w' hw' h
    rw [← zch_φ w hw, h, zch_φ w' hw']
  refine ⟨T.image zch, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn zch_inj, hTcard]
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_image.mp hz
    rw [← hzw]
    exact ⟨by rw [hgφ (zch w) (zch_mem w hw), zch_φ w hw, (hmem w).mp hw], zch_mem w hw⟩
  · intro z hz hzr
    rw [Finset.mem_image]
    have h1 : φ z ^ N = g z := (hgφ z hzr).symm
    have hzT : φ z ∈ T := (hmem (φ z)).mpr (by rw [h1, hz])
    refine ⟨φ z, hzT, ?_⟩
    have h2 : φ (zch (φ z)) = φ z := zch_φ (φ z) hzT
    have h3 : ‖zch (φ z) - z₀‖ < r := zch_mem (φ z) hzT
    exact hinj (by rw [Metric.mem_ball, dist_eq_norm]; exact h3)
      (by rw [Metric.mem_ball, dist_eq_norm]; exact hzr) h2

end Work.WilE3.Lib
