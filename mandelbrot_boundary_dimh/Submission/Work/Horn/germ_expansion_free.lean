import Mathlib

namespace Work.Horn

/-- Cycle-free copy of `Work.Horn.exists_germ_expansion_of_flat` (that file imports
`Work.Horn.horn_germ_F0`, so `horn_germ_F0` itself cannot use it).  If a holomorphic germ
`g` at `0` has a vanishing second jet (`g 0 = 0`, `g'(0) = 1`, `g''(0) = 0`) and is not
eventually the identity, then the first non-trivial Taylor term is `a · z^(q+1)` with `q ≥ 2`,
`a ≠ 0`, and the remainder is `o(z^(q+1))`. -/
theorem germ_expansion_free {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ)) (hg0 : g 0 = 0)
    (hg1 : deriv g 0 = 1) (hg2 : deriv (deriv g) 0 = 0)
    (hnz : ¬ ∀ᶠ ζ in nhds 0, g ζ = ζ) :
    ∃ q : ℕ, 2 ≤ q ∧ ∃ a : ℂ, a ≠ 0 ∧
      Filter.Tendsto (fun z : ℂ => (g z - z - a * z ^ (q + 1)) / z ^ (q + 1))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  -- `F = g - id` is analytic at `0` and has a vanishing second jet.
  let F : ℂ → ℂ := fun z : ℂ => g z - z
  have hgan : AnalyticAt ℂ g 0 := hg.analyticAt (Metric.ball_mem_nhds 0 hρ)
  have hF : F = (g - id) := rfl
  have hFan : AnalyticAt ℂ F 0 := by rw [hF]; exact hgan.sub analyticAt_id
  have hiter3 : ∀ i < 3, iteratedDeriv i F 0 = 0 := by
    intro i hi
    interval_cases i
    · simp [F, iteratedDeriv_zero, hg0]
    · rw [hF, iteratedDeriv_sub (n := 1) (f := g) (g := id) hgan.contDiffAt analyticAt_id.contDiffAt,
        iteratedDeriv_one, iteratedDeriv_one, deriv_id, hg1]
      ring
    · rw [hF, iteratedDeriv_sub (n := 2) (f := g) (g := id) hgan.contDiffAt analyticAt_id.contDiffAt]
      have h2g : iteratedDeriv 2 g 0 = 0 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]; exact hg2
      have hid2 : iteratedDeriv 2 (id : ℂ → ℂ) 0 = 0 := by
        simp [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, deriv_const]
      rw [h2g, hid2, sub_zero]
  -- `F` is not eventually `0` near `0`.
  have hnzF : ¬ (∀ᶠ z in nhds (0 : ℂ), F z = 0) := by
    intro h; apply hnz
    filter_upwards [h] with z hz
    simpa [F, sub_eq_zero] using hz
  have hne_top : analyticOrderAt F 0 ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    exact hnzF htop
  have h3 : (3 : ℕ∞) ≤ analyticOrderAt F 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hFan).mpr hiter3
  -- Factor `F z = z ^ m · K z` with `K 0 ≠ 0`.
  obtain ⟨K, hKan, hK0, hKeq⟩ := hFan.analyticOrderAt_ne_top.mp hne_top
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, analyticOrderNatAt F 0 = m := ⟨_, rfl⟩
  rw [hmdef] at hKeq
  have hm3 : 3 ≤ m := by
    have h := h3
    rw [← Nat.cast_analyticOrderNatAt hne_top] at h
    rw [hmdef] at h
    exact_mod_cast h
  have hm1 : 1 ≤ m := by omega
  have hq1 : m - 1 + 1 = m := Nat.sub_add_cancel hm1
  refine ⟨m - 1, by omega, K 0, hK0, ?_⟩
  rw [hq1]
  have hKeq' : F =ᶠ[nhds (0 : ℂ)] (fun z : ℂ => z ^ m * K z) := by
    filter_upwards [hKeq] with z hz
    rw [hz]; simp [smul_eq_mul]
  -- On the punctured neighbourhood, the quotient is `K z - K 0`.
  have hEq : (fun z : ℂ => (g z - z - K 0 * z ^ m) / z ^ m)
      =ᶠ[nhdsWithin 0 {0}ᶜ] (fun z => K z - K 0) := by
    filter_upwards [hKeq'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzne
    have hzne' : z ≠ 0 := by simpa using hzne
    have hz0 : z ^ m ≠ 0 := pow_ne_zero m hzne'
    have hz' : g z - z = z ^ m * K z := by simpa only [F] using hz
    rw [hz', show z ^ m * K z - K 0 * z ^ m = z ^ m * (K z - K 0) by ring,
      mul_div_cancel_left₀ (K z - K 0) hz0]
  refine Filter.Tendsto.congr' hEq.symm ?_
  have h1 : Filter.Tendsto (fun z : ℂ => K z) (nhds (0 : ℂ)) (nhds (K 0)) := hKan.continuousAt
  have h2 : Filter.Tendsto (fun _ : ℂ => K 0) (nhds (0 : ℂ)) (nhds (K 0)) := tendsto_const_nhds
  have h3' := h1.sub h2
  have hmain : Filter.Tendsto (fun z : ℂ => K z - K 0) (nhds (0 : ℂ)) (nhds (0 : ℂ)) := by
    simpa using h3'
  exact hmain.mono_left nhdsWithin_le_nhds

end Work.Horn
