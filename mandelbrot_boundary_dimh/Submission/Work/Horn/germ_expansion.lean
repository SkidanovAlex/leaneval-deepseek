import Mathlib
import Submission.Work.Horn.germ_expansion_free

namespace Work.Horn

/-!
# `Work.Horn.germ_expansion`

A holomorphic germ `g` at `0` with `g 0 = 0`, `g'(0) = 1` which is not eventually the identity
has a first non-trivial Taylor term beyond the linear one: there are `q ≥ 1` and `a ≠ 0` with

  `g z - z - a * z ^ (q + 1) = o (z ^ (q + 1))`   as `z → 0` through `{0}ᶜ`.

The proof is purely analytic.  Since `g` is holomorphic on a ball around `0`, it is analytic at
`0`; hence `F := z ↦ g z - z` is analytic at `0` with `F 0 = 0` and `F' 0 = 0`, while `hnz` says
exactly that `F` is not eventually `0`.  Therefore the vanishing order `m := ord₀ F` of `F` at `0`
is a natural number `≥ 2`, and `F z = z ^ m · K z` near `0` with `K` analytic at `0`, `K 0 ≠ 0`.
Taking `q := m - 1` and `a := K 0` gives the expansion.  (When `g''(0) ≠ 0` one has `m = 2` and
`q = 1`; when `g''(0) = 0` one has `m ≥ 3`, recovering `Work.Horn.germ_expansion_free`.)
-/

theorem germ_expansion {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ)) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 1)
    (hnz : ¬ ∀ᶠ ζ in nhds (0 : ℂ), g ζ = ζ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ a : ℂ, a ≠ 0 ∧
      Filter.Tendsto (fun z : ℂ => (g z - z - a * z ^ (q + 1)) / z ^ (q + 1))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  -- `F = g - id` is analytic at `0` with a vanishing two-jet and is not eventually `0`.
  let F : ℂ → ℂ := fun z : ℂ => g z - z
  have hgan : AnalyticAt ℂ g 0 := hg.analyticAt (Metric.ball_mem_nhds 0 hρ)
  have hF : F = (g - id) := rfl
  have hFan : AnalyticAt ℂ F 0 := by rw [hF]; exact hgan.sub analyticAt_id
  have hiter2 : ∀ i < 2, iteratedDeriv i F 0 = 0 := by
    intro i hi
    interval_cases i
    · simp [F, iteratedDeriv_zero, hg0]
    · rw [hF, iteratedDeriv_sub (n := 1) (f := g) (g := id) hgan.contDiffAt analyticAt_id.contDiffAt,
        iteratedDeriv_one, iteratedDeriv_one, deriv_id, hg1]
      ring
  have hnzF : ¬ (∀ᶠ z in nhds (0 : ℂ), F z = 0) := by
    intro h; apply hnz
    filter_upwards [h] with z hz
    simpa [F, sub_eq_zero] using hz
  have hne_top : analyticOrderAt F 0 ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    exact hnzF htop
  have h2 : (2 : ℕ∞) ≤ analyticOrderAt F 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hFan).mpr hiter2
  -- Factor `F z = z ^ m · K z` with `K 0 ≠ 0`.
  obtain ⟨K, hKan, hK0, hKeq⟩ := hFan.analyticOrderAt_ne_top.mp hne_top
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, analyticOrderNatAt F 0 = m := ⟨_, rfl⟩
  rw [hmdef] at hKeq
  have hm2 : 2 ≤ m := by
    have h := h2
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
  -- On the punctured neighbourhood the quotient is `K z - K 0`, which tends to `0`.
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
  have h2' : Filter.Tendsto (fun _ : ℂ => K 0) (nhds (0 : ℂ)) (nhds (K 0)) := tendsto_const_nhds
  have h3' := h1.sub h2'
  have hmain : Filter.Tendsto (fun z : ℂ => K z - K 0) (nhds (0 : ℂ)) (nhds (0 : ℂ)) := by
    simpa using h3'
  exact hmain.mono_left nhdsWithin_le_nhds

end Work.Horn
