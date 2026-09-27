import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

open Filter _root_.Topology

/-- Points of a chart `E` centred at `u₁` lying in `S` over `ψ₁ = u` with `u ≠ u₁` close to `u₁`
fall into any set that is a neighbourhood in `H0` of the fibre of `S` over `u₁`, provided the chart
is *redundant*: all its values over a small punctured disc around `ζ = 0` lie on one local section
`f` through a point `q` of the fibre over `u₁`. -/
theorem leg_in_sec_of_redundant {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) {S T : Set ChainData} {u₁ : ℂ} (hu₁ : u₁ ≠ 0)
    (hSH : S ⊆ H0 a h)
    (hScl : ∀ q ∈ closure S, q ∈ H0 a h → q ∈ S)
    (hT : ∀ q ∈ S, q.2.1 = u₁ → T ∈ 𝓝[H0 a h] q)
    {E : ℂ → ChainData} {κ : ℂ} {k : ℕ} (hE : IsChartData a h E u₁ κ k)
    {r₀ : ℝ} (hr₀ : 0 < r₀) {q : ChainData} (hqS : q ∈ S) (hq1 : q.2.1 = u₁)
    {ρ' : ℝ} {f : ℂ → ChainData} (hf : IsSection a h f q ρ')
    (hleg : ∀ ζ ∈ Metric.ball (0 : ℂ) r₀ \ {0}, E ζ ∈ f '' Metric.ball q.2.1 ρ') :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ → ∀ ζ ∈ Metric.ball (0 : ℂ) (1/2) \ {0},
      u₁ + κ * ζ ^ k = u → E ζ ∈ S → E ζ ∈ T := by
  obtain ⟨hk, hκ, hEmem, -, -⟩ := hE
  have hρ'pos : 0 < ρ' := hf.1
  have hfq : f q.2.1 = q := hf.2.1
  have hfmem : ∀ u ∈ Metric.ball q.2.1 ρ', f u ∈ H0 a h ∧ (f u).2.1 = u := hf.2.2.1
  -- `T` is a neighbourhood of `q = f u₁` in `H0`, hence (by continuity of the section at `u₁`)
  -- a neighbourhood of `f u` for `u` near `u₁`.
  have hTq : T ∈ 𝓝[H0 a h] q := hT q hqS hq1
  have hevT : ∀ᶠ y in 𝓝 q, y ∈ H0 a h → y ∈ T := mem_nhdsWithin_iff_eventually.mp hTq
  have hcont : ContinuousAt f u₁ := by rw [← hq1]; exact IsSection.continuousAt hf
  have hfu₁ : f u₁ = q := by rw [← hq1]; exact hfq
  have hev : ∀ᶠ u in 𝓝 u₁, (f u ∈ H0 a h → f u ∈ T) := by
    have h' : ∀ᶠ y in 𝓝 (f u₁), y ∈ H0 a h → y ∈ T := by rw [hfu₁]; exact hevT
    exact hcont.eventually h'
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hev
  -- the radius: small enough for the section and for `T`, and small enough that the equation
  -- `u₁ + κ ζ^k = u` forces `ζ` into the disc where `E = f`.
  set ρ : ℝ := min ρ' (min δ (‖κ‖ * r₀ ^ k)) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min hρ'pos (lt_min hδpos (mul_pos (norm_pos_iff.mpr hκ) (pow_pos hr₀ k)))
  have hρ_le_ρ' : ρ ≤ ρ' := by rw [hρdef]; exact min_le_left _ _
  have hρ_le_δ : ρ ≤ δ := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_κr : ρ ≤ ‖κ‖ * r₀ ^ k := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ, hρpos, ?_⟩
  intro u hu hun ζ hζ heq hES
  have hu_ρ' : u ∈ Metric.ball u₁ ρ' := Metric.ball_subset_ball hρ_le_ρ' hu
  have hu_δ : u ∈ Metric.ball u₁ δ := Metric.ball_subset_ball hρ_le_δ hu
  have hζ_ne : ζ ≠ 0 := hζ.2
  have hζ_lt_half : ‖ζ‖ < 1 / 2 := by
    have h := Metric.mem_ball.mp hζ.1
    rwa [dist_zero_right] at h
  have hζ_B1 : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    refine ⟨?_, hζ_ne⟩
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hEζpsi : (E ζ).2.1 = u := by rw [(hEmem ζ hζ_B1).2, heq]
  -- from the equation, `‖ζ‖^k = ‖u - u₁‖ / ‖κ‖ < r₀^k`
  have hd : ‖u - u₁‖ < ρ := by
    have h := Metric.mem_ball.mp hu
    rwa [dist_eq_norm] at h
  have hmul : κ * ζ ^ k = u - u₁ := by rw [← heq]; ring
  have hnorm : ‖κ‖ * ‖ζ‖ ^ k = ‖u - u₁‖ := by rw [← norm_pow, ← norm_mul, hmul]
  have hlt : ‖ζ‖ ^ k < r₀ ^ k := by
    have h1 : ‖κ‖ * ‖ζ‖ ^ k < ‖κ‖ * r₀ ^ k := by
      rw [hnorm]; exact lt_of_lt_of_le hd hρ_le_κr
    exact (mul_lt_mul_iff_of_pos_left (norm_pos_iff.mpr hκ)).mp h1
  have hζ_lt_r₀ : ‖ζ‖ < r₀ :=
    (pow_lt_pow_iff_left₀ (norm_nonneg ζ) (le_of_lt hr₀) hk.ne').mp hlt
  have hζ_r₀ : ζ ∈ Metric.ball (0 : ℂ) r₀ \ {0} :=
    ⟨Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hζ_lt_r₀), hζ_ne⟩
  -- so `E ζ` lies on the section, say `E ζ = f u`
  have hlegζ := hleg ζ hζ_r₀
  rw [hq1] at hlegζ
  obtain ⟨w, hw, hfw⟩ := hlegζ
  have hw_eq : w = u := by
    have h1 : (f w).2.1 = w := (hfmem w (by rw [hq1]; exact hw)).2
    have h2 : (f w).2.1 = u := by rw [hfw, hEζpsi]
    exact h1.symm.trans h2
  have hfu : f u = E ζ := by rw [← hw_eq]; exact hfw
  -- and `f u ∈ T` because `f` is continuous at `u₁` and `T` is a neighbourhood of `f u₁`
  have hu_ρ'' : u ∈ Metric.ball q.2.1 ρ' := by rw [hq1]; exact hu_ρ'
  have hfuH0 : f u ∈ H0 a h := (hfmem u hu_ρ'').1
  have hfuT : f u ∈ T := hδ hu_δ hfuH0
  rw [← hfu]; exact hfuT

end Work.EQ
