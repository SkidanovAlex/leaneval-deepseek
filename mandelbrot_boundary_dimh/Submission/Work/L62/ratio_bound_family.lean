import Mathlib
import Submission.Work.L62.contract_escape
import Submission.Work.L62.cont_family_of_selfmap
import Submission.Work.L62.uniform_escape2
import Submission.Work.L62.koenigs_aux
import Submission.Work.L62.deriv_ratio_iterate
import Submission.Work.L62.continuousOn_iterate_family
import Submission.Work.L62.local_ratio_contraction
import Submission.Work.L62.deriv_uniform_lower_bound
import Submission.Work.L62.tail_prod_bound

/-!
# Shishikura, Lemma 6.2: the uniform Koenigs/distortion bound

`Work.L62.ratio_bound_family`: for a jointly continuous family `H : ℂ → ℂ → ℂ` of injective
holomorphic self-maps of a bounded, preconnected open set `Ω ∋ 0`, with `H β 0 = 0` and
multipliers `deriv (H β) 0` bounded between `lam0 > 0` and `lam1 < 1` uniformly over the compact
parameter set `Λ`, the logarithmic derivative ratio

  `ζ ↦ deriv ((H β)^[j]) ζ * ζ / ((H β)^[j]) ζ`

of the `j`-th iterate is bounded above and below by a constant `C ≥ 1`, uniformly in `β ∈ Λ`,
`j : ℕ` and `ζ` in the compact set `K ⊆ Ω ∖ {0}`.

This is the "Koenigs distortion bound" uniformity step of Shishikura's §6: the ratio is a cocycle
along the orbit, each factor tends to `1` as the orbit contracts to the fixed point, and the
finitely many factors before the orbit enters the contracting ball are controlled by compactness
(on the compact set `S` of the first `J` images of `Λ × K`, the derivative of `H β` is uniformly
non-degenerate, since a limit of injective maps is injective and a non-constant injective
holomorphic map has nowhere vanishing derivative).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.L62

open Set Filter Topology Metric
open scoped Topology

/-! ### Helper lemmas -/

/-- Iterates of an injective self-map fixing `0` vanish only at `0`. -/
private lemma iterate_eq_zero_of_injective {Ω : Set ℂ} {H : ℂ → ℂ} (h0 : (0 : ℂ) ∈ Ω)
    (hmap : Set.MapsTo H Ω Ω) (hfix : H 0 = 0) (hinj : Set.InjOn H Ω) :
    ∀ (k : ℕ) {z : ℂ}, z ∈ Ω → (H^[k]) z = 0 → z = 0 := by
  intro k
  induction k with
  | zero =>
    intro z _ hz
    simpa using hz
  | succ k ih =>
    intro z hzΩ hz
    rw [Function.iterate_succ_apply'] at hz
    have hmem : (H^[k]) z ∈ Ω := hmap.iterate k hzΩ
    have hzero : (H^[k]) z = 0 := hinj hmem h0 (by rw [hz, hfix])
    exact ih hzΩ hzero

/-- Multiplicativity of the logarithmic derivative ratio. -/
private lemma ratio_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f (g z))
    (hg : DifferentiableAt ℂ g z) (hg0 : g z ≠ 0) :
    deriv (f ∘ g) z * z / f (g z)
      = (deriv f (g z) * (g z) / f (g z)) * (deriv g z * z / g z) := by
  rw [deriv_comp z hf hg]
  field_simp

/-- A compact subset of an open set admits a uniform ball-cover. -/
private lemma exists_ball_cover {Ω S : Set ℂ} (hΩo : IsOpen Ω) (hSc : IsCompact S)
    (hSΩ : S ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ S, Metric.ball w δ ⊆ Ω := by
  obtain ⟨δ, hδ0, hδsub⟩ := hSc.exists_cthickening_subset_open hΩo hSΩ
  refine ⟨δ / 2, by linarith, fun w hw x hx => ?_⟩
  refine hδsub (Metric.mem_cthickening_of_dist_le x w δ S hw ?_)
  have := Metric.mem_ball.mp hx
  linarith

/-- Uniform upper bound for the derivative on `Λ × S`. -/
private lemma deriv_bound_above {Ω Λ S : Set ℂ} {H : ℂ → ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hSc : IsCompact S) (hSΩ : S ⊆ Ω)
    (hmap : ∀ β ∈ Λ, Set.MapsTo (H β) Ω Ω)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ∈ Λ, ∀ w ∈ S, ‖deriv (H β) w‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := hΩb.exists_norm_le
  obtain ⟨δ, hδ0, hδ⟩ := exists_ball_cover hΩo hSc hSΩ
  refine ⟨max 0 (M₀ / (δ / 2)), le_max_left _ _, fun β hβ w hw => ?_⟩
  have hsub : Metric.closedBall w (δ / 2) ⊆ Ω := by
    intro z hz
    refine hδ w hw ?_
    rw [Metric.mem_ball]
    have h2 : dist z w ≤ δ / 2 := by simpa [Metric.mem_closedBall] using hz
    linarith
  have hcd : Complex.cderiv (δ / 2) (H β) w = deriv (H β) w :=
    Complex.cderiv_eq_deriv hΩo (hHdiff β hβ) (by linarith) hsub
  rw [← hcd]
  refine (Complex.norm_cderiv_le (by linarith) fun z hz => ?_).trans (le_max_right _ _)
  exact hM₀ (H β z) ((hmap β hβ) (hsub (Metric.sphere_subset_closedBall hz)))

/-- Two-sided bound for the logarithmic derivative ratio on a compact set. -/
private theorem factor_bound {Ω Λ S : Set ℂ} {H : ℂ → ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΛc : IsCompact Λ) (hSc : IsCompact S)
    (hSΩ : S ⊆ Ω) (hS0 : (0 : ℂ) ∉ S) (h0 : (0 : ℂ) ∈ Ω)
    (hmap : ∀ β ∈ Λ, Set.MapsTo (H β) Ω Ω)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω)
    (hfix : ∀ β ∈ Λ, H β 0 = 0) (hinj : ∀ β ∈ Λ, Set.InjOn (H β) Ω)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω))
    (hd : ∃ d : ℝ, 0 < d ∧ ∀ β ∈ Λ, ∀ w ∈ S, d ≤ ‖deriv (H β) w‖) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∃ D : ℝ, 1 ≤ D ∧ ∀ β ∈ Λ, ∀ w ∈ S,
      d ≤ ‖deriv (H β) w * w / (H β w)‖ ∧ ‖deriv (H β) w * w / (H β w)‖ ≤ D := by
  rcases hd with ⟨dder, hdderpos, hdder⟩
  obtain ⟨Mder, hMder0, hMder⟩ := deriv_bound_above hΩo hΩb hSc hSΩ hmap hHdiff
  by_cases hne : (Λ ×ˢ S).Nonempty
  · have hnormcont : ContinuousOn (fun p : ℂ × ℂ => ‖H p.1 p.2‖) (Λ ×ˢ S) :=
      (hcont.mono (Set.prod_mono_right hSΩ)).norm
    obtain ⟨p, hp, hpmin⟩ := (hΛc.prod hSc).exists_isMinOn hne hnormcont
    rw [isMinOn_iff] at hpmin
    rw [Set.mem_prod] at hp
    have hp1pos : 0 < ‖H p.1 p.2‖ := by
      refine norm_pos_iff.mpr fun hzero => hS0 ?_
      have hp2 : p.2 = 0 := hinj p.1 hp.1 (hSΩ hp.2) h0 (by rw [hzero, hfix p.1 hp.1])
      exact hp2 ▸ hp.2
    obtain ⟨M₂, hM₂⟩ := hΩb.exists_norm_le
    obtain ⟨w₀, hw₀, hw₀min⟩ := hSc.exists_isMinOn ⟨p.2, hp.2⟩ continuous_norm.continuousOn
    rw [isMinOn_iff] at hw₀min
    have hw₀pos : 0 < ‖w₀‖ := norm_pos_iff.mpr fun h => hS0 (h ▸ hw₀)
    obtain ⟨Mw, hMw⟩ := hSc.isBounded.exists_norm_le
    refine ⟨min (dder * ‖w₀‖ / max M₂ ‖H p.1 p.2‖) 1, lt_min (by positivity) one_pos,
      min_le_right _ _, max 1 (Mder * max Mw 0 / ‖H p.1 p.2‖), le_max_left _ _,
      fun β hβ w hw => ?_⟩
    have hHpw : ‖H β w‖ ≤ max M₂ ‖H p.1 p.2‖ :=
      (hM₂ _ ((hmap β hβ) (hSΩ hw))).trans (le_max_left _ _)
    have hpw : ‖H p.1 p.2‖ ≤ ‖H β w‖ :=
      hpmin (β, w) (by rw [Set.mem_prod]; exact ⟨hβ, hw⟩)
    have hw₀w : ‖w₀‖ ≤ ‖w‖ := hw₀min w hw
    have hww : ‖w‖ ≤ max Mw 0 := (hMw w hw).trans (le_max_left _ _)
    rw [norm_div, norm_mul]
    constructor
    · refine le_trans (min_le_left _ _) ?_
      refine div_le_div₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (hdder β hβ w hw) hw₀w (norm_nonneg w₀) (norm_nonneg _))
        (hp1pos.trans_le hpw) hHpw
    · refine le_trans (div_le_div₀ (mul_nonneg hMder0 (le_max_right _ _))
        (mul_le_mul (hMder β hβ w hw) hww (norm_nonneg w) hMder0) hp1pos hpw) ?_
      exact le_max_right _ _
  · refine ⟨1, one_pos, le_refl 1, 1, le_refl 1, fun β hβ w hw => ?_⟩
    exact absurd ⟨(β, w), by rw [Set.mem_prod]; exact ⟨hβ, hw⟩⟩ hne

/-- Tail product bound for the logarithmic derivative ratio near the fixed point. -/
private theorem tail_bound {Ω Λ : Set ℂ} {H : ℂ → ℂ → ℂ} {μ ρ L : ℝ}
    (hΩo : IsOpen Ω) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hρ0 : 0 < ρ) (hL0 : 0 ≤ L)
    (hLρ : L * ρ ≤ 1 / 2) (hρball : Metric.ball (0 : ℂ) ρ ⊆ Ω)
    (hmap : ∀ β ∈ Λ, Set.MapsTo (H β) Ω Ω)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω)
    (hfix : ∀ β ∈ Λ, H β 0 = 0) (hinj : ∀ β ∈ Λ, Set.InjOn (H β) Ω)
    (hcontr : ∀ β ∈ Λ, ∀ u : ℂ, ‖u‖ ≤ ρ → ‖H β u‖ ≤ μ * ‖u‖)
    (hratio : ∀ β ∈ Λ, ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ ρ →
        ‖deriv (H β) u * u / (H β u) - 1‖ ≤ L * ‖u‖) :
    ∀ β ∈ Λ, ∀ (m : ℕ) (w : ℂ), w ≠ 0 → w ∈ Metric.ball (0 : ℂ) ρ →
      Real.exp (-(2 * (L * ρ / (1 - μ)))) ≤ ‖deriv ((H β)^[m]) w * w / ((H β)^[m]) w‖ ∧
      ‖deriv ((H β)^[m]) w * w / ((H β)^[m]) w‖ ≤ Real.exp (L * ρ / (1 - μ)) := by
  intro β hβ m w hw0 hwball
  have hμ1' : μ ≤ 1 := le_of_lt hμ1
  have hwnorm : ‖w‖ < ρ := by
    have := Metric.mem_ball.mp hwball
    rwa [dist_zero_right] at this
  have hwle : ‖w‖ ≤ ρ := le_of_lt hwnorm
  have h0 : (0 : ℂ) ∈ Ω := hρball (by simp [Metric.mem_ball, hρ0])
  have hwΩ : w ∈ Ω := hρball hwball
  have hmemΩ : ∀ k : ℕ, ((H β)^[k]) w ∈ Ω := fun k => (hmap β hβ).iterate k hwΩ
  have hne : ∀ k : ℕ, ((H β)^[k]) w ≠ 0 := fun k h =>
    hw0 (iterate_eq_zero_of_injective h0 (hmap β hβ) (hfix β hβ) (hinj β hβ) k hwΩ h)
  have hgeo : ∀ k : ℕ, ‖((H β)^[k]) w‖ ≤ μ ^ k * ‖w‖ :=
    fun k => norm_iterate_le hμ0 hμ1' (hcontr β hβ) k w hwle
  have hleρ : ∀ k : ℕ, ‖((H β)^[k]) w‖ ≤ ρ := by
    intro k
    refine (hgeo k).trans ?_
    calc μ ^ k * ‖w‖ ≤ 1 * ρ :=
          mul_le_mul (pow_le_one₀ hμ0 hμ1') hwle (norm_nonneg w) zero_le_one
      _ = ρ := one_mul ρ
  have hdiff : ∀ k < m, DifferentiableAt ℂ (H β) (((H β)^[k]) w) := fun k _ =>
    (hHdiff β hβ).differentiableAt (hΩo.mem_nhds (hmemΩ k))
  have hpr := deriv_ratio_iterate (f := H β) (z := w) m hdiff (fun k _ => hne k)
  have hfactor : ∀ k : ℕ,
      ‖deriv (H β) (((H β)^[k]) w) * (((H β)^[k]) w) / (((H β)^[k + 1]) w) - 1‖
        ≤ (L * ρ) * μ ^ k := by
    intro k
    have hstep : (((H β)^[k + 1]) w) = H β (((H β)^[k]) w) := by
      rw [Nat.add_one]
      exact Function.iterate_succ_apply' (H β) k w
    rw [hstep]
    have h1 : ‖deriv (H β) (((H β)^[k]) w) * (((H β)^[k]) w)
          / (H β (((H β)^[k]) w)) - 1‖ ≤ L * ‖((H β)^[k]) w‖ :=
      hratio β hβ _ (hne k) (hleρ k)
    refine h1.trans ?_
    calc L * ‖((H β)^[k]) w‖ ≤ L * (μ ^ k * ‖w‖) := mul_le_mul_of_nonneg_left (hgeo k) hL0
      _ ≤ L * (μ ^ k * ρ) := by
          refine mul_le_mul_of_nonneg_left ?_ hL0
          exact mul_le_mul_of_nonneg_left hwle (pow_nonneg hμ0 k)
      _ = (L * ρ) * μ ^ k := by ring
  have htpb := tail_prod_bound (a := fun k => deriv (H β) (((H β)^[k]) w) * (((H β)^[k]) w)
      / (((H β)^[k + 1]) w)) (c := L * ρ) (μ := μ) (mul_nonneg hL0 hρ0.le) hμ0 hμ1 hLρ
      (fun k => hfactor k) m
  rw [hpr]
  exact ⟨htpb.2.1, htpb.2.2⟩

/-- **Uniform two-sided bound for the logarithmic derivative ratio of the iterates.** -/
theorem ratio_bound_family {Ω Λ K : Set ℂ} {H : ℂ → ℂ → ℂ} {lam0 lam1 : ℝ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩc : IsPreconnected Ω)
    (h0 : (0 : ℂ) ∈ Ω)
    (hΛc : IsCompact Λ) (hKc : IsCompact K) (hK : K ⊆ Ω) (hK0 : (0 : ℂ) ∉ K)
    (hlam0 : 0 < lam0) (hlam1 : lam1 < 1)
    (hlam : ∀ β ∈ Λ, lam0 ≤ ‖deriv (H β) 0‖ ∧ ‖deriv (H β) 0‖ ≤ lam1)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω) (hmap : ∀ β ∈ Λ, Set.MapsTo (H β) Ω Ω)
    (hfix : ∀ β ∈ Λ, H β 0 = 0) (hinj : ∀ β ∈ Λ, Set.InjOn (H β) Ω)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β ∈ Λ, ∀ j : ℕ, ∀ ζ ∈ K,
      C⁻¹ ≤ ‖deriv ((H β)^[j]) ζ * ζ / ((H β)^[j]) ζ‖ ∧
      ‖deriv ((H β)^[j]) ζ * ζ / ((H β)^[j]) ζ‖ ≤ C := by
  by_cases hne : (Λ ×ˢ K).Nonempty
  · obtain ⟨ρ₀, hρ₀pos, hρ₀ball, μ, hμ0, hμ1, hcontr₀, L, hL0, hratio₀⟩ :=
      local_ratio_contraction hΩo h0 hΛc hlam0 hlam1 hlam hHdiff hfix hcont
    set ρ : ℝ := min ρ₀ ((2 * L + 1)⁻¹)
    have hρpos : 0 < ρ := lt_min hρ₀pos (by positivity)
    have hρle : ρ ≤ ρ₀ := min_le_left _ _
    have hρball : Metric.ball (0 : ℂ) ρ ⊆ Ω := (Metric.ball_subset_ball hρle).trans hρ₀ball
    have hLρ : L * ρ ≤ 1 / 2 := by
      have h1 : ρ ≤ (2 * L + 1)⁻¹ := min_le_right _ _
      have hpos : (0 : ℝ) < 2 * L + 1 := by linarith
      calc L * ρ ≤ L * (2 * L + 1)⁻¹ := mul_le_mul_of_nonneg_left h1 hL0
        _ = L / (2 * L + 1) := by rw [div_eq_mul_inv]
        _ ≤ 1 / 2 := by
            rw [div_le_div_iff₀ hpos (by norm_num)]
            linarith
    have hcontr : ∀ β ∈ Λ, ∀ u : ℂ, ‖u‖ ≤ ρ → ‖H β u‖ ≤ μ * ‖u‖ :=
      fun β hβ u hu => hcontr₀ β hβ u (hu.trans hρle)
    have hratio : ∀ β ∈ Λ, ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ ρ →
        ‖deriv (H β) u * u / (H β u) - 1‖ ≤ L * ‖u‖ :=
      fun β hβ u hu0 hu => hratio₀ β hβ u hu0 (hu.trans hρle)
    have hball_le : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) ρ → ‖u‖ ≤ ρ := by
      intro u hu
      have hlt : ‖u‖ < ρ := by
        have h' := Metric.mem_ball.mp hu
        rwa [dist_zero_right] at h'
      exact le_of_lt hlt
    have hesc : ∀ β ∈ Λ, ∀ z ∈ K, ∃ n : ℕ, ((H β)^[n]) z ∈ Metric.ball (0 : ℂ) ρ := by
      intro β hβ z hz
      obtain ⟨N, hN⟩ := contract_escape hΩo hΩb hΩc h0 (hHdiff β hβ) (hmap β hβ)
        (hfix β hβ) (lt_of_le_of_lt (hlam β hβ).2 hlam1) ρ hρpos K hK hKc
      exact ⟨N, hN N le_rfl z hz⟩
    obtain ⟨J, hJ⟩ := uniform_escape2 hΩo hΛc hKc hK hρpos hρball hμ0 hμ1 hρpos hmap
      (fun β hβ u hu => hcontr β hβ u (hball_le u hu)) hcont hesc
    set S : Set ℂ := ⋃ k ∈ Finset.range (J + 1),
      (fun p : ℂ × ℂ => ((H p.1)^[k]) p.2) '' (Λ ×ˢ K) with hSdef
    have hmems : ∀ β ∈ Λ, ∀ ζ ∈ K, ∀ k ≤ J, ((H β)^[k]) ζ ∈ S := by
      intro β hβ ζ hζ k hk
      rw [hSdef]
      exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (by omega), (β, ζ), ⟨hβ, hζ⟩, rfl⟩
    have hSc : IsCompact S := by
      rw [hSdef]
      refine Finset.isCompact_biUnion _ fun k hk => ?_
      exact (hΛc.prod hKc).image_of_continuousOn
        ((continuousOn_iterate_family k hmap hcont).mono (Set.prod_mono_right hK))
    have hSΩ : S ⊆ Ω := by
      intro x hx
      rw [hSdef] at hx
      obtain ⟨k, hk, p, hp, rfl⟩ := Set.mem_iUnion₂.mp hx
      rw [Set.mem_prod] at hp
      exact (hmap p.1 hp.1).iterate k (hK hp.2)
    have hS0 : (0 : ℂ) ∉ S := by
      intro hx
      rw [hSdef] at hx
      obtain ⟨k, hk, p, hp, hpx⟩ := Set.mem_iUnion₂.mp hx
      rw [Set.mem_prod] at hp
      have hz : p.2 = 0 := iterate_eq_zero_of_injective h0 (hmap p.1 hp.1) (hfix p.1 hp.1)
        (hinj p.1 hp.1) k (hK hp.2) hpx
      exact hK0 (hz ▸ hp.2)
    obtain ⟨dder, hdderpos, hdder⟩ :=
      deriv_uniform_lower_bound hΩo hΛc hSc hSΩ hS0 hHdiff hfix hinj hcont
    obtain ⟨d, hd0, hd1, D, hD1, hfac⟩ := factor_bound hΩo hΩb hΛc hSc hSΩ hS0 h0 hmap
      hHdiff hfix hinj hcont ⟨dder, hdderpos, hdder⟩
    have htail := tail_bound hΩo hμ0 hμ1 hρpos hL0 hLρ hρball hmap hHdiff hfix hinj
      hcontr hratio
    have headb : ∀ (t : ℕ), t ≤ J → ∀ β ∈ Λ, ∀ ζ ∈ K,
        d ^ J ≤ ‖deriv ((H β)^[t]) ζ * ζ / ((H β)^[t]) ζ‖ ∧
        ‖deriv ((H β)^[t]) ζ * ζ / ((H β)^[t]) ζ‖ ≤ D ^ J := by
      intro t ht β hβ ζ hζ
      have hzΩ : ζ ∈ Ω := hK hζ
      have hmemΩ : ∀ k : ℕ, ((H β)^[k]) ζ ∈ Ω := fun k => (hmap β hβ).iterate k hzΩ
      have hdiff : ∀ k < t, DifferentiableAt ℂ (H β) (((H β)^[k]) ζ) := fun k _ =>
        (hHdiff β hβ).differentiableAt (hΩo.mem_nhds (hmemΩ k))
      have hne' : ∀ k ≤ t, ((H β)^[k]) ζ ≠ 0 := by
        intro k _ h'
        exact hK0 ((iterate_eq_zero_of_injective h0 (hmap β hβ) (hfix β hβ) (hinj β hβ) k
          hzΩ h') ▸ hζ)
      have hpr := deriv_ratio_iterate (f := H β) (z := ζ) t hdiff hne'
      have hstep : ∀ k : ℕ, (((H β)^[k + 1]) ζ) = H β (((H β)^[k]) ζ) := by
        intro k
        rw [Nat.add_one]
        exact Function.iterate_succ_apply' (H β) k ζ
      rw [hpr, norm_prod]
      have hfac_t : ∀ k ∈ Finset.range t,
          d ≤ ‖deriv (H β) (((H β)^[k]) ζ) * (((H β)^[k]) ζ) / (((H β)^[k + 1]) ζ)‖ ∧
          ‖deriv (H β) (((H β)^[k]) ζ) * (((H β)^[k]) ζ) / (((H β)^[k + 1]) ζ)‖ ≤ D := by
        intro k hk
        have hkJ : k ≤ J := le_trans (Finset.mem_range.mp hk).le ht
        have hgot := hfac β hβ (((H β)^[k]) ζ) (hmems β hβ ζ hζ k hkJ)
        rwa [← hstep k] at hgot
      constructor
      · calc d ^ J ≤ d ^ t := pow_le_pow_of_le_one hd0.le hd1 ht
          _ = ∏ b ∈ Finset.range t, d := by rw [Finset.prod_const, Finset.card_range]
          _ ≤ ∏ b ∈ Finset.range t,
                ‖deriv (H β) (((H β)^[b]) ζ) * (((H β)^[b]) ζ) / (((H β)^[b + 1]) ζ)‖ :=
              Finset.prod_le_prod₀ (fun b _ => hd0.le) fun k hk => (hfac_t k hk).1
      · calc ∏ k ∈ Finset.range t,
            ‖deriv (H β) (((H β)^[k]) ζ) * (((H β)^[k]) ζ) / (((H β)^[k + 1]) ζ)‖
            ≤ ∏ k ∈ Finset.range t, D :=
              Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k hk => (hfac_t k hk).2
          _ = D ^ t := by rw [Finset.prod_const, Finset.card_range]
          _ ≤ D ^ J := pow_le_pow_right₀ hD1 ht
    set T : ℝ := L * ρ / (1 - μ)
    have hT0 : 0 ≤ T := by
      rw [show T = L * ρ / (1 - μ) from rfl]
      exact div_nonneg (mul_nonneg hL0 hρpos.le) (by linarith)
    have hexpneg : Real.exp (-(2 * T)) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hexppos : 1 ≤ Real.exp T := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hT0
    set Chigh : ℝ := D ^ J * Real.exp T
    set Clow : ℝ := d ^ J * Real.exp (-(2 * T))
    have hClowpos : 0 < Clow := mul_pos (pow_pos hd0 J) (Real.exp_pos _)
    have hDT : Chigh ≤ max 1 (max Chigh Clow⁻¹) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hCi : Clow⁻¹ ≤ max 1 (max Chigh Clow⁻¹) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨max 1 (max Chigh Clow⁻¹), le_max_left _ _, ?_⟩
    intro β hβ j ζ hζ
    have key_low : Clow ≤ ‖deriv ((H β)^[j]) ζ * ζ / ((H β)^[j]) ζ‖ := by
      rcases le_or_gt j J with hj | hj
      · refine le_trans ?_ (headb j hj β hβ ζ hζ).1
        rw [show Clow = d ^ J * Real.exp (-(2 * T)) from rfl]
        exact mul_le_of_le_one_right (pow_nonneg hd0.le J) hexpneg
      · have hJle : J ≤ j := le_of_lt hj
        have hiter : (H β)^[j] = (H β)^[j - J] ∘ (H β)^[J] := by
          conv_lhs => rw [show j = (j - J) + J from (Nat.sub_add_cancel hJle).symm]
          rw [Function.iterate_add]
        have hdiff₁ : DifferentiableAt ℂ ((H β)^[j - J]) (((H β)^[J]) ζ) :=
          ((hHdiff β hβ).iterate (hmap β hβ) (j - J)).differentiableAt
            (hΩo.mem_nhds ((hmap β hβ).iterate J (hK hζ)))
        have hdiff₂ : DifferentiableAt ℂ ((H β)^[J]) ζ :=
          ((hHdiff β hβ).iterate (hmap β hβ) J).differentiableAt (hΩo.mem_nhds (hK hζ))
        have hwJ0 : ((H β)^[J]) ζ ≠ 0 := by
          intro h'
          exact hK0 ((iterate_eq_zero_of_injective h0 (hmap β hβ) (hfix β hβ) (hinj β hβ) J
            (hK hζ) h') ▸ hζ)
        have hcoc : deriv ((H β)^[j]) ζ * ζ / ((H β)^[j]) ζ
            = (deriv ((H β)^[j - J]) (((H β)^[J]) ζ) * (((H β)^[J]) ζ)
                / ((H β)^[j - J]) (((H β)^[J]) ζ))
              * (deriv ((H β)^[J]) ζ * ζ / ((H β)^[J]) ζ) := by
          rw [hiter]
          exact ratio_mul hdiff₁ hdiff₂ hwJ0
        have hb := headb J le_rfl β hβ ζ hζ
        have ht := htail β hβ (j - J) (((H β)^[J]) ζ) hwJ0 (hJ β hβ J le_rfl ζ hζ)
        rw [hcoc, norm_mul]
        rw [show Clow = d ^ J * Real.exp (-(2 * T)) from rfl]
        calc d ^ J * Real.exp (-(2 * T)) = Real.exp (-(2 * T)) * d ^ J := mul_comm _ _
          _ ≤ ‖deriv ((H β)^[j - J]) (((H β)^[J]) ζ) * (((H β)^[J]) ζ)
                / ((H β)^[j - J]) (((H β)^[J]) ζ)‖
              * ‖deriv ((H β)^[J]) ζ * ζ / ((H β)^[J]) ζ‖ :=
                mul_le_mul ht.1 hb.1 (pow_nonneg hd0.le J) (norm_nonneg _)
    have key_high : ‖deriv ((H β)^[j]) ζ * ζ / ((H β)^[j]) ζ‖ ≤ Chigh := by
      rcases le_or_gt j J with hj | hj
      · refine (headb j hj β hβ ζ hζ).2.trans ?_
        rw [show Chigh = D ^ J * Real.exp T from rfl]
        exact le_mul_of_one_le_right (pow_nonneg (le_trans zero_lt_one.le hD1) J) hexppos
      · have hJle : J ≤ j := le_of_lt hj
        have hiter : (H β)^[j] = (H β)^[j - J] ∘ (H β)^[J] := by
          conv_lhs => rw [show j = (j - J) + J from (Nat.sub_add_cancel hJle).symm]
          rw [Function.iterate_add]
        have hdiff₁ : DifferentiableAt ℂ ((H β)^[j - J]) (((H β)^[J]) ζ) :=
          ((hHdiff β hβ).iterate (hmap β hβ) (j - J)).differentiableAt
            (hΩo.mem_nhds ((hmap β hβ).iterate J (hK hζ)))
        have hdiff₂ : DifferentiableAt ℂ ((H β)^[J]) ζ :=
          ((hHdiff β hβ).iterate (hmap β hβ) J).differentiableAt (hΩo.mem_nhds (hK hζ))
        have hwJ0 : ((H β)^[J]) ζ ≠ 0 := by
          intro h'
          exact hK0 ((iterate_eq_zero_of_injective h0 (hmap β hβ) (hfix β hβ) (hinj β hβ) J
            (hK hζ) h') ▸ hζ)
        have hcoc : deriv ((H β)^[j]) ζ * ζ / ((H β)^[j]) ζ
            = (deriv ((H β)^[j - J]) (((H β)^[J]) ζ) * (((H β)^[J]) ζ)
                / ((H β)^[j - J]) (((H β)^[J]) ζ))
              * (deriv ((H β)^[J]) ζ * ζ / ((H β)^[J]) ζ) := by
          rw [hiter]
          exact ratio_mul hdiff₁ hdiff₂ hwJ0
        have hb := headb J le_rfl β hβ ζ hζ
        have ht := htail β hβ (j - J) (((H β)^[J]) ζ) hwJ0 (hJ β hβ J le_rfl ζ hζ)
        rw [hcoc, norm_mul]
        rw [show Chigh = D ^ J * Real.exp T from rfl]
        calc ‖deriv ((H β)^[j - J]) (((H β)^[J]) ζ) * (((H β)^[J]) ζ)
                / ((H β)^[j - J]) (((H β)^[J]) ζ)‖
              * ‖deriv ((H β)^[J]) ζ * ζ / ((H β)^[J]) ζ‖
            ≤ Real.exp T * D ^ J :=
              mul_le_mul ht.2 hb.2 (norm_nonneg _) (le_of_lt (Real.exp_pos _))
          _ = D ^ J * Real.exp T := mul_comm _ _
    constructor
    · calc (max 1 (max Chigh Clow⁻¹))⁻¹ = 1 / (max 1 (max Chigh Clow⁻¹)) := by
            rw [inv_eq_one_div]
        _ ≤ 1 / Clow⁻¹ := one_div_le_one_div_of_le (inv_pos.mpr hClowpos) hCi
        _ = Clow := by rw [one_div, inv_inv]
        _ ≤ ‖deriv ((H β)^[j]) ζ * ζ / ((H β)^[j]) ζ‖ := key_low
    · exact key_high.trans hDT
  · refine ⟨1, le_refl 1, fun β hβ j ζ hζ => ?_⟩
    exact absurd ⟨(β, ζ), by rw [Set.mem_prod]; exact ⟨hβ, hζ⟩⟩ hne

end Work.L62
