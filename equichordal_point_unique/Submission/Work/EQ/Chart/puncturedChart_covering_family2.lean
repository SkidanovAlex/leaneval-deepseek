import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_structure
import Submission.Work.Topology.exists_factor_of_root_invariant
import Submission.Work.Analysis.Complex.punctured_ball_connected
import Submission.Work.EQ.Chart.cpow_root_facts
import Submission.Work.EQ.Chart.finite_subgroup_complex_eq_rootsOfUnity
import Submission.Work.EQ.Chart.stab_invariance_of_one_point

namespace Work.EQ.Chart

open Complex Filter _root_.Topology
open scoped Topology

private lemma exists_analyticAt_descent_aux {d : ℕ} (hd : 0 < d) {ω : ℂ} (hω : ω ^ d = 1)
    (hprim : ∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hinv : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g (ω * z) = g z) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = G (z ^ d) := by
  classical
  -- radius of analyticity of `g` at `0`
  obtain ⟨r, hr, hran⟩ : ∃ r > 0, ∀ y : ℂ, ‖y‖ < r → AnalyticAt ℂ g y := by
    obtain ⟨r, hr, hre⟩ := Metric.eventually_nhds_iff.mp hg.eventually_analyticAt
    exact ⟨r, hr, fun y hy => hre (by rwa [dist_zero_right])⟩
  -- radius on which `g` is invariant
  obtain ⟨e, he, heinv⟩ : ∃ e > 0, ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < e → g (ω * z) = g z := by
    rw [eventually_nhdsWithin_iff] at hinv
    obtain ⟨e, he, he'⟩ := Metric.eventually_nhds_iff.mp hinv
    exact ⟨e, he, fun z h1 h2 => he' (by rwa [dist_zero_right]) (by simpa using h1.ne')⟩
  have hρ : 0 < min r e := lt_min hr he
  -- the descent on the punctured disc of radius `min r e`
  obtain ⟨G₀, hG₀an, hG₀eq⟩ := Work.Topology.exists_factor_of_root_invariant (ρ := min r e) hρ
    (fun y hy => hran y (lt_of_lt_of_le (by
      have := hy.1; rwa [Metric.mem_ball, dist_zero_right] at this) (min_le_left _ _)))
    hd hω hprim
    (fun t ht => heinv t (norm_pos_iff.mpr ht.2) (lt_of_lt_of_le (by
      have := ht.1; rwa [Metric.mem_ball, dist_zero_right] at this) (min_le_right _ _)))
  -- the `d`-th root of `u`
  have hroot_pow : ∀ u : ℂ, (u ^ ((d : ℂ)⁻¹)) ^ d = u := fun u =>
    Complex.cpow_nat_inv_pow u hd.ne'
  have hroot_norm : ∀ u : ℂ, ‖u ^ ((d : ℂ)⁻¹)‖ ^ d = ‖u‖ := by
    intro u
    rw [← norm_pow, hroot_pow u]
  have hmemR : Metric.ball (0 : ℂ) ((min r e) ^ d) ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 (pow_pos hρ d))
  -- on the punctured disc, `G₀` is `g` composed with the root map
  have hG₀_eq : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) ((min r e) ^ d) \ {0} →
      G₀ u = g (u ^ ((d : ℂ)⁻¹)) := by
    intro u hu
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu.2
    have hu1 : ‖u‖ < (min r e) ^ d := by
      have := hu.1; rwa [Metric.mem_ball, dist_zero_right] at this
    have ht0 : u ^ ((d : ℂ)⁻¹) ≠ 0 := by
      intro h0
      have := hroot_norm u
      rw [h0, norm_zero, zero_pow hd.ne'] at this
      exact hu0.ne' this.symm
    have htmem : u ^ ((d : ℂ)⁻¹) ∈ Metric.ball (0 : ℂ) (min r e) \ {0} := by
      refine ⟨?_, ht0⟩
      rw [Metric.mem_ball, dist_zero_right]
      have h2 : ‖u ^ ((d : ℂ)⁻¹)‖ ^ d < (min r e) ^ d := by
        rw [hroot_norm u]; exact hu1
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ.le hd.ne').mp h2
    have h := hG₀eq (u ^ ((d : ℂ)⁻¹)) htmem
    rw [hroot_pow u] at h
    exact h.symm
  -- the root map tends to `0`
  have hroot_tendsto : Tendsto (fun u : ℂ => u ^ ((d : ℂ)⁻¹)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 (pow_pos hδ d))] with u hu
    rw [Metric.mem_ball, dist_zero_right] at hu
    rw [dist_zero_right]
    have h2 : ‖u ^ ((d : ℂ)⁻¹)‖ ^ d < δ ^ d := by rw [hroot_norm u]; exact hu
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le hd.ne').mp h2
  have hG₀_tendsto : Tendsto G₀ (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) := by
    have h1 : Tendsto (fun u : ℂ => g (u ^ ((d : ℂ)⁻¹))) (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
      hg.continuousAt.tendsto.comp hroot_tendsto
    refine Filter.Tendsto.congr' ?_ h1
    filter_upwards [hmemR, self_mem_nhdsWithin] with u hu hune
    exact (hG₀_eq u ⟨hu, by simpa using hune⟩).symm
  -- the extension
  set G : ℂ → ℂ := Function.update G₀ 0 (g 0) with hGdef
  have hGcont : ContinuousAt G 0 := by
    rw [hGdef, continuousAt_update_same]
    exact hG₀_tendsto
  have hGan : AnalyticAt ℂ G 0 := by
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hGcont
    filter_upwards [hmemR, self_mem_nhdsWithin] with u hu hune
    have hu' : u ∈ Metric.ball (0 : ℂ) ((min r e) ^ d) \ {0} := ⟨hu, by simpa using hune⟩
    have hd1 : DifferentiableAt ℂ G₀ u := (hG₀an u hu').differentiableAt
    rw [hGdef]
    refine hd1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds (show u ≠ 0 from by simpa using hune)] with y hy
    exact Function.update_of_ne hy (g 0) G₀
  refine ⟨G, hGan, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hρ), self_mem_nhdsWithin]
    with z hz hzne
  have h1 := hG₀eq z ⟨hz, by simpa using hzne⟩
  rw [hGdef, h1]
  exact (Function.update_of_ne (pow_ne_zero d hzne) (g 0) G₀).symm

/-! ## Auxiliary facts about the chosen `d`-th root -/

/-- The `d`-th root of `ρ ^ d * ζ`, taken as the principal complex power `(ρᵈ ζ) ^ (1/d)`. -/
noncomputable def rRoot (ρ : ℝ) (d : ℕ) (ζ : ℂ) : ℂ := ((ρ : ℂ) ^ d * ζ) ^ ((d : ℂ)⁻¹)

lemma rRoot_pow {ρ : ℝ} {d : ℕ} (hd : 0 < d) (ζ : ℂ) : rRoot ρ d ζ ^ d = (ρ : ℂ) ^ d * ζ := by
  rw [rRoot]
  exact Complex.cpow_nat_inv_pow _ hd.ne'

lemma norm_rRoot_pow {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) (ζ : ℂ) :
    ‖rRoot ρ d ζ‖ ^ d = ρ ^ d * ‖ζ‖ := by
  rw [rRoot, ← norm_pow, Complex.cpow_nat_inv_pow _ hd.ne', norm_mul, norm_pow,
    Complex.norm_of_nonneg hρ.le]

/-- The four facts about `rRoot ρ d ζ` for `0 < ‖ζ‖ < 1` and a multiple `n` of `d`. -/
lemma rRoot_facts {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hζ0 : 0 < ‖ζ‖)
    (hζ1 : ‖ζ‖ < 1) {n : ℕ} (hn : d ∣ n) :
    0 < ‖rRoot ρ d ζ‖ ∧ ‖rRoot ρ d ζ‖ < ρ ∧ rRoot ρ d ζ ^ d = (ρ : ℂ) ^ d * ζ ∧
      rRoot ρ d ζ ^ n = (ρ : ℂ) ^ n * ζ ^ (n / d) := by
  have h := cpow_root_facts (ρ := ρ) hρ (d := d) hd hζ0 hζ1 (k := n) hn
  simpa only [rRoot] using h

/-- The same, with the power identity for every multiple of `d`. -/
lemma rRoot_facts_all {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hζ0 : 0 < ‖ζ‖)
    (hζ1 : ‖ζ‖ < 1) :
    0 < ‖rRoot ρ d ζ‖ ∧ ‖rRoot ρ d ζ‖ < ρ ∧ rRoot ρ d ζ ^ d = (ρ : ℂ) ^ d * ζ ∧
      ∀ n : ℕ, d ∣ n → rRoot ρ d ζ ^ n = (ρ : ℂ) ^ n * ζ ^ (n / d) := by
  obtain ⟨h1, h2, h3, -⟩ := rRoot_facts hρ hd hζ0 hζ1 (dvd_refl d)
  exact ⟨h1, h2, h3, fun n hn => (rRoot_facts hρ hd hζ0 hζ1 hn).2.2.2⟩

/-- Membership in a punctured ball, unfolded. -/
lemma mem_punctured_ball {R : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R \ {0}) :
    0 < ‖z‖ ∧ ‖z‖ < R :=
  ⟨norm_pos_iff.mpr hz.2, by have h := hz.1; rwa [Metric.mem_ball, dist_zero_right] at h⟩

/-- The punctured ball of radius `ρ ^ d` is invariant under `ζ ↦ ρ ^ d * ζ`, from the punctured
unit ball. -/
lemma mul_mem_punctured_ball {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} {ζ : ℂ}
    (hζ : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0}) :
    (ρ : ℂ) ^ d * ζ ∈ Metric.ball (0 : ℂ) (ρ ^ d) \ {0} := by
  obtain ⟨hζ0, hζ1⟩ := mem_punctured_ball hζ
  have hρc : ‖(ρ : ℂ)‖ = ρ := Complex.norm_of_nonneg hρ.le
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow, hρc]
    have : ρ ^ d * ‖ζ‖ < ρ ^ d * 1 :=
      mul_lt_mul_of_pos_left hζ1 (pow_pos hρ d)
    simpa using this
  · exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hρ.ne')) hζ.2

/-- **Meromorphy at `0` after composing with the root map.** If `f = Θ ∘ (·) ^ d` near `0` and `Θ`
is meromorphic at `0`, then `ζ ↦ f (rRoot ρ d ζ)` is meromorphic at `0`. -/
lemma meromorphicAt_rRoot_comp {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) {f Θ : ℂ → ℂ}
    (hΘ : MeromorphicAt Θ 0) (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = Θ (z ^ d)) :
    MeromorphicAt (fun ζ => f (rRoot ρ d ζ)) 0 := by
  have hΘ' : MeromorphicAt Θ ((fun ζ : ℂ => (ρ : ℂ) ^ d * ζ) 0) := by simpa using hΘ
  have hcomp : MeromorphicAt (fun ζ : ℂ => Θ ((ρ : ℂ) ^ d * ζ)) 0 :=
    hΘ'.comp_analyticAt (by fun_prop)
  refine hcomp.congr ?_
  show ∀ᶠ x in 𝓝[≠] (0 : ℂ), Θ ((ρ : ℂ) ^ d * x) = f (rRoot ρ d x)
  rw [eventually_nhdsWithin_iff] at h ⊢
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp h
  refine Metric.eventually_nhds_iff.mpr
    ⟨min ((ε / ρ) ^ d) (1 / 2), lt_min (by positivity) (by norm_num), fun ζ hζ hζne => ?_⟩
  have hζn : ‖ζ‖ < min ((ε / ρ) ^ d) (1 / 2) := by rwa [dist_zero_right] at hζ
  have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζne
  have hζ1 : ‖ζ‖ < 1 := lt_trans (lt_of_lt_of_le hζn (min_le_right _ _)) (by norm_num)
  have hlt : ‖ζ‖ < (ε / ρ) ^ d := lt_of_lt_of_le hζn (min_le_left _ _)
  have hr : ‖rRoot ρ d ζ‖ < ε := by
    have h1 : ‖rRoot ρ d ζ‖ ^ d < ε ^ d := by
      rw [norm_rRoot_pow hρ hd ζ]
      have h2 : ρ ^ d * ‖ζ‖ < ρ ^ d * (ε / ρ) ^ d := mul_lt_mul_of_pos_left hlt (pow_pos hρ d)
      have h3 : ρ ^ d * (ε / ρ) ^ d = ε ^ d := by
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero d hρ.ne')]
      rwa [h3] at h2
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le hd.ne').mp h1
  have hr0 : rRoot ρ d ζ ≠ 0 := by
    intro h0
    have h1 := rRoot_pow (ρ := ρ) hd ζ
    rw [h0, zero_pow hd.ne'] at h1
    exact (mul_ne_zero (pow_ne_zero d (Complex.ofReal_ne_zero.mpr hρ.ne')) hζne) h1.symm
  rw [hεP (by rwa [dist_zero_right]) hr0, rRoot_pow hd ζ]


/-- **Descent of a meromorphic germ invariant under a primitive root of unity**, proved from the
analytic-at-`0` descent. -/
lemma exists_meromorphic_descent' {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) {ω : ℂ}
    (hω : ω ^ d = 1) (hprim : ∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1) {f : ℂ → ℂ}
    (hmer : MeromorphicOn f (Metric.ball (0 : ℂ) ρ))
    (hinv : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → f (ω * t) = f t) :
    ∃ Θ : ℂ → ℂ, MeromorphicAt Θ 0 ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = Θ (z ^ d) := by
  classical
  have hprimroot : IsPrimitiveRoot ω d := by
    refine (IsPrimitiveRoot.iff_def ω d).mpr ⟨hω, fun l hl => ?_⟩
    by_contra hnd
    have hmod0 : l % d ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
    have hpos : 0 < l % d := Nat.pos_of_ne_zero hmod0
    have hlt : l % d < d := Nat.mod_lt _ hd
    have h1 : l = l % d + d * (l / d) := (Nat.mod_add_div l d).symm
    have hl1 : ω ^ (l % d) = 1 := by
      rw [h1, pow_add, pow_mul, hω, one_pow, mul_one] at hl
      exact hl
    exact hprim _ hpos hlt hl1
  have hωne : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow hd.ne'] at hω
    exact one_ne_zero hω.symm
  have hmer0 : MeromorphicAt f 0 := hmer 0 (by rw [Metric.mem_ball, dist_self]; exact hρ)
  rcases eq_or_ne (meromorphicOrderAt f 0) ⊤ with htop | htop
  · refine ⟨0, MeromorphicAt.const (0 : ℂ) 0, ?_⟩
    rw [meromorphicOrderAt_eq_top_iff] at htop
    filter_upwards [htop] with z hz
    rw [hz]; simp
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨g, hgan, hg0, heq⟩ := (meromorphicOrderAt_eq_int_iff hmer0).mp hn.symm
    have heq' : f =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z ^ n * g z := by
      filter_upwards [heq] with z hz
      simpa only [sub_zero, smul_eq_mul] using hz
    have hT : Tendsto (fun z : ℂ => ω * z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Tendsto (fun z : ℂ => ω * z) (𝓝 (0 : ℂ)) (𝓝 (ω * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        simpa using h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
        exact mul_ne_zero hωne hz
    have hinv' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f (ω * z) = f z := by
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hρ),
        self_mem_nhdsWithin] with z hz hzne
      exact hinv z (norm_pos_iff.mpr hzne) (by rwa [Metric.mem_ball, dist_zero_right] at hz)
    have hkey : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ω ^ n * g (ω * z) = g z := by
      filter_upwards [heq', hT.eventually heq', hinv', self_mem_nhdsWithin]
        with z h1 h2 h3 hzne
      have h4 : (ω * z) ^ n * g (ω * z) = z ^ n * g z := by rw [← h2, h3, h1]
      have hz : z ^ n ≠ 0 := zpow_ne_zero n hzne
      refine mul_left_cancel₀ hz ?_
      calc z ^ n * (ω ^ n * g (ω * z)) = (ω * z) ^ n * g (ω * z) := by
            rw [mul_zpow]; ring
        _ = z ^ n * g z := h4
    have hωn : ω ^ n = 1 := by
      have hωz : Tendsto (fun z : ℂ => ω * z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have h : Tendsto (fun z : ℂ => ω * z) (𝓝 (0 : ℂ)) (𝓝 (ω * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        simpa using h.mono_left nhdsWithin_le_nhds
      have hlim : Tendsto (fun z : ℂ => ω ^ n * g (ω * z)) (𝓝[≠] (0 : ℂ)) (𝓝 (ω ^ n * g 0)) :=
        Tendsto.mul tendsto_const_nhds (hgan.continuousAt.tendsto.comp hωz)
      have hg0t : Tendsto (fun z : ℂ => g z) (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
        hgan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hkey' : (fun z : ℂ => ω ^ n * g (ω * z)) =ᶠ[𝓝[≠] (0 : ℂ)] fun z => g z := hkey
      have hlim2 : Tendsto (fun z : ℂ => ω ^ n * g (ω * z)) (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
        Filter.Tendsto.congr' hkey'.symm hg0t
      have h3 : ω ^ n * g 0 = g 0 := tendsto_nhds_unique hlim hlim2
      exact mul_right_cancel₀ hg0 (by rw [h3, one_mul])
    obtain ⟨q, hq⟩ := hprimroot.zpow_eq_one_iff_dvd n |>.mp hωn
    have hginv : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g (ω * z) = g z := by
      filter_upwards [hkey] with z hz
      rw [hωn, one_mul] at hz
      exact hz
    obtain ⟨G, hGan, hGeq⟩ := exists_analyticAt_descent_aux hd hω hprim hgan hginv
    refine ⟨fun u => u ^ q * G u, ((MeromorphicAt.id 0).zpow q).mul hGan.meromorphicAt, ?_⟩
    filter_upwards [heq', hGeq] with z h1 h2
    rw [h1, h2, hq]
    have hzq : z ^ ((d : ℤ) * q) = (z ^ d) ^ q := by
      rw [zpow_mul, zpow_natCast]
    rw [hzq]

/-- **A continuous genuine family of chains over a punctured disc is covered by one punctured chart.**

`F` is a *continuous* map from the punctured disc of radius `ρ > 0` into chain data, takes values in
`⁰H`, satisfies `ψ₁ (F t) = z₀ + t^k` with `k ≥ 1` and `z₀ ≠ 0`, and every coordinate of `F` is
meromorphic on the ball `B(0,ρ)`. Then the image of `F` over the half disc `0 < ‖t‖ < ρ/2` is
contained in the image of a single punctured chart.

Continuity is essential: the stabiliser `{ω : ω^k = 1, F (ω t) = F t}` must be closed, which needs
the implication "`F (ω t₀) = F t₀` for one `t₀` implies `F (ω t) = F t` everywhere". That follows
from `Work.EQ.H0_structure` (clause 1: `IsLocalHomeomorph`/`LocalInj`, i.e. `ψ₁` is locally
injective on `H0`): the agreement set of two continuous sections is closed (by continuity) and open
(by local injectivity), and the punctured disc is connected.

This is the "primitive reduction" (Rychlik F3). The stabiliser is a cyclic subgroup `μ_d` of the
`k`-th roots of unity; a function meromorphic on the ball and invariant under a primitive `d`-th
root of unity is a meromorphic function of `t^d`; the family descends to `ξ ↦ F t`, `t^d = ξ` (well
defined by the invariance), the descended family has trivial stabiliser and hence is injective, and
`ψ₁ = z₀ + ξ^{k/d}`. The chart is the descended family rescaled by a suitable `c` with
`c ≤ ρ^d` (validity on the whole punctured unit disc) and `c/2 ≥ (ρ/2)^d` (coverage of the half
disc): its image over `‖ζ‖ < 1/2` contains `F t` for `0 < ‖t‖ < ρ/2`. The exact scale is
irrelevant since `κ` is existential. -/
theorem puncturedChart_covering_family2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {k : ℕ} (hk : 1 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) {F : ℂ → ChainData}
    (hcont : ContinuousOn F {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ})
    (hmem : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → F t ∈ H0 a h)
    (hpsi : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → (F t).2.1 = z₀ + t ^ k)
    (hmer1 : ∀ n : ℤ, MeromorphicOn (fun t => ((F t).1 n).1) (Metric.ball 0 ρ))
    (hmer2 : ∀ n : ℤ, MeromorphicOn (fun t => ((F t).1 n).2) (Metric.ball 0 ρ))
    (hmer3 : MeromorphicOn (fun t => (F t).2.2) (Metric.ball 0 ρ)) :
    ∃ (e : ℂ → ChainData) (u₀ : ℂ) (k' : ℕ), IsPuncturedChart a h e u₀ k' ∧
      ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ / 2 → F t ∈ e '' (Metric.ball (0 : ℂ) (1 / 2) \ {0}) := by
  classical
  have hk0 : k ≠ 0 := by omega
  -- the punctured disc of radius `ρ`, as an open set
  have hD : {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ} = Metric.ball (0 : ℂ) ρ \ {0} := by
    ext t
    simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, norm_pos_iff.mp h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨norm_pos_iff.mpr h2, h1⟩
  have hcontU : ContinuousOn F (Metric.ball (0 : ℂ) ρ \ {0}) := by rw [← hD]; exact hcont
  have hUopen : IsOpen (Metric.ball (0 : ℂ) ρ \ {0}) :=
    Work.Topology.isOpen_ball_diff_singleton ρ
  ----------------------------------------------------------------------------------------------
  -- ### 1. the stabiliser subgroup of the family
  ----------------------------------------------------------------------------------------------
  let S : Set ℂ := {ω : ℂ | ω ^ k = 1 ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → F (ω * t) = F t}
  have hSdef : ∀ ω : ℂ, ω ∈ S ↔
      ω ^ k = 1 ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → F (ω * t) = F t := fun ω => Iff.rfl
  have hSnorm : ∀ a : ℂ, a ∈ S → ‖a‖ = 1 := by
    intro a ha
    have h1 : ‖a‖ ^ k = 1 := by rw [← norm_pow, (hSdef a).mp ha |>.1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hk0).mp h1
  have hS1 : (1 : ℂ) ∈ S := by
    refine (hSdef 1).mpr ⟨one_pow k, ?_⟩
    intro t _ _; simp
  have hSmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    refine (hSdef (a * b)).mpr ⟨?_, ?_⟩
    · rw [mul_pow, (hSdef a).mp ha |>.1, (hSdef b).mp hb |>.1, one_mul]
    · intro t ht1 ht2
      have hbt : 0 < ‖b * t‖ ∧ ‖b * t‖ < ρ := by
        rw [norm_mul, hSnorm b hb, one_mul]; exact ⟨ht1, ht2⟩
      calc F ((a * b) * t) = F (a * (b * t)) := by rw [mul_assoc]
        _ = F (b * t) := (hSdef a).mp ha |>.2 (b * t) hbt.1 hbt.2
        _ = F t := (hSdef b).mp hb |>.2 t ht1 ht2
  have hSinv : ∀ a ∈ S, a⁻¹ ∈ S := by
    intro a ha
    have hane : a ≠ 0 := by
      intro h0
      have h1 := hSnorm a ha
      rw [h0, norm_zero] at h1
      exact one_ne_zero h1.symm
    refine (hSdef a⁻¹).mpr ⟨?_, ?_⟩
    · rw [inv_pow, (hSdef a).mp ha |>.1, inv_one]
    · intro t ht1 ht2
      have hat : 0 < ‖a⁻¹ * t‖ ∧ ‖a⁻¹ * t‖ < ρ := by
        rw [norm_mul, norm_inv, hSnorm a ha, inv_one, one_mul]; exact ⟨ht1, ht2⟩
      have h1 : F (a * (a⁻¹ * t)) = F (a⁻¹ * t) := (hSdef a).mp ha |>.2 (a⁻¹ * t) hat.1 hat.2
      rw [mul_inv_cancel_left₀ hane t] at h1
      exact h1.symm
  have hSfin : S.Finite := by
    haveI : NeZero k := ⟨hk0⟩
    have hsub : S ⊆ {z : ℂ | z ^ k = 1} := fun z hz => (hSdef z).mp hz |>.1
    have hfin : ({z : ℂ | z ^ k = 1} : Set ℂ).Finite := by
      have heq : {z : ℂ | z ^ k = 1} =
          (fun ζ : rootsOfUnity k ℂ => ((ζ : ℂˣ) : ℂ)) '' Set.univ := by
        ext z
        constructor
        · intro hz
          exact ⟨rootsOfUnity.mkOfPowEq z hz, Set.mem_univ _, rootsOfUnity.coe_mkOfPowEq hz⟩
        · rintro ⟨ζ, -, rfl⟩
          exact (mem_rootsOfUnity' k (ζ : ℂˣ)).mp ζ.2
      rw [heq]
      exact Set.Finite.image _ Set.finite_univ
    exact hfin.subset hsub
  obtain ⟨d, ω, hd, hdvd, hωS, hωd, hωprim, hSiff⟩ :=
    finite_subgroup_complex_eq_rootsOfUnity hk hS1 hSmul hSinv
      (fun a ha => (hSdef a).mp ha |>.1) hSfin
  have hFinv : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → F (ω * t) = F t := fun t h1 h2 =>
    (hSdef ω).mp hωS |>.2 t h1 h2
  have hmuS : ∀ u : ℂ, u ^ d = 1 → u ∈ S := fun u hu => (hSiff u).mpr hu
  have hSmu : ∀ u ∈ S, u ^ d = 1 := fun u hu => (hSiff u).mp hu
  ----------------------------------------------------------------------------------------------
  -- ### 2. the coordinates of `F` are analytic on the punctured disc
  ----------------------------------------------------------------------------------------------
  have hproj1 : ∀ n : ℤ, Continuous (fun p : ChainData => ((p.1 n).1)) := fun n =>
    continuous_fst.comp ((continuous_apply n).comp continuous_fst)
  have hproj2 : ∀ n : ℤ, Continuous (fun p : ChainData => ((p.1 n).2)) := fun n =>
    continuous_snd.comp ((continuous_apply n).comp continuous_fst)
  have hproj3 : Continuous (fun p : ChainData => p.2.1) := continuous_fst.comp continuous_snd
  have hproj4 : Continuous (fun p : ChainData => p.2.2) := continuous_snd.comp continuous_snd
  have hc1 : ∀ n : ℤ, ContinuousOn (fun t : ℂ => ((F t).1 n).1)
      (Metric.ball (0 : ℂ) ρ \ {0}) := fun n =>
    ((hproj1 n).continuousOn).comp hcontU (fun _ _ => Set.mem_univ _)
  have hc2 : ∀ n : ℤ, ContinuousOn (fun t : ℂ => ((F t).1 n).2)
      (Metric.ball (0 : ℂ) ρ \ {0}) := fun n =>
    ((hproj2 n).continuousOn).comp hcontU (fun _ _ => Set.mem_univ _)
  have hc3 : ContinuousOn (fun t : ℂ => (F t).2.2) (Metric.ball (0 : ℂ) ρ \ {0}) :=
    (hproj4.continuousOn).comp hcontU (fun _ _ => Set.mem_univ _)
  have hc4 : ContinuousOn (fun t : ℂ => (F t).2.1) (Metric.ball (0 : ℂ) ρ \ {0}) :=
    (hproj3.continuousOn).comp hcontU (fun _ _ => Set.mem_univ _)
  have han1 : ∀ n : ℤ, AnalyticOnNhd ℂ (fun t : ℂ => ((F t).1 n).1)
      (Metric.ball (0 : ℂ) ρ \ {0}) := by
    intro n t ht
    exact ((hmer1 n) t ht.1).analyticAt
      ((hc1 n).continuousWithinAt ht |>.continuousAt (hUopen.mem_nhds ht))
  have han2 : ∀ n : ℤ, AnalyticOnNhd ℂ (fun t : ℂ => ((F t).1 n).2)
      (Metric.ball (0 : ℂ) ρ \ {0}) := by
    intro n t ht
    exact ((hmer2 n) t ht.1).analyticAt
      ((hc2 n).continuousWithinAt ht |>.continuousAt (hUopen.mem_nhds ht))
  have han3 : AnalyticOnNhd ℂ (fun t : ℂ => (F t).2.2) (Metric.ball (0 : ℂ) ρ \ {0}) := by
    intro t ht
    exact (hmer3 t ht.1).analyticAt
      (hc3.continuousWithinAt ht |>.continuousAt (hUopen.mem_nhds ht))
  have hinv1 : ∀ n : ℤ, ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} →
      ((F (ω * t)).1 n).1 = ((F t).1 n).1 := by
    intro n t ht
    rw [hFinv t (mem_punctured_ball ht).1 (mem_punctured_ball ht).2]
  have hinv2 : ∀ n : ℤ, ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} →
      ((F (ω * t)).1 n).2 = ((F t).1 n).2 := by
    intro n t ht
    rw [hFinv t (mem_punctured_ball ht).1 (mem_punctured_ball ht).2]
  have hinv3 : ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → (F (ω * t)).2.2 = (F t).2.2 := by
    intro t ht
    rw [hFinv t (mem_punctured_ball ht).1 (mem_punctured_ball ht).2]
  have hinv4 : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → F (ω * t) = F t := hFinv
  ----------------------------------------------------------------------------------------------
  -- ### 3. the descents of the coordinate functions
  ----------------------------------------------------------------------------------------------
  have hfac1 : ∀ n : ℤ, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (ρ ^ d) \ {0}) ∧
      ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → ((F t).1 n).1 = g (t ^ d) := fun n =>
    Work.Topology.exists_factor_of_root_invariant hρ (han1 n) hd hωd hωprim (hinv1 n)
  have hfac2 : ∀ n : ℤ, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (ρ ^ d) \ {0}) ∧
      ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → ((F t).1 n).2 = g (t ^ d) := fun n =>
    Work.Topology.exists_factor_of_root_invariant hρ (han2 n) hd hωd hωprim (hinv2 n)
  have hfac3 : ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (ρ ^ d) \ {0}) ∧
      ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → (F t).2.2 = g (t ^ d) :=
    Work.Topology.exists_factor_of_root_invariant hρ han3 hd hωd hωprim hinv3
  choose g1 hg1an hg1eq using hfac1
  choose g2 hg2an hg2eq using hfac2
  choose g3 hg3an hg3eq using hfac3
  have hmerd1 : ∀ n : ℤ, ∃ Θ : ℂ → ℂ, MeromorphicAt Θ 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), ((F z).1 n).1 = Θ (z ^ d) := fun n =>
    exists_meromorphic_descent' hρ hd hωd hωprim (hmer1 n) (fun t h1 h2 => by rw [hFinv t h1 h2])
  have hmerd2 : ∀ n : ℤ, ∃ Θ : ℂ → ℂ, MeromorphicAt Θ 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), ((F z).1 n).2 = Θ (z ^ d) := fun n =>
    exists_meromorphic_descent' hρ hd hωd hωprim (hmer2 n) (fun t h1 h2 => by rw [hFinv t h1 h2])
  have hmerd3 : ∃ Θ : ℂ → ℂ, MeromorphicAt Θ 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), (F z).2.2 = Θ (z ^ d) :=
    exists_meromorphic_descent' hρ hd hωd hωprim hmer3 (fun t h1 h2 => by rw [hFinv t h1 h2])
  choose Θ1 hΘ1mer hΘ1eq using hmerd1
  choose Θ2 hΘ2mer hΘ2eq using hmerd2
  choose Θ3 hΘ3mer hΘ3eq using hmerd3
  ----------------------------------------------------------------------------------------------
  -- ### 4. the family, rescaled and descended, and its continuity
  ----------------------------------------------------------------------------------------------
  have hrt : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 →
      0 < ‖rRoot ρ d ζ‖ ∧ ‖rRoot ρ d ζ‖ < ρ ∧ rRoot ρ d ζ ^ d = (ρ : ℂ) ^ d * ζ ∧
        ∀ n : ℕ, d ∣ n → rRoot ρ d ζ ^ n = (ρ : ℂ) ^ n * ζ ^ (n / d) :=
    fun ζ h1 h2 => rRoot_facts_all hρ hd h1 h2
  have hrt_mem : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 → rRoot ρ d ζ ∈ Metric.ball (0 : ℂ) ρ \ {0} := by
    intro ζ h1 h2
    obtain ⟨h3, h4, -, -⟩ := hrt ζ h1 h2
    exact ⟨by rw [Metric.mem_ball, dist_zero_right]; exact h4, by simpa using h3.ne'⟩
  -- the explicit assembly of continuous coordinates
  have hmulc : ContinuousOn (fun ζ : ℂ => (ρ : ℂ) ^ d * ζ) (Metric.ball (0 : ℂ) 1 \ {0}) :=
    ContinuousOn.const_mul continuousOn_id ((ρ : ℂ) ^ d)
  have hEcont : ContinuousOn (fun ζ : ℂ =>
      ((fun n : ℤ => (g1 n ((ρ : ℂ) ^ d * ζ), g2 n ((ρ : ℂ) ^ d * ζ))),
        z₀ + (ρ : ℂ) ^ k * ζ ^ (k / d), g3 ((ρ : ℂ) ^ d * ζ)))
      (Metric.ball (0 : ℂ) 1 \ {0}) := by
    refine ContinuousOn.prodMk (continuousOn_pi' fun n => ContinuousOn.prodMk ?_ ?_)
      (ContinuousOn.prodMk ?_ ?_)
    · exact ((hg1an n).continuousOn).comp hmulc (fun ζ hζ => mul_mem_punctured_ball hρ hζ)
    · exact ((hg2an n).continuousOn).comp hmulc (fun ζ hζ => mul_mem_punctured_ball hρ hζ)
    · fun_prop
    · exact ((hg3an).continuousOn).comp hmulc (fun ζ hζ => mul_mem_punctured_ball hρ hζ)
  -- the chart function
  have hEE : ∀ ζ : ℂ, ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} →
      F (rRoot ρ d ζ) = ((fun n : ℤ => (g1 n ((ρ : ℂ) ^ d * ζ), g2 n ((ρ : ℂ) ^ d * ζ))),
        z₀ + (ρ : ℂ) ^ k * ζ ^ (k / d), g3 ((ρ : ℂ) ^ d * ζ)) := by
    intro ζ hζ
    obtain ⟨hζ0, hζ1⟩ := mem_punctured_ball hζ
    obtain ⟨hr0, hrρ, hrd, hrall⟩ := hrt ζ hζ0 hζ1
    have hrmem : rRoot ρ d ζ ∈ Metric.ball (0 : ℂ) ρ \ {0} := hrt_mem ζ hζ0 hζ1
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext n
      refine Prod.ext ?_ ?_
      · rw [hg1eq n (rRoot ρ d ζ) hrmem, hrd]
      · rw [hg2eq n (rRoot ρ d ζ) hrmem, hrd]
    · rw [hpsi (rRoot ρ d ζ) hr0 hrρ, hrall k hdvd]
    · rw [hg3eq (rRoot ρ d ζ) hrmem, hrd]
  have hchart_cont : ContinuousOn (fun ζ : ℂ => F (rRoot ρ d ζ)) (Metric.ball (0 : ℂ) 1 \ {0}) :=
    hEcont.congr hEE
  ----------------------------------------------------------------------------------------------
  -- ### 5. the chart's coordinates are meromorphic at `0`
  ----------------------------------------------------------------------------------------------
  have hmer_coord1 : ∀ n : ℤ, MeromorphicAt (fun ζ : ℂ => ((F (rRoot ρ d ζ)).1 n).1) 0 :=
    fun n => meromorphicAt_rRoot_comp hρ hd (hΘ1mer n) (hΘ1eq n)
  have hmer_coord2 : ∀ n : ℤ, MeromorphicAt (fun ζ : ℂ => ((F (rRoot ρ d ζ)).1 n).2) 0 :=
    fun n => meromorphicAt_rRoot_comp hρ hd (hΘ2mer n) (hΘ2eq n)
  have hmer_coord3 : MeromorphicAt (fun ζ : ℂ => (F (rRoot ρ d ζ)).2.2) 0 :=
    meromorphicAt_rRoot_comp hρ hd hΘ3mer hΘ3eq
  ----------------------------------------------------------------------------------------------
  -- ### 6. injectivity of the chart on the punctured unit disc
  ----------------------------------------------------------------------------------------------
  have hinj : Set.InjOn (fun ζ : ℂ => F (rRoot ρ d ζ)) (Metric.ball (0 : ℂ) 1 \ {0}) := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ heq
    have heq' : F (rRoot ρ d ζ₁) = F (rRoot ρ d ζ₂) := heq
    obtain ⟨hζ₁0, hζ₁1⟩ := mem_punctured_ball hζ₁
    obtain ⟨hζ₂0, hζ₂1⟩ := mem_punctured_ball hζ₂
    obtain ⟨hr₁0, hr₁ρ, hr₁d, hr₁k⟩ := rRoot_facts hρ hd hζ₁0 hζ₁1 hdvd
    obtain ⟨hr₂0, hr₂ρ, hr₂d, hr₂k⟩ := rRoot_facts hρ hd hζ₂0 hζ₂1 hdvd
    have hr₂ne : rRoot ρ d ζ₂ ≠ 0 := norm_pos_iff.mp hr₂0
    have hpsik : (rRoot ρ d ζ₁) ^ k = (rRoot ρ d ζ₂) ^ k := by
      have h1 := hpsi (rRoot ρ d ζ₁) hr₁0 hr₁ρ
      have h2 := hpsi (rRoot ρ d ζ₂) hr₂0 hr₂ρ
      have h3 : (F (rRoot ρ d ζ₁)).2.1 = (F (rRoot ρ d ζ₂)).2.1 := by rw [heq']
      rw [h1, h2] at h3
      exact add_left_cancel h3
    have huk : (rRoot ρ d ζ₁ / rRoot ρ d ζ₂) ^ k = 1 := by
      rw [div_pow, hpsik, div_self (pow_ne_zero k hr₂ne)]
    have hut : (rRoot ρ d ζ₁ / rRoot ρ d ζ₂) * rRoot ρ d ζ₂ = rRoot ρ d ζ₁ :=
      div_mul_cancel₀ _ hr₂ne
    have hfix : F ((rRoot ρ d ζ₁ / rRoot ρ d ζ₂) * rRoot ρ d ζ₂) = F (rRoot ρ d ζ₂) := by
      rw [hut, heq']
    have hstab := stab_invariance_of_one_point ha0 ha1 hh hk hρ hcont hmem hpsi huk hr₂0 hr₂ρ hfix
    have huS : rRoot ρ d ζ₁ / rRoot ρ d ζ₂ ∈ S :=
      (hSdef _).mpr ⟨huk, hstab⟩
    have hud : (rRoot ρ d ζ₁ / rRoot ρ d ζ₂) ^ d = 1 := hSmu _ huS
    have h1 : rRoot ρ d ζ₁ ^ d / rRoot ρ d ζ₂ ^ d = 1 := by rw [← div_pow]; exact hud
    have h2 : rRoot ρ d ζ₁ ^ d = rRoot ρ d ζ₂ ^ d :=
      (div_eq_one_iff_eq (pow_ne_zero d hr₂ne)).mp h1
    rw [hr₁d, hr₂d] at h2
    exact mul_left_cancel₀ (pow_ne_zero d (Complex.ofReal_ne_zero.mpr hρ.ne')) h2
  ----------------------------------------------------------------------------------------------
  -- ### 7. the claim
  ----------------------------------------------------------------------------------------------
  refine ⟨fun ζ => F (rRoot ρ d ζ), z₀, k / d, ?_, ?_⟩
  · unfold IsPuncturedChart
    refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd, hz₀, (ρ : ℂ) ^ k, ?_, ?_, hinj,
      hchart_cont, hmer_coord3, fun n => ⟨hmer_coord1 n, hmer_coord2 n⟩⟩
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hρ.ne')
    · intro ζ hζ
      obtain ⟨hζ0, hζ1⟩ := mem_punctured_ball hζ
      obtain ⟨hr0, hrρ, hrd, hrall⟩ := hrt ζ hζ0 hζ1
      refine ⟨hmem (rRoot ρ d ζ) hr0 hrρ, ?_⟩
      rw [hpsi (rRoot ρ d ζ) hr0 hrρ, hrall k hdvd]
  · -- coverage of the half disc
    intro t ht0 htρ
    have htne : t ≠ 0 := norm_pos_iff.mp ht0
    have htρ' : ‖t‖ < ρ := by linarith
    set ζ : ℂ := (t / (ρ : ℂ)) ^ d with hζdef
    have hζnorm : ‖(t / (ρ : ℂ))‖ < 1 / 2 := by
      rw [norm_div, Complex.norm_of_nonneg hρ.le, div_lt_iff₀ hρ]
      linarith
    have hζmem : ζ ∈ Metric.ball (0 : ℂ) (1 / 2) \ {0} := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, hζdef, norm_pow]
        have h2 : ‖t / (ρ : ℂ)‖ ^ d < (1 / 2) ^ d :=
          (pow_lt_pow_iff_left₀ (norm_nonneg _) (by norm_num) hd.ne').mpr hζnorm
        have h3 : (1 / 2 : ℝ) ^ d ≤ 1 / 2 :=
          pow_le_of_le_one (by norm_num) (by norm_num) hd.ne'
        linarith
      · rw [hζdef]
        exact pow_ne_zero _ (div_ne_zero htne (Complex.ofReal_ne_zero.mpr hρ.ne'))
    refine ⟨ζ, hζmem, ?_⟩
    obtain ⟨hζ0, hζ1⟩ := mem_punctured_ball hζmem
    obtain ⟨hr0, hrρ, hrd, -⟩ := hrt ζ hζ0 (lt_trans hζ1 (by norm_num))
    have hzt : (ρ : ℂ) ^ d * ζ = t ^ d := by
      rw [hζdef, div_pow,
        mul_div_cancel₀ _ (pow_ne_zero d (Complex.ofReal_ne_zero.mpr hρ.ne'))]
    have hroot : (rRoot ρ d ζ / t) ^ d = 1 := by
      rw [div_pow, hrd, hzt, div_self (pow_ne_zero d htne)]
    have huS : rRoot ρ d ζ / t ∈ S := hmuS _ hroot
    have hut : (rRoot ρ d ζ / t) * t = rRoot ρ d ζ := div_mul_cancel₀ _ htne
    show F (rRoot ρ d ζ) = F t
    rw [← hut, (hSdef _).mp huS |>.2 t ht0 htρ']
  ----------------------------------------------------------------------------------------------
  -- the auxiliary `hrt_mem` etc. remain available
  ----------------------------------------------------------------------------------------------

end Work.EQ.Chart
