import Mathlib
import Submission.Work.LandLeaves.SnailLemma
import Submission.Work.LandLeaves.exists_leading_coeff
import Submission.Work.LandLeaves.tendsto_sigma_zero
import Submission.Work.LandLeaves.tendsto_normRatio_sub
import Submission.Work.LandLeaves.isCompact_nonempty_isPreconnected_limitSet
import Submission.Work.LandLeaves.sphere_subset_closure_range_pow
import Submission.Work.LandLeaves.false_of_preconnected_sector_boundary
import Submission.Work.LandLeaves.false_of_preconnected_sector
import Submission.Work.LandLeaves.twist_tendsto_zero
import Submission.Work.LandLeaves.false_of_preconnected_sector_ord_ge_three
import Submission.Work.LandLeaves.isCompact_nonempty_isPreconnected_limitSet_of_subset_compact
import Submission.Work.LandLeaves.exists_unit_pow_pos
import Submission.Work.LandLeaves.sector_bound
import Submission.Work.LandLeaves.false_of_preconnected_sector_boundary_one_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Topology
open scoped Topology

namespace Work.LandLeaves

/-- Under the hypotheses of the Snail lemma, the shifted curve `Γ t = γ t - z₀` never vanishes
(the strict decrease at `t` already forces `γ t ≠ z₀` since `σ t ∈ (0,1]`), and the shifted germ
`F w = f (w + z₀) - z₀` intertwines `Γ` with `σ` and strictly decreases the norm. -/
theorem snail_setup {f : ℂ → ℂ} {z₀ : ℂ} {γ : ℝ → ℂ} {σ : ℝ → ℝ}
    (hcomp : ∀ t ∈ Set.Ioc (0:ℝ) 1, f (γ t) = γ (σ t))
    (hdec : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖γ (σ t) - z₀‖ < ‖γ t - z₀‖) :
    (∀ t ∈ Set.Ioc (0:ℝ) 1, γ t - z₀ ≠ 0) ∧
      (∀ t ∈ Set.Ioc (0:ℝ) 1, (fun w : ℂ => f (w + z₀) - z₀) (γ t - z₀) = γ (σ t) - z₀) ∧
      (∀ t ∈ Set.Ioc (0:ℝ) 1, ‖γ (σ t) - z₀‖ < ‖γ t - z₀‖) := by
  refine ⟨?_, ?_, hdec⟩
  · intro t ht hzero
    have h1 := hdec t ht
    rw [hzero, norm_zero] at h1
    exact absurd h1 (not_lt.mpr (norm_nonneg _))
  · intro t ht
    have h1 : γ t - z₀ + z₀ = γ t := by ring
    change f ((γ t - z₀) + z₀) - z₀ = γ (σ t) - z₀
    rw [h1, hcomp t ht]

theorem snailLemma : Work.LandLeaves.SnailLemma := by
  intro f z₀ γ σ hana hfix hnorm hγc hγt hσc hσm hcomp hdec
  set lam : ℂ := deriv f z₀ with hlamdef
  set F : ℂ → ℂ := fun w => f (w + z₀) - z₀ with hFdef
  set Γ : ℝ → ℂ := fun t => γ t - z₀ with hΓdef
  obtain ⟨hΓne0, hFcomp0, hdecΓ0⟩ := snail_setup hcomp hdec
  have hΓne : ∀ t ∈ Set.Ioc (0:ℝ) 1, Γ t ≠ 0 := by
    intro t ht
    rw [hΓdef]
    exact hΓne0 t ht
  have hFcomp : ∀ t ∈ Set.Ioc (0:ℝ) 1, F (Γ t) = Γ (σ t) := by
    intro t ht
    rw [hFdef, hΓdef]
    exact hFcomp0 t ht
  have hdecΓ : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Γ (σ t)‖ < ‖Γ t‖ := by
    intro t ht
    rw [hΓdef]
    exact hdecΓ0 t ht
  have hΓtend : Tendsto Γ (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hγt.sub (tendsto_const_nhds (x := z₀))
    simpa only [Pi.sub_apply, sub_self] using h
  have hΓcont : ContinuousOn Γ (Set.Ioc (0:ℝ) 1) := by
    have h := hγc.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => z₀) (Set.Ioc 0 1))
    convert h using 1
  have hσ0 : Tendsto σ (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_sigma_zero hΓcont hΓtend hσm hdecΓ
  have hFana : AnalyticAt ℂ F 0 := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => w + z₀) 0 := analyticAt_id.add analyticAt_const
    have hana' : AnalyticAt ℂ f ((fun w : ℂ => w + z₀) 0) := by simpa using hana
    have h2 : AnalyticAt ℂ (fun w : ℂ => f (w + z₀)) 0 := AnalyticAt.comp hana' h1
    have h3 : AnalyticAt ℂ (fun w : ℂ => f (w + z₀) - z₀) 0 := h2.sub analyticAt_const
    simpa [hFdef] using h3
  have hF0 : F 0 = 0 := by
    rw [hFdef]
    simp [hfix]
  have hFderiv : deriv F 0 = lam := by
    have h1 : HasDerivAt (fun w : ℂ => w + z₀) 1 0 := by
      simpa using (hasDerivAt_id (0:ℂ)).add_const z₀
    have h2 : HasDerivAt f (deriv f z₀) ((fun w : ℂ => w + z₀) 0) := by
      simpa using hana.differentiableAt.hasDerivAt
    have h3 : HasDerivAt (fun w : ℂ => f (w + z₀)) (deriv f z₀ * 1) 0 := h2.comp 0 h1
    have h5 : HasDerivAt (fun w : ℂ => f (w + z₀) - z₀) (deriv f z₀ * 1) 0 := h3.sub_const z₀
    have h6 : deriv (fun w : ℂ => f (w + z₀) - z₀) 0 = deriv f z₀ * 1 := by
      simpa using h5.deriv
    rw [hFdef, hlamdef, h6]
    ring
  have hexp1 : (fun z : ℂ => F z - lam * z) =o[𝓝 (0:ℂ)] (fun z : ℂ => z) := by
    have h := hFana.differentiableAt.hasDerivAt.isLittleO
    rw [hFderiv, hF0] at h
    simpa [mul_comm] using h
  -- the direction function and the limit set
  set u : ℝ → ℂ := fun t => Γ t / ‖Γ t‖ with hudef
  set L : Set ℂ := ⋂ δ ∈ Set.Ioc (0:ℝ) 1, closure (u '' Set.Ioc (0:ℝ) δ) with hLdef
  have hucont : ContinuousOn u (Set.Ioc (0:ℝ) 1) := by
    have hden : ContinuousOn (fun t : ℝ => ((‖Γ t‖ : ℝ) : ℂ)) (Set.Ioc (0:ℝ) 1) :=
      Complex.continuous_ofReal.comp_continuousOn hΓcont.norm
    have hmain : ContinuousOn (fun t : ℝ => Γ t / ((‖Γ t‖ : ℝ) : ℂ)) (Set.Ioc (0:ℝ) 1) :=
      hΓcont.div hden (by
        intro t ht
        exact fun h => norm_ne_zero_iff.mpr (hΓne t ht) (Complex.ofReal_eq_zero.mp h))
    simpa [hudef] using hmain
  have hu_sph : ∀ t ∈ Set.Ioc (0:ℝ) 1, u t ∈ Metric.sphere (0:ℂ) 1 := by
    intro t ht
    have hne : ‖Γ t‖ ≠ 0 := norm_ne_zero_iff.mpr (hΓne t ht)
    simp only [Metric.mem_sphere, dist_zero_right, sub_zero]
    rw [hudef]
    have h2 : ‖(((‖Γ t‖ : ℝ)) : ℂ)‖ = ‖Γ t‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [norm_div, h2, div_self hne]
  have hLdata : IsCompact L ∧ L.Nonempty ∧ IsPreconnected L := by
    have h := isCompact_nonempty_isPreconnected_limitSet_of_subset_compact
      (K := Metric.sphere (0:ℂ) 1) (isCompact_sphere 0 1) (δ₀ := 1) one_pos hucont
      (by intro t ht; exact hu_sph t ht)
    simpa [hLdef] using h
  obtain ⟨hLcpt, hLne, hLpre⟩ := hLdata
  have hLsph : ∀ d ∈ L, ‖d‖ = 1 := by
    intro d hd
    have hsub : u '' Set.Ioc (0:ℝ) 1 ⊆ Metric.sphere (0:ℂ) 1 := by
      rintro x ⟨t, ht, rfl⟩
      exact hu_sph t ht
    have hclosed : IsClosed (Metric.sphere (0:ℂ) 1) := Metric.isClosed_sphere
    have h1 : d ∈ closure (u '' Set.Ioc (0:ℝ) 1) := by
      rw [hLdef] at hd
      exact Set.mem_iInter₂.mp hd 1 ⟨one_pos, le_refl 1⟩
    have h2 : d ∈ Metric.sphere (0:ℂ) 1 := hclosed.closure_subset_iff.mpr hsub h1
    simpa [Metric.mem_sphere, dist_zero_right, sub_zero] using h2
  have hLsph' : L ⊆ Metric.sphere (0:ℂ) 1 := fun d hd => by
    simpa only [Metric.mem_sphere, dist_zero_right, sub_zero] using hLsph d hd
  have hΓt' : Tendsto Γ (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
    have htgt : 𝓝[≠] (0:ℂ) = 𝓝 (0:ℂ) ⊓ 𝓟 ({0}ᶜ) := rfl
    rw [htgt, tendsto_inf, tendsto_principal]
    refine ⟨by simpa [nhdsWithin] using hΓtend, ?_⟩
    filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    simpa using hΓne t ht
  have htwist : Tendsto (fun t : ℝ => F (Γ t) / ‖F (Γ t)‖ - lam * (Γ t / ‖Γ t‖)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    (twist_tendsto_zero hnorm hexp1).comp hΓt'
  have hLinv : ∀ d ∈ L, lam * d ∈ L := by
    intro d hd
    have hdL : d ∈ ⋂ δ ∈ Set.Ioc (0:ℝ) 1, closure (u '' Set.Ioc (0:ℝ) δ) := hd
    have hd' : ∀ δ ∈ Set.Ioc (0:ℝ) 1, d ∈ closure (u '' Set.Ioc (0:ℝ) δ) :=
      fun δ hδ => Set.mem_iInter₂.mp hdL δ hδ
    rw [hLdef]
    refine Set.mem_iInter₂.mpr ?_
    intro δ hδ
    obtain ⟨hδ0, hδ1⟩ := hδ
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hev1 : ∀ᶠ t in 𝓝[>] (0:ℝ), σ t ∈ Set.Ioc (0:ℝ) δ := by
      have hball : Metric.ball (0:ℝ) δ ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds 0 hδ0
      filter_upwards [hσ0.eventually hball,
        Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht1 ht2
      rw [dist_zero_right, Real.norm_eq_abs, abs_lt] at ht1
      have ht : t ∈ Set.Ioc (0:ℝ) 1 := ⟨ht2.1, ht2.2⟩
      have hσt := hσm t ht
      exact ⟨hσt.1, le_of_lt ht1.2⟩
    have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖F (Γ t) / ‖F (Γ t)‖ - lam * (Γ t / ‖Γ t‖)‖ < ε / 2 := by
      filter_upwards [htwist.eventually (Metric.ball_mem_nhds (0:ℂ) (half_pos hε))] with t ht
      simpa only [Metric.mem_ball, dist_zero_right] using ht
    obtain ⟨δ', hδ'0, hδ'⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp (hev1.and hev2)
    set δ'' : ℝ := min δ' 1 / 2 with hδ''
    have hδ''0 : 0 < δ'' := by rw [hδ'']; positivity
    have hδ''le1 : δ'' ≤ 1 := by rw [hδ'']; linarith [min_le_right δ' 1]
    have hδ''lt : δ'' < δ' := by rw [hδ'']; linarith [min_le_left δ' 1, hδ'0]
    have hmem : d ∈ closure (u '' Set.Ioc (0:ℝ) δ'') := hd' δ'' ⟨hδ''0, hδ''le1⟩
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨y, ⟨t, ht, rfl⟩, hdist⟩ := hmem (ε / 2) (by linarith)
    have ht' : t ∈ Set.Ioo (0:ℝ) δ' := ⟨ht.1, lt_of_le_of_lt ht.2 hδ''lt⟩
    obtain ⟨hσt, htw⟩ := hδ' ht'
    have ht01 : t ∈ Set.Ioc (0:ℝ) 1 := ⟨ht.1, le_trans ht.2 hδ''le1⟩
    refine ⟨u (σ t), ⟨σ t, hσt, rfl⟩, ?_⟩
    have huσ : u (σ t) = F (Γ t) / ‖F (Γ t)‖ := by
      rw [hudef]
      simp only
      rw [hFcomp t ht01]
    have h1 : dist (lam * d) (lam * u t) < ε / 2 := by
      rw [dist_eq_norm] at hdist ⊢
      rw [show lam * d - lam * u t = lam * (d - u t) by ring, norm_mul, hnorm, one_mul]
      exact hdist
    have h2 : dist (lam * u t) (u (σ t)) < ε / 2 := by
      rw [dist_eq_norm, huσ, hudef, norm_sub_rev]
      simpa using htw
    calc dist (lam * d) (u (σ t)) ≤ dist (lam * d) (lam * u t) + dist (lam * u t) (u (σ t)) :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  -- case: `F` is linear near `0`
  by_cases hlin : F =ᶠ[𝓝 (0:ℂ)] fun w => lam * w
  · exfalso
    have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), F (Γ t) = lam * Γ t := hΓtend.eventually hlin
    obtain ⟨δ, hδ0, hδ⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp h1
    set t₀ : ℝ := min δ 1 / 2 with ht₀
    have ht₀pos : 0 < t₀ := by rw [ht₀]; positivity
    have ht₀lt : t₀ < δ := by rw [ht₀]; linarith [min_le_left δ 1, hδ0]
    have ht₀le : t₀ ≤ 1 := by rw [ht₀]; linarith [min_le_right δ 1]
    have ht₀mem : t₀ ∈ Set.Ioc (0:ℝ) 1 := ⟨ht₀pos, ht₀le⟩
    have hlineq : F (Γ t₀) = lam * Γ t₀ := hδ ⟨ht₀pos, ht₀lt⟩
    have hdec_t := hdecΓ t₀ ht₀mem
    rw [← hFcomp t₀ ht₀mem, hlineq, norm_mul, hnorm, one_mul] at hdec_t
    exact absurd hdec_t (lt_irrefl _)
  · obtain ⟨n, c, hn1, hc0, hExp⟩ := exists_leading_coeff hFana hF0 hFderiv hlin
    have hlam0 : lam ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact one_ne_zero hnorm.symm
    have hc' : c / lam ≠ 0 := div_ne_zero hc0 hlam0
    have hbound : ∀ d ∈ L, ((c / lam) * d ^ n).re ≤ 0 := by
      intro d hd
      have hdL : d ∈ ⋂ δ ∈ Set.Ioc (0:ℝ) 1, closure (u '' Set.Ioc (0:ℝ) δ) := hd
      have hd' : ∀ δ ∈ Set.Ioc (0:ℝ) 1, d ∈ closure ((fun t => Γ t / ‖Γ t‖) '' Set.Ioc (0:ℝ) δ) :=
        fun δ hδ => Set.mem_iInter₂.mp hdL δ hδ
      refine sector_bound hn1 hnorm hExp one_pos hΓcont hΓtend hΓne (fun t ht => ?_)
        (fun δ hδ => hd' δ hδ)
      rw [hFcomp t ht]
      exact hdecΓ t ht
    by_cases hlam1 : lam = 1
    · exact hlam1
    · exfalso
      by_cases hfo : IsOfFinOrder lam
      · -- `lam` is a root of unity
        by_cases hlamn : lam ^ n = 1
        · -- `lam ^ n = 1`: the arc case
          have hn2 : 2 ≤ n := by
            by_contra hcon
            have h1 : n = 1 := by omega
            rw [h1, pow_one] at hlamn
            exact hlam1 hlamn
          exact false_of_preconnected_sector hn2 hc' hlamn hlam1 hLcpt hLpre hLne hLsph'
            hbound hLinv
        · -- `lam ^ n ≠ 1`: the multiplier `lam ^ n` has order at least two
          have hμfo : IsOfFinOrder (lam ^ n) := IsOfFinOrder.pow (n := n) hfo
          have hord2 : 2 ≤ orderOf (lam ^ n) := by
            have h0 : orderOf (lam ^ n) ≠ 0 := orderOf_ne_zero_iff.mpr hμfo
            have h1 : orderOf (lam ^ n) ≠ 1 := fun h => hlamn (orderOf_eq_one_iff.mp h)
            omega
          rcases Nat.lt_or_ge (orderOf (lam ^ n)) 3 with h3 | h3
          · -- the multiplier is `-1`
            have hkey : (lam ^ n) ^ 2 = 1 := by
              have hpow := pow_orderOf_eq_one (lam ^ n)
              rw [show orderOf (lam ^ n) = 2 by omega] at hpow
              exact hpow
            have hμneg : lam ^ n = -1 := by
              rcases sq_eq_one_iff.mp hkey with h | h
              · exact absurd h hlamn
              · exact h
            have hzero : ∀ d ∈ L, ((c / lam) * d ^ n).re = 0 := by
              intro d hd
              have h1 := hbound d hd
              have h2 := hbound (lam * d) (hLinv d hd)
              rw [mul_pow, hμneg, neg_one_mul] at h2
              rw [show (c / lam) * -d ^ n = -((c / lam) * d ^ n) by ring, Complex.neg_re] at h2
              linarith
            exact false_of_preconnected_sector_boundary_one_le hn1 hc' hμneg hlam1 hLcpt hLpre
              hLne hLsph' hzero hLinv
          · -- the multiplier has order at least three
            exact false_of_preconnected_sector_ord_ge_three hc' hlamn h3 hLpre hLne hLsph'
              hbound hLinv
      · -- `lam` is not a root of unity: the powers of `lam` are dense on the circle
        obtain ⟨d₀, hd₀⟩ := hLne
        have hd₀ne : d₀ ≠ 0 := by
          intro h
          have hs := hLsph d₀ hd₀
          rw [h, norm_zero] at hs
          exact one_ne_zero hs.symm
        have hp : ∀ k : ℕ, lam ^ k * d₀ ∈ L := by
          intro k
          induction k with
          | zero => simpa using hd₀
          | succ k ih =>
              have h := hLinv (lam ^ k * d₀) ih
              simpa only [pow_succ', mul_assoc] using h
        have hclL : IsClosed L := hLcpt.isClosed
        have h1 : closure (Set.range fun k : ℕ => lam ^ k * d₀) ⊆ L :=
          hclL.closure_subset_iff.mpr (by rintro x ⟨k, rfl⟩; exact hp k)
        have h2 : Metric.sphere (0:ℂ) 1 ⊆ closure (Set.range fun k : ℕ => lam ^ k * d₀) := by
          intro x hx
          have hx1 : ‖x‖ = 1 := by
            simpa only [Metric.mem_sphere, dist_zero_right, sub_zero] using hx
          have hxd : x / d₀ ∈ Metric.sphere (0:ℂ) 1 := by
            simp only [Metric.mem_sphere, dist_zero_right, sub_zero]
            rw [norm_div, hx1, hLsph d₀ hd₀]
            norm_num
          have h3 : x / d₀ ∈ closure (Set.range fun k : ℕ => lam ^ k) :=
            sphere_subset_closure_range_pow hnorm hfo hxd
          have hmul : Continuous fun w : ℂ => w * d₀ := continuous_id.mul continuous_const
          have h4 : x / d₀ * d₀ ∈
              closure ((fun w : ℂ => w * d₀) '' (Set.range fun k : ℕ => lam ^ k)) :=
            image_closure_subset_closure_image hmul ⟨x / d₀, h3, rfl⟩
          have h5 : (fun w : ℂ => w * d₀) '' (Set.range fun k : ℕ => lam ^ k) =
              Set.range fun k : ℕ => lam ^ k * d₀ := by
            ext y
            constructor
            · rintro ⟨w, ⟨k, rfl⟩, rfl⟩
              exact ⟨k, rfl⟩
            · rintro ⟨k, rfl⟩
              exact ⟨lam ^ k, ⟨k, rfl⟩, rfl⟩
          rw [h5] at h4
          rwa [div_mul_cancel₀ x hd₀ne] at h4
        have hsub : Metric.sphere (0:ℂ) 1 ⊆ L := fun x hx => h1 (h2 hx)
        obtain ⟨d, hd1, hd2⟩ := exists_unit_pow_pos hn1 hc'
        have hdmem : d ∈ Metric.sphere (0:ℂ) 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right, sub_zero] using hd1
        have hbd := hbound d (hsub hdmem)
        linarith

end Work.LandLeaves
