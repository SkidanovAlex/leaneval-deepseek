import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.Normal.hurwitz_nonvanishing
import Submission.Work.L62.tendsto_iterate_sub_div_pow

/-!
# Cartan's theorem (`Work.L62.cartan`)

If `Ω ⊆ ℂ` is a bounded open preconnected set ("domain"), `f` is holomorphic on `Ω` with
`f(Ω) ⊆ Ω`, and `f` fixes a point `a ∈ Ω`, then `‖deriv f a‖ ≤ 1`; moreover, if
`‖deriv f a‖ = 1` then `f` is a bijection of `Ω` onto itself.

The classical proof:

* The iterates `f^[n]` are uniformly bounded on `Ω` (they map `Ω` into the bounded set `Ω`), so
  by Montel they form a normal family.  Every locally uniform limit point `g` of a subsequence of
  iterates is holomorphic on `Ω`, and `deriv (f^[n]) a = (deriv f a)^n → deriv g a`.
* If `‖deriv f a‖ > 1` those derivatives diverge; hence `‖deriv f a‖ ≤ 1`.
* If `‖deriv f a‖ = 1`, choose exponents `n j ≥ 1` with `λ^(n j) → 1` (`λ = deriv f a`).  Along a
  locally uniformly convergent subsequence `g = lim f^[n j]` we get `g a = a` and `deriv g a = 1`;
  Hurwitz's theorem upgrades `g(Ω) ⊆ closure Ω` to `g(Ω) ⊆ Ω`, so Cartan's uniqueness theorem
  (`Work.L62.cartan_unique`) gives `g = id`.  Then `SurjOn` and `InjOn` follow from Hurwitz again.
-/

namespace Work.L62

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- On the unit circle there are exponents `n j ≥ 1` with `λ ^ (n j) → 1`. -/
theorem pow_tendsto_one {mu : ℂ} (hmu : ‖mu‖ = 1) :
    ∃ n : ℕ → ℕ, (∀ j, 1 ≤ n j) ∧ Tendsto (fun j => mu ^ n j) atTop (𝓝 1) := by
  by_cases hfin : ∃ k : ℕ, 1 ≤ k ∧ mu ^ k = 1
  · obtain ⟨k, hk1, hk⟩ := hfin
    refine ⟨fun j => k * (j + 1), fun j => Nat.succ_le_of_lt (Nat.mul_pos (by omega) (Nat.succ_pos j)), ?_⟩
    have hc : (fun j : ℕ => mu ^ (k * (j + 1))) = fun _ => (1 : ℂ) := by
      funext j; rw [pow_mul, hk, one_pow]
    rw [hc]; exact tendsto_const_nhds
  · push_neg at hfin
    have hmu0 : mu ≠ 0 := by
      intro h; rw [h, norm_zero] at hmu; exact zero_ne_one hmu
    obtain ⟨z, -, φ, hφ, hφlim⟩ :=
      (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq (x := fun j => mu ^ j) (fun j => by
        rw [mem_closedBall_zero_iff, norm_pow, hmu, one_pow])
    have hz1 : ‖z‖ = 1 := by
      have h : Tendsto (fun j => ‖mu ^ (φ j)‖) atTop (𝓝 ‖z‖) := hφlim.norm
      simp only [norm_pow, hmu, one_pow] at h
      exact tendsto_nhds_unique h tendsto_const_nhds
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
    have hmono : ∀ j, φ j ≤ φ (j + 1) := fun j => (hφ (Nat.lt_succ_self j)).le
    refine ⟨fun j => φ (j + 1) - φ j, fun j => Nat.succ_le_of_lt (Nat.sub_pos_iff_lt.mpr (hφ (Nat.lt_succ_self j))), ?_⟩
    have hnum : Tendsto (fun j => mu ^ (φ (j + 1))) atTop (𝓝 z) :=
      hφlim.comp (tendsto_add_atTop_nat 1)
    have hdiv : Tendsto (fun j => mu ^ (φ (j + 1)) / mu ^ (φ j)) atTop (𝓝 (z / z)) :=
      hnum.div hφlim hz0
    rw [div_self hz0] at hdiv
    refine hdiv.congr' ?_
    filter_upwards with j
    rw [show mu ^ (φ (j + 1)) = mu ^ (φ j) * mu ^ (φ (j + 1) - φ j) from by
      rw [← pow_add, Nat.add_sub_cancel' (hmono j)]]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hmu0)

/-- **Cartan's theorem.**  A holomorphic self-map `f` of a bounded domain `Ω` fixing a point `a`
has `‖deriv f a‖ ≤ 1`, and if `‖deriv f a‖ = 1` then `f` is a bijection of `Ω` onto itself. -/
theorem cartan {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩc : IsPreconnected Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hmap : MapsTo f Ω Ω)
    {a : ℂ} (ha : a ∈ Ω) (hfix : f a = a) :
    ‖deriv f a‖ ≤ 1 ∧ (‖deriv f a‖ = 1 → SurjOn f Ω Ω ∧ InjOn f Ω) := by
  have hmap' : ∀ n : ℕ, MapsTo (f^[n]) Ω Ω := fun n => hmap.iterate n
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (f^[n]) Ω := fun n => hf.iterate hmap n
  have hfix' : ∀ n : ℕ, (f^[n]) a = a := fun n => Function.iterate_fixed hfix n
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Ω, ‖z‖ ≤ M := by
    obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hΩb
    exact ⟨M, fun z hz => mem_closedBall_zero_iff.mp (hM hz)⟩
  have hbdd : Work.Normal.IsLocallyBoundedOn (Work.Normal.iterateFamily f) Ω := by
    intro K hKΩ _
    refine ⟨M, fun g hg z hz => ?_⟩
    obtain ⟨n, rfl⟩ := hg
    exact hM _ (hmap' n (hKΩ hz))
  have hnormal : Work.Normal.IsNormalFamily (Work.Normal.iterateFamily f) Ω :=
    Work.Normal.montel_locallyBounded hΩo (fun g hg => by
      obtain ⟨n, rfl⟩ := hg
      exact hdiff n) hbdd
  -- every sequence of iterates has a locally uniform limit (the `∞` alternative is impossible)
  have key : ∀ m : ℕ → ℕ, ∃ (ψ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun j => f^[m (ψ j)]) g atTop Ω := by
    intro m
    obtain ⟨ψ, hψ, hlim | hlim⟩ :=
      hnormal (fun j => f^[m j]) (fun j => Set.mem_range.mpr ⟨m j, rfl⟩)
    · obtain ⟨g, hg⟩ := hlim
      exact ⟨ψ, g, hψ, hg⟩
    · exfalso
      obtain ⟨N, hN⟩ := hlim {a} (singleton_subset_iff.mpr ha) isCompact_singleton (‖a‖ + 1)
      have h := hN N le_rfl a rfl
      simp only [hfix'] at h
      linarith
  have hHasDeriv : HasDerivAt f (deriv f a) a :=
    (hf.differentiableAt (hΩo.mem_nhds ha)).hasDerivAt
  have hderiv_iter : ∀ k : ℕ, deriv (f^[k]) a = (deriv f a) ^ k := fun k =>
    (hHasDeriv.iterate a hfix k).deriv
  constructor
  · -- `‖deriv f a‖ ≤ 1`
    obtain ⟨ψ, g, hψ, hlim⟩ := key id
    have hder := hlim.deriv (Eventually.of_forall fun j => hdiff (ψ j)) hΩo
    have hpt : Tendsto (fun j => deriv (f^[ψ j]) a) atTop (𝓝 (deriv g a)) := hder.tendsto_at ha
    have hpt' : Tendsto (fun j => (deriv f a) ^ (ψ j)) atTop (𝓝 (deriv g a)) := by
      refine hpt.congr' ?_
      filter_upwards with j using hderiv_iter (ψ j)
    by_contra hcon
    rw [not_le] at hcon
    have hL : Tendsto (fun j => ‖deriv f a‖ ^ (ψ j)) atTop (𝓝 ‖deriv g a‖) := by
      have h := hpt'.norm
      simpa only [norm_pow] using h
    have htop : Tendsto (fun j => ‖deriv f a‖ ^ (ψ j)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hcon).comp hψ.tendsto_atTop
    have h1 : ∀ᶠ j in atTop, ‖deriv f a‖ ^ (ψ j) < ‖deriv g a‖ + 1 :=
      hL (isOpen_Iio.mem_nhds (show ‖deriv g a‖ < ‖deriv g a‖ + 1 by linarith))
    have h2 : ∀ᶠ j in atTop, ‖deriv g a‖ + 1 ≤ ‖deriv f a‖ ^ (ψ j) :=
      htop (mem_atTop_sets.mpr ⟨‖deriv g a‖ + 1, fun _ hx => hx⟩)
    obtain ⟨j, hj1, hj2⟩ := (h1.and h2).exists
    linarith
  · -- the equality case
    intro hlen
    obtain ⟨m, hm1, hm⟩ := pow_tendsto_one hlen
    obtain ⟨ψ, g, hψ, hlim⟩ := key m
    have hder := hlim.deriv (Eventually.of_forall fun j => hdiff (m (ψ j))) hΩo
    have hpt : Tendsto (fun j => deriv (f^[m (ψ j)]) a) atTop (𝓝 (deriv g a)) := hder.tendsto_at ha
    have hpt' : Tendsto (fun j => (deriv f a) ^ (m (ψ j))) atTop (𝓝 (deriv g a)) := by
      refine hpt.congr' ?_
      filter_upwards with j using hderiv_iter (m (ψ j))
    have hm' : Tendsto (fun j => (deriv f a) ^ (m (ψ j))) atTop (𝓝 1) :=
      hm.comp hψ.tendsto_atTop
    have hdga : deriv g a = 1 := tendsto_nhds_unique hpt' hm'
    have hga : g a = a := by
      have h1 : Tendsto (fun j => (f^[m (ψ j)]) a) atTop (𝓝 (g a)) := hlim.tendsto_at ha
      have h2 : Tendsto (fun j => (f^[m (ψ j)]) a) atTop (𝓝 a) := by
        have : (fun j => (f^[m (ψ j)]) a) = fun _ => a := funext fun j => hfix' _
        rw [this]; exact tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    have hgdiff : DifferentiableOn ℂ g Ω :=
      hlim.differentiableOn (Eventually.of_forall fun j => hdiff (m (ψ j))) hΩo
    -- Hurwitz: the limit map still maps `Ω` into itself
    have hgmap : MapsTo g Ω Ω := by
      intro z hz
      by_contra hw
      have hconst : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => g z)
          (fun _ => g z) atTop Ω :=
        ((tendsto_const_nhds (f := atTop) (x := g z)).tendstoUniformlyOn_const Ω).tendstoLocallyUniformlyOn
      have hv : ∀ j, ∀ u ∈ Ω, (fun u => (f^[m (ψ j)]) u - g z) u ≠ 0 := by
        intro j u hu h
        exact hw (by
          have h2 : (f^[m (ψ j)]) u = g z := sub_eq_zero.mp h
          rw [← h2]
          exact hmap' (m (ψ j)) hu)
      have hlimv : TendstoLocallyUniformlyOn (fun j => fun u => (f^[m (ψ j)]) u - g z)
          (fun u => g u - g z) atTop Ω := hlim.sub hconst
      rcases Work.Normal.hurwitz_nonvanishing hΩo hΩc _ _
          (fun j => (hdiff (m (ψ j))).sub_const _) hv hlimv with hcase | hcase
      · exact hcase z hz (sub_self _)
      · have hzero : (fun u => g u - g z) =ᶠ[𝓝 a] fun _ => (0 : ℂ) :=
          Filter.eventually_of_mem (hΩo.mem_nhds ha) fun u hu => hcase u hu
        have h1 : deriv (fun u => g u - g z) a = 0 := by
          rw [hzero.deriv_eq]; simp
        have h2 : deriv (fun u => g u - g z) a = 1 := by
          have hd := ((hgdiff.differentiableAt (hΩo.mem_nhds ha)).hasDerivAt).sub_const (g z)
          simp [hd.deriv, hdga]
        rw [h2] at h1
        exact one_ne_zero h1
    -- Cartan's uniqueness theorem: `g` is the identity
    have hid : ∀ u ∈ Ω, g u = u := by
      by_contra hcon
      obtain ⟨z0, hz0Ω, hz0⟩ : ∃ u, u ∈ Ω ∧ g u ≠ u := by
        by_contra h
        exact hcon fun u hu => by
          by_contra hgu
          exact h ⟨u, hu, hgu⟩
      have hφan : AnalyticAt ℂ (fun z => g z - z) a :=
        (hgdiff.analyticOnNhd hΩo a ha).sub analyticAt_id
      have hφne : ¬ (fun z => g z - z) =ᶠ[𝓝 a] 0 := by
        intro h
        have hzero : EqOn (fun z => g z - z) 0 Ω :=
          AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
            ((hgdiff.analyticOnNhd hΩo).sub analyticOnNhd_id) hΩc ha h
        exact hz0 (sub_eq_zero.mp (hzero hz0Ω))
      have horder : analyticOrderAt (fun z => g z - z) a ≠ ⊤ :=
        fun h => hφne (analyticOrderAt_eq_top.mp h)
      obtain ⟨ψ, hψan, hψ0, hψeq⟩ := hφan.analyticOrderAt_ne_top.mp horder
      set m : ℕ := analyticOrderNatAt (fun z => g z - z) a with hm
      have hm2 : 2 ≤ m := by
        have h2 : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z => g z - z) a := by
          rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hφan]
          intro i hi
          have hi2 : i = 0 ∨ i = 1 := by omega
          rcases hi2 with rfl | rfl
          · rw [iteratedDeriv_zero]
            exact sub_eq_zero.mpr hga
          · rw [iteratedDeriv_one]
            have hd : deriv (fun z => g z - z) a = deriv g a - 1 := by
              have h1 : HasDerivAt (fun z : ℂ => g z) (deriv g a) a :=
                (hgdiff.differentiableAt (hΩo.mem_nhds ha)).hasDerivAt
              have h2 : HasDerivAt (fun z : ℂ => z) 1 a := hasDerivAt_id a
              exact (h1.sub h2).deriv
            rw [hd, hdga]
            norm_num
        have h2' : ((2 : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) := by
          rw [← Nat.cast_analyticOrderNatAt horder, ← hm] at h2
          exact h2
        exact_mod_cast h2'
      have hm1 : 1 ≤ m := by omega
      have hψ0' : ψ a ≠ 0 := hψ0
      have hU : ∀ᶠ z in 𝓝 a, g z = z + (z - a) ^ m * ψ z := by
        filter_upwards [hψeq] with z hz
        rw [smul_eq_mul] at hz
        rw [← hz]
        ring
      have hcoef : ∀ n : ℕ,
          Tendsto (fun z => ((g^[n]) z - z) / (z - a) ^ m) (𝓝[≠] a)
            (𝓝 ((n : ℂ) * ψ a)) :=
        fun n => tendsto_iterate_sub_div_pow hm2 hψan hU n
      -- a small closed ball around `a` inside `Ω`
      obtain ⟨R₁, hR₁pos, hR₁Ω⟩ : ∃ R₁ : ℝ, 0 < R₁ ∧ closedBall a R₁ ⊆ Ω := by
        obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hΩo.mem_nhds ha)
        refine ⟨r / 2, by linarith, fun z hz => hsub ?_⟩
        rw [mem_ball]
        have h := mem_closedBall.mp hz
        linarith
      have hballmem : ball a R₁ ∈ 𝓝 a := Metric.ball_mem_nhds a hR₁pos
      -- the iterates are tangent to `0` to order `m-1`
      have hlittle : ∀ n : ℕ,
          (fun w => (g^[n]) w - w - ((g^[n]) a - a)) =o[𝓝 a]
            (fun w => ‖w - a‖ ^ (m - 1)) := by
        intro n
        have ha0 : (g^[n]) a - a = 0 := by rw [Function.iterate_fixed hga n]; ring
        simp only [ha0, sub_zero]
        apply Asymptotics.IsLittleO.of_bound
        intro c hc
        have hCpos : (0 : ℝ) < ‖(n : ℂ) * ψ a‖ + 1 := by positivity
        have hC : ∀ᶠ z in 𝓝[≠] a,
            ‖(g^[n]) z - z‖ ≤ (‖(n : ℂ) * ψ a‖ + 1) * ‖z - a‖ ^ m := by
          have hb : Tendsto (fun z => ‖(g^[n]) z - z‖ / ‖z - a‖ ^ m) (𝓝[≠] a)
              (𝓝 ‖(n : ℂ) * ψ a‖) := by
            have h := (hcoef n).norm
            refine h.congr' ?_
            filter_upwards with z
            simp only [norm_div, norm_pow]
          have hb2 := hb (isOpen_Iio.mem_nhds
            (show ‖(n : ℂ) * ψ a‖ < ‖(n : ℂ) * ψ a‖ + 1 by linarith))
          filter_upwards [hb2, self_mem_nhdsWithin] with z hz1 hz2
          simp only [Set.mem_preimage, Set.mem_Iio] at hz1
          have hz : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz2)
          have hpow : (0 : ℝ) < ‖z - a‖ ^ m := pow_pos (norm_pos_iff.mpr hz) m
          rw [div_lt_iff₀ hpow] at hz1
          exact hz1.le
        have hsmall : ∀ᶠ w in 𝓝[≠] a,
            ‖(g^[n]) w - w‖ ≤ c * ‖w - a‖ ^ (m - 1) := by
          have hcp : (0 : ℝ) < c / (‖(n : ℂ) * ψ a‖ + 1) := div_pos hc hCpos
          filter_upwards [hC, self_mem_nhdsWithin,
            nhdsWithin_le_nhds (Metric.ball_mem_nhds a (by linarith : (0:ℝ) < c / (‖(n : ℂ) * ψ a‖ + 1)))]
            with w hw1 _ hw3
          have hw3' : ‖w - a‖ < c / (‖(n : ℂ) * ψ a‖ + 1) := by
            rw [← dist_eq_norm]; exact hw3
          have hA : ‖w - a‖ ^ m = ‖w - a‖ ^ (m - 1) * ‖w - a‖ := by
            rw [← pow_succ, Nat.sub_add_cancel hm1]
          calc ‖(g^[n]) w - w‖ ≤ (‖(n : ℂ) * ψ a‖ + 1) * ‖w - a‖ ^ m := hw1
            _ = (‖(n : ℂ) * ψ a‖ + 1) * ‖w - a‖ ^ (m - 1) * ‖w - a‖ := by rw [hA]; ring
            _ ≤ (‖(n : ℂ) * ψ a‖ + 1) * ‖w - a‖ ^ (m - 1)
                  * (c / (‖(n : ℂ) * ψ a‖ + 1)) := by
                gcongr
            _ = c * ‖w - a‖ ^ (m - 1) := by
                field_simp
        have hsmall' : ∀ᶠ w in 𝓝 a, w ≠ a → ‖(g^[n]) w - w‖ ≤ c * ‖w - a‖ ^ (m - 1) :=
          eventually_nhdsWithin_iff.mp hsmall
        filter_upwards [hsmall'] with w hw
        by_cases hwa : w = a
        · subst hwa
          have hm1'' : m - 1 ≠ 0 := by omega
          simp [Function.iterate_fixed hga n, hm1'']
        · simpa using hw hwa
      -- Schwarz bound for the iterates
      have hSch : ∀ n : ℕ, ∀ w ∈ ball a R₁,
          ‖(g^[n]) w - w‖ ≤ (M + ‖a‖ + R₁) * (‖w - a‖ / R₁) ^ m := by
        intro n w hw
        have hdiffn : DifferentiableOn ℂ (fun u => (g^[n]) u - u) (ball a R₁) :=
          ((hgdiff.iterate hgmap n).mono (ball_subset_closedBall.trans hR₁Ω)).sub
            differentiable_id.differentiableOn
        have ha0 : (g^[n]) a - a = 0 := by rw [Function.iterate_fixed hga n]; ring
        have hmaps : MapsTo (fun u => (g^[n]) u - u) (ball a R₁)
            (closedBall ((fun u => (g^[n]) u - u) a) (M + ‖a‖ + R₁)) := by
          intro u hu
          rw [mem_closedBall, dist_eq_norm]
          simp only [ha0, sub_zero]
          have huΩ : u ∈ Ω := (ball_subset_closedBall.trans hR₁Ω) hu
          have h1 : ‖(g^[n]) u‖ ≤ M := hM _ (hgmap.iterate n huΩ)
          have h2 : ‖u‖ ≤ ‖a‖ + R₁ := by
            have h3 := mem_ball.mp hu
            calc ‖u‖ = ‖(u - a) + a‖ := by rw [sub_add_cancel]
              _ ≤ ‖u - a‖ + ‖a‖ := norm_add_le _ _
              _ ≤ R₁ + ‖a‖ := by rw [dist_eq_norm] at h3; linarith
              _ = ‖a‖ + R₁ := by ring
          calc ‖(g^[n]) u - u‖ ≤ ‖(g^[n]) u‖ + ‖u‖ := norm_sub_le _ _
            _ ≤ M + (‖a‖ + R₁) := add_le_add h1 h2
            _ = M + ‖a‖ + R₁ := by ring
        have h := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
          (c := a) (R₁ := R₁) (R₂ := M + ‖a‖ + R₁) (n := m - 1)
          hdiffn hmaps (hlittle n) hw
        rw [Nat.sub_add_cancel hm1] at h
        simpa [ha0, dist_eq_norm] using h
      -- consequently `n * ‖ψ a‖` is bounded uniformly in `n`
      have hbd : ∀ n : ℕ, (n : ℝ) * ‖ψ a‖ ≤ (M + ‖a‖ + R₁) / R₁ ^ m := by
        intro n
        have h1 : Tendsto (fun w => ‖(g^[n]) w - w‖ / ‖w - a‖ ^ m) (𝓝[≠] a)
            (𝓝 ((n : ℝ) * ‖ψ a‖)) := by
          have h := (hcoef n).norm
          rw [norm_mul, Complex.norm_natCast] at h
          refine h.congr' ?_
          filter_upwards with w
          simp only [norm_div, norm_pow]
        have h2 : ∀ᶠ w in 𝓝[≠] a,
            ‖(g^[n]) w - w‖ / ‖w - a‖ ^ m ≤ (M + ‖a‖ + R₁) / R₁ ^ m := by
          filter_upwards [nhdsWithin_le_nhds hballmem, self_mem_nhdsWithin] with w hw1 hw2
          have hw2' : w ≠ a := by simpa using hw2
          have hb := hSch n w hw1
          have hpow : (0 : ℝ) < ‖w - a‖ ^ m :=
            pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hw2')) m
          rw [div_le_iff₀ hpow]
          calc ‖(g^[n]) w - w‖ ≤ (M + ‖a‖ + R₁) * (‖w - a‖ / R₁) ^ m := hb
            _ = ((M + ‖a‖ + R₁) / R₁ ^ m) * ‖w - a‖ ^ m := by rw [div_pow]; ring
        exact le_of_tendsto h1 h2
      obtain ⟨n, hn⟩ := exists_nat_gt ((M + ‖a‖ + R₁) / R₁ ^ m / ‖ψ a‖)
      have hψpos : 0 < ‖ψ a‖ := norm_pos_iff.mpr hψ0'
      have hlt : (M + ‖a‖ + R₁) / R₁ ^ m < (n : ℝ) * ‖ψ a‖ := by
        rw [div_lt_iff₀ hψpos] at hn
        simpa [mul_comm] using hn
      have := hbd n
      linarith
    refine ⟨?_, ?_⟩
    · -- surjectivity (Hurwitz again)
      intro w hw
      by_contra hcon
      have hne : ∀ u, u ∈ Ω → f u ≠ w := by
        intro u hu h
        exact hcon ⟨u, hu, h⟩
      have hconstw : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => w) (fun _ => w) atTop Ω :=
        ((tendsto_const_nhds (f := atTop) (x := w)).tendstoUniformlyOn_const Ω).tendstoLocallyUniformlyOn
      have hv : ∀ j, ∀ u ∈ Ω, (fun u => (f^[m (ψ j)]) u - w) u ≠ 0 := by
        intro j u hu h
        obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hm1 (ψ j))))
        refine hne ((f^[l]) u) (hmap' l hu) ?_
        rw [hl] at h
        simp only [Function.iterate_succ_apply'] at h
        exact sub_eq_zero.mp h
      have hlimw : TendstoLocallyUniformlyOn (fun j => fun u => (f^[m (ψ j)]) u - w)
          (fun u => u - w) atTop Ω :=
        (hlim.sub hconstw).congr_right (fun u hu => by simp only [Pi.sub_apply]; rw [hid u hu])
      rcases Work.Normal.hurwitz_nonvanishing hΩo hΩc _ _
          (fun j => (hdiff (m (ψ j))).sub_const _) hv hlimw with hcase | hcase
      · exact hcase w hw (sub_self w)
      · obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (hΩo.mem_nhds hw)
        have hmem : w + ((ρ / 2 : ℝ) : ℂ) ∈ Ω := hsub (by
          rw [mem_ball, dist_eq_norm]
          have hw' : w + ((ρ / 2 : ℝ) : ℂ) - w = ((ρ / 2 : ℝ) : ℂ) := by ring
          rw [hw', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          linarith)
        have hval := hcase (w + ((ρ / 2 : ℝ) : ℂ)) hmem
        have hρ2 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
          rwa [show w + ((ρ / 2 : ℝ) : ℂ) - w = ((ρ / 2 : ℝ) : ℂ) by ring] at hval
        have : ρ / 2 = 0 := Complex.ofReal_inj.mp hρ2
        linarith
    · -- injectivity
      intro z1 hz1 z2 hz2 hfeq
      have hiter : ∀ k : ℕ, 1 ≤ k → (f^[k]) z1 = (f^[k]) z2 := by
        intro k hk
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hfeq]
      have hEq : ∀ j, (f^[m (ψ j)]) z1 = (f^[m (ψ j)]) z2 := fun j => hiter _ (hm1 (ψ j))
      have e1 : Tendsto (fun j => (f^[m (ψ j)]) z1) atTop (𝓝 z1) := by
        have h := hlim.tendsto_at hz1
        rwa [hid z1 hz1] at h
      have e2 : Tendsto (fun j => (f^[m (ψ j)]) z1) atTop (𝓝 z2) := by
        have h := hlim.tendsto_at hz2
        rw [hid z2 hz2] at h
        refine h.congr' ?_
        filter_upwards with j using (hEq j).symm
      exact tendsto_nhds_unique e1 e2

end

end Work.L62
