import Mathlib

/-! # Hurwitz' theorem

Auxiliary lemma for `Work.Smooth.SphereJordan.planeDomain_homeo_unitBall`.

If `F n : ℂ → ℂ` are holomorphic and injective on an open preconnected set `U`, `f` is holomorphic
on `U` and `F n → f` locally uniformly, then `f` is injective on `U` or constant on `U`.

The proof only uses the *minimum modulus principle* (a corollary of the maximum modulus
principle): if `f - f a` has an isolated zero at `a ∈ U`, then for large `n` the function
`F n - f a` must have a zero near `a` (otherwise its value at `a`, which tends to `0`, would be
bounded below by its minimum on a small circle).
-/

namespace Work.Smooth.SphereJordan

open Filter Metric
open scoped Topology

/-- **Minimum modulus principle.**  If `g` is holomorphic on `ball c r`, nonvanishing on the
closed ball and bounded below by `δ` on the sphere, then it is bounded below by `δ` on the closed
ball. -/
theorem le_norm_of_forall_mem_sphere_le {g : ℂ → ℂ} {c : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hdiff : DiffContOnCl ℂ g (ball c r)) (hne : ∀ z ∈ closedBall c r, g z ≠ 0)
    (hsp : ∀ z ∈ sphere c r, δ ≤ ‖g z‖) : ∀ z ∈ closedBall c r, δ ≤ ‖g z‖ := by
  have hdiff' : DiffContOnCl ℂ (fun z => (g z)⁻¹) (ball c r) :=
    ⟨hdiff.differentiableOn.inv fun z hz => hne z (ball_subset_closedBall hz),
      hdiff.continuousOn.inv₀ fun z hz => hne z (by rwa [closure_ball c hr.ne'] at hz)⟩
  intro z hz
  have hzcl : z ∈ closure (ball c r) := by rw [closure_ball c hr.ne']; exact hz
  have hb := Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hdiff'
    (C := δ⁻¹) (fun w hw => ?_) hzcl
  · rw [norm_inv] at hb
    have hpos : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z hz)
    exact (inv_le_inv₀ hpos hδ).mp hb
  · have hw' : w ∈ sphere c r := by rwa [frontier_ball c hr.ne'] at hw
    have h1 : 1 / ‖g w‖ ≤ 1 / δ := one_div_le_one_div_of_le hδ (hsp w hw')
    rw [one_div, one_div] at h1
    rw [norm_inv]
    exact h1

/-- **Hurwitz' theorem.**  A locally uniform limit of injective holomorphic functions is injective
or constant. -/
theorem injOn_or_exists_forall_eq_of_tendstoLocallyUniformlyOn {U : Set ℂ} (hUo : IsOpen U)
    (hUp : IsPreconnected U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hf : DifferentiableOn ℂ f U)
    (hinj : ∀ n, Set.InjOn (F n) U) (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    Set.InjOn f U ∨ ∃ c : ℂ, ∀ z ∈ U, f z = c := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfnotinj, hfnotconst⟩ := hcon
  obtain ⟨a, ha, b, hb, hfab, hab⟩ : ∃ a ∈ U, ∃ b ∈ U, f a = f b ∧ a ≠ b := by
    by_contra h
    push_neg at h
    exact hfnotinj fun x hx y hy hxy => h x hx y hy hxy
  -- `f - f a` does not vanish identically near `a`
  have hnotEvZero : ¬ (∀ᶠ z in 𝓝 a, f z - f a = 0) := by
    intro h
    have hana : AnalyticOnNhd ℂ (fun z => f z - f a) U :=
      (hf.sub_const (f a)).analyticOnNhd hUo
    have hzero : Set.EqOn (fun z => f z - f a) 0 U :=
      hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUp ha (show (fun z => f z - f a) =ᶠ[𝓝 a] 0 from h)
    exact hfnotconst ⟨f a, fun z hz => sub_eq_zero.mp (hzero hz)⟩
  -- isolated zero at `a`
  have hisol : ∀ᶠ z in 𝓝[{a}ᶜ] a, f z - f a ≠ 0 := by
    rcases ((hf.sub_const (f a)).analyticAt (hUo.mem_nhds ha)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h hnotEvZero
    · exact h
  obtain ⟨r₁, hr₁, hr₁'⟩ : ∃ r > 0, ∀ z, z ∈ ball a r → z ≠ a → f z - f a ≠ 0 := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hisol
    obtain ⟨r, hr, hr'⟩ := hisol
    refine ⟨r, hr, fun z hz hzne => hr' (y := z) ?_ ?_⟩
    · rwa [mem_ball] at hz
    · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hzne
  have hfnotconst' : ¬ ∀ z ∈ U, f z = f b := fun h => hfnotconst ⟨f b, h⟩
  have hnotEvZero_b : ¬ (∀ᶠ z in 𝓝 b, f z - f b = 0) := by
    intro h
    have hana : AnalyticOnNhd ℂ (fun z => f z - f b) U :=
      (hf.sub_const (f b)).analyticOnNhd hUo
    have hzero : Set.EqOn (fun z => f z - f b) 0 U :=
      hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUp hb (show (fun z => f z - f b) =ᶠ[𝓝 b] 0 from h)
    exact hfnotconst' fun z hz => sub_eq_zero.mp (hzero hz)
  have hisol_b : ∀ᶠ z in 𝓝[{b}ᶜ] b, f z - f b ≠ 0 := by
    rcases ((hf.sub_const (f b)).analyticAt (hUo.mem_nhds hb)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h hnotEvZero_b
    · exact h
  obtain ⟨r₂, hr₂, hr₂'⟩ : ∃ r > 0, ∀ z, z ∈ ball b r → z ≠ b → f z - f b ≠ 0 := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hisol_b
    obtain ⟨r, hr, hr'⟩ := hisol_b
    refine ⟨r, hr, fun z hz hzne => hr' (y := z) ?_ ?_⟩
    · rwa [mem_ball] at hz
    · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hzne
  -- small closed balls around `a` and `b` inside `U`
  obtain ⟨ρa, hρa, hρaU⟩ : ∃ ρ > 0, closedBall a ρ ⊆ U := by
    rcases Metric.mem_nhds_iff.mp (hUo.mem_nhds ha) with ⟨r, hr, hr'⟩
    exact ⟨r / 2, by linarith, fun z hz => hr' (by
      rw [mem_ball, mem_closedBall] at *
      linarith)⟩
  obtain ⟨ρb, hρb, hρbU⟩ : ∃ ρ > 0, closedBall b ρ ⊆ U := by
    rcases Metric.mem_nhds_iff.mp (hUo.mem_nhds hb) with ⟨r, hr, hr'⟩
    exact ⟨r / 2, by linarith, fun z hz => hr' (by
      rw [mem_ball, mem_closedBall] at *
      linarith)⟩
  have hdab : 0 < dist a b := dist_pos.mpr hab
  set ε : ℝ := min (min (ρa / 2) (ρb / 2)) (min (min (r₁ / 2) (r₂ / 2)) (dist a b / 4)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (lt_min (by linarith) (by linarith))
      (by linarith))
  have hεaU : closedBall a ε ⊆ U := fun z hz =>
    hρaU (closedBall_subset_closedBall (by
      rw [hεdef]
      exact ((min_le_left _ _).trans (min_le_left _ _)).trans (by linarith)) hz)
  have hεbU : closedBall b ε ⊆ U := fun z hz =>
    hρbU (closedBall_subset_closedBall (by
      rw [hεdef]
      exact ((min_le_left _ _).trans (min_le_right _ _)).trans (by linarith)) hz)
  have hεdisj : Disjoint (closedBall a ε) (closedBall b ε) := by
    rw [Set.disjoint_left]
    intro z hza hzb
    rw [mem_closedBall] at hza hzb
    have h4 : ε ≤ dist a b / 4 := by
      rw [hεdef]; exact (min_le_right _ _).trans (min_le_right _ _)
    have h6 : dist a b ≤ ε + ε := by
      have h5 := dist_triangle a z b
      rw [dist_comm a z] at h5
      exact h5.trans (add_le_add hza hzb)
    linarith
  have hεr₁ : ∀ z ∈ sphere a ε, f z - f a ≠ 0 := by
    intro z hz
    refine hr₁' z ?_ ?_
    · rw [mem_ball, mem_sphere] at *
      have h2 : ε ≤ r₁ / 2 := by
        rw [hεdef]
        exact ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
      linarith
    · rw [mem_sphere] at hz
      intro hza
      rw [hza, dist_self] at hz
      linarith
  have hεr₂ : ∀ z ∈ sphere b ε, f z - f b ≠ 0 := by
    intro z hz
    refine hr₂' z ?_ ?_
    · rw [mem_ball, mem_sphere] at *
      have h2 : ε ≤ r₂ / 2 := by
        rw [hεdef]
        exact ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
      linarith
    · rw [mem_sphere] at hz
      intro hzb
      rw [hzb, dist_self] at hz
      linarith
  -- a positive lower bound for `‖f - f a‖` on the sphere around `a`
  obtain ⟨z₀, hz₀, hmin⟩ : ∃ z ∈ sphere a ε, ∀ w ∈ sphere a ε, ‖f z - f a‖ ≤ ‖f w - f a‖ := by
    refine (isCompact_sphere a ε).exists_isMinOn (f := fun z => ‖f z - f a‖) ⟨a + (ε : ℂ), ?_⟩ ?_
    · rw [mem_sphere, dist_eq_norm]
      simp [Real.norm_of_nonneg hεpos.le]
    · exact (((hf.continuousOn.mono ((sphere_subset_closedBall).trans hεaU)).sub
        (continuousOn_const (c := f a))).norm)
  have hδpos : 0 < ‖f z₀ - f a‖ := norm_pos_iff.mpr (hεr₁ z₀ hz₀)
  -- a positive lower bound for `‖f - f b‖` on the sphere around `b`
  obtain ⟨w₀, hw₀, hmin₀⟩ : ∃ z ∈ sphere b ε, ∀ w ∈ sphere b ε, ‖f z - f b‖ ≤ ‖f w - f b‖ := by
    refine (isCompact_sphere b ε).exists_isMinOn (f := fun z => ‖f z - f b‖)
      ⟨b + (ε : ℂ), ?_⟩ ?_
    · rw [mem_sphere, dist_eq_norm]
      simp [Real.norm_of_nonneg hεpos.le]
    · exact (((hf.continuousOn.mono ((sphere_subset_closedBall).trans hεbU)).sub
        (continuousOn_const (c := f b))).norm)
  have hδpos' : 0 < ‖f w₀ - f b‖ := norm_pos_iff.mpr (hεr₂ w₀ hw₀)
  -- uniform convergence on the two spheres and convergence of the values at `a` and `b`
  have hconv_a : TendstoUniformlyOn F f atTop (sphere a ε) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).mp hconv _ (fun z hz => hεaU (sphere_subset_closedBall hz)) (isCompact_sphere a ε)
  have hconv_b : TendstoUniformlyOn F f atTop (sphere b ε) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).mp hconv _ (fun z hz => hεbU (sphere_subset_closedBall hz)) (isCompact_sphere b ε)
  have hev_a : ∀ᶠ n in atTop, ∀ z ∈ sphere a ε, dist (f z) (F n z) < ‖f z₀ - f a‖ / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hconv_a) _ (half_pos hδpos)
  have hev_b : ∀ᶠ n in atTop, ∀ z ∈ sphere b ε, dist (f z) (F n z) < ‖f w₀ - f b‖ / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hconv_b) _ (half_pos hδpos')
  have hev_na : ∀ᶠ n in atTop, dist (F n a) (f a) < ‖f z₀ - f a‖ / 2 := by
    filter_upwards [(hconv.tendsto_at ha).eventually
      (Metric.ball_mem_nhds _ (half_pos hδpos))] with n hn
    exact hn
  have hev_nb : ∀ᶠ n in atTop, dist (F n b) (f b) < ‖f w₀ - f b‖ / 2 := by
    filter_upwards [(hconv.tendsto_at hb).eventually
      (Metric.ball_mem_nhds (f b) (half_pos hδpos'))] with n hn
    exact hn
  obtain ⟨n, hza, hzb, hna, hnb⟩ := (hev_a.and (hev_b.and (hev_na.and hev_nb))).exists
  have hzero_a : ∃ z ∈ closedBall a ε, F n z - f a = 0 := by
    by_contra h
    push_neg at h
    have hsp : ∀ z ∈ sphere a ε, ‖f z₀ - f a‖ / 2 ≤ ‖F n z - f a‖ := by
      intro z hz
      have h1 : ‖f z - F n z‖ < ‖f z₀ - f a‖ / 2 := by
        have := hza z hz
        rwa [dist_eq_norm] at this
      have h2 : ‖f z₀ - f a‖ ≤ ‖f z - f a‖ := hmin z hz
      have h3 : ‖f z - f a‖ - ‖f z - F n z‖ ≤ ‖F n z - f a‖ := by
        have h4 : ‖f z - f a‖ ≤ ‖F n z - f a‖ + ‖f z - F n z‖ := by
          have h5 := norm_add_le (F n z - f a) (f z - F n z)
          have e1 : (F n z - f a) + (f z - F n z) = f z - f a := by ring
          rwa [e1] at h5
        exact sub_le_iff_le_add.mpr h4
      linarith
    have hminz := le_norm_of_forall_mem_sphere_le (g := fun z => F n z - f a) hεpos
      (half_pos hδpos) (((hF n).sub_const (f a)).diffContOnCl_ball hεaU) h hsp
    have hza' := hminz a (by rw [mem_closedBall, dist_self]; exact hεpos.le)
    have hc : ‖F n a - f a‖ < ‖f z₀ - f a‖ / 2 := by
      have := hna
      rwa [dist_eq_norm] at this
    linarith
  have hzero_b : ∃ z ∈ closedBall b ε, F n z - f b = 0 := by
    by_contra h
    push_neg at h
    have hsp : ∀ z ∈ sphere b ε, ‖f w₀ - f b‖ / 2 ≤ ‖F n z - f b‖ := by
      intro z hz
      have h1 : ‖f z - F n z‖ < ‖f w₀ - f b‖ / 2 := by
        have := hzb z hz
        rwa [dist_eq_norm] at this
      have h2 : ‖f w₀ - f b‖ ≤ ‖f z - f b‖ := hmin₀ z hz
      have h3 : ‖f z - f b‖ - ‖f z - F n z‖ ≤ ‖F n z - f b‖ := by
        have h4 : ‖f z - f b‖ ≤ ‖F n z - f b‖ + ‖f z - F n z‖ := by
          have h5 := norm_add_le (F n z - f b) (f z - F n z)
          have e1 : (F n z - f b) + (f z - F n z) = f z - f b := by ring
          rwa [e1] at h5
        exact sub_le_iff_le_add.mpr h4
      linarith
    have hminz := le_norm_of_forall_mem_sphere_le (g := fun z => F n z - f b) hεpos
      (half_pos hδpos') (((hF n).sub_const (f b)).diffContOnCl_ball hεbU) h hsp
    have hzb' := hminz b (by rw [mem_closedBall, dist_self]; exact hεpos.le)
    have hc : ‖F n b - f b‖ < ‖f w₀ - f b‖ / 2 := by
      have := hnb
      rwa [dist_eq_norm] at this
    linarith
  obtain ⟨y₁, hy₁, hy₁'⟩ := hzero_a
  obtain ⟨y₂, hy₂, hy₂'⟩ := hzero_b
  have hy₁U : y₁ ∈ U := hεaU hy₁
  have hy₂U : y₂ ∈ U := hεbU hy₂
  have hneq : y₁ ≠ y₂ := by
    intro h
    have : y₁ ∈ closedBall b ε := h ▸ hy₂
    exact (Set.disjoint_left.mp hεdisj) hy₁ this
  have heq' : F n y₁ = F n y₂ := by
    have h1 : F n y₁ = f a := sub_eq_zero.mp hy₁'
    have h2 : F n y₂ = f b := sub_eq_zero.mp hy₂'
    rw [h1, h2, hfab]
  exact hneq (hinj n hy₁U hy₂U heq')

end Work.Smooth.SphereJordan


/-!
TODO (parked, 12 elaboration errors remaining):
  * `le_norm_of_forall_mem_sphere_le` line ~39: the final `simpa [inv_eq_one_div]` still fails;
    replace by rewriting `δ⁻¹` to `1/δ` on both sides first (`rw [inv_eq_one_div]` on the goal).
  * the `∃ r > 0, ∀ z ∈ ball a r, z ≠ a → f z - f a ≠ 0` extractions from the `𝓝[{a}ᶜ]`-statements
    (lines ~62-68 and ~79-84): `rw [eventually_nhdsWithin_iff] at hisol` then `Metric.mem_nhds_iff`
    needs the set written as `{z | z ∈ {a}ᶜ → ...}`; use `Filter.eventually_nhdsWithin_iff` and
    `Metric.mem_nhds_iff` with an explicit `have : {z | z ≠ a → f z - f a ≠ 0} ∈ 𝓝 a`.
  * the `linarith` at line ~121 in the reverse-triangle estimate: feed
    `dist_eq_norm`-rewritten hypotheses explicitly.
  * the last lines (~144, ~151): `F n z₁ = f a` from `F n z₁ - f a = 0` needs
    `sub_eq_zero.mp`, and `rw [← dist_eq_norm, dist_comm]` must be replaced by
    `Metric.mem_ball`/`dist_comm` rewrites.
The mathematical content is complete; only Lean bookkeeping is missing.
-/
