/-
# The derivative of the critical Böttcher coordinate at the critical value

**(D1) of the `Work.NAKANE2` design note.**  For `c ∉ M*` the canonical critical Böttcher
coordinate `varphiCrit c` of `T_c(z) = z̄² + c` is analytic on the critical domain
`critDomain c = {G_c > G_c 0}`, which contains the critical value `c`.  This file proves that its
derivative there does not vanish, `deriv (varphiCrit c) c ≠ 0`.

The proof follows the classical argument, in the exact form in which the sibling area proves the
same statement on the *escape set* for `c ∈ M*` (`Work.Bottcher.Inverse.deriv_ne_zero_of_mem_escapeSet`):

1. `varphiCrit c` solves the *quartic* Böttcher equation `φ (p_c z) = (φ z)^4` on the critical
   domain (`p_c = T_c ∘ T_c`, from `varphiCrit_comm_Tantibar` applied twice).
2. The critical points of the quartic `p_c` are `0` and `±√(-c̄)`; for `c ∉ M*` the Green function
   at these points is `G_c 0 = G_c(c)/2 > 0` resp. `G_c 0/2 < G_c 0`, so none of them lies in
   `critDomain c`.  Hence `p_c' ≠ 0` on the critical domain
   (`pDeriv_ne_zero_of_mem_CritDomain`), and a zero of `φ'` propagates forward along the orbit:
   `deriv_eq_zero_of_deriv_eq_zero_pMap_crit` differentiates `φ ∘ p_c = φ^4`.
3. The orbit of every point of the critical domain escapes, so some iterate `(p_c)^[N] c` lies
   beyond the radius `critFarRadius c` where the critical domain contains the whole exterior ball
   (`CritBasic.critFar_subset_CritDomain`) *and* beyond `64 (1 + ‖c‖)`.
4. There, `varphiCrit c` agrees with the explicit product formula `bottcher c`
   (`varphiCrit_eq_bottcher_of_critFar`, via the ratio/uniqueness argument
   `eq_bottcher_of_analytic_gen`), whose derivative is nonvanishing far out
   (`Work.Bottcher.Inverse.deriv_bottcher_ne_zero_of_far`).

The only genuinely new ingredient is `eq_bottcher_of_analytic_gen`, the far-region uniqueness
`Work.Bottcher.Core.eq_bottcher_of_analytic` with the escape radius replaced by an arbitrary
radius `R ≥ escapeRadius c` — which is what lets the *critical domain* (whose far end is the
larger radius `critFarRadius c`) be fed into it.
-/
import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function Set
open scoped Topology ComplexConjugate

namespace Work.NAKANE2.Deriv

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## The quartic Böttcher equation of the critical coordinate -/

theorem pMap_eq_Tantibar_comp (c z : ℂ) :
    Work.Bottcher.pMap c z = Tantibar c (Tantibar c z) := by
  simp only [Work.Bottcher.pMap, Tantibar, map_add, map_pow, Complex.conj_conj]

/-- The quartic Böttcher equation `φ (p_c z) = (φ z)^4` of the canonical critical coordinate on
the critical domain. -/
theorem varphiCrit_comm_pMap {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    Work.Bottcher.varphiCrit c (Work.Bottcher.pMap c z) =
      (Work.Bottcher.varphiCrit c z) ^ 4 := by
  have hT : Tantibar c z ∈ Work.ParamRays.critDomain c :=
    Work.ParamRays.Tantibar_mem_critDomain hz
  rw [pMap_eq_Tantibar_comp, Work.Bottcher.varphiCrit_comm_Tantibar hT,
    Work.Bottcher.varphiCrit_comm_Tantibar hz, map_pow, Complex.conj_conj]
  ring

/-! ## Uniqueness of the Böttcher coordinate on an exterior ball of arbitrary radius

`Work.Bottcher.Core.eq_bottcher_of_analytic` proves that an analytic solution of the Böttcher
problem on the closed far region `{escapeRadius c ≤ ‖z‖}` agrees with the product formula
`bottcher c` there.  The critical domain, however, only contains the exterior of the (possibly
larger) ball of radius `critFarRadius c`; the two facts that enter the proof — preconnectedness of
the exterior ball and its invariance under `p_c` — hold for *every* radius `R ≥ escapeRadius c`.
We therefore record the statement for arbitrary `R ≥ escapeRadius c`. -/

theorem eq_bottcher_of_analytic_gen (c : ℂ) (R : ℝ) (hR : Work.Bottcher.escapeRadius c ≤ R)
    (ψ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ ψ {z : ℂ | R < ‖z‖})
    (hfe : ∀ z : ℂ, R < ‖z‖ → ψ (Work.Bottcher.pMap c z) = (ψ z) ^ 4)
    (hmod : ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Tendsto (fun z : ℂ => ψ z / z) (cocompact ℂ) (nhds (1 : ℂ)))
    {z : ℂ} (hz : R < ‖z‖) : ψ z = Work.Bottcher.bottcher c z := by
  classical
  have hRpos : 0 < R := lt_of_lt_of_le (Work.Bottcher.Core.escapeRadius_pos c) hR
  have hRnneg : 0 ≤ R := hRpos.le
  have hR2 : (2 : ℝ) ≤ R := le_trans (Work.Bottcher.Core.two_le_escapeRadius c) hR
  have hfar_le : ∀ w : ℂ, R < ‖w‖ → Work.Bottcher.escapeRadius c ≤ ‖w‖ :=
    fun w hw => le_trans hR hw.le
  -- ## `p_c` preserves the exterior ball `{R < ‖z‖}`
  have hpS : ∀ w : ℂ, R < ‖w‖ → R < ‖Work.Bottcher.pMap c w‖ := by
    intro w hw
    have h2 : 2 + ‖c‖ ≤ ‖w‖ :=
      le_trans (Work.Bottcher.Core.two_add_norm_le_escapeRadius c) (le_trans hR hw.le)
    have h6 : ‖w‖ ^ 4 / 2 ≤ ‖Work.Bottcher.pMap c w‖ :=
      (Work.Bottcher.Core.pMap_norm_step c w h2).2.1
    have hR3 : (8 : ℝ) ≤ R ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hR2 3
      norm_num at h
      exact h
    have hw4 : R ^ 4 < ‖w‖ ^ 4 := pow_lt_pow_left₀ hw hRnneg (by norm_num : (4 : ℕ) ≠ 0)
    have hmid : R < R ^ 4 / 2 := by nlinarith [hR3, hRpos]
    linarith [h6, hw4, hmid]
  -- ## The product formula on the far region
  have hmodφ : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ →
      ‖Work.Bottcher.bottcher c w‖ = Real.exp (Work.Bottcher.green c w) :=
    fun w hw => Work.Bottcher.Core.norm_bottcher_eq_exp_green_of_escapeRadius_le c hw
  have hφne : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ → Work.Bottcher.bottcher c w ≠ 0 := by
    intro w hw h
    have h1 := hmodφ w hw
    rw [h, norm_zero] at h1
    exact absurd h1.symm (Real.exp_ne_zero _)
  have hfeφ : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ →
      Work.Bottcher.bottcher c (Work.Bottcher.pMap c w) = (Work.Bottcher.bottcher c w) ^ 4 :=
    fun w hw => Work.Bottcher.Core.bottcher_comm_pMap_of_escapeRadius_le c hw
  have hfeU : ∀ w : ℂ, R < ‖w‖ →
      ψ (Work.Bottcher.pMap c w) / Work.Bottcher.bottcher c (Work.Bottcher.pMap c w)
        = (ψ w / Work.Bottcher.bottcher c w) ^ 4 := by
    intro w hw
    rw [hfe w hw, hfeφ w (hfar_le w hw), div_pow]
  -- ## The ratio `u = ψ / φ_c` tends to `1` at infinity
  have hUtendsto : Tendsto (fun u : ℂ => ψ u / Work.Bottcher.bottcher c u)
      (cocompact ℂ) (nhds (1 : ℂ)) := by
    have hratio : Tendsto (fun u : ℂ => (ψ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds ((1 : ℂ) / 1)) :=
      has.div (Work.Bottcher.Core.bottcher_tendsto_atTop c) one_ne_zero
    have hratio' : Tendsto (fun u : ℂ => (ψ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds (1 : ℂ)) := by
      simpa using hratio
    refine hratio'.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with u hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu
      norm_num at hu
    have hφu0 : Work.Bottcher.bottcher c u ≠ 0 := by
      rw [Work.Bottcher.bottcher]
      exact mul_ne_zero hu0 (Complex.exp_ne_zero _)
    field_simp
  -- ## The ratio is continuous and the exterior ball is preconnected
  have hSpre : IsPreconnected {z : ℂ | R < ‖z‖} :=
    Work.ParamRays.isPreconnected_lt_norm hRnneg
  have hcontU : ContinuousOn (fun u : ℂ => ψ u / Work.Bottcher.bottcher c u)
      {z : ℂ | R < ‖z‖} := by
    refine ContinuousOn.div han.continuousOn ?_ ?_
    · intro w hw
      exact (Work.Bottcher.Core.analyticAt_bottcher c w (hfar_le w hw)).continuousAt.continuousWithinAt
    · intro w hw
      exact hφne w (hfar_le w hw)
  have hpre : IsPreconnected
      ((fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) '' {z : ℂ | R < ‖z‖}) :=
    hSpre.image _ hcontU
  -- ## Every value of the ratio on the exterior ball is a `2`-power root of unity
  have hcert : ∀ w : ℂ, R < ‖w‖ → ∃ N : ℕ,
      (ψ w / Work.Bottcher.bottcher c w) ^ (2 ^ N) = 1 := by
    intro w hw
    have hiterS : ∀ n : ℕ, R < ‖(Work.Bottcher.pMap c)^[n] w‖ := by
      intro n
      induction n with
      | zero => simpa using hw
      | succ n ih => rw [Function.iterate_succ_apply']; exact hpS _ ih
    have hiterU : ∀ n : ℕ,
        ψ ((Work.Bottcher.pMap c)^[n] w) / Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] w)
          = (ψ w / Work.Bottcher.bottcher c w) ^ (4 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', hfeU _ (hiterS n), ih, ← pow_mul, pow_succ]
    have hcoc : Tendsto (fun n : ℕ => (Work.Bottcher.pMap c)^[n] w) atTop (cocompact ℂ) := by
      refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
      have hT := Work.Bottcher.Core.tendsto_norm_Tantibar_iterate_of_escapeRadius_le c (hfar_le w hw)
      have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
        tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
      have h1 : Tendsto (fun n : ℕ => ‖(Tantibar c)^[2 * n] w‖) atTop atTop := hT.comp h2n
      refine h1.congr' (Eventually.of_forall (fun n => ?_))
      simp only [dist_zero_right]
      rw [Work.Bottcher.pMap_iterate]
    have hlim : Tendsto (fun n : ℕ =>
        ψ ((Work.Bottcher.pMap c)^[n] w) / Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] w))
        atTop (nhds 1) := hUtendsto.comp hcoc
    have hpow : Tendsto (fun n : ℕ => (ψ w / Work.Bottcher.bottcher c w) ^ (4 ^ n))
        atTop (nhds 1) :=
      hlim.congr' (Eventually.of_forall (fun n => hiterU n))
    exact Work.Bottcher.Core.exists_pow_two_pow_eq_one_of_tendsto_pow_four hpow
  have hsingle :
      ((fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) '' {z : ℂ | R < ‖z‖}).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre
      (by rintro ζ ⟨w, hw, rfl⟩; exact hcert w hw)
  -- ## The constant value is `1`
  set w₀ : ℂ := ((R + 1 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = R + 1 := by
    rw [hw₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hw₀S : R < ‖w₀‖ := by rw [hw₀norm]; linarith
  have hconst : ∀ w : ℂ, R < ‖w‖ →
      ψ w / Work.Bottcher.bottcher c w = ψ w₀ / Work.Bottcher.bottcher c w₀ :=
    fun w hw => hsingle ⟨w, hw, rfl⟩ ⟨w₀, hw₀S, rfl⟩
  have hval : ψ w₀ / Work.Bottcher.bottcher c w₀ = 1 := by
    have hclose : ∀ ε : ℝ, 0 < ε → ‖ψ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ < ε := by
      intro ε hε
      have hmem : {u : ℂ | dist (ψ u / Work.Bottcher.bottcher c u) 1 < ε} ∈ cocompact ℂ :=
        (Metric.tendsto_nhds.mp hUtendsto) ε hε
      rw [Filter.mem_cocompact] at hmem
      obtain ⟨K, hKc, hKsub⟩ := hmem
      obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
      set t : ℝ := max R M + 1 with htdef
      have ht0 : 0 ≤ t := by
        rw [htdef]
        have h := le_max_left R M
        linarith [hRpos.le]
      have htnorm : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      have htmem : R < ‖(t : ℂ)‖ := by
        rw [htnorm, htdef]
        linarith [le_max_left R M]
      have htK : (t : ℂ) ∉ K := by
        intro ht
        have h1 := hM ht
        rw [Metric.mem_closedBall, dist_zero_right, htnorm, htdef] at h1
        linarith [le_max_right R M]
      have hd := hKsub htK
      rw [Set.mem_ofPred_eq, dist_eq_norm] at hd
      rw [hconst t htmem] at hd
      exact hd
    have hzero : ‖ψ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ ≤ 0 :=
      le_of_forall_pos_le_add (fun ε hε => by simpa using (hclose ε hε).le)
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))
  have hfinal : ψ z / Work.Bottcher.bottcher c z = 1 := (hconst z hz).trans hval
  exact (div_eq_one_iff_eq (hφne z (hfar_le z hz))).mp hfinal

/-! ## The critical coordinate is the product formula far out -/

/-- Beyond `critFarRadius c` the critical Böttcher coordinate agrees with the explicit product
formula `bottcher c`. -/
theorem varphiCrit_eq_bottcher_of_critFar (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.CritBasic.critFarRadius c < ‖z‖) :
    Work.Bottcher.varphiCrit c z = Work.Bottcher.bottcher c z := by
  have hcrit : ∀ w : ℂ, Work.Bottcher.CritBasic.critFarRadius c < ‖w‖ →
      w ∈ Work.ParamRays.critDomain c := fun w hw => by
    rw [← Work.Bottcher.CritBasic.critDomain_eq]
    exact Work.Bottcher.CritBasic.critFar_subset_CritDomain c hw
  exact eq_bottcher_of_analytic_gen c (Work.Bottcher.CritBasic.critFarRadius c)
    (Work.Bottcher.CritBasic.escapeRadius_le_critFarRadius c) (Work.Bottcher.varphiCrit c)
    ((Work.Bottcher.analyticOnNhd_varphiCrit c).mono (fun w hw => hcrit w hw))
    (fun w hw => varphiCrit_comm_pMap (hcrit w hw))
    (fun w hw => Work.Bottcher.norm_varphiCrit (hcrit w hw))
    (Work.Bottcher.varphiCrit_div_tendsto_one c) hz

/-! ## The quartic has no critical point in the critical domain -/

/-- For `c ∉ M*` the quartic `p_c` has no critical point in `critDomain c`: the critical points
`0` and `±√(-c̄)` have Green values `G_c 0 > 0` and `G_c 0 / 2 < G_c 0`. -/
theorem pDeriv_ne_zero_of_mem_CritDomain {c z : ℂ} (hc : c ∉ Work.NAKANE2.Mb)
    (hz : z ∈ Work.Bottcher.CritDomain c) : Work.Bottcher.Core.pDeriv c z ≠ 0 := by
  have hgp : 0 < Work.Bottcher.greenParam c := (Work.Bottcher.Green.greenParam_pos_iff c).mpr hc
  have hgz : Work.Bottcher.greenParam c < Work.Bottcher.green c z :=
    Work.Bottcher.mem_CritDomain.mp hz
  intro h
  rw [Work.Bottcher.Core.pDeriv] at h
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' h4
    · rw [h''] at hgz
      rw [← Work.Bottcher.greenParam_def] at hgz
      exact lt_irrefl _ hgz
  · have hsq : z ^ 2 = -(starRingEnd ℂ c) := by linear_combination h'
    have hc' : (starRingEnd ℂ z) ^ 2 = -c := by
      rw [← map_pow, hsq, map_neg, Complex.conj_conj]
    have hT0 : Tantibar c z = 0 := by
      rw [Tantibar, hc']; ring
    have hgreen : Work.Bottcher.green c z = Work.Bottcher.greenParam c / 2 := by
      have h := Work.Bottcher.Green.green_comm c z
      rw [hT0, ← Work.Bottcher.greenParam_def] at h
      linarith
    rw [hgreen] at hgz
    linarith

/-! ## A zero of `φ'` propagates forward along the critical orbit -/

/-- If `φ` is analytic on the critical domain, solves the quartic Böttcher equation there, and
`deriv φ z = 0` at a point `z` of the critical domain, then `deriv φ (p_c z) = 0`.  This is the
derivative of `φ ∘ p_c = φ^4` together with `p_c' ≠ 0` on the critical domain
(`pDeriv_ne_zero_of_mem_CritDomain`). -/
theorem deriv_eq_zero_of_deriv_eq_zero_pMap_crit (c : ℂ) (hc : c ∉ Work.NAKANE2.Mb)
    {φ : ℂ → ℂ}
    (han : AnalyticOnNhd ℂ φ (Work.Bottcher.CritDomain c))
    (hfe : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    {z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) (hzd : deriv φ z = 0) :
    deriv φ (Work.Bottcher.pMap c z) = 0 := by
  have hpz : Work.Bottcher.pMap c z ∈ Work.Bottcher.CritDomain c :=
    Work.Bottcher.CritBasic.pMap_mem_CritDomain hz
  have hφz : HasDerivAt φ (deriv φ z) z := (han z hz).differentiableAt.hasDerivAt
  have hφpz : HasDerivAt φ (deriv φ (Work.Bottcher.pMap c z)) (Work.Bottcher.pMap c z) :=
    (han _ hpz).differentiableAt.hasDerivAt
  have hp : HasDerivAt (Work.Bottcher.pMap c) (Work.Bottcher.Core.pDeriv c z) z :=
    Work.Bottcher.Core.hasDerivAt_pMap c z
  have hcomp : HasDerivAt (fun w => φ (Work.Bottcher.pMap c w))
      (deriv φ (Work.Bottcher.pMap c z) * Work.Bottcher.Core.pDeriv c z) z :=
    hφpz.comp z hp
  have hpow : HasDerivAt (fun w => (φ w) ^ 4) (4 * (φ z) ^ 3 * deriv φ z) z := by
    convert hφz.pow 4 using 1
  have hCritOpen : IsOpen (Work.Bottcher.CritDomain c) :=
    Work.Bottcher.CritBasic.isOpen_CritDomain c
  have heq : (fun w => φ (Work.Bottcher.pMap c w)) =ᶠ[𝓝 z] (fun w => (φ w) ^ 4) := by
    filter_upwards [hCritOpen.mem_nhds hz] with w hw
    exact hfe w hw
  have hder := heq.deriv_eq
  rw [hcomp.deriv, hpow.deriv, hzd, mul_zero] at hder
  rcases mul_eq_zero.mp hder with h' | h'
  · exact h'
  · exact absurd h' (pDeriv_ne_zero_of_mem_CritDomain hc hz)

/-! ## The target -/

theorem deriv_varphiCrit_self_ne_zero {c : ℂ} (hc : c ∉ Work.NAKANE2.Mb) :
    deriv (Work.Bottcher.varphiCrit c) c ≠ 0 := by
  intro hd0
  have hzp : c ∈ Work.ParamRays.critDomain c := Work.ParamRays.self_mem_critDomain hc
  have hzc : c ∈ Work.Bottcher.CritDomain c := by
    rw [Work.Bottcher.CritBasic.critDomain_eq]; exact hzp
  have hgreen_pos : 0 < Work.Bottcher.green c c := by
    have h := Work.Bottcher.mem_CritDomain.mp hzc
    have h0 := Work.Bottcher.Contraction.greenParam_nonneg' c
    linarith
  have han : AnalyticOnNhd ℂ (Work.Bottcher.varphiCrit c) (Work.Bottcher.CritDomain c) := by
    rw [Work.Bottcher.CritBasic.critDomain_eq]
    exact Work.Bottcher.analyticOnNhd_varphiCrit c
  have hfe : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      Work.Bottcher.varphiCrit c (Work.Bottcher.pMap c z) =
        (Work.Bottcher.varphiCrit c z) ^ 4 := by
    intro z hz
    rw [Work.Bottcher.CritBasic.critDomain_eq] at hz
    exact varphiCrit_comm_pMap hz
  have hiter_crit : ∀ n : ℕ, (Work.Bottcher.pMap c)^[n] c ∈ Work.Bottcher.CritDomain c := by
    intro n
    induction n with
    | zero => simpa using hzc
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact Work.Bottcher.CritBasic.pMap_mem_CritDomain ih
  have hiter0 : ∀ n : ℕ,
      deriv (Work.Bottcher.varphiCrit c) ((Work.Bottcher.pMap c)^[n] c) = 0 := by
    intro n
    induction n with
    | zero => simpa using hd0
    | succ n ih =>
        have h' := deriv_eq_zero_of_deriv_eq_zero_pMap_crit c hc han hfe (hiter_crit n) ih
        simpa only [Function.iterate_succ_apply'] using h'
  have hnorm : Tendsto (fun n : ℕ => ‖(Work.Bottcher.pMap c)^[n] c‖) atTop atTop := by
    have hT : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] c‖) atTop atTop :=
      (Work.Bottcher.Green.green_pos_iff c c).mp hgreen_pos
    have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
    refine (hT.comp h2n).congr' (Eventually.of_forall (fun n => ?_))
    simp only [Function.comp_apply]
    rw [Work.Bottcher.pMap_iterate]
  obtain ⟨N, hN⟩ := (hnorm.eventually
    (eventually_ge_atTop (max (Work.Bottcher.CritBasic.critFarRadius c + 1) (64 * (1 + ‖c‖))))).exists
  set w : ℂ := (Work.Bottcher.pMap c)^[N] c with hwdef
  have hw_far : Work.Bottcher.CritBasic.critFarRadius c < ‖w‖ := by
    have h1 : Work.Bottcher.CritBasic.critFarRadius c + 1 ≤ ‖w‖ :=
      le_trans (le_max_left _ _) hN
    linarith
  have hw_64 : 64 * (1 + ‖c‖) ≤ ‖w‖ := le_trans (le_max_right _ _) hN
  have hw0 : deriv (Work.Bottcher.varphiCrit c) w = 0 := by
    rw [hwdef]; exact hiter0 N
  have hopen : IsOpen {z : ℂ | Work.Bottcher.CritBasic.critFarRadius c < ‖z‖} :=
    isOpen_lt continuous_const continuous_norm
  have heq : Work.Bottcher.varphiCrit c =ᶠ[𝓝 w] Work.Bottcher.bottcher c := by
    filter_upwards [hopen.mem_nhds hw_far] with z hz
    exact varphiCrit_eq_bottcher_of_critFar c hz
  have hderiv_eq : deriv (Work.Bottcher.varphiCrit c) w = deriv (Work.Bottcher.bottcher c) w :=
    heq.deriv_eq
  rw [hw0] at hderiv_eq
  exact (Work.Bottcher.Inverse.deriv_bottcher_ne_zero_of_far c hw_64) hderiv_eq.symm

end

end Work.NAKANE2.Deriv
