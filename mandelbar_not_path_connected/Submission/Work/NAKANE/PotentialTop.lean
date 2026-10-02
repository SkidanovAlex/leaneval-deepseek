/-
# The potential at infinity, and the boundary behaviour of `Φ`

This file collects everything about `Φ` that follows from

* the modulus identity `‖Φ c‖ = exp (2 G_c(0))` (`Work.ParamRays.norm_Phi_eq_exp`, from Böttcher's
  theorem `Work.Bottcher.bottcherExists_crit`),
* the product-formula asymptotic `B_c(c) / c → 1`
  (`Work.Bottcher.Critical.Phi_isBigO_atTop`), and
* the *continuity* of the parameter potential (`Work.NAKANE.continuous_paramPotential`):

* `Work.NAKANE.bottcher_self_div_tendsto_one` : `bottcher c c / c → 1`;
* `Work.NAKANE.norm_bottcher_self_eq_norm_Phi` : the product formula and the canonical coordinate
  have the *same modulus* at the critical value (`‖B_c(c)‖ = ‖φ_c(c)‖`) — obtained from
  `(B_c(c))^4 = B_c(p_c c) = φ_c(p_c c)` in the far region, so no branch ambiguity is involved;
* `Work.NAKANE.Phi_lower_bound_atTop` : `‖c‖ / 2 ≤ ‖Φ c‖` for all large `c`;
* `Work.NAKANE.paramPotential_tendsto_atTop` and `Work.NAKANE.isCompact_paramPotential_le`: the
  parameter potential diverges at infinity and its sublevel sets are compact;
* `Work.NAKANE.tendsto_norm_Phi_near_Mb`: `‖Φ c‖ → 1` as `c → Mb` — the *boundary* limit of `Φ` is
  the unit circle, not `0` (the junk value `Φ = 0` on `Mb` is a genuine discontinuity: `Φ` is not
  continuous at the boundary of `Mb`).

The last two are exactly what makes `Φ` *proper* as a map `Mbᶜ → {1 < ‖w‖}`
(`Work.NAKANE.PhiProper`).
-/
import Submission.Work.NAKANE.PhiContinuity
import Submission.Work.Bottcher.Critical.Phi_isBigO_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The product-formula asymptotic -/

/-- **The product formula is asymptotic to the identity along the diagonal.** -/
theorem bottcher_self_div_tendsto_one :
    Tendsto (fun c : ℂ => Work.Bottcher.bottcher c c / c) (cocompact ℂ) (nhds (1 : ℂ)) := by
  refine Tendsto.congr' ?_ Work.Bottcher.Critical.Phi_isBigO_atTop
  filter_upwards [Work.ParamRays.eventually_not_mem_mandelbar] with c hc
  rw [Work.Bottcher.Phi_eq_bottcher hc]

/-! ## The modulus of the product formula at the critical value -/

/-- The `p_c`-orbit of `c` leaves the far region as soon as `‖c‖ > 8`: the coarse far radius
`2 (max 2 (1 + ‖c‖))^2 + 2` is dominated by `‖p_c c‖ = ‖(c² + c̄)² + c‖ ≥ (‖c‖² - ‖c‖)² - ‖c‖`. -/
theorem farRadius_lt_norm_pMap_self {c : ℂ} (hc : 8 < ‖c‖) :
    farRadius ‖c‖ < ‖Work.Bottcher.pMap c c‖ := by
  have hcpos : (0 : ℝ) < ‖c‖ := by linarith
  have h1 : (‖c‖ ^ 2 - ‖c‖) ^ 2 - ‖c‖ ≤ ‖Work.Bottcher.pMap c c‖ := by
    have h2 : ‖c‖ ^ 2 - ‖c‖ ≤ ‖c ^ 2 + conj c‖ := by
      have h2a : ‖c ^ 2‖ ≤ ‖c ^ 2 + conj c‖ + ‖conj c‖ := by
        have h := norm_sub_le (c ^ 2 + conj c) (conj c)
        rw [show c ^ 2 + conj c - conj c = c ^ 2 by ring] at h
        exact h
      rw [norm_pow, Complex.norm_conj] at h2a
      linarith
    have h3 : ‖c ^ 2 + conj c‖ ^ 2 - ‖c‖ ≤ ‖(c ^ 2 + conj c) ^ 2 + c‖ := by
      have h3a : ‖(c ^ 2 + conj c) ^ 2‖ ≤ ‖(c ^ 2 + conj c) ^ 2 + c‖ + ‖c‖ := by
        have h := norm_sub_le ((c ^ 2 + conj c) ^ 2 + c) c
        rw [show (c ^ 2 + conj c) ^ 2 + c - c = (c ^ 2 + conj c) ^ 2 by ring] at h
        exact h
      rw [norm_pow] at h3a
      linarith
    have h4 : (‖c‖ ^ 2 - ‖c‖) ^ 2 ≤ ‖c ^ 2 + conj c‖ ^ 2 := by
      have h5 : (0 : ℝ) ≤ ‖c‖ ^ 2 - ‖c‖ := by nlinarith
      exact pow_le_pow_left₀ h5 h2 2
    rw [Work.Bottcher.pMap_apply]
    linarith
  have hx8 : (8 : ℝ) ≤ ‖c‖ := le_of_lt hc
  have hq2 : (0 : ℝ) ≤ (‖c‖ - 1) ^ 2 - 49 := by
    nlinarith [hx8, sq_nonneg (‖c‖ - 8)]
  have hq : 49 * ‖c‖ ^ 2 ≤ (‖c‖ ^ 2 - ‖c‖) ^ 2 := by nlinarith [hq2, hcpos]
  have h4 : (max 2 (1 + ‖c‖)) ^ 2 ≤ 4 * ‖c‖ ^ 2 := by
    have h3 : max 2 (1 + ‖c‖) ≤ 2 * ‖c‖ := max_le (by linarith) (by linarith)
    have h5 : (0 : ℝ) ≤ max 2 (1 + ‖c‖) := by positivity
    nlinarith [h3, hcpos]
  have h6 : 2 * (max 2 (1 + ‖c‖)) ^ 2 + 2 < (‖c‖ ^ 2 - ‖c‖) ^ 2 - ‖c‖ := by
    nlinarith [h4, hq, hx8]
  have h7 : farRadius ‖c‖ ≤ 2 * (max 2 (1 + ‖c‖)) ^ 2 + 2 := le_rfl
  linarith

/-- The second `T_c`-iterate of `c` is in the critical domain. -/
theorem pMap_self_mem_critDomain {c : ℂ} (hcMb : c ∉ Mb) :
    Work.Bottcher.pMap c c ∈ Work.ParamRays.critDomain c := by
  have h1 : c ∈ Work.ParamRays.critDomain c := Work.ParamRays.self_mem_critDomain hcMb
  rw [Work.NAKANE.BottcherFar.pMap_eq_Tantibar_comp]
  exact Work.ParamRays.Tantibar_mem_critDomain (Work.ParamRays.Tantibar_mem_critDomain h1)

/-- **The product formula and the canonical Böttcher coordinate have the same modulus at the
critical value.**  For `c` outside the mandelbar with `‖c‖ > 8`, `‖bottcher c c‖ = ‖Φ c‖`.

Indeed `(B_c c)^4 = B_c (p_c c)` (`bottcher_comm_pMap_iterate`) and `B_c (p_c c) = φ_c (p_c c)` in the
far region (`jointVarphi_eq_jointBottcher_of_far'`), while
`‖φ_c (p_c c)‖ = exp (G_c (p_c c)) = exp (8 G_c 0) = ‖φ_c c‖^4`
(`norm_varphiCrit`, `greenFun_orbit`, and the critical value identity `G_c c = 2 G_c 0`). -/
theorem norm_bottcher_self_eq_norm_Phi {c : ℂ} (hcMb : c ∉ Mb) (hc : 8 < ‖c‖) :
    ‖Work.Bottcher.bottcher c c‖ = ‖Work.ParamRays.Phi c‖ := by
  have hcrit : c ∈ Work.ParamRays.critDomain c := Work.ParamRays.self_mem_critDomain hcMb
  have hcrit2 : Work.Bottcher.pMap c c ∈ Work.ParamRays.critDomain c :=
    pMap_self_mem_critDomain hcMb
  -- the critical value identity `G_c c = 2 G_c 0`
  have hGc : Work.ParamRays.greenFun c c = 2 * Work.ParamRays.paramPotential c := by
    have h := Work.ParamRays.greenFun_orbit c 0 1
    rw [Work.ParamRays.orbit_zero_one] at h
    rw [h, Work.ParamRays.paramPotential]
    norm_num
  have hmod_self : ‖Work.Bottcher.varphiCrit c c‖
      = Real.exp (2 * Work.ParamRays.paramPotential c) := by
    rw [Work.Bottcher.norm_varphiCrit hcrit, Work.Bottcher.Contraction.green_eq_greenFun c c, hGc]
  -- the `p_c`-iterate stays in the critical domain and doubles the potential twice
  have hgreen2 : Work.ParamRays.greenFun c (Work.Bottcher.pMap c c)
      = 4 * Work.ParamRays.greenFun c c := by
    have h := Work.ParamRays.greenFun_orbit c c 2
    rw [show Work.ParamRays.orbit c c 2 = Work.Bottcher.pMap c c by
      rw [Work.Bottcher.pMap_eq_iterate_two]
      rfl] at h
    rw [h]
    norm_num
  have hmod_pMap : ‖Work.Bottcher.varphiCrit c (Work.Bottcher.pMap c c)‖
      = Real.exp (8 * Work.ParamRays.paramPotential c) := by
    rw [Work.Bottcher.norm_varphiCrit hcrit2,
      Work.Bottcher.Contraction.green_eq_greenFun c (Work.Bottcher.pMap c c), hgreen2, hGc]
    congr 1
    ring
  have hmod2 : ‖Work.Bottcher.varphiCrit c (Work.Bottcher.pMap c c)‖
      = ‖Work.Bottcher.varphiCrit c c‖ ^ 4 := by
    rw [hmod_pMap, hmod_self, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- the functional equation of the product formula and the far identity
  have hB4 : (Work.Bottcher.bottcher c c) ^ 4
      = Work.Bottcher.bottcher c (Work.Bottcher.pMap c c) := by
    have h := Work.NAKANE.BottcherFar.bottcher_comm_pMap_iterate hcrit 1
    simpa using h
  have hfar : Work.Bottcher.bottcher c (Work.Bottcher.pMap c c)
      = Work.Bottcher.varphiCrit c (Work.Bottcher.pMap c c) :=
    (Work.NAKANE.jointVarphi_eq_jointBottcher_of_far' (C := ‖c‖) le_rfl
      (farRadius_lt_norm_pMap_self hc)).symm
  have hpow : ‖Work.Bottcher.bottcher c c‖ ^ 4 = ‖Work.Bottcher.varphiCrit c c‖ ^ 4 := by
    rw [← norm_pow, hB4, hfar, hmod2]
  have hphi4 : ‖Work.Bottcher.varphiCrit c c‖ = ‖Work.ParamRays.Phi c‖ := by
    rw [Phi_eq_varphiCrit hcMb]
  rw [hphi4] at hpow
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp hpow

/-! ## The growth of `Φ` at infinity -/

/-- **`‖Φ c‖` grows at least like `‖c‖ / 2` at infinity.** -/
theorem Phi_lower_bound_atTop :
    ∀ᶠ c : ℂ in cocompact ℂ, ‖c‖ / 2 ≤ ‖Work.ParamRays.Phi c‖ := by
  have h1 : ∀ᶠ c : ℂ in cocompact ℂ, ‖Work.Bottcher.bottcher c c / c - 1‖ < 1 / 2 := by
    have := (Metric.tendsto_nhds.mp bottcher_self_div_tendsto_one) (1 / 2) (by norm_num)
    simpa [dist_eq_norm] using this
  filter_upwards [h1, Work.ParamRays.eventually_not_mem_mandelbar,
    tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop (8 : ℝ))] with c hc hcMb hc8
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc8
    norm_num at hc8
  have h2 : (1 : ℝ) / 2 < ‖Work.Bottcher.bottcher c c / c‖ := by
    have h3 : |‖Work.Bottcher.bottcher c c / c‖ - 1| < 1 / 2 := by
      have h4 := abs_norm_sub_norm_le (Work.Bottcher.bottcher c c / c) (1 : ℂ)
      rw [norm_one] at h4
      linarith
    linarith [(abs_lt.mp h3).1]
  have hcb : Work.Bottcher.bottcher c c = c * (Work.Bottcher.bottcher c c / c) := by
    field_simp
  have hB : ‖c‖ / 2 ≤ ‖Work.Bottcher.bottcher c c‖ := by
    rw [hcb, norm_mul]
    nlinarith [norm_pos_iff.mpr hcne, h2]
  rw [← norm_bottcher_self_eq_norm_Phi hcMb hc8]
  exact hB

/-- **The parameter potential tends to `+∞` at infinity.** -/
theorem paramPotential_tendsto_atTop (t : ℝ) :
    ∃ R : ℝ, ∀ c : ℂ, R ≤ ‖c‖ → t ≤ Work.ParamRays.paramPotential c := by
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.mp Phi_lower_bound_atTop
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max M (2 * Real.exp (2 * t)) + 1, fun c hc => ?_⟩
  have hMc : M < ‖c‖ := by
    have := le_max_left M (2 * Real.exp (2 * t))
    linarith
  have hcK : c ∉ K := by
    intro hmem
    have h1 := hM hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  have hbound : ‖c‖ / 2 ≤ ‖Work.ParamRays.Phi c‖ := hKs hcK
  by_cases hcMb : c ∈ Mb
  · have h0 : Work.ParamRays.Phi c = 0 := Work.ParamRays.Phi_eq_zero_of_mem hcMb
    rw [h0, norm_zero] at hbound
    have hpos : (0 : ℝ) < ‖c‖ := by
      have h2 := le_max_right M (2 * Real.exp (2 * t))
      have h3 : (0 : ℝ) < Real.exp (2 * t) := Real.exp_pos _
      linarith
    linarith
  · have hmod : ‖Work.ParamRays.Phi c‖ = Real.exp (2 * Work.ParamRays.paramPotential c) :=
      Work.ParamRays.norm_Phi_eq_exp Work.Bottcher.bottcherExists_crit hcMb
    rw [hmod] at hbound
    have hexp : Real.exp (2 * t) < Real.exp (2 * Work.ParamRays.paramPotential c) := by
      have h2 : 2 * Real.exp (2 * t) < ‖c‖ := by
        have := le_max_right M (2 * Real.exp (2 * t))
        linarith
      linarith
    have := Real.exp_lt_exp.mp hexp
    linarith

/-- **The sublevel sets of the parameter potential are compact.** -/
theorem isCompact_paramPotential_le (t : ℝ) :
    IsCompact {c : ℂ | Work.ParamRays.paramPotential c ≤ t} := by
  obtain ⟨R, hR⟩ := paramPotential_tendsto_atTop (t + 1)
  have hclosed : IsClosed {c : ℂ | Work.ParamRays.paramPotential c ≤ t} :=
    isClosed_le continuous_paramPotential continuous_const
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, ?_⟩
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max R 1)).subset fun c hc => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  have h1 : R ≤ ‖c‖ := le_trans (le_max_left R 1) hcon.le
  have h2 := hR c h1
  have hc' : Work.ParamRays.paramPotential c ≤ t := hc
  linarith

/-! ## The boundary behaviour of `Φ` -/

/-- **`‖Φ c‖ → 1` at the boundary of the mandelbar.**  For `c₀ ∈ Mb` and `ε > 0` there is `δ > 0`
with `‖Φ c‖ < 1 + ε` for all `c` at distance `< δ` from `c₀` outside the mandelbar.

(Note that the *junk value* on `Mb` itself is `0`, so `Φ` is *not* continuous at the boundary: the
limit is on the unit circle, not `0`.) -/
theorem tendsto_norm_Phi_near_Mb {c₀ : ℂ} (hc₀ : c₀ ∈ Mb) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ c : ℂ, dist c c₀ < δ → c ∉ Mb → ‖Work.ParamRays.Phi c‖ < 1 + ε := by
  have hlog : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  set η : ℝ := Real.log (1 + ε) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have h0 : Work.ParamRays.paramPotential c₀ = 0 :=
    (Work.ParamRays.paramPotential_eq_zero_iff c₀).mpr hc₀
  have hev : ∀ᶠ c : ℂ in nhds c₀,
      dist (Work.ParamRays.paramPotential c) (Work.ParamRays.paramPotential c₀) < η :=
    (continuous_paramPotential.tendsto c₀).eventually (Metric.ball_mem_nhds _ hη)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ, hδ, fun c hc hcMb => ?_⟩
  have h1 : Work.ParamRays.paramPotential c < η := by
    have h2 : dist (Work.ParamRays.paramPotential c) (Work.ParamRays.paramPotential c₀) < η :=
      hδ' hc
    rw [h0, Real.dist_eq, sub_zero, abs_lt] at h2
    exact h2.2
  have hmod : ‖Work.ParamRays.Phi c‖ = Real.exp (2 * Work.ParamRays.paramPotential c) :=
    Work.ParamRays.norm_Phi_eq_exp Work.Bottcher.bottcherExists_crit hcMb
  rw [hmod]
  calc Real.exp (2 * Work.ParamRays.paramPotential c)
      < Real.exp (2 * η) := Real.exp_lt_exp.mpr (by linarith)
    _ = Real.exp (Real.log (1 + ε)) := by
        congr 1
        rw [hηdef]
        ring
    _ = 1 + ε := Real.exp_log (by linarith)

end Work.NAKANE
