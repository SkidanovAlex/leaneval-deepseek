import Mathlib
import Submission.Work.GATE.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE.Segment

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **The transit coordinate drops below `A₀ - 2` near a frontier point.**  If the phase of the
transit coordinate blows up (`Re trans → -∞`) at `p` inside `Nm`, and the straight path to `p`
stays in `Nm` up to `p`, then there is `μ₀ ∈ (0, 1)` at which the real part of the transit
coordinate along the path is `< A₀ - 2`. -/
private lemma aux_mu_re_lt {y p : ℂ} {trans : ℂ → ℂ} {Nm : Set ℂ} {A₀ : ℝ}
    (hblow : Tendsto (fun c => (trans c).re) (𝓝[Nm] p) atBot)
    (hseg : ∀ μ ∈ Set.Ico (0 : ℝ) 1, y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm) :
    ∃ μ₀ ∈ Set.Ioo (0 : ℝ) 1,
      (trans (y + ((μ₀ : ℝ) : ℂ) * (p - y))).re < A₀ - 2 := by
  rw [tendsto_atBot] at hblow
  have hb : ∀ᶠ c in 𝓝[Nm] p, (trans c).re ≤ A₀ - 3 := hblow (A₀ - 3)
  rw [eventually_nhdsWithin_iff] at hb
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hb
  have hcont : Continuous fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hp1 : y + (((1 : ℝ) : ℂ)) * (p - y) = p := by
    rw [Complex.ofReal_one, one_mul]; abel
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hcont.continuousAt δ hδpos
  set t : ℝ := min η (1 / 2) with ht
  have htpos : 0 < t := by rw [ht]; exact lt_min hηpos (by norm_num)
  have htle1 : t ≤ η := by rw [ht]; exact min_le_left _ _
  have htle2 : t ≤ 1 / 2 := by rw [ht]; exact min_le_right _ _
  refine ⟨1 - t / 2, ⟨by linarith, by linarith⟩, ?_⟩
  have hd : dist (1 - t / 2) (1 : ℝ) < η := by
    rw [Real.dist_eq]
    have h1 : 1 - t / 2 - 1 = -(t / 2) := by ring
    rw [h1, abs_neg, abs_of_nonneg (by linarith)]
    linarith
  have hdist : dist (y + (((1 - t / 2 : ℝ)) : ℂ) * (p - y)) p < δ := by
    have := hη (x := 1 - t / 2) hd
    rwa [hp1] at this
  have hmem : y + (((1 - t / 2 : ℝ)) : ℂ) * (p - y) ∈ Nm :=
    hseg _ ⟨by linarith, by linarith⟩
  have hbd : (trans (y + (((1 - t / 2 : ℝ)) : ℂ) * (p - y))).re ≤ A₀ - 3 :=
    hδ hdist hmem
  linarith

theorem seg_tongues {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm) (hfront : c₀ ∈ frontier Nm)
    (TD : Work.GATE.TransitData c₀ Nm) {r : ℝ} (hr : 0 < r) :
    ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y,
        e₁ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧ e₂ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
        Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e₁ ∧
        Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e₂ := by
  -- (0) frontier data
  have hfron : c₀ ∈ closure Nm \ Nm := by rwa [hOpen.frontier_eq] at hfront
  have hc0not : c₀ ∉ Nm := hfron.2
  have hc0cl : c₀ ∈ closure Nm := hfron.1
  have hminpos : 0 < min TD.ρ r := lt_min TD.hρ hr
  -- (1) a point `y ∈ Nm` close to `c₀`
  have hy_ex : ∃ y ∈ Nm, dist c₀ y < min TD.ρ r / 8 := by
    rw [Metric.mem_closure_iff] at hc0cl
    exact hc0cl _ (div_pos hminpos (by norm_num))
  obtain ⟨y, hyNm, hyc0⟩ := hy_ex
  have hyc0' : dist y c₀ < min TD.ρ r / 8 := by rw [dist_comm]; exact hyc0
  -- (2) the nearest frontier point `p`
  have hNm_univ : Nm ≠ Set.univ := by
    intro h; rw [h, frontier_univ] at hfront; exact hfront
  obtain ⟨p, hpfron, hpd⟩ := exists_mem_frontier_infDist_compl_eq_dist hyNm hNm_univ
  have hpnotNm : p ∉ Nm := by
    have h := hpfron; rw [hOpen.frontier_eq] at h; exact h.2
  have hc0c : c₀ ∈ Nmᶜ := by simpa using hc0not
  have hle1 : dist y p ≤ dist c₀ y := by
    calc dist y p = Metric.infDist y Nmᶜ := hpd.symm
      _ ≤ dist y c₀ := Metric.infDist_le_dist_of_mem hc0c
      _ = dist c₀ y := dist_comm _ _
  have hpdist : dist c₀ p < min TD.ρ r / 4 := by
    have h1 : dist y p < min TD.ρ r / 8 := lt_of_le_of_lt hle1 hyc0
    calc dist c₀ p ≤ dist c₀ y + dist y p := dist_triangle _ _ _
      _ < min TD.ρ r / 8 + min TD.ρ r / 8 := by linarith
      _ = min TD.ρ r / 4 := by ring
  have hpdist' : dist p c₀ < min TD.ρ r / 4 := by rw [dist_comm]; exact hpdist
  -- (3) the straight path
  have hφcont : Continuous fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hYeq : ∀ μ : ℝ, y + ((μ : ℝ) : ℂ) * (p - y) - y = ((μ : ℝ) : ℂ) * (p - y) :=
    fun μ => by ring
  have hdist_φ : ∀ μ : ℝ, dist y (y + ((μ : ℝ) : ℂ) * (p - y)) = |μ| * dist y p := by
    intro μ
    have hpp : dist y p = ‖p - y‖ := by rw [dist_eq_norm, norm_sub_rev]
    rw [hpp, dist_eq_norm, norm_sub_rev, hYeq μ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hball_near : ∀ z : ℂ, dist y z < dist y p → z ∈ Nm := by
    intro z hz
    by_contra hzn
    have hzm : z ∈ Nmᶜ := by simpa using hzn
    have h := Metric.infDist_le_dist_of_mem (x := y) (s := Nmᶜ) hzm
    rw [hpd] at h
    linarith
  have hφ_mem_Nm : ∀ μ ∈ Set.Ico (0 : ℝ) 1, y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm := by
    intro μ hμ
    have hμ0 : 0 ≤ μ := hμ.1
    have hμ1 : μ < 1 := hμ.2
    have hpos : 0 < dist y p := dist_pos.mpr (by intro h; exact hpnotNm (h ▸ hyNm))
    have hbd : dist y (y + ((μ : ℝ) : ℂ) * (p - y)) < dist y p := by
      rw [hdist_φ]
      calc |μ| * dist y p = μ * dist y p := by rw [abs_of_nonneg hμ0]
        _ < 1 * dist y p := mul_lt_mul_of_pos_right hμ1 hpos
        _ = dist y p := one_mul _
    exact hball_near _ hbd
  -- ball memberships
  have hyball : y ∈ Metric.ball c₀ (min TD.ρ r / 4) := by
    rw [Metric.mem_ball]; linarith [hyc0', hminpos]
  have hpball4 : p ∈ Metric.ball c₀ (min TD.ρ r / 4) := by
    rw [Metric.mem_ball]; linarith [hpdist']
  have hφ_conv : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      y + ((μ : ℝ) : ℂ) * (p - y) ∈ Metric.ball c₀ (min TD.ρ r / 4) := by
    intro μ hμ
    have hpp : y + (p - y) ∈ Metric.ball c₀ (min TD.ρ r / 4) := by
      have : y + (p - y) = p := by abel
      rw [this]; exact hpball4
    have hc := (convex_ball c₀ (min TD.ρ r / 4)).add_smul_mem hyball hpp hμ
    simpa [Complex.real_smul] using hc
  have hφ_mem_ballρ : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      y + ((μ : ℝ) : ℂ) * (p - y) ∈ Metric.ball c₀ TD.ρ := by
    intro μ hμ
    have h := hφ_conv μ hμ
    rw [Metric.mem_ball] at h ⊢
    have h2 : min TD.ρ r / 4 < TD.ρ := by have := min_le_left TD.ρ r; linarith [TD.hρ]
    linarith
  have hφ_mem_ballr : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      y + ((μ : ℝ) : ℂ) * (p - y) ∈ Metric.ball c₀ r := by
    intro μ hμ
    have h := hφ_conv μ hμ
    rw [Metric.mem_ball] at h ⊢
    have h2 : min TD.ρ r / 4 < r := by have := min_le_right TD.ρ r; linarith [hr]
    linarith
  have hyballρ : y ∈ Metric.ball c₀ TD.ρ := by
    rw [Metric.mem_ball]
    have := min_le_left TD.ρ r; linarith [TD.hρ, hyc0']
  have hpballρ : p ∈ Metric.ball c₀ TD.ρ := by
    rw [Metric.mem_ball]
    have := min_le_left TD.ρ r; linarith [TD.hρ, hpdist']
  -- (4) the phase blows up: find `μ₀`
  obtain ⟨μ₀, hμ₀, hμ₀'⟩ := aux_mu_re_lt (trans := TD.trans) (A₀ := (TD.trans y).re)
    (TD.blowup p ⟨hpfron, hpballρ⟩) hφ_mem_Nm
  -- (5) continuity on `[0, μ₀]` and the lattice crossings
  have hmaps : MapsTo (fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y)) (Set.Icc (0 : ℝ) μ₀)
      (Nm ∩ Metric.ball c₀ TD.ρ) := by
    intro μ hμ
    exact ⟨hφ_mem_Nm μ ⟨hμ.1, lt_of_le_of_lt hμ.2 hμ₀.2⟩,
      hφ_mem_ballρ μ ⟨hμ.1, le_of_lt (lt_of_le_of_lt hμ.2 hμ₀.2)⟩⟩
  have hcomp : ContinuousOn (TD.trans ∘ fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y))
      (Set.Icc (0 : ℝ) μ₀) :=
    TD.cont.comp hφcont.continuousOn hmaps
  have hfcont : ContinuousOn (fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re)
      (Set.Icc (0 : ℝ) μ₀) :=
    Complex.continuous_re.comp_continuousOn hcomp
  have hf0 : (fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re) 0 = (TD.trans y).re := by
    simp
  have hv1 : TD.xLeak + ((⌊(TD.trans y).re - TD.xLeak⌋ : ℤ) : ℝ) ∈
      Set.Icc ((fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re) μ₀)
              ((fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re) 0) := by
    refine ⟨?_, ?_⟩
    · change (TD.trans (y + ((μ₀ : ℝ) : ℂ) * (p - y))).re ≤
        TD.xLeak + ((⌊(TD.trans y).re - TD.xLeak⌋ : ℤ) : ℝ)
      have h := Int.lt_floor_add_one ((TD.trans y).re - TD.xLeak)
      linarith
    · rw [hf0]
      have h := Int.floor_le ((TD.trans y).re - TD.xLeak)
      linarith
  have hv2 : TD.xLeak + 1 / 2 + ((⌊(TD.trans y).re - TD.xLeak - 1 / 2⌋ : ℤ) : ℝ) ∈
      Set.Icc ((fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re) μ₀)
              ((fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re) 0) := by
    refine ⟨?_, ?_⟩
    · change (TD.trans (y + ((μ₀ : ℝ) : ℂ) * (p - y))).re ≤
        TD.xLeak + 1 / 2 + ((⌊(TD.trans y).re - TD.xLeak - 1 / 2⌋ : ℤ) : ℝ)
      have h := Int.lt_floor_add_one ((TD.trans y).re - TD.xLeak - 1 / 2)
      linarith
    · rw [hf0]
      have h := Int.floor_le ((TD.trans y).re - TD.xLeak - 1 / 2)
      linarith
  have hile : (0 : ℝ) ≤ μ₀ := le_of_lt hμ₀.1
  obtain ⟨μ₁, hμ₁, hfμ₁⟩ := (intermediate_value_Icc' hile hfcont) hv1
  obtain ⟨μ₂, hμ₂, hfμ₂⟩ := (intermediate_value_Icc' hile hfcont) hv2
  -- (6) the two escape points
  have hm₁ : y + ((μ₁ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ TD.ρ := hmaps hμ₁
  have hm₂ : y + ((μ₂ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ TD.ρ := hmaps hμ₂
  have him₁ : |(TD.trans (y + ((μ₁ : ℝ) : ℂ) * (p - y))).im| < TD.r₀ / 2 :=
    lt_of_le_of_lt (TD.height _ hm₁) (by linarith [TD.hr₀])
  have him₂ : |(TD.trans (y + ((μ₂ : ℝ) : ℂ) * (p - y))).im| < TD.r₀ / 2 :=
    lt_of_le_of_lt (TD.height _ hm₂) (by linarith [TD.hr₀])
  have hb₁ : Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ (y + ((μ₁ : ℝ) : ℂ) * (p - y)) :=
    Work.GATE.bTongue_of_re_eq hfμ₁ him₁
  have hi₂ : Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ (y + ((μ₂ : ℝ) : ℂ) * (p - y)) :=
    Work.GATE.iotaTongue_of_re_eq hfμ₂ him₂
  have he₁M : (y + ((μ₁ : ℝ) : ℂ) * (p - y)) ∉ Mandelbar := TD.escape_b _ hm₁ hb₁
  have he₂M : (y + ((μ₂ : ℝ) : ℂ) * (p - y)) ∉ Mandelbar := TD.escape_iota _ hm₂ hi₂
  -- (7) assemble
  have hμ₀ne : μ₀ ≠ 0 := ne_of_gt hμ₀.1
  have hY0 : y + ((μ₀ : ℝ) : ℂ) * (p - y) - y = ((μ₀ : ℝ) : ℂ) * (p - y) := by ring
  refine ⟨y, y + ((μ₀ : ℝ) : ℂ) * (p - y), ?_, y + ((μ₁ : ℝ) : ℂ) * (p - y), ?_,
    y + ((μ₂ : ℝ) : ℂ) * (p - y), ?_, he₁M, he₂M, hb₁, hi₂⟩
  · intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    change y + θ • (y + ((μ₀ : ℝ) : ℂ) * (p - y) - y) ∈ Nm ∩ Metric.ball c₀ r
    have hθ' : θ * μ₀ ∈ Set.Ico (0 : ℝ) 1 := by
      refine ⟨mul_nonneg hθ.1 (le_of_lt hμ₀.1), ?_⟩
      have h1 : θ * μ₀ ≤ μ₀ := by nlinarith [hθ.1, hθ.2, hμ₀.1]
      linarith [hμ₀.2]
    rw [hY0, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    exact ⟨hφ_mem_Nm (θ * μ₀) hθ', hφ_mem_ballr (θ * μ₀) ⟨hθ'.1, le_of_lt hθ'.2⟩⟩
  · rw [segment_eq_image']
    refine ⟨μ₁ / μ₀, ⟨div_nonneg hμ₁.1 (le_of_lt hμ₀.1), (div_le_one hμ₀.1).mpr hμ₁.2⟩, ?_⟩
    change y + (μ₁ / μ₀) • (y + ((μ₀ : ℝ) : ℂ) * (p - y) - y) = y + ((μ₁ : ℝ) : ℂ) * (p - y)
    rw [hY0, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      div_mul_cancel₀ (b := μ₀) μ₁ hμ₀ne]
  · rw [segment_eq_image']
    refine ⟨μ₂ / μ₀, ⟨div_nonneg hμ₂.1 (le_of_lt hμ₀.1), (div_le_one hμ₀.1).mpr hμ₂.2⟩, ?_⟩
    change y + (μ₂ / μ₀) • (y + ((μ₀ : ℝ) : ℂ) * (p - y) - y) = y + ((μ₂ : ℝ) : ℂ) * (p - y)
    rw [hY0, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      div_mul_cancel₀ (b := μ₀) μ₂ hμ₀ne]

end Work.GATE.Segment
