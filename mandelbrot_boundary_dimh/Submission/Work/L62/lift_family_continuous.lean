import Mathlib
import Submission.Work.L62.l62c_end
import Submission.Work.L62.avail_up
import Submission.Work.L62.l62c_basic
import Submission.Work.L62.epsDesc_spec
import Submission.Work.L62.l62c_head
import Submission.Work.L62.l62c_mid
import Submission.Work.Horn.basic

/-!
# L62 — continuity and holomorphy of the family of lifted sections

`Work.L62.lift_exists_unique` describes the family `σ_β` of *sections* of `ĥ = d.E - β` over the
upper horn `hd.Bu`: `σ_β w` is the unique `u ∈ hd.Bu` with `π u = H β (π w)` and `d.E u = w + β`.

Here we prove that such a family is automatically `β`-jointly continuous on the box
`{0 ≤ Re β ≤ 1, |Im β| ≤ b}` intersected with the available set, and that each `σ_β` is
holomorphic on `hd.Bu`.

The key point is that `σ_β` is *explicitly* determined by `H`:

  `σ_β w = w + β - epsDesc (π (σ_β w)) = w + β - epsDesc (H β (π w))`,

because `epsDesc` is the descent of `d.E - id` to the cylinder (`Work.L62.epsDesc_spec`:
`epsDesc (π u) = d.E u - u` for `u ∈ hd.Bu`).  Since `π (σ_β w) = H β (π w)` lies in the *open*
set `π '' hd.Bu` on which `epsDesc` has a holomorphic local model (`epsDesc_local_holo`), the
formula gives both joint continuity (`continuousOn_epsDesc_comp`) and holomorphy in `w`.
-/

namespace Work.L62

open MandelDim Set Filter Topology Metric
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Elementary facts about `π` -/

theorem continuousAt_piExp (w : ℂ) : ContinuousAt MandelDim.piExp w :=
  continuous_piExp.continuousAt

theorem differentiableAt_piExp (w : ℂ) : DifferentiableAt ℂ MandelDim.piExp w := by
  rw [show MandelDim.piExp = fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)
    from rfl]
  fun_prop

/-- `π w` lies in the cylinder domain `Ω = {0} ∪ π '' Bu` for `w ∈ hd.Bu`. -/
theorem piExp_mem_upOmega {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {w : ℂ}
    (hw : w ∈ hd.Bu) : MandelDim.piExp w ∈ upOmega d hd :=
  Or.inr ⟨w, hw, rfl⟩

/-! ## The local holomorphic model of `epsDesc` -/

/-- The local holomorphic section `z ↦ w₀ + log (z / ζ₀)/(2πi)` of `π` through `w₀` above `ζ₀`
(`ζ₀ ≠ 0`); it is holomorphic on the ball of radius `‖ζ₀‖` around `ζ₀`. -/
noncomputable def localSheet (ζ₀ w₀ : ℂ) (z : ℂ) : ℂ :=
  w₀ + Complex.log (z / ζ₀) / (2 * Real.pi * Complex.I)

theorem localSheet_apply (ζ₀ w₀ z : ℂ) :
    localSheet ζ₀ w₀ z = w₀ + Complex.log (z / ζ₀) / (2 * Real.pi * Complex.I) := rfl

/-- **The local holomorphic model of `epsDesc`.**  At every point `ζ₀` of the *open* set
`π '' hd.Bu` (the cylinder points whose principal lift lies in `hd.Bu`) the descended correction
`epsDesc = (d.E - id)` admits a holomorphic local model `G`, and `epsDesc` agrees with `G` on
`ball ζ₀ ε ∩ π '' hd.Bu`.  This is the useful (Sard-type) form: we never need `epsDesc` to be
holomorphic on all of `ℂ`, only along the maps that stay inside `π '' hd.Bu`. -/
theorem epsDesc_local_holo {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ MandelDim.piExp '' hd.Bu) :
    ∃ (G : ℂ → ℂ) (ε : ℝ), 0 < ε ∧ DifferentiableOn ℂ G (Metric.ball ζ₀ ε) ∧
      ∀ ζ ∈ Metric.ball ζ₀ ε, ζ ∈ MandelDim.piExp '' hd.Bu →
        Work.L62.epsDesc d hd ζ = G ζ := by
  have hζ₀ne : ζ₀ ≠ 0 := by
    obtain ⟨w, -, rfl⟩ := hζ₀
    exact Work.Horn.MandelDim.piExp_ne_zero w
  have hζ₀pos : 0 < ‖ζ₀‖ := norm_pos_iff.mpr hζ₀ne
  set w₀ : ℂ := Complex.log ζ₀ / (2 * Real.pi * Complex.I) with hw₀def
  have hw₀Bu : w₀ ∈ hd.Bu := log_div_mem_Bu d hd hζ₀
  have hπw₀ : MandelDim.piExp w₀ = ζ₀ := Work.Horn.MandelDim.piExp_log_div ζ₀ hζ₀ne
  obtain ⟨r, hr, hballr⟩ := Metric.mem_nhds_iff.mp (hd.Bu_open.mem_nhds hw₀Bu)
  -- the local sheet is continuous at `ζ₀`
  have hsheet_cont : ContinuousAt (localSheet ζ₀ w₀) ζ₀ := by
    have h1 : ContinuousAt (fun z : ℂ => z / ζ₀) ζ₀ := continuousAt_id.div_const ζ₀
    have h2 : (fun z : ℂ => z / ζ₀) ζ₀ ∈ Complex.slitPlane := by
      show ζ₀ / ζ₀ ∈ Complex.slitPlane
      rw [div_self hζ₀ne]; exact Complex.one_mem_slitPlane
    have h3 : ContinuousAt (fun z : ℂ => Complex.log (z / ζ₀)) ζ₀ := h1.clog h2
    have h4 : ContinuousAt (fun z : ℂ => Complex.log (z / ζ₀) / (2 * Real.pi * Complex.I)) ζ₀ :=
      h3.div_const _
    have h5 : ContinuousAt (fun z : ℂ => w₀ + Complex.log (z / ζ₀) / (2 * Real.pi * Complex.I))
        ζ₀ := h4.const_add w₀
    exact h5
  have hsheet_val : localSheet ζ₀ w₀ ζ₀ = w₀ := by
    rw [localSheet_apply, div_self hζ₀ne, Complex.log_one, zero_div, add_zero]
  have hpre : (localSheet ζ₀ w₀) ⁻¹' Metric.ball w₀ r ∈ 𝓝 ζ₀ :=
    hsheet_cont.preimage_mem_nhds (by rw [hsheet_val]; exact Metric.ball_mem_nhds _ hr)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hpre
  set ε : ℝ := min δ ‖ζ₀‖ with hεdef
  have hεpos : 0 < ε := lt_min hδ hζ₀pos
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεnorm : ε ≤ ‖ζ₀‖ := min_le_right _ _
  refine ⟨fun z => d.E (localSheet ζ₀ w₀ z) - localSheet ζ₀ w₀ z, ε, hεpos, ?_, ?_⟩
  · -- `z ↦ d.E (sheet z) - sheet z` is holomorphic on the ball
    intro z hz
    have hzδ : z ∈ Metric.ball ζ₀ δ := Metric.ball_subset_ball hεδ hz
    have hzBu : localSheet ζ₀ w₀ z ∈ hd.Bu := hballr (hδball hzδ)
    have hslit : z / ζ₀ ∈ Complex.slitPlane := by
      have hzlt : ‖z - ζ₀‖ < ‖ζ₀‖ :=
        lt_of_lt_of_le (by simpa [dist_eq_norm] using Metric.mem_ball.mp hz) hεnorm
      have h1 : ‖z / ζ₀ - 1‖ < 1 := by
        rw [show z / ζ₀ - 1 = (z - ζ₀) / ζ₀ by field_simp]
        rw [norm_div, div_lt_one hζ₀pos]
        simpa using hzlt
      have h3 : |(z / ζ₀ - 1).re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm _) h1
      have h4 : -1 < (z / ζ₀ - 1).re := (abs_lt.mp h3).1
      rw [Complex.sub_re, Complex.one_re] at h4
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
    have hsheet_diff : DifferentiableAt ℂ (localSheet ζ₀ w₀) z := by
      have h1 : DifferentiableAt ℂ (fun t : ℂ => t / ζ₀) z := differentiableAt_id.div_const ζ₀
      have h3 : DifferentiableAt ℂ (fun t : ℂ => Complex.log (t / ζ₀)) z := h1.clog hslit
      have h4 : DifferentiableAt ℂ
          (fun t : ℂ => Complex.log (t / ζ₀) / (2 * Real.pi * Complex.I)) z := h3.div_const _
      have h5 : DifferentiableAt ℂ
          (fun t : ℂ => w₀ + Complex.log (t / ζ₀) / (2 * Real.pi * Complex.I)) z := h4.const_add w₀
      exact h5
    have hE_diff : DifferentiableAt ℂ d.E (localSheet ζ₀ w₀ z) :=
      (differentiableOn_E_Bu d hd).differentiableAt (hd.Bu_open.mem_nhds hzBu)
    exact ((hE_diff.comp z hsheet_diff).sub hsheet_diff).differentiableWithinAt
  · -- the agreement on `ball ζ₀ ε ∩ π '' Bu`
    intro ζ hζ hζU
    have hζne : ζ ≠ 0 := by
      obtain ⟨w, -, rfl⟩ := hζU
      exact Work.Horn.MandelDim.piExp_ne_zero w
    have hzδ : ζ ∈ Metric.ball ζ₀ δ := Metric.ball_subset_ball hεδ hζ
    have hsheetBu : localSheet ζ₀ w₀ ζ ∈ hd.Bu := hballr (hδball hzδ)
    have hprinBu : Complex.log ζ / (2 * Real.pi * Complex.I) ∈ hd.Bu := log_div_mem_Bu d hd hζU
    have hsheet_pi : MandelDim.piExp (localSheet ζ₀ w₀ ζ) = ζ := by
      rw [localSheet_apply, piExp_add', hπw₀,
        Work.Horn.MandelDim.piExp_log_div (ζ / ζ₀) (div_ne_zero hζne hζ₀ne)]
      field_simp
    have hprin_pi : MandelDim.piExp (Complex.log ζ / (2 * Real.pi * Complex.I)) = ζ :=
      Work.Horn.MandelDim.piExp_log_div ζ hζne
    have hind := epsDesc_lift_independent d hd hprinBu hsheetBu (hprin_pi.trans hsheet_pi.symm)
    rw [epsDesc, ite_eq_right hζne]
    exact hind

/-! ## `epsDesc` composed with a holomorphic family is holomorphic -/

/-- **Holomorphy of `w ↦ epsDesc (H (π w))`.**  If `H` is holomorphic on `Ω = {0} ∪ π '' Bu` and
`H (π w) ∈ π '' hd.Bu` for `w ∈ hd.Bu`, then `w ↦ epsDesc (H (π w))` is holomorphic on `hd.Bu`.

Reason: `H (π w)` stays in the open set `π '' hd.Bu`, on which `epsDesc` agrees locally with the
holomorphic model `G` of `epsDesc_local_holo`; the composition with `G` is holomorphic. -/
theorem differentiableOn_epsDesc_comp {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {H : ℂ → ℂ} (Hdiff : DifferentiableOn ℂ H (upOmega d hd))
    (Hmem : ∀ w ∈ hd.Bu, H (MandelDim.piExp w) ∈ MandelDim.piExp '' hd.Bu) :
    DifferentiableOn ℂ (fun w => epsDesc d hd (H (MandelDim.piExp w))) hd.Bu := by
  intro w₀ hw₀
  have hζ₀ : H (MandelDim.piExp w₀) ∈ MandelDim.piExp '' hd.Bu := Hmem w₀ hw₀
  obtain ⟨G, ε, hε, hGdiff, hGagree⟩ := epsDesc_local_holo d hd hζ₀
  have hπw₀Ω : MandelDim.piExp w₀ ∈ upOmega d hd := piExp_mem_upOmega hw₀
  have hinner_cont : ContinuousAt (fun w => H (MandelDim.piExp w)) w₀ :=
    (Hdiff.continuousOn.continuousAt ((isOpen_upOmega d hd).mem_nhds hπw₀Ω)).comp
      (continuousAt_piExp w₀)
  have hinner_diff : DifferentiableAt ℂ (fun w => H (MandelDim.piExp w)) w₀ :=
    (Hdiff.differentiableAt ((isOpen_upOmega d hd).mem_nhds hπw₀Ω)).comp w₀
      (differentiableAt_piExp w₀)
  have hGat : DifferentiableAt ℂ G (H (MandelDim.piExp w₀)) :=
    hGdiff.differentiableAt (Metric.ball_mem_nhds _ hε)
  have hev : (fun w => epsDesc d hd (H (MandelDim.piExp w))) =ᶠ[𝓝 w₀]
      (fun w => G (H (MandelDim.piExp w))) := by
    filter_upwards [hinner_cont.eventually (Metric.ball_mem_nhds _ hε),
      Filter.eventually_of_mem (hd.Bu_open.mem_nhds hw₀) (fun w hw => Hmem w hw)]
      with w hwball hwU
    exact hGagree (H (MandelDim.piExp w)) hwball hwU
  exact ((hGat.comp w₀ hinner_diff).congr_of_eventuallyEq hev).differentiableWithinAt

/-! ## Joint continuity of `(β, w) ↦ epsDesc (H β (π w))` -/

/-- **Joint continuity of `(β, w) ↦ epsDesc (H β (π w))`.**  `epsDesc` is continuous on
`Ω = {0} ∪ π '' Bu` (`epsDesc_spec`), and `(β, w) ↦ H β (π w)` is jointly continuous there by
`Hcont`; `Hmem` supplies the membership in `Ω` needed to compose. -/
theorem continuousOn_epsDesc_comp {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {A : Set ℂ} {H : ℂ → ℂ → ℂ}
    (Hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (A ×ˢ Work.L62.upOmega d hd))
    (Hmem : ∀ β ∈ A, ∀ w ∈ hd.Bu, H β (MandelDim.piExp w) ∈ MandelDim.piExp '' hd.Bu) :
    ContinuousOn (fun p : ℂ × ℂ => Work.L62.epsDesc d hd (H p.1 (MandelDim.piExp p.2)))
      (A ×ˢ hd.Bu) := by
  have hinner_cont : ContinuousOn (fun p : ℂ × ℂ => (p.1, MandelDim.piExp p.2)) (A ×ˢ hd.Bu) :=
    (continuous_fst.prodMk (continuous_piExp.comp continuous_snd)).continuousOn
  have hmaps : MapsTo (fun p : ℂ × ℂ => (p.1, MandelDim.piExp p.2)) (A ×ˢ hd.Bu)
      (A ×ˢ upOmega d hd) :=
    fun p hp => ⟨hp.1, piExp_mem_upOmega hp.2⟩
  have hH : ContinuousOn (fun p : ℂ × ℂ => H p.1 (MandelDim.piExp p.2)) (A ×ˢ hd.Bu) :=
    Hcont.comp hinner_cont hmaps
  have heps : ContinuousOn (Work.L62.epsDesc d hd) (upOmega d hd) :=
    (epsDesc_spec d hd).1
  have hmaps2 : MapsTo (fun p : ℂ × ℂ => H p.1 (MandelDim.piExp p.2)) (A ×ˢ hd.Bu)
      (upOmega d hd) :=
    fun p hp => Or.inr (Hmem p.1 hp.1 p.2 hp.2)
  exact heps.comp hH hmaps2

/-! ## The main theorem -/

theorem lift_family_continuous {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b : ℝ} (hb : 0 < b) (H : ℂ → ℂ → ℂ)
    (Hdiff : ∀ β : ℂ, Work.L62.AvailableUp d hd β →
      DifferentiableOn ℂ (H β) (Work.L62.upOmega d hd))
    (Hsec : ∀ β : ℂ, Work.L62.AvailableUp d hd β → ∀ ζ ∈ Work.L62.upOmega d hd, ζ ≠ 0 →
      MandelDim.pushdown d.E (H β ζ) = MandelDim.piExp β * ζ)
    (Hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2)
      (({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
        {β : ℂ | Work.L62.AvailableUp d hd β}) ×ˢ Work.L62.upOmega d hd))
    (σ : ℂ → ℂ → ℂ)
    (hσ : ∀ β : ℂ, Work.L62.AvailableUp d hd β → ∀ w ∈ hd.Bu,
      σ β w ∈ hd.Bu ∧ d.E (σ β w) = w + β ∧ MandelDim.piExp (σ β w) = H β (MandelDim.piExp w))
    (huniq : ∀ β : ℂ, Work.L62.AvailableUp d hd β → ∀ w ∈ hd.Bu, ∀ u : ℂ,
      u ∈ hd.Bu → MandelDim.piExp u = H β (MandelDim.piExp w) → d.E u = w + β → u = σ β w) :
    (∀ β : ℂ, Work.L62.AvailableUp d hd β → DifferentiableOn ℂ (σ β) hd.Bu) ∧
    ContinuousOn (fun p : ℂ × ℂ => σ p.1 p.2)
      (({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
        {β : ℂ | Work.L62.AvailableUp d hd β}) ×ˢ hd.Bu) := by
  -- `σ_β w` is determined by `H`: `σ_β w = w + β - epsDesc (H β (π w))`
  have hform : ∀ β : ℂ, Work.L62.AvailableUp d hd β → ∀ w ∈ hd.Bu,
      σ β w = w + β - Work.L62.epsDesc d hd (H β (MandelDim.piExp w)) := by
    intro β hβ w hw
    obtain ⟨hmem, hE, hpi⟩ := hσ β hβ w hw
    have hdesc := epsDesc_piExp d hd hmem
    rw [hpi, hE] at hdesc
    linear_combination hdesc
  constructor
  · -- differentiability of each `σ_β` on `hd.Bu`
    intro β hβ
    have hHmem : ∀ w ∈ hd.Bu, H β (MandelDim.piExp w) ∈ MandelDim.piExp '' hd.Bu :=
      fun w hw => ⟨σ β w, (hσ β hβ w hw).1, (hσ β hβ w hw).2.2⟩
    have hcomp := differentiableOn_epsDesc_comp d hd (Hdiff β hβ) hHmem
    intro w₀ hw₀
    have h1 : DifferentiableAt ℂ
        (fun w => w + β - Work.L62.epsDesc d hd (H β (MandelDim.piExp w))) w₀ :=
      (differentiableAt_id.add_const β).sub (hcomp.differentiableAt (hd.Bu_open.mem_nhds hw₀))
    have hev : (fun w => σ β w) =ᶠ[𝓝 w₀]
        (fun w => w + β - Work.L62.epsDesc d hd (H β (MandelDim.piExp w))) :=
      Filter.eventually_of_mem (hd.Bu_open.mem_nhds hw₀) (fun w hw => hform β hβ w hw)
    exact (h1.congr_of_eventuallyEq hev).differentiableWithinAt
  · -- joint continuity
    set A : Set ℂ := {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
      {β : ℂ | Work.L62.AvailableUp d hd β} with hAdef
    have hHmem : ∀ β ∈ A, ∀ w ∈ hd.Bu,
        H β (MandelDim.piExp w) ∈ MandelDim.piExp '' hd.Bu :=
      fun β hβ w hw => ⟨σ β w, (hσ β hβ.2 w hw).1, (hσ β hβ.2 w hw).2.2⟩
    have hcont := continuousOn_epsDesc_comp d hd (A := A) Hcont hHmem
    have hsum : ContinuousOn (fun p : ℂ × ℂ => p.2 + p.1) (A ×ˢ hd.Bu) :=
      (continuous_snd.add continuous_fst).continuousOn
    have hmain : ContinuousOn
        (fun p : ℂ × ℂ => p.2 + p.1 - Work.L62.epsDesc d hd (H p.1 (MandelDim.piExp p.2)))
        (A ×ˢ hd.Bu) := hsum.sub hcont
    refine hmain.congr (fun p hp => ?_)
    exact hform p.1 hp.1.2 p.2 hp.2

end

end Work.L62
