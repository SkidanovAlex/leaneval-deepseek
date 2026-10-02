import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.analytic_local_crossing
import Submission.Work.ELRig.chart_local_inverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
variable {L : Work.ELRig.RayCylLift d fl}

/-- **The local angle identity around a far-left point of the lift, without the pair input.**

This is the first (pair-free) part of `Work.ELRig.exists_local_angle_at_lift`: near `p = γ₁ s`
there is an open set `D` inside the far-left half plane on which `Ψ` misses the filled Julia set
and the external angle equals `α₁` exactly on the lift `γ₁`. -/
theorem exists_local_angle_ray (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s : ℝ} (hre : (L.γ₁ s).re < -L.R) :
    ∃ D : Set ℂ, IsOpen D ∧ L.γ₁ s ∈ D ∧ D ⊆ {w : ℂ | w.re < -L.R} ∧
      (∀ w ∈ D, fl.Ψ w ∉ Work.EL.K c) ∧
      (∀ w ∈ D, Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) = Work.EL.alpha1
          ↔ w ∈ Set.range L.γ₁) := by
  have hzK : fl.Ψ (L.γ₁ s) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s]
    exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s)
  obtain ⟨ε, hεpos, hεball⟩ :=
    Metric.isOpen_iff.mp (Work.ParamRays.isClosed_filledJulia c).isOpen_compl
      (fl.Ψ (L.γ₁ s)) hzK
  have hε : ∀ z : ℂ, dist z (fl.Ψ (L.γ₁ s)) < ε → z ∉ Work.EL.K c :=
    fun z hz => hεball (Metric.mem_ball.mpr hz)
  have hcont : Continuous fl.Ψ := fl.Ψ_diff.continuous
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp hcont.continuousAt ε hεpos
  refine ⟨Metric.ball (L.γ₁ s) δ ∩ {w : ℂ | w.re < -L.R},
    (Metric.isOpen_ball).inter (isOpen_lt Complex.continuous_re continuous_const),
    ⟨Metric.mem_ball_self hδpos, hre⟩, fun w hw => hw.2, ?_, ?_⟩
  · intro w hw
    exact hε (fl.Ψ w) (hδ (Metric.mem_ball.mp hw.1))
  · intro w hw
    have hwK : fl.Ψ w ∉ Work.EL.K c := hε (fl.Ψ w) (hδ (Metric.mem_ball.mp hw.1))
    constructor
    · intro h
      have hmem : fl.Ψ w ∈ Work.Top.NakaneData.paramRay d.hN
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)) :=
        Work.Top.mem_paramRay_extAngle d.hN hwK
      rw [h] at hmem
      exact L.tailId₁ w hw.2 hmem
    · rintro ⟨s', rfl⟩
      exact Work.Top.extAngle_of_mem_paramRay d.hN alpha1_mem_Ico.1 alpha1_mem_Ico.2
        (L.img₁ s')

/-- **A neighbourhood of `p = γ₁ s₀` on which the zero set of the imaginary part of the chart is
exactly the lift.** -/
theorem exists_chart_zero_neighbourhood {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ ε > 0, ∀ w : ℂ, ‖w - L.γ₁ s₀‖ < ε →
      ((Work.ELRig.sideFlipChart c d fl L s₀ w).im = 0 ↔ w ∈ Set.range L.γ₁) := by
  obtain ⟨D, hDopen, hpD, hDsub, hDK, _⟩ := exists_local_angle_ray d fl L hre
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.isOpen_iff.mp hDopen (L.γ₁ s₀) hpD
  have hcont : ContinuousAt (Work.ELRig.sideFlipChart c d fl L s₀) (L.γ₁ s₀) :=
    sideFlipChart_continuousAt
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.continuousAt_iff.mp hcont (1/2) (by norm_num)
  refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, fun w hw => ?_⟩
  have hw' : dist w (L.γ₁ s₀) < min ε₁ ε₂ := by rw [dist_eq_norm]; exact hw
  have hwD : w ∈ D := hε₁ (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hw' (min_le_left _ _))
  have hwK : fl.Ψ w ∉ Work.EL.K c := hDK w hwD
  have hre0 : (1 : ℝ) / 2 < (Work.ELRig.sideFlipChart c d fl L s₀ w).re := by
    have hε₂w := hε₂ (lt_of_lt_of_le hw' (min_le_right _ _))
    rw [sideFlipChart_at_p, dist_eq_norm] at hε₂w
    have h2 : |(Work.ELRig.sideFlipChart c d fl L s₀ w).re - 1| ≤
        ‖Work.ELRig.sideFlipChart c d fl L s₀ w - 1‖ := by
      simpa using Complex.abs_re_le_norm (Work.ELRig.sideFlipChart c d fl L s₀ w - 1)
    linarith [(abs_lt.mp (lt_of_le_of_lt h2 hε₂w)).1]
  constructor
  · intro him
    have hreal : Work.ELRig.sideFlipChart c d fl L s₀ w
        = (((Work.ELRig.sideFlipChart c d fl L s₀ w).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simpa using him)
    have hne := rayPoint_alpha1_ne_zero (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀)
    have h1 : Work.EL.dynPhi c d.φ (fl.Ψ w)
        = Work.ELRig.sideFlipChart c d fl L s₀ w
          * Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀) := by
      rw [sideFlipChart_apply, div_mul_cancel₀ _ hne]
    have hray : Work.EL.dynPhi c d.φ (fl.Ψ w)
        = Work.Top.NakaneData.rayPoint Work.EL.alpha1
          ((Work.ELRig.sideFlipChart c d fl L s₀ w).re * L.τ s₀) := by
      rw [h1, hreal]
      simp only [Work.Top.NakaneData.rayPoint, Complex.ofReal_mul, Complex.ofReal_re]
      ring
    refine L.tailId₁ w (hDsub hwD) ?_
    rw [Work.Top.NakaneData.mem_paramRay_iff]
    refine ⟨hwK, (Work.ELRig.sideFlipChart c d fl L s₀ w).re * L.τ s₀, ?_, hray⟩
    have hnorm : ‖Work.Top.NakaneData.rayPoint Work.EL.alpha1
        ((Work.ELRig.sideFlipChart c d fl L s₀ w).re * L.τ s₀)‖
        = (Work.ELRig.sideFlipChart c d fl L s₀ w).re * L.τ s₀ := by
      rw [Work.Top.NakaneData.norm_rayPoint, abs_of_nonneg
        (mul_nonneg (le_of_lt (by linarith)) (le_of_lt (lt_trans zero_lt_one (L.hτ1 s₀))))]
    have hg : 1 < ‖Work.EL.dynPhi c d.φ (fl.Ψ w)‖ := d.hN.Phi_mem_exteriorDisc hwK
    rw [hray, hnorm] at hg
    exact hg
  · rintro ⟨s, rfl⟩
    rw [sideFlipChart_eq_ofReal]
    exact Complex.ofReal_im _

/-- The first lift grows at least linearly: `|s| ≤ ‖γ₁ s‖ + M` for some `M`. -/
theorem rayCylLift_norm_growth (L : Work.ELRig.RayCylLift d fl) :
    ∃ M : ℝ, ∀ s : ℝ, |s| ≤ ‖L.γ₁ s‖ + M := by
  have hper : Function.Periodic (fun s : ℝ => L.γ₁ s - (s : ℂ)) 1 := by
    intro s
    show L.γ₁ (s + 1) - (((s + 1 : ℝ)) : ℂ) = L.γ₁ s - (s : ℂ)
    rw [L.per₁ s]
    push_cast
    ring
  have hcont : Continuous (fun s : ℝ => L.γ₁ s - (s : ℂ)) :=
    L.cont₁.sub (Complex.continuous_ofReal)
  obtain ⟨M, hM⟩ := (hper.isBounded_of_continuous one_ne_zero hcont).exists_norm_le
  refine ⟨M, fun s => ?_⟩
  have h2 : (s : ℂ) = L.γ₁ s - (L.γ₁ s - (s : ℂ)) := by ring
  calc |s| = ‖(s : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖L.γ₁ s - (L.γ₁ s - (s : ℂ))‖ := congrArg norm h2
    _ ≤ ‖L.γ₁ s‖ + ‖L.γ₁ s - (s : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖L.γ₁ s‖ + M := by linarith [hM (L.γ₁ s - (s : ℂ)) ⟨s, rfl⟩]

/-- The first lift is injective (the level map `τ` is strictly increasing). -/
theorem rayCylLift_injective (L : Work.ELRig.RayCylLift d fl) : Function.Injective L.γ₁ := by
  intro s s' h
  have h1 : Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ s)
      = Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ s') := by
    rw [← L.hΨ₁ s, ← L.hΨ₁ s', h]
  exact L.hτmono.injective (Work.ELRig.rayPt_level_inj d.hN (L.hτ1 s) (L.hτ1 s') h1)

/-- **No crossing radius**: for a continuous injective curve with at least linear growth there is
`ε > 0` such that every point of the curve at distance `< ε` from the centre lies in the given
window around the parameter of the centre. -/
theorem exists_no_crossing_radius {p : ℂ} {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hinj : Function.Injective γ) (hbound : ∃ M, ∀ s, |s| ≤ ‖γ s‖ + M)
    {s₀ : ℝ} (hs₀ : γ s₀ = p) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ ε > 0, ∀ s : ℝ, ‖γ s - p‖ < ε → s ∈ Set.Ioo (s₀ - δ') (s₀ + δ') := by
  set ρ : ℝ → ℝ := fun s => ‖γ s - p‖ with hρ
  have hρcont : Continuous ρ := (hcont.sub continuous_const).norm
  obtain ⟨M, hM⟩ := hbound
  set C : ℝ := M + ‖p‖ + 1 with hC
  have hb : ∀ s, ρ s < 1 → |s| ≤ C := by
    intro s hs
    have h1 : |s| ≤ ‖γ s‖ + M := hM s
    have h2 : ‖γ s‖ ≤ ‖γ s - p‖ + ‖p‖ := by
      calc ‖γ s‖ = ‖(γ s - p) + p‖ := by ring_nf
        _ ≤ ‖γ s - p‖ + ‖p‖ := norm_add_le _ _
    simp only [hρ] at hs
    rw [hC]; linarith
  have hρpos : ∀ s, s ∉ Set.Ioo (s₀ - δ') (s₀ + δ') → 0 < ρ s := by
    intro s hs
    refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm fun h0 => ?_)
    have h1 : γ s = p := by
      simp only [hρ] at h0
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    have h2 : s = s₀ := hinj (h1.trans hs₀.symm)
    rw [h2] at hs
    exact hs ⟨by linarith, by linarith⟩
  set T : Set ℝ := (Set.Ioo (s₀ - δ') (s₀ + δ'))ᶜ ∩ Set.Icc (-C) C with hT
  have hSclosed : IsClosed (Set.Ioo (s₀ - δ') (s₀ + δ'))ᶜ := isOpen_Ioo.isClosed_compl
  have hTcompact : IsCompact T := isCompact_Icc.inter_left hSclosed
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨1, one_pos, fun s hs => ?_⟩
    by_contra hcon
    have hmem : s ∈ T := by
      rw [hT]
      exact ⟨hcon, abs_le.mp (hb s hs)⟩
    rw [hTe] at hmem
    exact hmem
  · obtain ⟨x, hxT, hxmin⟩ := hTcompact.exists_isMinOn hTne hρcont.continuousOn
    refine ⟨min 1 (ρ x), lt_min one_pos (hρpos x hxT.1), fun s hs => ?_⟩
    by_contra hcon
    have hlt : ρ s < 1 := lt_of_lt_of_le hs (min_le_left _ _)
    have hmem : s ∈ T := by
      rw [hT]
      exact ⟨hcon, abs_le.mp (hb s hlt)⟩
    have hxle : ρ x ≤ ρ s := hxmin hmem
    have : min 1 (ρ x) ≤ ρ s := le_trans (min_le_right _ _) hxle
    linarith

/-- The level map `τ` of a `RayCylLift` is continuous. -/
theorem rayCylLift_tau_continuous (L : Work.ELRig.RayCylLift d fl) : Continuous L.τ := by
  have hcont : Continuous fun s : ℝ => Work.EL.dynPhi c d.φ (fl.Ψ (L.γ₁ s)) :=
    (continuousOn_dynPhi (c := c) (d := d)).comp_continuous
      (fl.Ψ_diff.continuous.comp L.cont₁)
      (fun s => by rw [L.hΨ₁ s]; exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s))
  have hτ : L.τ = fun s : ℝ => ‖Work.EL.dynPhi c d.φ (fl.Ψ (L.γ₁ s))‖ := by
    funext s
    rw [L.hΨ₁ s, Work.Top.NakaneData.Phi_rayPt d.hN (L.hτ1 s),
      Work.Top.NakaneData.norm_rayPoint, abs_of_pos (lt_trans zero_lt_one (L.hτ1 s))]
  rw [hτ]; exact hcont.norm

/-- **The local first-exit crossings.**  There are `δ' > 0` and `r_loc > 0` such that for every
radius `r ∈ (0, r_loc)` the equation `‖γ₁ s - γ₁ s₀‖ = r` has exactly one solution on each side of
`s₀` inside the window `(s₀ - δ', s₀ + δ')`. -/
theorem local_exit_crossings {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ δ' > 0, ∃ r_loc > 0, ∀ r ∈ Set.Ioo (0:ℝ) r_loc,
      (∃! s : ℝ, s ∈ Set.Ioo (s₀ - δ') s₀ ∧ ‖L.γ₁ s - L.γ₁ s₀‖ = r) ∧
      (∃! s : ℝ, s ∈ Set.Ioo s₀ (s₀ + δ') ∧ ‖L.γ₁ s - L.γ₁ s₀‖ = r) := by
  obtain ⟨δ₁, hδ₁pos, δ₂, hδ₂pos, k, hk_an, _hk_right, hk_left, hk_deriv⟩ :=
    chart_local_inverse d fl L hre
  have hk1 : k 1 = L.γ₁ s₀ := by
    rw [← sideFlipChart_at_p (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀)]
    exact hk_left (L.γ₁ s₀) (Metric.mem_ball_self hδ₁pos)
  have h1mem : (1:ℂ) ∈ Metric.ball 1 δ₂ := Metric.mem_ball_self hδ₂pos
  set G : ℂ → ℂ := fun z => k (1 + z) - L.γ₁ s₀ with hG
  have hGan : AnalyticAt ℂ G 0 := by
    rw [hG]
    have h1 : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0 := analyticAt_const.add analyticAt_id
    have h2 : AnalyticAt ℂ (fun z : ℂ => k (1 + z)) 0 :=
      AnalyticAt.comp (by simpa using (hk_an 1 h1mem)) h1
    exact h2.sub analyticAt_const
  have hG0 : G 0 = 0 := by rw [hG]; simp [hk1]
  have hGd : deriv G 0 ≠ 0 := by
    rw [hG]
    have h2 : HasDerivAt k (deriv k 1) 1 := (hk_an 1 h1mem).hasStrictDerivAt.hasDerivAt
    have h1 : HasDerivAt (fun z : ℂ => 1 + z) (1:ℂ) 0 :=
      HasDerivAt.const_add (1:ℂ) (hasDerivAt_id (0:ℂ))
    have h3 : HasDerivAt (fun z : ℂ => k (1 + z)) (deriv k 1 * 1) 0 :=
      HasDerivAt.comp (0:ℂ) (by simpa using h2) h1
    have h4 : HasDerivAt (fun z : ℂ => k (1 + z) - L.γ₁ s₀) (deriv k 1 * 1) 0 :=
      HasDerivAt.sub_const _ h3
    rw [h4.deriv]; simpa using hk_deriv
  obtain ⟨δG, hδGpos, cG, hcGpos, μ₀G, hμ₀Gpos, hGbd, hGcross⟩ :=
    analytic_local_crossing hGan hG0 hGd
  set u : ℝ → ℝ := fun s => L.τ s / L.τ s₀ - 1 with hu
  have hτpos : 0 < L.τ s₀ := lt_trans zero_lt_one (L.hτ1 s₀)
  have hu_cont : Continuous u := ((rayCylLift_tau_continuous L).div_const _).sub continuous_const
  have hu_strict : StrictMono u := by
    intro a b hab
    have h : L.τ a < L.τ b := L.hτmono hab
    simp only [hu]
    exact sub_lt_sub_right (div_lt_div_of_pos_right h hτpos) 1
  have hus₀ : u s₀ = 0 := by simp only [hu]; rw [div_self (ne_of_gt hτpos)]; ring
  have hkey : ∀ s : ℝ, ‖L.γ₁ s - L.γ₁ s₀‖ < δ₁ → L.γ₁ s = k (1 + (u s : ℂ)) := by
    intro s hs
    have hmem : L.γ₁ s ∈ Metric.ball (L.γ₁ s₀) δ₁ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hs
    have h1 := hk_left (L.γ₁ s) hmem
    have h2 : Work.ELRig.sideFlipChart c d fl L s₀ (L.γ₁ s) = 1 + (u s : ℂ) := by
      rw [sideFlipChart_eq_ofReal]
      simp only [hu, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
      ring
    rw [h2] at h1; exact h1.symm
  have hc1 : ContinuousAt L.γ₁ s₀ := L.cont₁.continuousAt
  obtain ⟨δ₁', hδ₁'pos, hδ₁'⟩ := Metric.continuousAt_iff.mp hc1 δ₁ hδ₁pos
  have hc2 : ContinuousAt u s₀ := hu_cont.continuousAt
  obtain ⟨δ₂', hδ₂'pos, hδ₂'⟩ := Metric.continuousAt_iff.mp hc2 δG hδGpos
  set δ' : ℝ := min δ₁' δ₂' with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ₁'pos hδ₂'pos
  have hb1 : ∀ s : ℝ, |s - s₀| < δ' → ‖L.γ₁ s - L.γ₁ s₀‖ < δ₁ := by
    intro s hs
    have h : dist s s₀ < δ₁' := lt_of_lt_of_le (by rwa [Real.dist_eq]) (min_le_left _ _)
    simpa [dist_eq_norm] using hδ₁' h
  have hb2 : ∀ s : ℝ, |s - s₀| < δ' → |u s| < δG := by
    intro s hs
    have h : dist s s₀ < δ₂' := lt_of_lt_of_le (by rwa [Real.dist_eq]) (min_le_right _ _)
    have := hδ₂' h
    rw [Real.dist_eq, hus₀, sub_zero] at this
    exact this
  have huL : u (s₀ - δ') < 0 := by rw [← hus₀]; exact hu_strict (by linarith)
  have huR : 0 < u (s₀ + δ') := by rw [← hus₀]; exact hu_strict (by linarith)
  refine ⟨δ', hδ'pos, min μ₀G (min (cG * (-(u (s₀ - δ')))) (cG * u (s₀ + δ'))),
    lt_min hμ₀Gpos (lt_min (mul_pos hcGpos (by linarith)) (mul_pos hcGpos huR)), fun r hr => ?_⟩
  have hrμ : r < μ₀G := lt_of_lt_of_le hr.2 (min_le_left _ _)
  have hrη : r < min (cG * (-(u (s₀ - δ')))) (cG * u (s₀ + δ')) :=
    lt_of_lt_of_le hr.2 (min_le_right _ _)
  have hrηL : r < cG * (-(u (s₀ - δ'))) := lt_of_lt_of_le hrη (min_le_left _ _)
  have hrηR : r < cG * (u (s₀ + δ')) := lt_of_lt_of_le hrη (min_le_right _ _)
  have hrr : 0 < r := hr.1
  obtain ⟨⟨tR, ⟨htRmem, htReq⟩, htRuniq⟩, ⟨tL, ⟨htLmem, htLeq⟩, htLuniq⟩⟩ :=
    hGcross r ⟨hrr, hrμ⟩
  have htLabs : |tL| < δG := abs_lt.mpr ⟨htLmem.1, by linarith [htLmem.2, hδGpos]⟩
  have htRabs : |tR| < δG := abs_lt.mpr ⟨by linarith [htRmem.1, hδGpos], htRmem.2⟩
  have htL_in : tL ∈ Set.Ioo (u (s₀ - δ')) 0 := by
    refine ⟨?_, htLmem.2⟩
    have h1 : r / cG < -(u (s₀ - δ')) := by rw [div_lt_iff₀ hcGpos]; linarith
    have h2 : cG * |tL| ≤ r := by rw [← htLeq]; exact hGbd tL htLabs (ne_of_lt htLmem.2)
    have h3 : |tL| ≤ r / cG := by rw [le_div_iff₀ hcGpos]; linarith
    linarith [neg_abs_le tL]
  have htR_in : tR ∈ Set.Ioo 0 (u (s₀ + δ')) := by
    refine ⟨htRmem.1, ?_⟩
    have h1 : r / cG < u (s₀ + δ') := by rw [div_lt_iff₀ hcGpos]; linarith
    have h2 : cG * |tR| ≤ r := by rw [← htReq]; exact hGbd tR htRabs (ne_of_gt htRmem.1)
    have h3 : |tR| ≤ r / cG := by rw [le_div_iff₀ hcGpos]; linarith
    linarith [le_abs_self tR]
  have himgL : u '' Set.Ioo (s₀ - δ') s₀ = Set.Ioo (u (s₀ - δ')) (u s₀) :=
    hu_cont.image_Ioo_of_strictMono hu_strict
  have himgR : u '' Set.Ioo s₀ (s₀ + δ') = Set.Ioo (u s₀) (u (s₀ + δ')) :=
    hu_cont.image_Ioo_of_strictMono hu_strict
  constructor
  · obtain ⟨sL, hsLmem, hsLu⟩ : ∃ sL ∈ Set.Ioo (s₀ - δ') s₀, u sL = tL := by
      have h : tL ∈ u '' Set.Ioo (s₀ - δ') s₀ := by rw [himgL, hus₀]; exact htL_in
      simpa using h
    have hsLlt : |sL - s₀| < δ' := by
      rw [abs_lt]; exact ⟨by linarith [hsLmem.1], by linarith [hsLmem.2]⟩
    have hsLeq : ‖L.γ₁ sL - L.γ₁ s₀‖ = r := by
      have hke := hkey sL (hb1 sL hsLlt)
      have hGt : k (1 + (tL : ℂ)) - L.γ₁ s₀ = G tL := by rw [hG]
      rw [hke, hsLu, hGt]; exact htLeq
    refine ⟨sL, ⟨hsLmem, hsLeq⟩, fun y hy => ?_⟩
    have hyllt : |y - s₀| < δ' := by
      rw [abs_lt]; exact ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
    have hykey := hkey y (hb1 y hyllt)
    have hyu : u y ∈ Set.Ioo (-δG) 0 := by
      refine ⟨?_, lt_of_lt_of_le (hu_strict hy.1.2) (le_of_eq hus₀)⟩
      have := hb2 y hyllt; linarith [neg_abs_le (u y)]
    have hyeq : ‖G ((u y : ℝ) : ℂ)‖ = r := by
      have hthis : G ((u y : ℝ) : ℂ) = L.γ₁ y - L.γ₁ s₀ := by rw [hG, hykey]
      rw [hthis]; exact hy.2
    have hyut : (u y : ℝ) = tL := htLuniq (u y) ⟨hyu, hyeq⟩
    exact hu_strict.injective (by rw [hyut, hsLu])
  · obtain ⟨sR, hsRmem, hsRu⟩ : ∃ sR ∈ Set.Ioo s₀ (s₀ + δ'), u sR = tR := by
      have h : tR ∈ u '' Set.Ioo s₀ (s₀ + δ') := by rw [himgR, hus₀]; exact htR_in
      simpa using h
    have hsRlt : |sR - s₀| < δ' := by
      rw [abs_lt]; exact ⟨by linarith [hsRmem.1], by linarith [hsRmem.2]⟩
    have hsReq : ‖L.γ₁ sR - L.γ₁ s₀‖ = r := by
      have hke := hkey sR (hb1 sR hsRlt)
      have hGt : k (1 + (tR : ℂ)) - L.γ₁ s₀ = G tR := by rw [hG]
      rw [hke, hsRu, hGt]; exact htReq
    refine ⟨sR, ⟨hsRmem, hsReq⟩, fun y hy => ?_⟩
    have hyllt : |y - s₀| < δ' := by
      rw [abs_lt]; exact ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
    have hykey := hkey y (hb1 y hyllt)
    have hyu : u y ∈ Set.Ioo (0:ℝ) δG := by
      refine ⟨?_, ?_⟩
      · rw [← hus₀]; exact hu_strict hy.1.1
      · have := hb2 y hyllt; linarith [le_abs_self (u y)]
    have hyeq : ‖G ((u y : ℝ) : ℂ)‖ = r := by
      have hthis : G ((u y : ℝ) : ℂ) = L.γ₁ y - L.γ₁ s₀ := by rw [hG, hykey]
      rw [hthis]; exact hy.2
    have hyut : (u y : ℝ) = tR := htRuniq (u y) ⟨hyu, hyeq⟩
    exact hu_strict.injective (by rw [hyut, hsRu])

/-- For the straightening chart `sideFlipChart` of the lift `γ₁` at the far-left point
`p = γ₁ s₀`, there is a radius `r > 0` such that the circle of radius `r` around `p` meets the
zero set of the chart's imaginary part exactly in the two "first exit" points `γ₁ sL`, `γ₁ sR` of
the lift from that circle, the arc between them lying inside the circle and the point `p` being
strictly between `sL` and `s₀ < sR`. -/
theorem chart_sphere_crossings {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ r > 0, ∃ sL sR : ℝ, sL < s₀ ∧ s₀ < sR ∧
      (∀ s ∈ Set.Ioo sL sR, ‖L.γ₁ s - L.γ₁ s₀‖ < r) ∧
      ‖L.γ₁ sL - L.γ₁ s₀‖ = r ∧ ‖L.γ₁ sR - L.γ₁ s₀‖ = r ∧
      (∀ w : ℂ, ‖w - L.γ₁ s₀‖ = r →
        ((Work.ELRig.sideFlipChart c d fl L s₀ w).im = 0 ↔ w = L.γ₁ sL ∨ w = L.γ₁ sR)) := by
  obtain ⟨εU, hεUpos, hU⟩ := exists_chart_zero_neighbourhood (c := c) (d := d) (fl := fl) (L := L) hre
  obtain ⟨δ', hδ'pos, r_loc, hr_loc_pos, hloc⟩ :=
    local_exit_crossings (c := c) (d := d) (fl := fl) (L := L) hre
  obtain ⟨εno, hεnopos, hno⟩ := exists_no_crossing_radius L.cont₁
    (rayCylLift_injective L) (rayCylLift_norm_growth L) (s₀ := s₀) rfl hδ'pos
  set M : ℝ := min (min εU εno) r_loc with hM
  have hMpos : 0 < M := by rw [hM]; exact lt_min (lt_min hεUpos hεnopos) hr_loc_pos
  set r : ℝ := M / 2 with hrr
  have hrpos : 0 < r := by rw [hrr]; linarith
  have hrU : r < εU := by
    rw [hrr]; have : M ≤ εU := by rw [hM]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hrno : r < εno := by
    rw [hrr]; have : M ≤ εno := by rw [hM]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hrloc : r < r_loc := by
    rw [hrr]; have : M ≤ r_loc := by rw [hM]; exact min_le_right _ _
    linarith
  obtain ⟨sL, ⟨hsLmem, hsLeq⟩, hsLuniq⟩ := (hloc r ⟨hrpos, hrloc⟩).1
  obtain ⟨sR, ⟨hsRmem, hsReq⟩, hsRuniq⟩ := (hloc r ⟨hrpos, hrloc⟩).2
  have hsolve : ∀ s : ℝ, ‖L.γ₁ s - L.γ₁ s₀‖ = r → s = sL ∨ s = sR := by
    intro s hs
    have hmem : s ∈ Set.Ioo (s₀ - δ') (s₀ + δ') := hno s (by rw [hs]; exact hrno)
    rcases lt_trichotomy s s₀ with h | h | h
    · exact Or.inl (hsLuniq s ⟨⟨hmem.1, h⟩, hs⟩)
    · exfalso; rw [h] at hs; simp at hs; linarith
    · exact Or.inr (hsRuniq s ⟨⟨h, hmem.2⟩, hs⟩)
  have hinside : ∀ s ∈ Set.Ioo sL sR, ‖L.γ₁ s - L.γ₁ s₀‖ < r := by
    intro s hs
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hsne₀ : s ≠ s₀ := by intro h; rw [h] at hlt; simp at hlt; linarith
      rcases lt_or_gt_of_ne hsne₀ with hslt | hsgt
      · have hcont : ContinuousOn (fun t => ‖L.γ₁ t - L.γ₁ s₀‖) (Set.Icc s s₀) :=
          ((L.cont₁.sub continuous_const).norm).continuousOn
        have hrmem : r ∈ Set.Icc (‖L.γ₁ s₀ - L.γ₁ s₀‖) (‖L.γ₁ s - L.γ₁ s₀‖) :=
          ⟨by simp only [sub_self, norm_zero]; exact le_of_lt hrpos, le_of_lt hlt⟩
        obtain ⟨cc, hcmem, hceq⟩ := intermediate_value_Icc' (le_of_lt hslt) hcont hrmem
        rcases hsolve cc hceq with h | h
        · exact absurd (hs.1.trans_le hcmem.1) (by rw [h]; exact lt_irrefl sL)
        · exact (not_lt_of_ge hcmem.2) (by rw [h]; exact hsRmem.1)
      · have hcont : ContinuousOn (fun t => ‖L.γ₁ t - L.γ₁ s₀‖) (Set.Icc s₀ s) :=
          ((L.cont₁.sub continuous_const).norm).continuousOn
        have hrmem : r ∈ Set.Icc (‖L.γ₁ s₀ - L.γ₁ s₀‖) (‖L.γ₁ s - L.γ₁ s₀‖) :=
          ⟨by simp only [sub_self, norm_zero]; exact le_of_lt hrpos, le_of_lt hlt⟩
        obtain ⟨cc, hcmem, hceq⟩ := intermediate_value_Icc (le_of_lt hsgt) hcont hrmem
        rcases hsolve cc hceq with h | h
        · exact (not_lt_of_ge hcmem.1) (by rw [h]; exact hsLmem.2)
        · exact absurd (hcmem.2.trans_lt hs.2) (by rw [h]; exact lt_irrefl sR)
    · rcases hsolve s heq.symm with h | h
      · exact (ne_of_gt hs.1) h
      · exact (ne_of_lt hs.2) h
  refine ⟨r, hrpos, sL, sR, hsLmem.2, hsRmem.1, hinside, hsLeq, hsReq, ?_⟩
  intro w hw
  constructor
  · intro him
    have hwU : ‖w - L.γ₁ s₀‖ < εU := by rw [hw]; exact hrU
    obtain ⟨s, rfl⟩ := (hU w hwU).mp him
    rcases hsolve s hw with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  · rintro (h | h)
    · rw [h, sideFlipChart_eq_ofReal]; exact Complex.ofReal_im _
    · rw [h, sideFlipChart_eq_ofReal]; exact Complex.ofReal_im _

end Work.ELRig
