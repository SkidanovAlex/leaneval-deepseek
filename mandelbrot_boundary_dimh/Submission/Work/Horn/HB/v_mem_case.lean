import Mathlib
import Submission.Work.Horn.isCoveringMapOn_restrictToPreimage
import Submission.Work.BasinSC.cover_basic
import Submission.Work.BasinSC.defs
import Submission.Work.BasinSC.step
import Submission.Work.BasinSC.StepOneCrit.uniformization_to_ball
import Submission.Work.BasinSC.StepOneCrit.isConnected_diff_finite
import Submission.Work.BasinSC.StepOneCrit.Auxiliary
import Submission.Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit
import Submission.Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap
import Submission.Work.HornCov.isPreconnected_diff_critOrbit
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero
import Submission.Work.Horn.HB.aux1
import Submission.Work.Horn.HB.ambient_local_homeo
import Submission.Work.Horn.HB.exists_analytic_extension_of_bounded
import Submission.Work.Horn.HB.localComponent_ball_image
import Submission.Work.Horn.HB.LF_smaller_ball
import Submission.Work.Horn.HB.isCoveringMap_subtype_of_isClopen
import Submission.Work.Horn.HB.range_lift_eq_pathComponent
import Submission.Work.Horn.HB.homeo_Vstar_puncturedDisc
import Submission.Work.Horn.HB.exists_unique_preimage_of_root
import Submission.Work.Horn.HB.lf_component_image
import Submission.Work.Horn.HB.exists_homeo_Vstar_puncturedDisc_apply
import Submission.Work.Horn.HB.isDiscrete_fiber_v_of_component_image
import Submission.Work.Horn.HB.infinite_fiber_of_gamma_eq_bot
import Submission.Work.Horn.HB.preconnected_preimage_puncturedDisc_of_gamma_eq_bot
import Submission.Work.Horn.HB.exists_ncard_fiber_eq_of_gamma_ne_bot
import Submission.Work.Horn.HB.isCompact_preimage_of_isCoveringMap_finite

/-!
# The case `v ∈ V` of `Work.Horn.HB.proper_of_covering_LF`

If the critical value `v` lies in the simply connected domain `V`, the component `W` of `D ∩ g ⁻¹' V`
through `x` is a finite-degree branched cover of `V` over `v`.  See the module doc-comment of the
previous version for the five-step plan; the proof below follows it literally.
-/

namespace Work.Horn.HB

open MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- **Restriction of a covering map to the preimage of a subset of the base.**  If
`(fun z : ↥Ω => p z)` is a covering map over `D'`, then the restriction of `p` to
`Ω ∩ p ⁻¹' D'`, viewed as a map onto `↥D'`, is a covering map. -/
theorem isCoveringMap_restrictPreimage_inter {Ω D' : Set ℂ} {p : ℂ → ℂ}
    (hcov : IsCoveringMapOn (fun z : ↥Ω => p z) D') :
    IsCoveringMap (fun w : ↥(Ω ∩ p ⁻¹' D') => (⟨p w.1, w.2.2⟩ : ↥D')) := by
  have h := isCoveringMapOn_restrictToPreimage (Ω := Ω) (D := D') hcov
  let e : ↥(Ω ∩ p ⁻¹' D') ≃ₜ ↥{z : ℂ | z ∈ Ω ∧ p z ∈ D'} :=
  { toFun := fun w => ⟨w.1, w.2.1, w.2.2⟩
    invFun := fun v => ⟨v.1, v.2.1, v.2.2⟩
    left_inv := fun w => rfl
    right_inv := fun v => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have h2 := h.comp_homeomorph e
  convert h2 using 1
  ext w
  rfl

/-- Two components of the same set that meet are equal. -/
theorem connectedComponentIn_eq_of_mem {α : Type*} [TopologicalSpace α] {F : Set α} {x y z : α}
    (hz : z ∈ connectedComponentIn F y) (hz' : z ∈ connectedComponentIn F x) :
    connectedComponentIn F x = connectedComponentIn F y :=
  (connectedComponentIn_eq hz').trans (connectedComponentIn_eq hz).symm

/-- The component of `D ∩ g ⁻¹' ball v r` through a point is contained in the component of
`D ∩ g ⁻¹' V` through that point, when `ball v r ⊆ V`. -/
theorem connectedComponentIn_ball_subset {g : ℂ → ℂ} {D V : Set ℂ} {v : ℂ} {r : ℝ}
    (hball : Metric.ball v r ⊆ V) {x : ℂ} (hx : x ∈ D ∩ g ⁻¹' Metric.ball v r) :
    connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ⊆
      connectedComponentIn (D ∩ g ⁻¹' V) x := by
  refine (isPreconnected_connectedComponentIn).subset_connectedComponentIn
    (mem_connectedComponentIn hx) ?_
  intro z hz
  exact ⟨(connectedComponentIn_subset _ _ hz).1, hball (connectedComponentIn_subset _ _ hz).2⟩

/-- **The case `v ∈ V`.**  If the critical value lies in the simply connected domain `V`, then the
component `W` of `D ∩ g ⁻¹' V` through `x` is a finite-degree branched cover of `V` with a unique
preimage of `v`, which is critical exactly when `g` is not injective on `W`. -/
theorem v_mem_case {g : ℂ → ℂ} {D V : Set ℂ} {v : ℂ} {r : ℝ}
    (hDo : IsOpen D) (hg : DifferentiableOn ℂ g D) (hr : 0 < r) (hrv : r < ‖v‖)
    (hcov : IsCoveringMapOn (fun z : ↥D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K))
    {V : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V) (hVsc : SimplyConnectedSpace ↥V)
    (h0V : (0 : ℂ) ∉ V) (hvV : v ∈ V) {x : ℂ} (hxD : x ∈ D) (hxV : g x ∈ V) {W : Set ℂ}
    (hW : W = connectedComponentIn (D ∩ g ⁻¹' V) x) :
    (∀ K ⊆ V, IsCompact K → IsCompact (W ∩ g ⁻¹' K)) ∧ V ⊆ g '' W ∧
      SimplyConnectedSpace ↥W ∧
      (∃ a ∈ W, g a = v ∧ (∀ b ∈ W, g b = v → b = a) ∧
        (¬ Set.InjOn g W → deriv g a = 0)) := by
  classical
  -- ### 0. Basic facts about the component `W`
  have hgcont : ∀ z ∈ D, ContinuousAt g z :=
    fun z hz => (hg.differentiableAt (hDo.mem_nhds hz)).continuousAt
  have hAopen : IsOpen (D ∩ g ⁻¹' V) := isOpen_inter_preimage_of_continuousAt hDo hVo hgcont
  have hxW : x ∈ W := by rw [hW]; exact mem_connectedComponentIn ⟨hxD, hxV⟩
  have hWsub : W ⊆ D ∩ g ⁻¹' V := by rw [hW]; exact connectedComponentIn_subset _ _
  have hWopen : IsOpen W := by rw [hW]; exact hAopen.connectedComponentIn
  have hWpre : IsPreconnected W := by rw [hW]; exact isPreconnected_connectedComponentIn
  have hWD : W ⊆ D := fun z hz => (hWsub hz).1
  have hWgV : ∀ z ∈ W, g z ∈ V := fun z hz => (hWsub hz).2
  have hWcont : ∀ z ∈ W, ContinuousAt g z := fun z hz => hgcont z (hWD hz)
  have hWdiff : ∀ z ∈ W, DifferentiableAt ℂ g z :=
    fun z hz => hg.differentiableAt (hDo.mem_nhds (hWD hz))
  have hVproper : V ≠ Set.univ := by
    intro h; rw [h] at h0V; exact h0V (Set.mem_univ 0)
  have hVne : V.Nonempty := ⟨v, hvV⟩
  have hlocS : IsLocalHomeomorphOn g (D ∩ g ⁻¹' {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v}) :=
    ambient_local_homeo hDo hcov
  have hVstar_sub : V \ {v} ⊆ {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} := by
    rintro y ⟨hyV, hyv⟩
    exact ⟨fun h => h0V (h ▸ hyV), hyv⟩
  have hcovV : IsCoveringMapOn (fun z : ↥D => g z) (V \ {v}) := hcov.mono hVstar_sub
  -- ### 0b. choose a radius `ρ` with `ball v ρ ⊆ V` and `ρ ≤ r`
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := Metric.isOpen_iff.mp hVo v hvV
  set ρ : ℝ := min ρ₀ r with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀pos hr
  have hρr : ρ ≤ r := min_le_right _ _
  have hρv : ρ < ‖v‖ := lt_of_le_of_lt hρr hrv
  have hballρ : Metric.ball v ρ ⊆ V := (Metric.ball_subset_ball (min_le_left _ _)).trans hρ₀sub
  have h0ball : (0 : ℂ) ∉ Metric.ball v ρ := by
    intro h
    rw [Metric.mem_ball, dist_eq_norm] at h
    simp only [zero_sub, norm_neg] at h
    exact absurd (lt_of_lt_of_le h hρv.le) (lt_irrefl ‖v‖)
  have hballρ_self : v ∈ Metric.ball v ρ := Metric.mem_ball_self hρpos
  have hLFρ : ∀ z ∈ D, g z ∈ Metric.ball v ρ → ∀ K ⊆ Metric.ball v ρ, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z ∩ g ⁻¹' K) :=
    LF_smaller_ball hρr hLF
  have himg : ∀ z ∈ D, g z ∈ Metric.ball v ρ →
      Metric.ball v ρ ⊆ g '' connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z :=
    fun z hzD hzρ => (lf_component_image hDo hg hρpos hρv hcov hLFρ hzD hzρ).1
  have hmeet : ∀ z ∈ D, g z ∈ Metric.ball v ρ →
      (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z ∩ g ⁻¹' {v}).Nonempty :=
    fun z hzD hzρ => (lf_component_image hDo hg hρpos hρv hcov hLFρ hzD hzρ).2
  have hcompW : ∀ z ∈ W, g z ∈ Metric.ball v ρ →
      connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z ⊆ W := by
    intro z hzW hzρ
    have h1 := connectedComponentIn_ball_subset (g := g) (D := D) (V := V) (v := v) (r := ρ)
      hballρ (x := z) ⟨hWD hzW, hzρ⟩
    have h2 : connectedComponentIn (D ∩ g ⁻¹' V) z = W := by
      rw [hW]
      exact (connectedComponentIn_eq (show z ∈ connectedComponentIn (D ∩ g ⁻¹' V) x from by
        rw [← hW]; exact hzW)).symm
    rw [h2] at h1
    exact h1
  -- ### 1. a point of `W` above `V* = V ∖ {v}`
  have hv_mem_ball : v + (((ρ / 2 : ℝ)) : ℂ) ∈ Metric.ball v ρ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (le_of_lt (half_pos hρpos))]
    linarith
  have hv_ne : v + (((ρ / 2 : ℝ)) : ℂ) ≠ v := by
    intro h
    have h1 : (((ρ / 2 : ℝ)) : ℂ) = 0 := by
      have := congrArg (fun w : ℂ => w - v) h
      simpa using this
    have h2 : ρ / 2 = 0 := Complex.ofReal_eq_zero.mp h1
    linarith
  have hx1 : ∃ x₁ ∈ W, g x₁ ∈ V \ {v} := by
    by_cases hgx : g x = v
    · obtain ⟨z, hzC, hzg⟩ := himg x hxD (by rw [hgx]; exact hballρ_self) hv_mem_ball
      exact ⟨z, hcompW x hxW (by rw [hgx]; exact hballρ_self) hzC,
        by rw [hzg]; exact ⟨hballρ hv_mem_ball, hv_ne⟩⟩
    · exact ⟨x, hxW, hWgV x hxW, hgx⟩
  -- ### 2. the covering over the puncture, and path lifting
  set Vstar : Set ℂ := V \ {v} with hVstar
  have hVstaropen : IsOpen Vstar := hVo.sdiff isClosed_singleton
  have hVstar_pc : IsPreconnected Vstar :=
    Work.BasinSC.StepOneCrit.isPreconnected_diff_singleton hVo hVc.isPreconnected v
  have hVstar_ne : Vstar.Nonempty :=
    ⟨v + (((ρ / 2 : ℝ)) : ℂ), hballρ hv_mem_ball, hv_ne⟩
  haveI : PreconnectedSpace ↥Vstar := isPreconnected_iff_preconnectedSpace.mp hVstar_pc
  haveI : LocallyPathConnectedSpace ↥Vstar := hVstaropen.locallyPathConnectedSpace
  haveI : PathConnectedSpace ↥Vstar :=
    pathConnectedSpace_of_preconnected_of_locallyPathConnected ↥Vstar
      ⟨hVstar_ne.choose, hVstar_ne.choose_spec⟩
  have hcovVstar : IsCoveringMapOn (fun z : ↥D => g z) Vstar := hcov.mono hVstar_sub
  set E : Set ℂ := D ∩ g ⁻¹' Vstar with hE
  have hP : IsCoveringMap (fun e : ↥E => (⟨g e.1, e.2.2⟩ : ↥Vstar)) :=
    isCoveringMap_restrictPreimage_inter hcovVstar
  set Ws : Set ℂ := W ∩ g ⁻¹' Vstar with hWs
  -- ### 3. `W` maps onto `V*`
  have hsurjVstar : Vstar ⊆ g '' W := by
    rintro y hy
    obtain ⟨x₁, hx₁W, hx₁V⟩ := hx1
    let P : ↥E → ↥Vstar := fun e => ⟨g e.1, e.2.2⟩
    let e₁ : ↥E := ⟨x₁, hWD hx₁W, hx₁V⟩
    let γ : Path (⟨g x₁, hx₁V⟩ : ↥Vstar) ⟨y, hy⟩ := PathConnectedSpace.somePath _ _
    have hγ : (γ : C(unitInterval, ↥Vstar)) 0 = P e₁ := by
      have h := γ.source
      simpa [P, e₁, γ] using h
    let lift : C(unitInterval, ↥E) := hP.liftPath (γ : C(unitInterval, ↥Vstar)) e₁ hγ
    have hlift_lifts : ∀ t, P (lift t) = γ t := fun t =>
      congrFun (hP.liftPath_lifts (γ : C(unitInterval, ↥Vstar)) e₁ hγ) t
    have hlift0 : (lift 0 : ↥E) = e₁ := hP.liftPath_zero (γ : C(unitInterval, ↥Vstar)) e₁ hγ
    have hval : ∀ t, g (lift t).1 = (γ t : ℂ) := fun t => congrArg Subtype.val (hlift_lifts t)
    refine ⟨(lift 1).1, ?_, ?_⟩
    · have hcont : Continuous fun t : unitInterval => (lift t).1 :=
        continuous_subtype_val.comp lift.continuous
      have hpre : IsPreconnected (Set.range fun t : unitInterval => (lift t).1) := by
        simpa only [Set.image_univ] using
          isPreconnected_univ.image (fun t : unitInterval => (lift t).1) hcont.continuousOn
      have hlift0' : (lift 0).1 = x₁ := by rw [hlift0]
      have hsubF : Set.range (fun t : unitInterval => (lift t).1) ⊆ D ∩ g ⁻¹' V := by
        rintro z ⟨t, rfl⟩
        have h1 : (lift t).1 ∈ D := (lift t).2.1
        have h2 : g (lift t).1 ∈ V := by
          have h := (lift t).2.2
          rw [hVstar] at h
          exact h.1
        exact ⟨h1, h2⟩
      have hmem : (lift 0).1 ∈ Set.range fun t : unitInterval => (lift t).1 := ⟨0, rfl⟩
      have hres := hpre.subset_connectedComponentIn hmem hsubF
      have hcomp : connectedComponentIn (D ∩ g ⁻¹' V) ((lift 0).1) = W := by
        rw [hW, hlift0']
        exact (connectedComponentIn_eq (show x₁ ∈ connectedComponentIn (D ∩ g ⁻¹' V) x from by
          rw [← hW]; exact hx₁W)).symm
      rw [hcomp] at hres
      exact hres ⟨1, rfl⟩
    · rw [hval 1, γ.target]
  -- ### 4. `v` is attained in `W`
  have hv_image : v ∈ g '' W := by
    obtain ⟨z, hzW, hzg⟩ := hsurjVstar ⟨hballρ hv_mem_ball, hv_ne⟩
    have hzg' : g z = v + (((ρ / 2 : ℝ)) : ℂ) := hzg
    have hzρ : g z ∈ Metric.ball v ρ := by rw [hzg']; exact hv_mem_ball
    obtain ⟨b, hbC, hgb⟩ := hmeet z (hWD hzW) hzρ
    exact ⟨b, hcompW z hzW hzρ hbC, hgb⟩
  have hsurj : V ⊆ g '' W := by
    intro y hy
    rcases eq_or_ne y v with rfl | hyv
    · exact hv_image
    · exact hsurjVstar ⟨hy, by simpa using hyv⟩
  have hne_v : (g ⁻¹' {v} ∩ W).Nonempty := by
    obtain ⟨b, hbW, hgb⟩ := hv_image
    exact ⟨b, by simpa using hgb, hbW⟩
  -- ### 5. the covering `q : W* → 𝔻*` of the punctured disc
  obtain ⟨φ, ψ, hφv, hφmaps, hψmaps, hφψ, hψφ, hφdiff, hψdiff, hφderiv, hψderiv⟩ :=
    Work.BasinSC.StepOneCrit.uniformization_to_ball hVo hVne hVsc hVproper hvV
  have hψ0 : ψ 0 = v := by
    have h := hφψ v hvV
    rw [hφv] at h
    exact h
  obtain ⟨Φ, hΦapply⟩ := exists_homeo_Vstar_puncturedDisc_apply hvV hφv hφmaps hψmaps hφψ hψφ
    (fun z hz => (hφdiff z hz).continuousAt) (fun w hw => (hψdiff w hw).continuousAt)
  set C : Set ↥E := {e | e.1 ∈ W} with hC
  have hCopen : IsOpen C := hWopen.preimage continuous_subtype_val
  have hCclosed : IsClosed C := by
    let ι : ↥E → ↥(D ∩ g ⁻¹' V) := fun e => ⟨e.1, ⟨e.2.1, e.2.2.1⟩⟩
    have hι : Continuous ι := by fun_prop
    have hclosed : IsClosed (Subtype.val ⁻¹' W : Set ↥(D ∩ g ⁻¹' V)) := by
      have h1 : connectedComponentIn (D ∩ g ⁻¹' V) x
          = Subtype.val '' connectedComponent (⟨x, hxD, hxV⟩ : ↥(D ∩ g ⁻¹' V)) :=
        connectedComponentIn_eq_image (show x ∈ D ∩ g ⁻¹' V from ⟨hxD, hxV⟩)
      rw [hW, h1, Set.preimage_image_eq _ Subtype.val_injective]
      exact isClosed_connectedComponent
    have hCeq : C = ι ⁻¹' (Subtype.val ⁻¹' W : Set ↥(D ∩ g ⁻¹' V)) := by
      ext e; rfl
    rw [hCeq]
    exact hclosed.preimage hι
  have hCcl : IsClopen C := ⟨hCclosed, hCopen⟩
  have hQC : IsCoveringMap (fun c : C => (⟨g c.1.1, c.1.2.2⟩ : ↥Vstar)) :=
    isCoveringMap_subtype_of_isClopen hP hCcl
  let eC : ↥Ws ≃ₜ ↥C :=
  { toFun := fun w => ⟨⟨w.1, ⟨hWD w.2.1, w.2.2⟩⟩, w.2.1⟩
    invFun := fun c => ⟨c.1.1, ⟨c.2, c.1.2.2⟩⟩
    left_inv := fun w => by ext <;> rfl
    right_inv := fun c => by ext <;> rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let q : ↥Ws → ↥Work.BasinSC.puncturedDisc := fun w => Φ ⟨g w.1, w.2.2⟩
  have hq : IsCoveringMap q := by
    have h1 : IsCoveringMap (fun c : C => Φ ⟨g c.1.1, c.1.2.2⟩) := hQC.homeomorph_comp Φ
    have h2 : IsCoveringMap (fun w : ↥Ws => Φ ⟨g (eC w).1.1, (eC w).1.2.2⟩) :=
      h1.comp_homeomorph eC
    exact h2
  have hq_apply : ∀ w : ↥Ws, (q w : ℂ) = φ (g w.1) := fun w => hΦapply ⟨g w.1, w.2.2⟩
  -- ### 6. `W*` is path connected
  have hWs_eq : Ws = W \ g ⁻¹' {v} := by
    ext z; constructor
    · rintro ⟨hzW, hzg⟩
      exact ⟨hzW, by simpa using hzg.2⟩
    · rintro ⟨hzW, hzv⟩
      exact ⟨hzW, ⟨hWgV z hzW, by simpa using hzv⟩⟩
  have hdisc : IsDiscrete (g ⁻¹' {v} ∩ W) :=
    isDiscrete_fiber_v_of_component_image hDo hg hρpos hWopen hWD hLFρ himg
  have hZcount : (g ⁻¹' {v} ∩ W).Countable := by
    haveI : HereditarilyLindelofSpace ℂ := inferInstance
    exact IsLindelof.countable_of_isDiscrete (HereditarilyLindelofSpace.isLindelof _) hdisc
  have hWspre : IsPreconnected Ws := by
    have h1 : IsPreconnected (W \ (g ⁻¹' {v} ∩ W)) :=
      Work.HornCov.isPreconnected_diff_countable hWopen hWpre hZcount
    rw [hWs_eq]
    convert h1 using 1
    ext z
    constructor
    · rintro ⟨hzW, hzv⟩
      exact ⟨hzW, fun h => hzv h.1⟩
    · rintro ⟨hzW, hzv⟩
      exact ⟨hzW, fun h => hzv ⟨h, hzW⟩⟩
  have hWsopen : IsOpen Ws := by
    rw [hWs]
    exact isOpen_inter_preimage_of_continuousAt hWopen hVstaropen (fun z hz => hWcont z hz)
  haveI : PreconnectedSpace ↥Ws := isPreconnected_iff_preconnectedSpace.mp hWspre
  haveI : LocallyPathConnectedSpace ↥Ws := hWsopen.locallyPathConnectedSpace
  have hWs_ne : Nonempty ↥Ws := by
    obtain ⟨x₁, hx₁W, hx₁V⟩ := hx1
    exact ⟨⟨x₁, hx₁W, hx₁V⟩⟩
  haveI : PathConnectedSpace ↥Ws :=
    pathConnectedSpace_of_preconnected_of_locallyPathConnected ↥Ws hWs_ne
  -- ### 7. the stabiliser of the lift is non-trivial
  obtain ⟨x₁, hx₁W, hx₁V⟩ := hx1
  let c₀ : ↥Ws := ⟨x₁, hx₁W, hx₁V⟩
  obtain ⟨t₀, ht₀⟩ := Work.BasinSC.CoverDisc.u_surjective (q c₀)
  have ht₀' : q c₀ = Work.BasinSC.CoverDisc.u t₀ := ht₀.symm
  have hΓ_ne : Work.BasinSC.CoverDisc.Gamma hq t₀ c₀ ht₀' ≠ ⊥ := by
    intro hΓbot
    -- a small punctured disc around `0` in `𝔻*` whose `ψ`-image sits in `ball v ρ`
    have hψcont0 : ContinuousAt ψ 0 := (hψdiff 0 (by norm_num)).continuousAt
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp
      (hψcont0.preimage_mem_nhds (by rw [hψ0]; exact Metric.ball_mem_nhds v hρpos))
    have hδsub' : ∀ w : ℂ, ‖w‖ < δ → ψ w ∈ Metric.ball v ρ := by
      intro w hw
      exact hδsub (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hw)
    set r' : ℝ := min δ 1 / 2 with hr'def
    have hr'0 : 0 < r' := half_pos (lt_min hδpos one_pos)
    have hr'1 : r' < 1 := by
      have h : min δ 1 ≤ 1 := min_le_right _ _
      linarith
    have hr'δ : r' ≤ δ := by
      have h : min δ 1 ≤ δ := min_le_left _ _
      linarith
    -- the preimage of the punctured disc is preconnected and non-empty
    have hSpre : IsPreconnected (q ⁻¹' {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r'}) :=
      preconnected_preimage_puncturedDisc_of_gamma_eq_bot hq ht₀' hΓbot hr'0 hr'1
    have hw₁ : ∃ w : ↥Work.BasinSC.puncturedDisc, ‖(w : ℂ)‖ < r' := by
      refine ⟨⟨(((r' / 2 : ℝ)) : ℂ), ?_, ?_⟩, ?_⟩
      · rw [ne_eq, Complex.ofReal_eq_zero]
        linarith
      · rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt (half_pos hr'0))]
        linarith
      · rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt (half_pos hr'0))]
        linarith
    obtain ⟨w₁, hw₁lt⟩ := hw₁
    have hw₁ball : (w₁ : ℂ) ∈ Metric.ball 0 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact w₁.2.2
    have hinf : (q ⁻¹' {w₁}).Infinite := infinite_fiber_of_gamma_eq_bot hq ht₀' hΓbot w₁
    have hSne : (q ⁻¹' {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r'}).Nonempty := by
      obtain ⟨w, hw⟩ := hinf.nonempty
      exact ⟨w, by rw [Set.mem_preimage, hw]; exact hw₁lt⟩
    obtain ⟨z₀, hz₀S⟩ := hSne
    have hz₀ball : g z₀.1 ∈ Metric.ball v ρ := by
      have hψq : ψ (q z₀ : ℂ) = g z₀.1 := by
        rw [hq_apply z₀]
        exact hφψ (g z₀.1) (hWgV z₀.1 z₀.2.1)
      rw [← hψq]
      exact hδsub' _ (lt_of_lt_of_le hz₀S hr'δ)
    -- the component of `D ∩ g ⁻¹' ball v ρ` containing the whole preimage
    set C₀ : Set ℂ := connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z₀.1 with hC₀
    have hSC₀ : ∀ w ∈ q ⁻¹' {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r'},
        w.1 ∈ C₀ := by
      intro w hw
      have hpre : IsPreconnected (Subtype.val '' (q ⁻¹'
          {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r'})) :=
        hSpre.image _ continuous_subtype_val.continuousOn
      have hsubF : Subtype.val '' (q ⁻¹'
          {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r'}) ⊆ D ∩ g ⁻¹' Metric.ball v ρ := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨hWD u.2.1, ?_⟩
        rw [Set.mem_preimage]
        have hψq : ψ (q u : ℂ) = g u.1 := by
          rw [hq_apply u]
          exact hφψ (g u.1) (hWgV u.1 u.2.1)
        rw [← hψq]
        exact hδsub' _ (lt_of_lt_of_le hu hr'δ)
      have hmem : z₀.1 ∈ Subtype.val '' (q ⁻¹'
          {w : ↥Work.BasinSC.puncturedDisc | ‖(w : ℂ)‖ < r'}) := ⟨z₀, hz₀S, rfl⟩
      have hres := hpre.subset_connectedComponentIn hmem hsubF
      exact hres ⟨w, hw, rfl⟩
    -- the fibre over `w₁` is infinite and lives in `C₀ ∩ g ⁻¹' {ψ w₁}`
    have hsub : ∀ w ∈ q ⁻¹' {w₁}, w.1 ∈ C₀ ∩ g ⁻¹' {ψ (w₁ : ℂ)} := by
      intro w hw
      have hwS : w ∈ q ⁻¹' {w' : ↥Work.BasinSC.puncturedDisc | ‖(w' : ℂ)‖ < r'} := by
        rw [Set.mem_preimage]
        have hq_eq : q w = w₁ := by
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
          exact hw
        rw [hq_eq]
        exact hw₁lt
      refine ⟨hSC₀ w hwS, ?_⟩
      have hval : g w.1 = ψ (w₁ : ℂ) := by
        have h2 : (q w : ℂ) = (w₁ : ℂ) := by
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
          rw [hw]
        have h1 : φ (g w.1) = (w₁ : ℂ) := by rw [← hq_apply w, h2]
        calc g w.1 = ψ (φ (g w.1)) := (hφψ (g w.1) (hWgV w.1 w.2.1)).symm
          _ = ψ (w₁ : ℂ) := by rw [h1]
      rw [Set.mem_preimage]
      simpa using hval
    -- but that set is compact and discrete, hence finite
    have hcomp : IsCompact (C₀ ∩ g ⁻¹' {ψ (w₁ : ℂ)}) := by
      refine hLFρ z₀.1 (hWD z₀.2.1) hz₀ball {ψ (w₁ : ℂ)} ?_ isCompact_singleton
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hδsub' _ (lt_of_lt_of_le hw₁lt hr'δ)
    have hdisc' : IsDiscrete (C₀ ∩ g ⁻¹' {ψ (w₁ : ℂ)}) := by
      have hψw₁ne : ψ (w₁ : ℂ) ≠ v := by
        intro h
        have h1 : φ (ψ (w₁ : ℂ)) = (w₁ : ℂ) := hψφ (w₁ : ℂ) hw₁ball
        rw [h, hφv] at h1
        exact w₁.2.1 h1.symm
      have h0 : ψ (w₁ : ℂ) ≠ 0 :=
        fun h => h0ball (h ▸ hδsub' _ (lt_of_lt_of_le hw₁lt hr'δ))
      have hsub' : C₀ ∩ g ⁻¹' {ψ (w₁ : ℂ)} ⊆
          (D ∩ g ⁻¹' {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v}) ∩ g ⁻¹' {ψ (w₁ : ℂ)} := by
        rintro z ⟨hzC, hzg⟩
        have hzg' : g z = ψ (w₁ : ℂ) := by simpa using hzg
        exact ⟨⟨(connectedComponentIn_subset _ _ hzC).1, by
          rw [Set.mem_preimage]
          rw [hzg']
          exact ⟨h0, hψw₁ne⟩⟩, hzg⟩
      exact (isDiscrete_fiber_of_isLocalHomeomorphOn hlocS).mono hsub'
    haveI : CompactSpace ↥(C₀ ∩ g ⁻¹' {ψ (w₁ : ℂ)}) := isCompact_iff_compactSpace.mp hcomp
    haveI : DiscreteTopology ↥(C₀ ∩ g ⁻¹' {ψ (w₁ : ℂ)}) :=
      discreteTopology_subtype_iff.mpr (isDiscrete_iff_nhdsNE.mp hdisc')
    have hfinS : (C₀ ∩ g ⁻¹' {ψ (w₁ : ℂ)}).Finite :=
      Set.finite_coe_iff.mpr finite_of_compact_of_discrete
    have himgfin : (Subtype.val '' (q ⁻¹' {w₁}) : Set ℂ).Finite :=
      hfinS.subset (by rintro _ ⟨w, hw, rfl⟩; exact hsub w hw)
    have himginf : (Subtype.val '' (q ⁻¹' {w₁}) : Set ℂ).Infinite :=
      hinf.image (fun a _ b _ hab => Subtype.ext hab)
    exact himginf himgfin
  -- ### 8. finite degree and the root map
  obtain ⟨d, hdpos, hd⟩ := exists_ncard_fiber_eq_of_gamma_ne_bot hq ht₀' hΓ_ne
  obtain ⟨d', hd'pos, ψD, hψDpow⟩ :=
    Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap hq ⟨d, hdpos, hd⟩
  -- ### 9. uniqueness of the preimage of `v` in `W`
  let Ψ : ℂ → ℂ := fun z => if h : z ∈ Ws then ((ψD ⟨z, h⟩ : ↥Work.BasinSC.puncturedDisc) : ℂ)
    else 0
  have hWs_mem : ∀ z, z ∈ Ws ↔ z ∈ W \ g ⁻¹' {v} := by
    intro z; rw [hWs_eq]
  have hΨana : ∀ z ∈ W \ g ⁻¹' {v}, AnalyticAt ℂ Ψ z := by
    intro z hz
    have hzWs : z ∈ Ws := (hWs_mem z).mpr hz
    have hzW : z ∈ W := by
      have h := hz
      rw [Set.sdiff_eq] at h
      exact h.1
    have hgzV : g z ∈ V := hWgV z hzW
    have hgzVstar : g z ∈ Vstar := by
      rw [hWs] at hzWs
      exact hzWs.2
    have hqana : AnalyticAt ℂ (fun u : ℂ => φ (g u)) z := by
      have h1 : DifferentiableOn ℂ (fun u : ℂ => φ (g u)) W := fun u hu =>
        ((hφdiff (g u) (hWgV u hu)).comp u (hWdiff u hu)).differentiableWithinAt
      exact (h1.analyticOnNhd hWopen) z hzW
    have hqne : φ (g z) ≠ 0 := by
      intro h
      have h1 : ψ (φ (g z)) = g z := hφψ (g z) hgzV
      rw [h, hψ0] at h1
      exact hgzVstar.2 (by simpa using h1.symm)
    have hcont : ContinuousAt Ψ z := by
      have hcontOn : ContinuousOn Ψ Ws := by
        have h2 : Continuous (fun w : ↥Ws => Ψ w.1) := by
          have h3 : Continuous (fun w : ↥Ws => ((ψD w : ↥Work.BasinSC.puncturedDisc) : ℂ)) :=
            continuous_subtype_val.comp ψD.continuous
          convert h3 using 1
          ext w
          simp only [Ψ]
          rw [dif_pos w.2]
        exact continuousOn_iff_continuous_restrict.mpr h2
      exact hcontOn.continuousAt (hWsopen.mem_nhds hzWs)
    have hpow : ∀ᶠ u in 𝓝 z, (Ψ u) ^ d' = φ (g u) := by
      filter_upwards [hWsopen.mem_nhds hzWs] with u hu
      simp only [Ψ, dif_pos hu]
      rw [hψDpow ⟨u, hu⟩]
      exact hq_apply ⟨u, hu⟩
    exact Work.BasinSC.StepOneCrit.analyticAt_of_pow_eq_of_continuousAt hd'pos hqana hqne hcont hpow
  have hbdd : ∀ z ∈ W \ g ⁻¹' {v}, ‖Ψ z‖ ≤ 1 := by
    intro z hz
    have hzWs : z ∈ Ws := (hWs_mem z).mpr hz
    simp only [Ψ, dif_pos hzWs]
    exact le_of_lt (ψD ⟨z, hzWs⟩).2.2
  have hpw : ∀ z ∈ W \ g ⁻¹' {v}, (Ψ z) ^ d' = φ (g z) := by
    intro z hz
    have hzWs : z ∈ Ws := (hWs_mem z).mpr hz
    simp only [Ψ, dif_pos hzWs]
    rw [hψDpow ⟨z, hzWs⟩]
    exact hq_apply ⟨z, hzWs⟩
  have hinj : Set.InjOn Ψ (W \ g ⁻¹' {v}) := by
    intro p hp q hq hpq
    have hpWs : p ∈ Ws := (hWs_mem p).mpr hp
    have hqWs : q ∈ Ws := (hWs_mem q).mpr hq
    simp only [Ψ, dif_pos hpWs, dif_pos hqWs] at hpq
    have : (⟨p, hpWs⟩ : ↥Ws) = ⟨q, hqWs⟩ := ψD.injective (Subtype.ext hpq)
    exact congrArg Subtype.val this
  obtain ⟨a, haW, hga, huniq, hcrit⟩ :=
    exists_unique_preimage_of_root hd'pos hWopen hvV hφv hφderiv (fun z hz => hWgV z hz)
      (fun z hz => hWcont z hz) (fun z hz => hWdiff z hz) hdisc hΨana hbdd hpw hinj hne_v
  -- ### 10. properness over `V`
  have ha_ball : g a ∈ Metric.ball v ρ := by rw [hga]; exact hballρ_self
  have hproper : ∀ K ⊆ V, IsCompact K → IsCompact (W ∩ g ⁻¹' K) := by
    intro K hKV hKc
    have hclosedball : Metric.closedBall v (ρ/2) ⊆ Metric.ball v ρ :=
      Metric.closedBall_subset_ball (by linarith)
    have hpart1 : IsCompact (W ∩ g ⁻¹' (K ∩ Metric.closedBall v (ρ/2))) := by
      have hK1 : IsCompact (K ∩ Metric.closedBall v (ρ/2)) := hKc.inter_right isClosed_closedBall
      have hK1sub : K ∩ Metric.closedBall v (ρ/2) ⊆ Metric.ball v ρ := fun z hz =>
        hclosedball hz.2
      have hLF1 := hLFρ a (hWD haW) ha_ball _ hK1sub hK1
      have heq : connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) a ∩ g ⁻¹'
          (K ∩ Metric.closedBall v (ρ/2)) = W ∩ g ⁻¹' (K ∩ Metric.closedBall v (ρ/2)) := by
        ext z; constructor
        · rintro ⟨hzC, hzK⟩
          exact ⟨hcompW a haW ha_ball hzC, hzK⟩
        · rintro ⟨hzW, hzK⟩
          have hzρ : g z ∈ Metric.ball v ρ := hK1sub hzK
          obtain ⟨b, hbC, hgb⟩ := hmeet z (hWD hzW) hzρ
          have hba : b = a := huniq b (hcompW z hzW hzρ hbC) hgb
          have hbCz : b ∈ connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z := hbC
          have haCz : a ∈ connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z := by
            rw [← hba]; exact hbCz
          have heqc : connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z
              = connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) a :=
            connectedComponentIn_eq haCz
          exact ⟨heqc ▸ mem_connectedComponentIn ⟨hWD hzW, hzρ⟩, hzK⟩
      rw [← heq]
      exact hLF1
    have hpart2 : IsCompact (W ∩ g ⁻¹' (K \ Metric.ball v (ρ/2))) := by
      have hKc' : IsCompact (K \ Metric.ball v (ρ/2)) := by
        rw [Set.sdiff_eq]
        exact hKc.inter_right Metric.isOpen_ball.isClosed_compl
      have hKc'sub : K \ Metric.ball v (ρ/2) ⊆ Vstar := by
        intro z hz
        have hznot : z ∉ Metric.ball v (ρ/2) := hz.2
        refine ⟨hKV hz.1, ?_⟩
        intro h
        rw [Set.mem_singleton_iff] at h
        rw [h] at hznot
        exact hznot (Metric.mem_ball_self (by linarith))
      let T : Set ↥Vstar := {y | y.1 ∈ K \ Metric.ball v (ρ/2)}
      have hT : IsCompact T := by
        haveI : CompactSpace ↥(K \ Metric.ball v (ρ/2)) := isCompact_iff_compactSpace.mp hKc'
        have hcont : Continuous fun z : ↥(K \ Metric.ball v (ρ/2)) =>
            (⟨z.1, hKc'sub z.2⟩ : ↥Vstar) := by fun_prop
        have h2 : IsCompact (Set.range fun z : ↥(K \ Metric.ball v (ρ/2)) =>
            (⟨z.1, hKc'sub z.2⟩ : ↥Vstar)) := by
          simpa only [Set.image_univ] using (isCompact_univ.image hcont)
        have h3 : Set.range (fun z : ↥(K \ Metric.ball v (ρ/2)) =>
            (⟨z.1, hKc'sub z.2⟩ : ↥Vstar)) = T := by
          ext y; constructor
          · rintro ⟨s, rfl⟩; exact s.2
          · intro hy; exact ⟨⟨y.1, hy⟩, rfl⟩
        rwa [h3] at h2
      haveI : LocallyCompactSpace ↥Work.BasinSC.puncturedDisc := by
        have h : Work.BasinSC.puncturedDisc = Metric.ball (0:ℂ) 1 \ {0} := by
          ext w
          simp only [Work.BasinSC.puncturedDisc, Set.mem_ofPred_eq, Set.mem_sdiff,
            Set.mem_singleton_iff, Metric.mem_ball, dist_eq_norm, sub_zero]
          tauto
        rw [h]
        exact (Metric.isOpen_ball.sdiff isClosed_singleton).locallyCompactSpace
      have hKimg : IsCompact (Φ '' T) := hT.image Φ.continuous
      have hfin : ∀ b ∈ Φ '' T, (q ⁻¹' {b}).Finite := fun b _ =>
        Set.finite_of_ncard_ne_zero (by rw [hd b]; exact hdpos.ne')
      have hcomp := isCompact_preimage_of_isCoveringMap_finite hq hKimg hfin
      have himg : (Subtype.val '' (q ⁻¹' (Φ '' T)) : Set ℂ)
          = W ∩ g ⁻¹' (K \ Metric.ball v (ρ/2)) := by
        ext z; constructor
        · rintro ⟨w, hw, rfl⟩
          have hwW : w.1 ∈ W := w.2.1
          obtain ⟨y, hy, hqy⟩ := hw
          have hgy : g w.1 = y.1 := by
            have h1 : Φ ⟨g w.1, w.2.2⟩ = Φ y := hqy.symm
            exact congrArg Subtype.val (Φ.injective h1)
          refine ⟨hwW, ?_⟩
          rw [Set.mem_preimage]
          rw [hgy]
          exact hy
        · rintro ⟨hzW, hzK⟩
          have hzVstar : g z ∈ Vstar := hKc'sub hzK
          refine ⟨⟨z, hzW, hzVstar⟩, ?_, rfl⟩
          exact ⟨⟨g z, hzVstar⟩, hzK, rfl⟩
      rw [← himg]
      exact hcomp.image continuous_subtype_val
    have hsplit : W ∩ g ⁻¹' K
        = (W ∩ g ⁻¹' (K ∩ Metric.closedBall v (ρ/2))) ∪ (W ∩ g ⁻¹' (K \ Metric.ball v (ρ/2))) := by
      ext z; constructor
      · rintro ⟨hzW, hzK⟩
        by_cases h : g z ∈ Metric.ball v (ρ/2)
        · exact Or.inl ⟨hzW, hzK, Metric.ball_subset_closedBall h⟩
        · exact Or.inr ⟨hzW, hzK, h⟩
      · rintro (⟨hzW, hzK⟩ | ⟨hzW, hzK⟩) <;> exact ⟨hzW, hzK.1⟩
    rw [hsplit]
    exact hpart1.union hpart2
  -- ### 11. simple connectivity
  have hWd : IsConnected W := ⟨⟨x, hxW⟩, hWpre⟩
  have hderiv_ne : ∀ z ∈ W, g z ≠ v → deriv g z ≠ 0 := by
    intro z hzW hzv hd0
    have hzs : z ∈ D ∩ g ⁻¹' {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} :=
      ⟨hWD hzW, fun h => h0V (h ▸ hWgV z hzW), hzv⟩
    obtain ⟨e, hze, heq⟩ := hlocS z hzs
    have hana : AnalyticAt ℂ g z := (hg.analyticOnNhd hDo) z (hWD hzW)
    have hnc : ¬ ∀ᶠ u in 𝓝 z, g u = g z := not_eventually_eq_of_isLocalHomeomorphOn hlocS hzs
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hze)
    obtain ⟨w, hwne, hwlt, p, q, hpq, hp, hq, hgp, hgq⟩ :=
      Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero hana hd0 hnc hεpos
    have hpe : p ∈ e.source := hεsub (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
    have hqe : q ∈ e.source := hεsub (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
    have : p = q := e.injOn hpe hqe (by
      rw [show (e : ℂ → ℂ) = g from heq.symm]
      exact hgp.trans hgq.symm)
    exact hpq this
  have hsc : SimplyConnectedSpace ↥W := by
    by_cases hcrit0 : deriv g a = 0
    · exact Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit
        hVo hVne hVsc hVproper hWopen hWd (hg.mono hWD) (fun z hz => hWgV z hz) hsurj
        (fun K hKV hKc => hproper K hKV hKc) haW hcrit0
        (fun z hz hz0 => by
          by_contra hza
          exact hderiv_ne z hz (fun h => hza (huniq z hz h)) hz0)
    · exact Work.BasinSC.simplyConnected_of_proper_holomorphic_no_crit
        hVo hVne hVsc hWopen hWd (hg.mono hWD) (fun z hz => hWgV z hz)
        (fun K hKV hKc => hproper K hKV hKc)
        (fun z hz => by
          by_contra hz0
          by_cases hgv : g z = v
          · exact hcrit0 (by rw [← huniq z hz hgv]; exact hz0)
          · exact hderiv_ne z hz hgv hz0)
  exact ⟨hproper, hsurj, hsc, a, haW, hga, huniq, hcrit⟩

end

end Work.Horn.HB
