import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.GreenData
import Submission.Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero
import Submission.Work.SimplyConnected.ABS.isPreconnected_of_isGreenOn

/-!
# The disc lemma of Anghel–Bruin–Stan, from a Green function and its modulus

Let `X` be a Riemann surface, `Ω ⊆ X` an open set, `x₀ ∈ Ω`, `E` the Green function of `Ω` with pole
`x₀` (`Work.SimplyConnected.ABS.IsGreenOn`) and `Φ` a holomorphic modulus of `E` on `Ω`
(`Work.SimplyConnected.ABS.IsModulusOn`).  The theorem proved here produces a biholomorphism
`χ : Ω → 𝒟(0, r)` with `χ x₀ = 0` and `χ'(x₀) = 1`, extended by `0` outside `Ω` — the disc lemma
([ABS, Theorem 10]) in the form consumed by the ABS exhaustion argument.

The proof has three ingredients.

* `E > 0` and harmonic on `Ω ∖ {x₀}`, with superlevel sets relatively compact in `Ω`, forces `Ω` to be
  connected (`Work.SimplyConnected.ABS.isPreconnected_of_isGreenOn`): on a non-compact component of
  `Ω` a positive harmonic function cannot tend to `0` at the ideal boundary.
* On the open sub-surface `↥Ω`, the modulus `Φ` is a holomorphic map into the unit disc which is
  *proper into the disc* (the preimage of a compact subset of the disc is contained in a compact
  subset of `Ω` union `{x₀}`, by `‖Φ‖ = exp (-E)`) and whose only zero is the simple zero at `x₀`;
  the Commons lemma
  `Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero` then makes
  `Φ` a bijection onto the unit disc.
* Rescaling `Φ` by the inverse of its chart derivative at `x₀` normalises the derivative to `1` and
  turns the unit disc into the disc of radius `‖c‖`.

The only transport between the surface `X` and its open sub-surface `↥Ω` is the fact that the chart of
an open subset at a point is the restriction of the ambient chart
(`TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Chart bookkeeping for an open subset -/

/-- The chart of an open subset `U` at a point `x` agrees, at `x`, with the ambient chart at `x`. -/
theorem subtypeChartAt_apply {U : TopologicalSpace.Opens X} (x : ↥U) :
    (chartAt ℂ x) x = (chartAt ℂ (x : X)) (x : X) := by
  rw [TopologicalSpace.Opens.chartAt_eq (x := x), OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The pullback of a function by the chart of an open subset at `x` is, near the relevant point,
the pullback by the ambient chart at `x`. -/
theorem subtypeChart_eventuallyEq {U : TopologicalSpace.Opens X} {Φ : X → ℂ} (x : ↥U) :
    ((fun ξ : ↥U => Φ ξ) ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝 ((chartAt ℂ (x : X)) (x : X))] (Φ ∘ (chartAt ℂ (x : X)).symm) := by
  have h := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) U (x := x)
  filter_upwards [h] with w hw
  simp only [Function.comp_apply] at hw ⊢
  rw [← hw]

/-- **Transport of holomorphy to an open sub-surface.** -/
theorem subtypeHolomorphicOnXAt {U : TopologicalSpace.Opens X} {Φ : X → ℂ} (x : ↥U)
    (h : Submission.HolomorphicOnXAt Φ (x : X)) :
    Submission.HolomorphicOnXAt (X := ↥U) (fun ξ : ↥U => Φ ξ) x := by
  rw [Submission.HolomorphicOnXAt] at h ⊢
  rw [subtypeChartAt_apply x]
  exact h.congr (subtypeChart_eventuallyEq (Φ := Φ) x).symm

/-- **The chart derivative is the same on an open sub-surface as on the ambient surface.** -/
theorem subtypeDerivChart_eq {U : TopologicalSpace.Opens X} {Φ : X → ℂ} (x : ↥U) :
    deriv ((fun ξ : ↥U => Φ ξ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      = deriv (Φ ∘ (chartAt ℂ (x : X)).symm) ((chartAt ℂ (x : X)) (x : X)) := by
  rw [subtypeChartAt_apply x]
  exact (subtypeChart_eventuallyEq (Φ := Φ) x).deriv_eq

/-! ## Consequences of `IsModulusOn` at the pole -/

/-- The modulus vanishes at the pole: `Φ x₀ = 0`. -/
theorem phi_zero_of_isModulusOn {Ω : Set X} {x₀ : X} {E : X → ℝ} {Φ : X → ℂ}
    (hx₀ : x₀ ∈ Ω) (hΦ : IsModulusOn Ω x₀ E Φ) : Φ x₀ = 0 := by
  set c := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  obtain ⟨H, hHana, -, hev⟩ := hΦ.2.1
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have htend_c : Tendsto c.symm (𝓝 a) (𝓝 x₀) := c.tendsto_symm hsrc
  have htend1 : Tendsto (Φ ∘ c.symm) (𝓝 a) (𝓝 (Φ x₀)) :=
    ((hΦ.1 x₀ hx₀).continuousAt).tendsto.comp htend_c
  have htend2 : Tendsto (Φ ∘ c.symm) (𝓝 a) (𝓝 0) := by
    have hmul : Tendsto (fun w : ℂ => (w - a) * H w) (𝓝 a) (𝓝 ((a - a) * H a)) :=
      ((tendsto_id.sub tendsto_const_nhds).mul hHana.continuousAt)
    have h0 : ((a - a) * H a) = 0 := by simp
    rw [h0] at hmul
    exact hmul.congr' hev.symm
  exact tendsto_nhds_unique htend1 htend2

/-- The chart derivative of the modulus at the pole does not vanish. -/
theorem deriv_ne_zero_of_isModulusOn {Ω : Set X} {x₀ : X} {E : X → ℝ} {Φ : X → ℂ}
    (hΦ : IsModulusOn Ω x₀ E Φ) :
    deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 :=
  Submission.phi_deriv_ne_zero_of_logPole hΦ.2.1

/-- The image of the unit ball of `ℂ` under multiplication by `c ≠ 0` is the ball of radius
`‖c‖`. -/
theorem image_mul_ball (c : ℂ) (hc : c ≠ 0) :
    (fun z : ℂ => c * z) '' Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) ‖c‖ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    rw [norm_mul]
    calc ‖c‖ * ‖w‖ < ‖c‖ * 1 := by
          exact mul_lt_mul_of_pos_left hw (norm_pos_iff.mpr hc)
      _ = ‖c‖ := mul_one _
  · intro hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    refine ⟨z / c, ?_, by field_simp⟩
    rw [Metric.mem_ball, dist_zero_right, norm_div]
    rw [div_lt_one (norm_pos_iff.mpr hc)]
    exact hz

end Work.SimplyConnected.ABS

namespace Work.SimplyConnected.ABS

/-- **The disc lemma from a Green function and its holomorphic modulus.**  If `Ω ⊆ X` is an open
domain in a Riemann surface, `x₀ ∈ Ω`, `E` is the Green function of `Ω` with pole `x₀` and `Φ` a
holomorphic modulus of `E` on `Ω`, then there is a normalised biholomorphism of `Ω` onto a disc:
a holomorphic `χ` on `Ω`, injective on `Ω`, with `χ x₀ = 0`, chart derivative `1` at `x₀`,
`χ '' Ω = Metric.ball 0 r` for some `r > 0`, and `χ = 0` outside `Ω`.

(Anghel–Bruin–Stan, *Uniformization of Riemann surfaces revisited*, Theorem 10.) -/
theorem exists_biholomorphicOn_of_greenOn_modulus {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {Ω : Set X} (hΩo : IsOpen Ω) (hΩne : Ω ≠ Set.univ)
    (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω)
    {E : X → ℝ} {Φ : X → ℂ}
    (hE : Work.SimplyConnected.ABS.IsGreenOn Ω x₀ E)
    (hΦ : Work.SimplyConnected.ABS.IsModulusOn Ω x₀ E Φ) :
    ∃ (r : ℝ) (χ : X → ℂ), 0 < r ∧ (∀ x ∈ Ω, Submission.HolomorphicOnXAt χ x) ∧
      Set.InjOn χ Ω ∧ χ x₀ = 0 ∧ χ '' Ω = Metric.ball (0 : ℂ) r ∧
      deriv (χ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 ∧ (∀ x ∉ Ω, χ x = 0) := by
  classical
  -- ### Step 1: `Ω` is connected (a Green function cannot live on a non-compact component).
  have hΩpre : IsPreconnected Ω := isPreconnected_of_isGreenOn hΩo hΩne hE
  obtain ⟨hEpos, hEharm, hEsup, hEpole⟩ := hE
  obtain ⟨hΦhol, hΦpole, hΦmod⟩ := hΦ
  have hzero : Φ x₀ = 0 := phi_zero_of_isModulusOn hx₀ ⟨hΦhol, hΦpole, hΦmod⟩
  have hDne : deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 :=
    deriv_ne_zero_of_isModulusOn ⟨hΦhol, hΦpole, hΦmod⟩
  -- ### Step 2: the modulus, restricted to `Ω`, is a bijection onto the unit disc.
  let U : TopologicalSpace.Opens X := ⟨Ω, hΩo⟩
  haveI : ConnectedSpace ↥U := isConnected_iff_connectedSpace.mp ⟨⟨x₀, hx₀⟩, hΩpre⟩
  let ξ₀ : ↥U := ⟨x₀, hx₀⟩
  let Φ' : ↥U → ℂ := fun ξ => Φ ξ
  have hposU : ∀ ξ : ↥U, ξ ≠ ξ₀ → 0 < E ξ :=
    fun ξ hξ => hEpos ξ ξ.2 (fun h => hξ (Subtype.ext h))
  have hmodU : ∀ ξ : ↥U, ξ ≠ ξ₀ → ‖Φ' ξ‖ = Real.exp (-(E ξ)) :=
    fun ξ hξ => hΦmod ξ ξ.2 (fun h => hξ (Subtype.ext h))
  have hzeroU : Φ' ξ₀ = 0 := hzero
  have hmaps : ∀ ξ : ↥U, Φ' ξ ∈ Metric.ball (0 : ℂ) 1 :=
    fun ξ => Submission.phi_mem_ball hposU hmodU hzeroU ξ
  have hholU : ∀ ξ : ↥U, Submission.HolomorphicOnXAt Φ' ξ :=
    fun ξ => subtypeHolomorphicOnXAt ξ (hΦhol ξ ξ.2)
  have hfib : Φ' ⁻¹' {0} = {ξ₀} := Submission.phi_preimage_zero hposU hmodU hzeroU
  have hloc : deriv (Φ' ∘ (chartAt ℂ ξ₀).symm) ((chartAt ℂ ξ₀) ξ₀) ≠ 0 := by
    rw [subtypeDerivChart_eq (Φ := Φ) ξ₀]
    exact hDne
  -- ### Step 3: properness of `Φ` into the disc.
  have hprop : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 →
      IsCompact (Φ' ⁻¹' K) := by
    intro K hK hKsub
    set S : Set X := {x : X | x ∈ U ∧ Φ x ∈ K} with hSdef
    have himg : (Subtype.val '' (Φ' ⁻¹' K) : Set X) = S := by
      ext x; constructor
      · rintro ⟨ξ, hξ, rfl⟩; exact ⟨ξ.2, hξ⟩
      · rintro ⟨hxU, hxK⟩; exact ⟨⟨x, hxU⟩, hxK, rfl⟩
    have hScomp : IsCompact S := by
      rcases K.eq_empty_or_nonempty with rfl | hne
      · have hSe : S = ∅ := by
          ext x; simp [hSdef]
        rw [hSe]; exact isCompact_empty
      obtain ⟨w₀, hw₀K, hw₀max⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
      set r : ℝ := ‖w₀‖ with hrdef
      have hrlt : r < 1 := by
        have h := hKsub hw₀K
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
        exact h
      have hrle : 0 ≤ r := norm_nonneg w₀
      rcases eq_or_ne r 0 with hr0 | hrne
      · -- the value `0` is the only norm attained on `K`
        have hKsub' : K ⊆ ({0} : Set ℂ) := by
          intro z hz
          have h1 : ‖z‖ ≤ r := hw₀max hz
          rw [hr0] at h1
          simp only [Set.mem_singleton_iff]
          exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg z))
        have h0K : (0 : ℂ) ∈ K := by
          obtain ⟨z, hz⟩ := hne
          have hz0 : z = 0 := by simpa using hKsub' hz
          rwa [← hz0]
        have hSeq : S = {x₀} := by
          ext x; constructor
          · rintro ⟨hxU, hxK⟩
            rw [Set.mem_singleton_iff]
            have h0 : Φ x = 0 := hKsub' hxK
            by_contra hxne
            have h1 := hΦmod x hxU hxne
            rw [h0, norm_zero] at h1
            have h2 := Real.exp_pos (-(E x))
            linarith
          · intro hx
            rw [Set.mem_singleton_iff] at hx
            subst hx
            exact ⟨hx₀, by rw [hzero]; exact h0K⟩
        rw [hSeq]; exact isCompact_singleton
      · have hrpos : 0 < r := lt_of_le_of_ne hrle (Ne.symm hrne)
        have hlog : Real.log r < 0 := Real.log_neg hrpos hrlt
        set ε : ℝ := -Real.log r with hεdef
        have hεpos : 0 < ε := by rw [hεdef, neg_pos]; exact hlog
        obtain ⟨K', hK'c, hK'sub, hK'⟩ := hEsup ε hεpos
        set Kh : Set X := K' ∪ {x₀} with hKhdef
        have hKhc : IsCompact Kh := hK'c.union isCompact_singleton
        have hKhclosed : IsClosed Kh := hKhc.isClosed
        have hSsub : S ⊆ Kh := by
          rintro x ⟨hxU, hxK⟩
          by_cases hxx : x = x₀
          · exact Or.inr hxx
          · refine Or.inl ?_
            by_contra hxK'
            have h2 : E x < ε := hK' x hxU hxK'
            have h3 : ‖Φ x‖ = Real.exp (-(E x)) := hΦmod x hxU hxx
            have h4 : ‖Φ x‖ ≤ r := hw₀max hxK
            have h5 : Real.exp (-ε) = r := by
              rw [hεdef, neg_neg, Real.exp_log hrpos]
            have h6 : Real.exp (-ε) < Real.exp (-(E x)) := Real.exp_lt_exp.mpr (by linarith)
            rw [h5, ← h3] at h6
            linarith
        have hSclosed : IsClosed S := by
          rw [← closure_subset_iff_isClosed]
          intro x hx
          have hxmem : x ∈ Kh := by
            have h1 : x ∈ closure Kh := closure_mono hSsub hx
            rwa [hKhclosed.closure_eq] at h1
          have hxU : x ∈ U := by
            rcases hxmem with h | h
            · exact hK'sub h
            · rw [Set.mem_singleton_iff] at h
              rw [h]
              exact hx₀
          refine ⟨hxU, ?_⟩
          haveI : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
          have hcont : ContinuousAt Φ x := (hΦhol x hxU).continuousAt
          have hev : ∀ᶠ z in 𝓝[S] x, Φ z ∈ K :=
            Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => hz.2)
          exact hK.isClosed.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
        exact hKhc.of_isClosed_subset hSclosed hSsub
    exact Subtype.isCompact_iff.mpr (by rw [himg]; exact hScomp)
  -- ### Step 4: the bijection.
  have hbij : Function.Bijective
      (fun ξ : ↥U => (⟨Φ' ξ, hmaps ξ⟩ : Metric.ball (0 : ℂ) 1)) :=
    Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero
      (Φ := Φ') (z₀ := ξ₀) hmaps hprop hholU hfib hloc
  have himage : Φ '' Ω = Metric.ball (0 : ℂ) 1 := by
    ext w; constructor
    · rintro ⟨x, hx, rfl⟩; exact hmaps ⟨x, hx⟩
    · intro hw
      obtain ⟨ξ, hξ⟩ := hbij.2 ⟨w, hw⟩
      exact ⟨ξ, ξ.2, congrArg Subtype.val hξ⟩
  have hinj : Set.InjOn Φ Ω := by
    intro a ha b hb hab
    have h1 : (⟨Φ' ⟨a, ha⟩, hmaps ⟨a, ha⟩⟩ : Metric.ball (0 : ℂ) 1)
        = ⟨Φ' ⟨b, hb⟩, hmaps ⟨b, hb⟩⟩ := Subtype.ext hab
    exact congrArg Subtype.val (hbij.1 h1)
  -- ### Step 5: rescale and extend by `0`.
  let D : ℂ := deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
  let c : ℂ := D⁻¹
  have hDne' : D ≠ 0 := hDne
  have hcne : c ≠ 0 := inv_ne_zero hDne'
  have hDc : c * D = 1 := inv_mul_cancel₀ hDne'
  refine ⟨‖c‖, fun y => if y ∈ Ω then c * Φ y else 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact norm_pos_iff.mpr hcne
  · -- holomorphy on `Ω`
    intro y hy
    have hev : (fun z : X => if z ∈ Ω then c * Φ z else 0) =ᶠ[𝓝 y] (fun z => c * Φ z) :=
      Filter.eventually_of_mem (hΩo.mem_nhds hy) (fun z hz => by simp [hz])
    have htend : Tendsto (chartAt ℂ y).symm (𝓝 ((chartAt ℂ y) y)) (𝓝 y) :=
      (chartAt ℂ y).tendsto_symm (mem_chart_source ℂ y)
    have hev' : ((fun z : X => if z ∈ Ω then c * Φ z else 0) ∘ (chartAt ℂ y).symm)
        =ᶠ[𝓝 ((chartAt ℂ y) y)] ((fun z => c * Φ z) ∘ (chartAt ℂ y).symm) :=
      htend.eventually hev
    exact ((hΦhol y hy).const_mul c).congr hev'.symm
  · -- injectivity on `Ω`
    intro a ha b hb hab
    simp only [if_pos ha, if_pos hb] at hab
    exact hinj ha hb (mul_left_cancel₀ hcne hab)
  · -- value at the pole
    simp only [if_pos hx₀, hzero, mul_zero]
  · -- the image is the disc of radius `‖c‖`
    have h1 : (fun y : X => if y ∈ Ω then c * Φ y else 0) '' Ω
        = (fun y : X => c * Φ y) '' Ω :=
      Set.image_congr (fun y hy => by simp [hy])
    have h2 : (fun y : X => c * Φ y) '' Ω = (fun z : ℂ => c * z) '' (Φ '' Ω) := by
      rw [Set.image_image]
    rw [h1, h2, himage, image_mul_ball c hcne]
  · -- the derivative at the pole is `1`
    have htend : Tendsto (chartAt ℂ x₀).symm (𝓝 ((chartAt ℂ x₀) x₀)) (𝓝 x₀) :=
      (chartAt ℂ x₀).tendsto_symm (mem_chart_source ℂ x₀)
    have hev : ((fun z : X => if z ∈ Ω then c * Φ z else 0) ∘ (chartAt ℂ x₀).symm)
        =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)] (fun w : ℂ => c * (Φ ∘ (chartAt ℂ x₀).symm) w) := by
      filter_upwards [htend.eventually (hΩo.eventually_mem hx₀)] with w hw
      simp only [Function.comp_apply, if_pos hw]
    rw [hev.deriv_eq]
    have hmul : deriv (fun w : ℂ => c * (Φ ∘ (chartAt ℂ x₀).symm) w)
        ((chartAt ℂ x₀) x₀)
        = c * deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) :=
      deriv_const_mul c ((hΦhol x₀ hx₀).differentiableAt)
    rw [hmul]
    exact hDc
  · -- vanishing outside `Ω`
    intro x hx
    simp only [if_neg hx]

end Work.SimplyConnected.ABS
