import Mathlib
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.RiemannSphere
import Submission.Work.BoxShrink.PinchOff.exists_untop_continuous
import Submission.Work.BoxShrink.PinchOff.mem_range_E_of_mem_unboundedSide
import Submission.Work.BoxShrink.PinchOff.exists_delta_infDist_lt
import Submission.Work.BoxShrink.PinchOff.exists_push_small

namespace Work.BoxShrink.PinchOff

open Set

noncomputable section


/-- **Pushing the plane off a Jordan curve, into the unbounded side.**

`c` is a simple closed plane curve with separation datum `h` (`h.U` the unbounded side, `h.V` the
bounded side).  `E` is a parametrisation of the *outer* closed disc, valued in the Riemann sphere:
a continuous injection of the model disc whose boundary circle maps to `c` (in the given
parametrisation), whose marked interior point `u₀` maps to `∞`, and whose open disc minus `u₀` maps
into the unbounded side `h.U`.

The conclusion: for every `ε > 0` there is a continuous `ψ : ℂ → ℂ` which moves every point by at
most `ε`, fixes every point at distance `≥ ε` from the curve, and sends every point that is not in
the bounded side `h.V` (in particular every point of the curve and of the unbounded side) into the
unbounded side `h.U`.

Note (both reviewers): the naive formula `ψ z = E ((1-σ)w + σ u₀)` on the image of `E` extended by
the identity off it is *not* continuous at the curve: the third conjunct forces curve points to move
while points of `h.V` nearby must also move.  A working construction: prescribe `ψ = id` on
`{Metric.infDist · (range c.γ) ≥ ε}` (which lies in `E '' {‖w‖ ≤ 1-δ}` for a suitable `δ`), prescribe
`ψ z = E ((1-σ(‖w‖)) w + σ(‖w‖) u₀)` for `z = E w` on the closed piece `h.U ∪ range c.γ`, check the two
prescriptions agree on the overlap, and extend the difference `ψ - id` to all of `ℂ` with values in
the closed ball of radius `ε/4` (Tietze; `arc_not_separate.lean` in `JordanSeparation` uses Tietze),
then set `ψ := id + h̃` and adjust with a radial retraction. -/
theorem jordan_push
    {c : Work.Smooth.Jordan.PlaneCurve} (h : Work.Smooth.Jordan.PlaneSeparation c)
    (u₀ : Work.Smooth.Jordan.Disc) (hu₀ : ‖(u₀ : ℂ)‖ < 1)
    (E : Work.Smooth.Jordan.Disc → OnePoint ℂ) (hE : Continuous E) (hEinj : Function.Injective E)
    (hEb : ∀ θ : ℝ, E (Work.Smooth.Jordan.circlePoint θ) = ((c.γ θ : ℂ) : OnePoint ℂ))
    (hEu₀ : E u₀ = OnePoint.infty)
    (hEopen : ∀ w : Work.Smooth.Jordan.Disc, ‖(w : ℂ)‖ < 1 → w ≠ u₀ →
      ∃ z : ℂ, E w = (z : OnePoint ℂ) ∧ z ∈ h.U) :
    ∀ ε : ℝ, 0 < ε → ∃ ψ : ℂ → ℂ, Continuous ψ ∧
      (∀ z : ℂ, ‖ψ z - z‖ ≤ ε) ∧
      (∀ z : ℂ, ε ≤ Metric.infDist z (Set.range c.γ) → ψ z = z) ∧
      (∀ z : ℂ, (z ∈ h.U ∨ ∃ θ : ℝ, z = c.γ θ) → ψ z ∈ h.U) := by
  -- The construction, in four steps (each of the first three is a separate lemma in this
  -- directory).
  --
  -- 1. `mem_range_E_of_mem_unboundedSide`: `E` covers the whole unbounded side.  (This is the
  --    "clopen" argument: `E '' 𝔻` is compact, hence closed in the sphere, and it is contained in
  --    `↑''U ∪ ↑''(range c.γ) ∪ {∞}`; the open set `S² \ E '' 𝔻` cuts `↑''U` into a clopen piece
  --    which is not all of `↑''U`, so it is empty.)
  -- 2. `exists_delta_infDist_lt`: there is `δ > 0` with `‖u₀‖ < 1 - δ` such that the preimage of
  --    the "far" region `{z | ε ≤ infDist z (range c.γ)}` lies in `{‖w‖ ≤ 1 - δ}`.
  -- 3. `exists_push_small`: a continuous push `φ : 𝔻 → 𝔻` fixing `{‖w‖ ≤ 1 - δ}`, sending `𝔻` into
  --    the open disc and avoiding `u₀` (so that `E ∘ φ` takes values in the finite part, indeed in
  --    `h.U`), and moving the image under `E` by at most `ε/4`.
  -- 4. The prescription `ψ := E ∘ φ ∘ E⁻¹` on the closed set `F = h.U ∪ range c.γ` agrees with the
  --    identity on `F ∩ {infDist · (range c.γ) ≥ ε}` by 2. and 3.; Tietze extends the difference
  --    `ψ - id` (prescribed on the closed set `F ∪ {infDist · (range c.γ) ≥ ε}`, with values in
  --    the closed ball of radius `ε/4`) to all of `ℂ`, and we set `ψ := id + (that extension)`.
  intro ε hε
  classical
  have hrange := mem_range_E_of_mem_unboundedSide h hE hEinj hEb hEu₀ hEopen
  obtain ⟨δ, hδpos, hu₀δ, hδbad⟩ := exists_delta_infDist_lt h hε hE hEb hEu₀
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨φ, hφc, hφfix, hφball, hφne, hφmove⟩ :=
    exists_push_small hδpos hε hu₀δ hE hEinj hEu₀ hEopen
  obtain ⟨u, hu, huc⟩ := exists_untop_continuous
  let T : Set ℂ := {z : ℂ | ε ≤ Metric.infDist z (Set.range c.γ)}
  let F : Set ℂ := h.U ∪ Set.range c.γ
  have hTclosed : IsClosed T :=
    isClosed_le continuous_const (Metric.continuous_infDist_pt (Set.range c.γ))
  have hFcompl : Fᶜ = h.V := by
    ext z
    constructor
    · intro hz
      have hz' : z ∉ h.U ∧ z ∉ Set.range c.γ := by
        simpa [F] using hz
      have hV : z ∈ h.U ∪ h.V := by rw [h.union_eq]; exact hz'.2
      rcases hV with h' | h'
      · exact absurd h' hz'.1
      · exact h'
    · intro hz
      have hz' : z ∉ h.U ∧ z ∉ Set.range c.γ := by
        refine ⟨fun h1 => Set.disjoint_left.mp h.disjoint_UV h1 hz, fun h1 => ?_⟩
        have hVsub : h.V ⊆ c.traceᶜ := by
          intro y hy; rw [← h.union_eq]; exact Or.inr hy
        exact (hVsub hz) h1
      simpa [F] using hz'
  have hFclosed : IsClosed F := by
    rw [← isOpen_compl_iff]
    rw [hFcompl]
    exact h.isOpen_V
  have hGclosed : IsClosed (F ∪ T) := hFclosed.union hTclosed
  have hmemE : ∀ z : ℂ, z ∈ F → (z : OnePoint ℂ) ∈ Set.range E := by
    intro z hz
    have hz' : z ∈ h.U ∨ z ∈ Set.range c.γ := by simpa [F] using hz
    rcases hz' with h1 | h1
    · obtain ⟨w, hw⟩ := hrange z h1; exact ⟨w, hw⟩
    · obtain ⟨θ, rfl⟩ := h1; exact ⟨Work.Smooth.Jordan.circlePoint θ, hEb θ⟩
  have hEmb : Topology.IsEmbedding E := (hE.isClosedEmbedding hEinj).toIsEmbedding
  let eH : Work.Smooth.Jordan.Disc ≃ₜ Set.range E := hEmb.toHomeomorph
  have hEeH : ∀ w : Work.Smooth.Jordan.Disc,
      ((eH w : Set.range E) : OnePoint ℂ) = E w :=
    fun w => Topology.IsEmbedding.toHomeomorph_apply_coe hEmb w
  let pre : F → Work.Smooth.Jordan.Disc := fun z => eH.symm ⟨(z : ℂ), hmemE z z.2⟩
  have hpreE : ∀ z : F, E (pre z) = (z : OnePoint ℂ) := by
    intro z
    have h1 : eH (pre z) = ⟨(z : ℂ), hmemE z z.2⟩ := eH.apply_symm_apply _
    have h2 := hEeH (pre z)
    rw [h1] at h2
    exact h2.symm
  let Ψ : F → OnePoint ℂ := fun z => E (φ (pre z))
  have hcoF : Continuous (fun z : F => (z : ℂ)) := continuous_subtype_val
  have htoRange : Continuous (fun z : F => (⟨(z : ℂ), hmemE z z.2⟩ : Set.range E)) :=
    Continuous.subtype_mk (OnePoint.continuous_coe.comp hcoF) (fun z => hmemE z z.2)
  have hΨc : Continuous Ψ := hE.comp (hφc.comp (eH.symm.continuous.comp htoRange))
  have hΨU : ∀ z : F, ∃ y ∈ h.U, Ψ z = (y : OnePoint ℂ) := by
    intro z
    have hne : pre z ≠ u₀ := by
      intro hh
      have hcc : ((z : ℂ) : OnePoint ℂ) = OnePoint.infty := by
        rw [← hpreE z, hh, hEu₀]
      exact OnePoint.coe_ne_infty (z : ℂ) hcc
    have hne' : φ (pre z) ≠ u₀ := by
      intro hcon
      exact hφne (pre z) (fun hh => hne (Subtype.ext hh)) (congrArg Subtype.val hcon)
    obtain ⟨y, hy1, hy2⟩ := hEopen (φ (pre z)) (hφball (pre z)) hne'
    exact ⟨y, hy2, by show E (φ (pre z)) = ((y : ℂ) : OnePoint ℂ); exact hy1⟩
  let val : F → ℂ := fun z => Classical.choose (hΨU z)
  have hvalcoe : ∀ z : F, (val z : OnePoint ℂ) = Ψ z :=
    fun z => ((Classical.choose_spec (hΨU z)).2).symm
  have hvalmem : ∀ z : F, val z ∈ h.U :=
    fun z => (Classical.choose_spec (hΨU z)).1
  have hΨne : ∀ z : F, Ψ z ≠ OnePoint.infty := by
    intro z
    rw [← hvalcoe z]
    exact OnePoint.coe_ne_infty (val z)
  have hvalc : Continuous val := by
    have h1 : val = fun z : F => u (Ψ z) := by
      funext z
      exact OnePoint.coe_injective ((hvalcoe z).trans (hu (Ψ z) (hΨne z)).symm)
    rw [h1]
    exact continuous_iff_continuousAt.mpr
      (fun z => (huc (Ψ z) (hΨne z)).comp hΨc.continuousAt)
  have hvalT : ∀ x : F, (x : ℂ) ∈ T → val x = (x : ℂ) := by
    intro x hx
    have hw : ‖(pre x : ℂ)‖ < 1 - δ := by
      by_contra h
      exact hδbad (pre x) (le_of_not_gt h) ⟨(x : ℂ), hpreE x, hx⟩
    have hfix := hφfix (pre x) (le_of_lt hw)
    have hcoe : (val x : OnePoint ℂ) = ((x : ℂ) : OnePoint ℂ) := by
      rw [hvalcoe x]
      show E (φ (pre x)) = ((x : ℂ) : OnePoint ℂ)
      rw [hfix, hpreE x]
    exact OnePoint.coe_injective hcoe
  set f₁ : ℂ → ℂ := fun z => if hz : z ∈ F then val ⟨z, hz⟩ - z else 0 with hf₁
  have hf₁_in : ∀ z (hz : z ∈ F), f₁ z = val ⟨z, hz⟩ - z := by
    intro z hz
    simp only [hf₁, dif_pos hz]
  have hf₁_out : ∀ z (hz : z ∉ F), f₁ z = 0 := by
    intro z hz
    simp only [hf₁, dif_neg hz]
  have hf₁F : ContinuousOn f₁ F := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : F.domRestrict f₁ = fun x : F => val x - (x : ℂ) := by
      funext x
      show f₁ (x : ℂ) = val x - (x : ℂ)
      rw [hf₁_in (x : ℂ) x.2]
    rw [hEq]
    exact hvalc.sub continuous_subtype_val
  have hf₁T : ContinuousOn f₁ T := by
    refine ContinuousOn.congr (f := fun _ : ℂ => (0 : ℂ)) continuousOn_const ?_
    intro z hz
    by_cases hzF : z ∈ F
    · rw [hf₁_in z hzF]
      have hvz : val ⟨z, hzF⟩ = z := hvalT ⟨z, hzF⟩ hz
      rw [hvz, sub_self]
    · rw [hf₁_out z hzF]
  have hf₁G : ContinuousOn f₁ (F ∪ T) := by
    rw [continuousOn_union_iff_of_isClosed hFclosed hTclosed]
    exact ⟨hf₁F, hf₁T⟩
  have fcont : Continuous (fun x : ↥(F ∪ T) => f₁ (x : ℂ)) :=
    hf₁G.comp_continuous continuous_subtype_val (fun x => x.2)
  have hballf : ∀ x : ↥(F ∪ T), f₁ (x : ℂ) ∈ Metric.closedBall (0 : ℂ) (ε / 4) := by
    intro x
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_cases hxF : (x : ℂ) ∈ F
    · rw [hf₁_in (x : ℂ) hxF]
      obtain ⟨a, ha, hda⟩ := hφmove (pre ⟨(x : ℂ), hxF⟩) (x : ℂ) (hpreE ⟨(x : ℂ), hxF⟩)
      have hvala : val ⟨(x : ℂ), hxF⟩ = a := by
        apply OnePoint.coe_injective
        rw [hvalcoe]
        show E (φ (pre ⟨(x : ℂ), hxF⟩)) = ((a : ℂ) : OnePoint ℂ)
        exact ha
      rw [hvala, sub_zero]
      exact hda
    · rw [hf₁_out (x : ℂ) hxF]
      simp only [sub_zero, norm_zero]
      linarith
  haveI hTietze : TietzeExtension ↥(Metric.closedBall (0 : ℂ) (ε / 4)) :=
    Metric.instTietzeExtensionClosedBall ℝ (0 : ℂ) hε4
  obtain ⟨g', hg'mem, hg'restr⟩ := ContinuousMap.exists_forall_mem_restrict_eq (X := ℂ)
    hGclosed ⟨fun x : ↥(F ∪ T) => f₁ (x : ℂ), fcont⟩ hballf
  have hg' : ∀ x : ↥(F ∪ T), g' x = f₁ (x : ℂ) :=
    fun x => DFunLike.congr_fun hg'restr x
  refine ⟨fun z => z + g' z, ?_, ?_, ?_, ?_⟩
  · exact continuous_id.add g'.continuous
  · intro z
    show ‖z + g' z - z‖ ≤ ε
    have h := hg'mem z
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    calc ‖z + g' z - z‖ = ‖g' z‖ := by rw [add_sub_cancel_left]
      _ ≤ ε / 4 := by simpa using h
      _ ≤ ε := by linarith
  · intro z hz
    show z + g' z = z
    have hkey : g' z = f₁ z := hg' ⟨z, Or.inr hz⟩
    rw [hkey]
    by_cases hzF : z ∈ F
    · rw [hf₁_in z hzF]
      have hvz : val ⟨z, hzF⟩ = z := hvalT ⟨z, hzF⟩ hz
      rw [hvz]
      ring
    · rw [hf₁_out z hzF]
      ring
  · intro z hz
    show z + g' z ∈ h.U
    have hzF : z ∈ F := by
      rcases hz with h | ⟨θ, hθ⟩
      · exact Or.inl h
      · exact Or.inr ⟨θ, hθ.symm⟩
    have hkey : g' z = f₁ z := hg' ⟨z, Or.inl hzF⟩
    rw [hkey, hf₁_in z hzF]
    have : z + (val ⟨z, hzF⟩ - z) = val ⟨z, hzF⟩ := by ring
    rw [this]
    exact hvalmem ⟨z, hzF⟩


end

end Work.BoxShrink.PinchOff
