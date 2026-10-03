import Mathlib

/-!
# Discreteness of a fibre of a holomorphic map from the saturation of one component

Piece HB of the Horn/basin development (Shishikura, Prop. 5.3 / Lemma 5.4).

Let `g : ℂ → ℂ` be holomorphic on an open set `D` and let `v ∈ ℂ`, `ρ > 0`.  Suppose that
whenever `z ∈ D` is mapped by `g` into the disc `ball v ρ`, the corresponding connected component
`C_z` of `D ∩ g ⁻¹' ball v ρ` is *saturated* over the disc, i.e. `ball v ρ ⊆ g '' C_z`
(hypothesis `himg`; this is the "finite local monodromy over `v`" property `LF_v` produced by
`Work.Horn.HB.lf_component_image`).  Then the fibre `g ⁻¹' {v} ∩ W` is discrete (for any
`W ⊆ D`).

The mathematical content is the usual structure of the zeros of a non-constant holomorphic
function.  If `y ∈ g ⁻¹' {v} ∩ W` were a point at which `g` were *eventually constant* equal to
`v`, then by the identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, applied
to the connected component `C_y`) the map `g` would be identically `v` on all of `C_y`, so that
`g '' C_y = {v}`.  Combined with `himg` this would force `ball v ρ ⊆ {v}`, impossible because
`ρ > 0`.  Hence `g` is nowhere locally constant on its fibre over `v`, and the principle of
isolated zeros (`AnalyticAt.eventually_eq_or_eventually_ne`) isolates each fibre point.
-/

namespace Work.Horn.HB

open Set Metric Filter Topology

-- The hypotheses `hWopen` and `hLF` belong to the requested statement but are not needed for
-- this conclusion (the proof only uses the saturation `himg` of one component, the
-- differentiability of `g` and the openness of `D`).
set_option linter.unusedVariables false in
theorem isDiscrete_fiber_v_of_component_image {g : ℂ → ℂ} {D W : Set ℂ} {v : ℂ} {ρ : ℝ}
    (hDo : IsOpen D) (hg : DifferentiableOn ℂ g D) (hρ : 0 < ρ) (hWopen : IsOpen W) (hWD : W ⊆ D)
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v ρ → ∀ K ⊆ Metric.ball v ρ, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) x ∩ g ⁻¹' K))
    (himg : ∀ z ∈ D, g z ∈ Metric.ball v ρ →
      Metric.ball v ρ ⊆ g '' connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z) :
    IsDiscrete (g ⁻¹' {v} ∩ W) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  obtain ⟨hyg, hyW⟩ := hy
  have hyD : y ∈ D := hWD hyW
  have hgy : g y = v := hyg
  have han : AnalyticAt ℂ g y := hg.analyticAt (hDo.mem_nhds hyD)
  by_cases hloc : ∀ᶠ z in 𝓝 y, g z = v
  · -- `g` is locally constant, equal to `v`, at `y`: the identity theorem on the component of
    -- `y` in `D ∩ g ⁻¹' ball v ρ` contradicts the saturation hypothesis `himg`.
    exfalso
    let C := connectedComponentIn (D ∩ g ⁻¹' ball v ρ) y
    have hyF : y ∈ D ∩ g ⁻¹' ball v ρ := by
      refine ⟨hyD, ?_⟩
      rw [mem_preimage, hgy]
      exact mem_ball_self hρ
    have hyC : y ∈ C := mem_connectedComponentIn hyF
    have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCsubD : C ⊆ D := fun z hz => (connectedComponentIn_subset _ _ hz).1
    have hanC : AnalyticOnNhd ℂ g C := fun z hz => hg.analyticAt (hDo.mem_nhds (hCsubD hz))
    have hEq : EqOn g (fun _ => v) C :=
      hanC.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hCpre hyC hloc
    have hsub : g '' C ⊆ ({v} : Set ℂ) := by
      rintro w ⟨z, hz, rfl⟩
      exact hEq hz
    have hball := himg y hyD (by rw [hgy]; exact mem_ball_self hρ)
    have hwball : v + ((ρ / 2 : ℝ) : ℂ) ∈ ball v ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left,
        show ‖((ρ / 2 : ℝ) : ℂ)‖ = |(ρ / 2 : ℝ)| from RCLike.norm_ofReal _,
        abs_of_pos (by linarith : (0 : ℝ) < ρ / 2)]
      linarith
    have hwne : v + ((ρ / 2 : ℝ) : ℂ) ≠ v := by
      intro h
      have h1 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
        have := congrArg (fun t : ℂ => t - v) h
        simpa using this
      have h2 : (ρ / 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h1
      linarith
    exact hwne (by simpa using hsub (hball hwball))
  · -- `g` is not locally constant at `y`: the fibre is isolated at `y`.
    have hne : ∀ᶠ z in 𝓝[≠] y, g z ≠ v :=
      (han.eventually_eq_or_eventually_ne (analyticAt_const (v := v) (x := y))).resolve_left hloc
    rw [eventually_nhdsWithin_iff] at hne
    obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hne
    refine ⟨ball y ε, isOpen_ball, ?_⟩
    ext z
    constructor
    · rintro ⟨hz1, hz2, _⟩
      rw [mem_singleton_iff]
      by_contra hzy
      exact hε hz1 hzy hz2
    · intro hz
      rw [mem_singleton_iff] at hz
      subst hz
      exact ⟨mem_ball_self hεpos, hgy, hyW⟩

end Work.Horn.HB
