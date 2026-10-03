import Mathlib
import Submission.Work.Horn.exists_ball_injOn_and_mapsTo
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn

/-!
# `φ ∘ f` is locally injective and locally surjective off the critical value `v`

Let `B ⊆ ℂ` be open, `f : ℂ → ℂ` holomorphic on `B` and mapping `B` into itself, all of whose
critical values in `B` equal a fixed value `v` (`hcritval`), and let `φ` be a holomorphic
injection of `B` (in the intended application, the Riemann map of the immediate basin of a
parabolic germ).  Then for every `x ∈ B` with `f x ≠ v` the composite `z ↦ φ (f z)` is a local
homeomorphism at `x`: there are arbitrarily small radii `ρ` on which it is injective, and whose
image contains a ball around `φ (f x)`.

The two inputs are the inverse function theorem in ball form
(`Work.Horn.exists_ball_injOn_and_mapsTo`), which only needs `deriv ≠ 0` at the center:

* for `f` at `x`: `hcritval` turns `f x ≠ v` into `deriv f x ≠ 0`, so `f` maps a ball around `x`
  onto a ball around `f x`; points of the image are `≠ v` after shrinking, so the preimage point
  found lies in `B \ f ⁻¹' {v}`;
* for `φ` at `f x`: injectivity of `φ` on the open set `B` forces `deriv φ (f x) ≠ 0`
  (`Work.Parab.inversion.deriv_ne_zero_of_injOn`), so `φ` maps a ball around `f x` onto a ball
  around `φ (f x)`.

Injectivity of `φ ∘ f` then follows from injectivity of `f` on that ball together with injectivity
of `φ` on `B`, and surjectivity by composing the two surjectivities — for this the radius of the
`φ`-ball is chosen smaller than the radius of the ball already known to be contained in the
`f`-image.
-/

namespace Work.HornSeq

open Set Metric
open scoped Topology

/-- **Local surjectivity of an injective holomorphic map.**  If `φ` is holomorphic and injective on
the open set `B` and `y ∈ B`, then for every `ε > 0` there are `ρ ∈ (0, ε)` with `ball y ρ ⊆ B` and
`δ > 0` with `ball (φ y) δ ⊆ φ '' (ball y ρ ∩ B)`.

Injectivity on the open set `B` makes `deriv φ y ≠ 0` (`deriv_ne_zero_of_injOn`), so this is the
inverse function theorem in ball form (`exists_ball_injOn_and_mapsTo`) with the domain of the image
restricted to `B` (which is harmless because `ball y ρ ⊆ B`). -/
theorem ball_subset_image_ball_of_injOn_analytic {B : Set ℂ} {φ : ℂ → ℂ}
    (hB : IsOpen B) (hφana : ∀ z ∈ B, AnalyticAt ℂ φ z) (hφinj : Set.InjOn φ B)
    {y : ℂ} (hy : y ∈ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ ρ < ε ∧ 0 < δ ∧ Metric.ball y ρ ⊆ B ∧
      Metric.ball (φ y) δ ⊆ φ '' (Metric.ball y ρ ∩ B) := by
  have hφdiff : DifferentiableOn ℂ φ B :=
    fun z hz => (hφana z hz).differentiableAt.differentiableWithinAt
  have hne : deriv φ y ≠ 0 :=
    Work.Parab.inversion.deriv_ne_zero_of_injOn hB hφdiff hφinj y hy
  obtain ⟨ρ, hρ0, hρlt, δ, hδ0, hρsub, -, hsurj⟩ :=
    Work.Horn.exists_ball_injOn_and_mapsTo hB hφdiff hy hne hε
  exact ⟨ρ, δ, hρ0, hρlt, hδ0, hρsub, fun w hw => by
    obtain ⟨u, hu, hfu⟩ := hsurj w (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
    exact ⟨u, ⟨hu, hρsub hu⟩, hfu⟩⟩

/-- **Local injectivity *and* surjectivity of `f` over the complement of the value `v`.**  If `f` is
holomorphic on the open set `B`, `x ∈ B`, `deriv f x ≠ 0` and `f x ≠ v`, then for every `ε > 0`
there are `ρ ∈ (0, ε)` and `δ > 0` with `ball x ρ ⊆ B` such that `f` is injective on
`ball x ρ ∩ (B \ (B ∩ f ⁻¹' {v}))` and the `f`-image of that set contains `ball (f x) δ`.

The second ingredient beyond the inverse function theorem is the positivity of `dist (f x) v`, which
lets us shrink `δ` so that every point of `ball (f x) δ` differs from `v`; the preimage point of
such a point therefore lies in `B \ f ⁻¹' {v}`. -/
theorem ball_injOn_surj_diff_singleton {B : Set ℂ} {f : ℂ → ℂ} {x v : ℂ}
    (hB : IsOpen B) (hf : DifferentiableOn ℂ f B) (hx : x ∈ B) (hne : deriv f x ≠ 0)
    (hv : f x ≠ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ ρ < ε ∧ 0 < δ ∧ Metric.ball x ρ ⊆ B ∧
      Set.InjOn f (Metric.ball x ρ ∩ (B \ (B ∩ f ⁻¹' {v}))) ∧
      Metric.ball (f x) δ ⊆ f '' (Metric.ball x ρ ∩ (B \ (B ∩ f ⁻¹' {v}))) := by
  obtain ⟨ρ, hρ0, hρlt, δ₀, hδ₀0, hρsub, hinj, hsurj⟩ :=
    Work.Horn.exists_ball_injOn_and_mapsTo hB hf hx hne hε
  have hdist : 0 < dist (f x) v := dist_pos.mpr hv
  refine ⟨ρ, min δ₀ (dist (f x) v), hρ0, hρlt, lt_min hδ₀0 hdist, hρsub, ?_, ?_⟩
  · exact fun a ha b hb hab => hinj ha.1 hb.1 hab
  · rintro w hw
    have hwδ : dist w (f x) < min δ₀ (dist (f x) v) := by simpa using hw
    have hw₀ : dist w (f x) < δ₀ := lt_of_lt_of_le hwδ (min_le_left _ _)
    have hwv : w ≠ v := by
      intro hwv
      have hlt : dist (f x) v < dist (f x) v := by
        calc dist (f x) v = dist w (f x) := by rw [hwv, dist_comm]
          _ < dist (f x) v := lt_of_lt_of_le hwδ (min_le_right _ _)
      exact absurd hlt (lt_irrefl _)
    obtain ⟨u, hu, hfu⟩ := hsurj w (by simpa [dist_eq_norm] using hw₀)
    refine ⟨u, ⟨hu, hρsub hu, fun hmem => hwv ?_⟩, hfu⟩
    exact hfu.symm.trans (by simpa using hmem.2)

set_option linter.unusedVariables false in
theorem local_inj_surj_phi_comp {B : Set ℂ} {f φ : ℂ → ℂ} {v : ℂ}
    (hBopen : IsOpen B) (hf : DifferentiableOn ℂ f B) (hmap : Set.MapsTo f B B)
    (hcritval : ∀ z ∈ B, deriv f z = 0 → f z = v)
    (hφ0 : φ v = 0) (hφmaps : ∀ z ∈ B, ‖φ z‖ < 1)
    (hφsurj : ∀ w : ℂ, ‖w‖ < 1 → ∃ z ∈ B, φ z = w)
    (hφne : ∀ z ∈ B, z ≠ v → φ z ≠ 0)
    (hφana : ∀ z ∈ B, AnalyticAt ℂ φ z)
    (hφinj : Set.InjOn φ B) :
    ∀ x ∈ B \ (B ∩ f ⁻¹' {v}), ∀ ε : ℝ, 0 < ε → ∃ ρ δ : ℝ,
      0 < ρ ∧ ρ < ε ∧ 0 < δ ∧
      Set.InjOn (fun z => φ (f z)) (Metric.ball x ρ ∩ (B \ (B ∩ f ⁻¹' {v}))) ∧
      Metric.ball (φ (f x)) δ ⊆ (fun z => φ (f z)) '' (Metric.ball x ρ ∩ (B \ (B ∩ f ⁻¹' {v}))) := by
  intro x hx ε hε
  have hxB : x ∈ B := hx.1
  have hfxv : f x ≠ v := fun h => hx.2 ⟨hxB, h⟩
  have hdne : deriv f x ≠ 0 := fun h => hfxv (hcritval x hxB h)
  -- `f` is a local biholomorphism at `x` over the complement of the value `v`
  obtain ⟨ρ, δf, hρ0, hρlt, hδf0, hρsub, hinjf, hsurjf⟩ :=
    ball_injOn_surj_diff_singleton hBopen hf hxB hdne hfxv hε
  -- `φ` is a local biholomorphism at `f x`, with radius smaller than `δf`
  obtain ⟨ρ', δ, hρ'0, hρ'lt, hδ0, -, hsurjφ⟩ :=
    ball_subset_image_ball_of_injOn_analytic hBopen hφana hφinj (hmap hxB) hδf0
  refine ⟨ρ, δ, hρ0, hρlt, hδ0, ?_, ?_⟩
  · -- injectivity: first `φ`, then `f`
    rintro a ⟨ha, haB, ha'⟩ b ⟨hb, hbB, hb'⟩ hab
    have h1 : f a = f b := hφinj (hmap haB) (hmap hbB) hab
    exact hinjf ⟨ha, haB, ha'⟩ ⟨hb, hbB, hb'⟩ h1
  · -- surjectivity: `φ` onto `ball (φ (f x)) δ`, then `f` onto the ball of radius `δf ≥ ρ'`
    intro w hw
    obtain ⟨u, hu, hφu⟩ := hsurjφ hw
    have hu' : u ∈ Metric.ball (f x) δf :=
      Metric.ball_subset_ball (le_of_lt hρ'lt) hu.1
    obtain ⟨z, hz, hfz⟩ := hsurjf hu'
    exact ⟨z, hz, by simp only [hfz, hφu]⟩

end Work.HornSeq
