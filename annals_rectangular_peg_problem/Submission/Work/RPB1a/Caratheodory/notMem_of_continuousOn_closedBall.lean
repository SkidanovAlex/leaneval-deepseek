import Mathlib
import Submission.Work.RPB1a.differentiableOn_invFunOn
import Submission.Work.RPB1a.deriv_ne_zero_of_injOn
import Submission.Work.RPB1a.isOpen_image_of_differentiableOn_of_injOn

namespace Work.RPB1a.Caratheodory

open Complex Set Metric Filter
open scoped ContDiff Real Topology

/-- A holomorphic injection of the open unit disc onto a set `D` cannot have a continuous extension
to the closed disc which takes an interior value of `D` at a point of the unit circle: the
continuous inverse of `Φ` on `D` would force that circle point to be the preimage of the value,
which lies in the open disc. -/
theorem notMem_of_continuousOn_closedBall {D : Set ℂ} {Φ Ψ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ (ball 0 1)) (hΦi : InjOn Φ (ball 0 1))
    (hΦs : Φ '' ball 0 1 = D) (hΨc : ContinuousOn Ψ (closedBall 0 1))
    (hΨeq : EqOn Ψ Φ (ball 0 1)) {ζ : ℂ} (hζ : ζ ∈ sphere 0 1) :
    Ψ ζ ∉ D := by
  intro hζD
  -- `Ψ ζ = Φ u` for some `u` in the open disc.
  rw [← hΦs] at hζD
  obtain ⟨u, hu, huz⟩ := hζD
  -- `D` is open, being the image of the open disc under an injective holomorphic map.
  have hDo : IsOpen D :=
    hΦs ▸ isOpen_image_of_differentiableOn_of_injOn isOpen_ball hΦd hΦi
  -- The inverse of `Φ` is holomorphic, hence continuous, on `D`.
  have hne : ∀ z ∈ ball 0 1, deriv Φ z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hΦd hΦi
  have hinv : DifferentiableOn ℂ (Function.invFunOn Φ (ball 0 1)) (Φ '' ball 0 1) :=
    differentiableOn_invFunOn isOpen_ball hΦd hΦi hne
  have hinvc : ContinuousOn (Function.invFunOn Φ (ball 0 1)) D := hΦs ▸ hinv.continuousOn
  have hinv_eq : ∀ u ∈ ball 0 1, Function.invFunOn Φ (ball 0 1) (Φ u) = u := by
    intro u hu
    exact hΦi (Function.invFunOn_mem ⟨u, hu, rfl⟩) hu (Function.invFunOn_eq ⟨u, hu, rfl⟩)
  -- `ζ` is in the closure of the open disc, so `Ψ` has a limit along the open disc there.
  have hzcb : ζ ∈ closedBall 0 1 := sphere_subset_closedBall hζ
  have hz1 : ‖ζ‖ = 1 := by
    have := mem_sphere.mp hζ
    rwa [dist_eq_norm, sub_zero] at this
  have hzclos : ζ ∈ closure (ball 0 1) := by
    rw [closure_ball 0 one_ne_zero]; exact hzcb
  have hneBot : (𝓝[ball 0 1] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzclos
  have hΨlim : Tendsto Ψ (𝓝[ball 0 1] ζ) (𝓝 (Ψ ζ)) :=
    ((hΨc.continuousWithinAt hzcb).tendsto).mono_left
      (nhdsWithin_mono ζ ball_subset_closedBall)
  have huwD : Φ u ∈ D := hΦs ▸ ⟨u, hu, rfl⟩
  have hΨlim' : Tendsto Ψ (𝓝[ball 0 1] ζ) (𝓝 (Φ u)) := by
    rw [huz]; exact hΨlim
  -- The inverse map tends to `u` at `Φ u`.
  have hinvlim : Tendsto (Function.invFunOn Φ (ball 0 1)) (𝓝 (Φ u)) (𝓝 u) := by
    have h := (hinvc.continuousAt (hDo.mem_nhds huwD)).tendsto
    rwa [hinv_eq u hu] at h
  have hcomp : Tendsto (fun y => Function.invFunOn Φ (ball 0 1) (Ψ y))
      (𝓝[ball 0 1] ζ) (𝓝 u) := hinvlim.comp hΨlim'
  -- On the open disc, `invFunOn Φ (ball 0 1) ∘ Ψ = id`.
  have hev : (fun y => Function.invFunOn Φ (ball 0 1) (Ψ y)) =ᶠ[𝓝[ball 0 1] ζ] id := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [hΨeq hy, hinv_eq y hy]
    rfl
  have hcomp' : Tendsto id (𝓝[ball 0 1] ζ) (𝓝 u) := Tendsto.congr' hev hcomp
  -- Hence `u = ζ` by uniqueness of limits, but `u` is in the open disc and `ζ` on the circle.
  have huz' : u = ζ :=
    tendsto_nhds_unique hcomp' (tendsto_id.mono_right nhdsWithin_le_nhds)
  rw [huz', mem_ball, dist_zero_right, hz1] at hu
  exact lt_irrefl 1 hu

end Work.RPB1a.Caratheodory
