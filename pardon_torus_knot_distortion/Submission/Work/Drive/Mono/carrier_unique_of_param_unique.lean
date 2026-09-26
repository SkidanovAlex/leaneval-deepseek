import Mathlib
import Submission.Work.Drive.Mono.SphereFaceDefs
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen

namespace Work.Drive.Mono

/-- **From uniqueness in the parameter plane to uniqueness on the surface.**

Let `z = par ψ p` (here `par ψ` is the parametrisation `Work.BoxShrink.Pinch.par`).  Suppose the
two level conditions `boxH = 0` (i.e. `boxNorm = s` on the surface) and `planeG = 0` (i.e.
`⟪v,·⟫ = ⟪v,c⟫ + u + h`) have the single common zero `p` in a ball of the parameter plane around
`p`.  Then on the surface there is a radius `ρ₀ > 0` such that any point `y` of the carrier of the
surface within distance `ρ₀` of `z` satisfying both level equations is `z` itself.

(The image under `par ψ` of an open ball of parameters is open in the carrier —
`Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen` — so a Euclidean ball around `z`
intersected with the carrier is contained in `par ψ '' ball p δ`; a point of it is
`par ψ q` with `q` in the parameter ball, and the two level conditions become `boxH q = 0` and
`planeG q = 0` there.) -/
theorem carrier_unique_of_param_unique {ψ : Submission.Diffeo} {s u : ℝ}
    {c : EuclideanSpace ℝ (Fin 3)} {σ : Equiv.Perm (Fin 3)} {v : EuclideanSpace ℝ (Fin 3)}
    {h : ℝ} {z : EuclideanSpace ℝ (Fin 3)} {p : ℝ × ℝ}
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (huniq : ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℝ × ℝ, dist q p < δ →
      Work.Drive.Mono.boxH ψ s c σ q = 0 → Work.Drive.Mono.planeG ψ c v u h q = 0 → q = p) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y : EuclideanSpace ℝ (Fin 3),
      y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      dist y z < ρ₀ → Submission.boxNorm c σ y = s →
      inner ℝ v y = inner ℝ v c + u + h → y = z := by
  obtain ⟨δ, hδpos, hδuniq⟩ := huniq
  -- the parameter ball is open, so its image is open in the carrier
  have hUopen : IsOpen (Metric.ball p δ) := Metric.isOpen_ball
  have himg : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Pinch.par ψ '' Metric.ball p δ) := by
    have hh := Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hUopen
    simpa only [Work.BoxShrink.Pinch.par_def, Work.Drive.EpsSphere.torusOf] using hh
  rw [Work.SurgeryInvariance.IsOpenInCarrier] at himg
  -- `z` lies in that image, so it is an interior point of it in the carrier
  have hzcar : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
    rw [← hp]; exact Work.BoxShrink.Pinch.par_mem_carrier ψ p
  have hzmem : z ∈ Work.BoxShrink.Pinch.par ψ '' Metric.ball p δ :=
    ⟨p, by rw [Metric.mem_ball, dist_self]; exact hδpos, hp⟩
  obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp himg
    (⟨z, hzcar⟩ : (Work.Drive.EpsSphere.torusOf ψ).carrier) hzmem
  refine ⟨ε, hεpos, ?_⟩
  intro y hycar hydist hbox hplane
  -- a carrier point close to `z` is `par ψ q` with `q` in the parameter ball
  have hyball : (⟨y, hycar⟩ : (Work.Drive.EpsSphere.torusOf ψ).carrier) ∈
      Metric.ball (⟨z, hzcar⟩ : (Work.Drive.EpsSphere.torusOf ψ).carrier) ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    exact hydist
  have hyimg := hεball hyball
  have hyimg' : y ∈ Work.BoxShrink.Pinch.par ψ '' Metric.ball p δ := hyimg
  obtain ⟨q, hqmem, hqeq⟩ := hyimg'
  have hqdist : dist q p < δ := by
    rw [Metric.mem_ball] at hqmem; exact hqmem
  -- the two level conditions pull back to the parameter plane
  have hqbox : Work.Drive.Mono.boxH ψ s c σ q = 0 := by
    rw [Work.Drive.Mono.boxH_apply, hqeq]
    exact sub_eq_zero.mpr hbox
  have hqplane : Work.Drive.Mono.planeG ψ c v u h q = 0 := by
    rw [Work.Drive.Mono.planeG_apply, hqeq]
    exact sub_eq_zero.mpr hplane
  -- uniqueness in the parameter plane concludes
  have hqp : q = p := hδuniq q hqdist hqbox hqplane
  rw [← hqeq, hqp, hp]

end Work.Drive.Mono
