import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Dispatch

open MeasureTheory Set Filter

/-- The angular weight `sin(2θ)` is invariant under the reflection `θ ↦ π/2 - θ`:
`sin(2(π/2 - θ)) = sin(2θ)`. -/
lemma sin_two_sub_mirror (θ : ℝ) :
    Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
  have h : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
  rw [h, Real.sin_pi_sub]

/-- The weighted angular factor `sin(2θ)^{-η}` is invariant under the reflection
`θ ↦ π/2 - θ`. -/
lemma rpow_sin_two_sub_mirror (θ : ℝ) :
    (Real.sin (2 * (Real.pi / 2 - θ))) ^ (-(Work.Spaces.eta)) =
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [sin_two_sub_mirror]

/-- Integrability on `(0, π/2)` is invariant under the reflection `θ ↦ π/2 - θ`.

The reflection is an affine involution mapping the interval `(0, π/2)` onto itself, hence it
preserves the restricted Lebesgue measure there.  We prove this through interval integrability,
using that `IntervalIntegrable` is invariant under `θ ↦ c - θ` and symmetric in its endpoints. -/
lemma integrableOn_mirror {F : ℝ → ℝ} :
    IntegrableOn (fun θ => F (Real.pi / 2 - θ)) (Ioo 0 (Real.pi / 2)) ↔
      IntegrableOn F (Ioo 0 (Real.pi / 2)) := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h1 : IntervalIntegrable (fun θ => F (Real.pi / 2 - θ)) volume 0 (Real.pi / 2) ↔
      IntervalIntegrable (fun θ => F (Real.pi / 2 - θ)) volume (Real.pi / 2) 0 :=
    IntervalIntegrable.symm_iff
  have h2 : IntervalIntegrable (fun θ => F (Real.pi / 2 - θ)) volume (Real.pi / 2) 0 ↔
      IntervalIntegrable F volume 0 (Real.pi / 2) := by
    have h := IntervalIntegrable.comp_sub_left_iff (f := F) (a := (0 : ℝ))
      (b := Real.pi / 2) (c := Real.pi / 2)
    simpa using h
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hle,
    ← intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
  exact h1.trans h2

/-- The second derivative of a reflected function is the reflection of the second derivative:
with `c` the reflection centre, `deriv (deriv (fun τ => g (c - τ))) x = deriv (deriv g) (c - x)`.
The reflection `τ ↦ c - τ` has derivative `-1`, and the two minus signs cancel. -/
lemma deriv_deriv_comp_const_sub (g : ℝ → ℝ) (c x : ℝ) :
    deriv (deriv (fun τ => g (c - τ))) x = deriv (deriv g) (c - x) := by
  have hfun : deriv (fun τ => g (c - τ)) = fun τ => -deriv g (c - τ) := by
    funext y
    exact deriv_comp_const_sub g c y
  rw [hfun]
  have h2 : deriv (fun τ => -deriv g (c - τ)) x = deriv (deriv g) (c - x) := by
    have h := deriv_comp_const_sub (f := fun y => -deriv g y) (a := c) (x := x)
    simpa using h
  exact h2

theorem flux_mirror_symmetry {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hpi : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hP : MeasureTheory.IntegrableOn
      (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)))
    (hT : MeasureTheory.IntegrableOn
      (fun θ => f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2))) :
    (ContDiffOn ℝ 2 (fun θ => f (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 2)) ∧
      Filter.Tendsto (fun θ => f (Real.pi / 2 - θ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => f (Real.pi / 2 - θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
      MeasureTheory.IntegrableOn
        (fun θ => (f (Real.pi / 2 - θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo 0 (Real.pi / 2)) ∧
      MeasureTheory.IntegrableOn
        (fun θ => (f (Real.pi / 2 - θ)) * deriv (deriv (fun τ => f (Real.pi / 2 - τ))) θ
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2))) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun τ => (Real.sin (2 * τ)) ^ (-(Work.Spaces.eta)) * (f (Real.pi / 2 - τ)) ^ 2) θ
        = -deriv (fun τ => (Real.sin (2 * τ)) ^ (-(Work.Spaces.eta)) * (f τ) ^ 2)
            (Real.pi / 2 - θ))
:= by
  -- the reflection `θ ↦ π/2 - θ` maps `(0, π/2)` onto itself
  have hmaps : MapsTo (fun θ : ℝ => Real.pi / 2 - θ) (Ioo 0 (Real.pi / 2)) (Ioo 0 (Real.pi / 2)) := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- regularity of the reflected function
  have hcd : ContDiffOn ℝ 2 (fun θ => f (Real.pi / 2 - θ)) (Ioo 0 (Real.pi / 2)) := by
    have hg : ContDiffOn ℝ 2 (fun θ : ℝ => Real.pi / 2 - θ) (Ioo 0 (Real.pi / 2)) :=
      contDiffOn_const.sub contDiffOn_id
    simpa [Function.comp_def] using hf.comp hg hmaps
  -- the reflection maps the two boundary filters into one another
  have hφ_hi : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous fun θ : ℝ => Real.pi / 2 - θ := continuous_const.sub continuous_id
      simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact sub_lt_self _ (Set.mem_Ioi.mp hθ)
  have hφ_lo : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2)))
      (nhdsWithin 0 (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous fun θ : ℝ => Real.pi / 2 - θ := continuous_const.sub continuous_id
      simpa using (hcont.tendsto (Real.pi / 2)).mono_left
        (nhdsWithin_le_nhds (s := Iio (Real.pi / 2)))
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact sub_pos.mpr (Set.mem_Iio.mp hθ)
  have htend1 : Tendsto (fun θ => f (Real.pi / 2 - θ)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using hpi.comp hφ_hi
  have htend2 : Tendsto (fun θ => f (Real.pi / 2 - θ))
      (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) := by
    simpa [Function.comp_def] using h0.comp hφ_lo
  -- integrability of the reflected square
  have hP' : IntegrableOn
      (fun θ => (f (Real.pi / 2 - θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Ioo 0 (Real.pi / 2)) := by
    have h := (integrableOn_mirror
      (F := fun y => f y ^ 2 * (Real.sin (2 * y)) ^ (-(Work.Spaces.eta)))).mpr hP
    refine h.congr_fun ?_ measurableSet_Ioo
    intro θ _
    show f (Real.pi / 2 - θ) ^ 2 * (Real.sin (2 * (Real.pi / 2 - θ))) ^ (-(Work.Spaces.eta))
        = f (Real.pi / 2 - θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [rpow_sin_two_sub_mirror θ]
  -- integrability of the reflected second-order pairing
  have hT' : IntegrableOn
      (fun θ => (f (Real.pi / 2 - θ)) * deriv (deriv (fun τ => f (Real.pi / 2 - τ))) θ
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Ioo 0 (Real.pi / 2)) := by
    have h := (integrableOn_mirror
      (F := fun y => f y * deriv (deriv f) y * (Real.sin (2 * y)) ^ (-(Work.Spaces.eta)))).mpr hT
    refine h.congr_fun ?_ measurableSet_Ioo
    intro θ _
    show f (Real.pi / 2 - θ) * deriv (deriv f) (Real.pi / 2 - θ)
          * (Real.sin (2 * (Real.pi / 2 - θ))) ^ (-(Work.Spaces.eta))
        = f (Real.pi / 2 - θ) * deriv (deriv (fun τ => f (Real.pi / 2 - τ))) θ
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [deriv_deriv_comp_const_sub f (Real.pi / 2) θ, rpow_sin_two_sub_mirror θ]
  refine ⟨⟨hcd, htend1, htend2, hP', hT'⟩, ?_⟩
  -- the flux identity: the reflected flux is minus the flux of the reflected point
  intro θ _
  have hfun : (fun x : ℝ => (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
        * (f (Real.pi / 2 - x)) ^ 2)
      = fun x : ℝ => (fun y => (Real.sin (2 * y)) ^ (-(Work.Spaces.eta)) * f y ^ 2)
          (Real.pi / 2 - x) := by
    funext x
    show (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) * (f (Real.pi / 2 - x)) ^ 2
        = (Real.sin (2 * (Real.pi / 2 - x))) ^ (-(Work.Spaces.eta)) * (f (Real.pi / 2 - x)) ^ 2
    rw [rpow_sin_two_sub_mirror x]
  rw [hfun]
  exact deriv_comp_const_sub (fun y : ℝ => (Real.sin (2 * y)) ^ (-(Work.Spaces.eta)) * f y ^ 2)
    (Real.pi / 2) θ

end Work.FTS.EllipticEst.Dispatch
