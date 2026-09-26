import Mathlib

/-!
# Lifting a holomorphic function on `ℍ` along `z ↦ ofComplex (z + I)`

Let `u : ℍ → ℂ` be such that `u ∘ ofComplex` is holomorphic on the upper half plane
`{z : ℂ | 0 < z.im}` (the image of `ℍ` under `UpperHalfPlane.ofComplex`).  Then the
pullback

  `z ↦ u (ofComplex (z + I))`

is continuous on the shifted half plane `{z : ℂ | -1 < z.im}` and is holomorphic for all
sufficiently large imaginary part (i.e. eventually with respect to `comap im atTop`).

The point is that for `-1 < z.im` the point `z + I` lies in the upper half plane, where
`UpperHalfPlane.ofComplex` is the identity followed by the coercion `ℍ → ℂ`; hence on that
region the map in question agrees with `(u ∘ ofComplex) ∘ (z ↦ z + I)`, a composition of
the holomorphic (hence continuous) `u ∘ ofComplex` with an affine map.  No hypothesis on the
behaviour of `ofComplex` off the upper half plane is needed.
-/

namespace Work.Rigidity.PeriodicDecay

theorem mdiff_shift_lift {u : UpperHalfPlane → ℂ}
    (hu : DifferentiableOn ℂ (u ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im}) :
    ContinuousOn (fun z : ℂ => u (UpperHalfPlane.ofComplex (z + Complex.I))) {z : ℂ | -1 < z.im} ∧
    (∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop,
      DifferentiableAt ℂ (fun z : ℂ => u (UpperHalfPlane.ofComplex (z + Complex.I))) z) := by
  -- The affine shift `z ↦ z + I` sends the half plane `-1 < im` into the upper half plane.
  have hmap : Set.MapsTo (fun z : ℂ => z + Complex.I) {z : ℂ | -1 < z.im} {w : ℂ | 0 < w.im} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    simp only [Complex.add_im, Complex.I_im]
    linarith
  constructor
  · -- continuity: compose `u ∘ ofComplex` with the continuous affine shift
    exact hu.continuousOn.comp (by fun_prop) hmap
  · -- holomorphy: eventually `-1 < im`, where `z + I` is in the upper half plane
    have hev : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, -1 < z.im := by
      rw [Filter.eventually_comap, Filter.eventually_atTop]
      exact ⟨0, fun b hb z hz => by rw [hz]; linarith⟩
    filter_upwards [hev] with z hz
    have hz' : 0 < (z + Complex.I).im := by
      simp only [Complex.add_im, Complex.I_im]; linarith
    have h1 : DifferentiableAt ℂ (u ∘ UpperHalfPlane.ofComplex) (z + Complex.I) :=
      hu.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
    have h2 : DifferentiableAt ℂ (fun z : ℂ => z + Complex.I) z :=
      differentiableAt_id.add_const Complex.I
    have h3 : DifferentiableAt ℂ
        ((u ∘ UpperHalfPlane.ofComplex) ∘ (fun z : ℂ => z + Complex.I)) z :=
      h1.comp z h2
    exact h3

end Work.Rigidity.PeriodicDecay
