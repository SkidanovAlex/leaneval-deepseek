import Mathlib

namespace Work.WilG4c

/-- The `m`-th iterated derivative of an affine composition `y ↦ f (b + A y)` is obtained from the
`m`-th iterated derivative of `f` at `b + A x` by composing all `m` slots with the linear map `A`.
Consequently its operator norm is bounded by `‖D^m f (b + A x)‖ * ‖A‖^m`. -/
lemma affine_iteratedFDeriv_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r m : ℕ) (hm : m ≤ r) (f : E → F) (b x : E) (A : E →L[ℝ] E)
    (hf : ContDiffAt ℝ r f (b + A x)) :
    ‖iteratedFDeriv ℝ m (fun y : E => f (b + A y)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (b + A x)‖ * ‖A‖ ^ m := by
  have hfun : (fun y : E => f (b + A y)) = (fun z : E => f (b + z)) ∘ (A : E → E) := by
    funext y; rfl
  rw [hfun]
  -- The shift `z ↦ b + z` is smooth, so `z ↦ f (b + z)` is `C^r` at `A x`.
  have hshift : ContDiffAt ℝ r (fun z : E => b + z) (A x) := by
    have h := (contDiffAt_const (𝕜 := ℝ) (n := (r : WithTop ℕ∞)) (c := b) (x := A x)).add
      (contDiffAt_id (𝕜 := ℝ) (n := (r : WithTop ℕ∞)) (x := A x))
    simpa using h
  have hg_at : ContDiffAt ℝ r (fun z : E => f (b + z)) (A x) := by
    have h := ContDiffAt.comp (A x) (f := fun z : E => b + z) (g := f) hf hshift
    exact h
  -- Extract an open neighbourhood `s` of `A x` on which `z ↦ f (b + z)` is `C^r`.
  obtain ⟨u, hu, hgu⟩ := hg_at.contDiffOn le_rfl (fun h => absurd h (by simp))
  obtain ⟨s, hsu, hsopen, hsx⟩ := mem_nhds_iff.mp hu
  have hgs : ContDiffOn ℝ (r : WithTop ℕ∞) (fun z : E => f (b + z)) s := hgu.mono hsu
  -- The iterated derivative of the composition with `A`, within `A ⁻¹' s`.
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (s := s)
    (f := fun z : E => f (b + z)) A hgs hsopen.uniqueDiffOn
    (hsopen.preimage A.continuous).uniqueDiffOn hsx (i := m) (by exact_mod_cast hm)
  -- Pass from the auxiliary open sets to the full space.
  have h1 : iteratedFDerivWithin ℝ m
        ((fun z : E => f (b + z)) ∘ (A : E → E)) (A ⁻¹' s) x
      = iteratedFDeriv ℝ m ((fun z : E => f (b + z)) ∘ (A : E → E)) x :=
    iteratedFDerivWithin_of_isOpen m (hsopen.preimage A.continuous) (by simpa using hsx)
  have h2 : iteratedFDerivWithin ℝ m (fun z : E => f (b + z)) s (A x)
      = iteratedFDeriv ℝ m (fun z : E => f (b + z)) (A x) :=
    iteratedFDerivWithin_of_isOpen m hsopen hsx
  have h3 : iteratedFDeriv ℝ m (fun z : E => f (b + z)) (A x)
      = iteratedFDeriv ℝ m f (b + A x) :=
    iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) m b (A x)
  -- Norm bound for composing a multilinear map with the constant family `A`.
  have hb : ‖(iteratedFDerivWithin ℝ m (fun z : E => f (b + z)) s (A x)).compContinuousLinearMap
        (fun _ : Fin m => A)‖
      ≤ ‖iteratedFDerivWithin ℝ m (fun z : E => f (b + z)) s (A x)‖ * ‖A‖ ^ m := by
    calc ‖(iteratedFDerivWithin ℝ m (fun z : E => f (b + z)) s (A x)).compContinuousLinearMap
            (fun _ : Fin m => A)‖
        ≤ ‖iteratedFDerivWithin ℝ m (fun z : E => f (b + z)) s (A x)‖ * ∏ _i : Fin m, ‖A‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDerivWithin ℝ m (fun z : E => f (b + z)) s (A x)‖ * ‖A‖ ^ m := by simp
  calc ‖iteratedFDeriv ℝ m ((fun z : E => f (b + z)) ∘ (A : E → E)) x‖
      = ‖iteratedFDerivWithin ℝ m ((fun z : E => f (b + z)) ∘ (A : E → E)) (A ⁻¹' s) x‖ := by
        rw [h1]
    _ = ‖(iteratedFDerivWithin ℝ m (fun z : E => f (b + z)) s (A x)).compContinuousLinearMap
            (fun _ : Fin m => A)‖ := by rw [hcomp]
    _ ≤ ‖iteratedFDerivWithin ℝ m (fun z : E => f (b + z)) s (A x)‖ * ‖A‖ ^ m := hb
    _ = ‖iteratedFDeriv ℝ m f (b + A x)‖ * ‖A‖ ^ m := by rw [h2, h3]

end Work.WilG4c
