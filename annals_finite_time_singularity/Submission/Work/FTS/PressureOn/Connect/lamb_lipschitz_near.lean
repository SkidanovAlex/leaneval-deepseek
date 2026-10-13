/-
# `Work.FTS.PressureOn.Connect.lamb_lipschitz_near`

The Lamb vector `lamb u ω y s = u y s × ω y s` is Lipschitz in the time variable, uniformly in the
space variable `y`, on any time interval on which the velocity and the vorticity are Lipschitz in
time with a common constant `C` and bounded by a common constant `B`.

The only ingredient is the bilinearity of the cross product together with the norm bound
`‖a × b‖ ≤ ‖a‖ ‖b‖`:

  `(u y s × ω y s) - (u y t × ω y t) = ((u y s - u y t) × ω y s) + (u y t × (ω y s - ω y t))`,

so that, taking norms and using the two hypotheses (and the triangle inequality to bound the
*base-point* value `‖u y t‖ ≤ B + C/2` from the nearby point `t + 1/2`), one gets
`‖lamb y s - lamb y t‖ ≤ (C |s - t|) B + (B + C/2) (C |s - t|)`, i.e. the constant
`C' := C * B + (B + C/2) * C` works.  No sign hypothesis on `B` or `C` is needed: the
nonnegativity of `C |s - t|` used in the two product estimates is *derived* from the Lipschitz
hypotheses themselves.
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

/-- **The norm bound for the cross product**: `‖a × b‖ ≤ ‖a‖ ‖b‖`.  It follows from the identity
`‖a × b‖ = ‖a‖ ‖b‖ sin ∠(a,b)` of `InnerProductGeometry.norm_ofLp_crossProduct`. -/
private lemma norm_crossVec_le (a b : R3) : ‖crossVec a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h := InnerProductGeometry.norm_ofLp_crossProduct a b
  have hsin : Real.sin (InnerProductGeometry.angle a b) ≤ 1 := Real.sin_le_one _
  have hnn : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg a) (norm_nonneg b)
  calc ‖crossVec a b‖ = ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b) := h
    _ ≤ ‖a‖ * ‖b‖ * 1 := mul_le_mul_of_nonneg_left hsin hnn
    _ = ‖a‖ * ‖b‖ := by ring

/-- **Bilinearity of the cross product**, in the form of the difference identity
`a × b - a' × b' = (a - a') × b + a' × (b - b')`. -/
private lemma crossVec_sub_sub (a a' b b' : R3) :
    crossVec a b - crossVec a' b' = crossVec (a - a') b + crossVec a' (b - b') := by
  rw [WithLp.ext_iff]
  simp only [crossVec_apply, WithLp.ofLp_sub, WithLp.ofLp_add, map_sub]
  simp

/-- **The Lamb vector difference bound**: splitting the difference of the two cross products and
applying the norm bound to each term. -/
private lemma norm_lamb_sub_le (u ω : R3 → ℝ → R3) (y : R3) (s t : ℝ) :
    ‖lamb u ω y s - lamb u ω y t‖
      ≤ ‖u y s - u y t‖ * ‖ω y s‖ + ‖u y t‖ * ‖ω y s - ω y t‖ := by
  have h1 : lamb u ω y s = crossVec (u y s) (ω y s) := rfl
  have h2 : lamb u ω y t = crossVec (u y t) (ω y t) := rfl
  rw [h1, h2, crossVec_sub_sub]
  calc ‖crossVec (u y s - u y t) (ω y s) + crossVec (u y t) (ω y s - ω y t)‖
      ≤ ‖crossVec (u y s - u y t) (ω y s)‖ + ‖crossVec (u y t) (ω y s - ω y t)‖ :=
        norm_add_le _ _
    _ ≤ ‖u y s - u y t‖ * ‖ω y s‖ + ‖u y t‖ * ‖ω y s - ω y t‖ :=
        add_le_add (norm_crossVec_le _ _) (norm_crossVec_le _ _)

theorem lamb_lipschitz_near {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {t B C : ℝ}
    (hu : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u y s - u y t‖ ≤ C * |s - t|)
    (hω : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖ω y s - ω y t‖ ≤ C * |s - t|)
    (hub : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u y s‖ ≤ B)
    (hωb : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖ω y s‖ ≤ B) :
    ∃ C' : ℝ, ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      ‖Work.FTS.PressureOn.lamb u ω y s - Work.FTS.PressureOn.lamb u ω y t‖ ≤ C' * |s - t| := by
  -- the auxiliary point `t + 1/2`, at distance `1/2 < 1` from `t`
  have hmem : t + 1 / 2 ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  refine ⟨C * B + (B + C / 2) * C, fun y s hs => ?_⟩
  -- the base point `t` is controlled from the auxiliary point
  have hut : ‖u y t‖ ≤ B + C / 2 := by
    have h1 := hub y (t + 1 / 2) hmem
    have h2 : ‖u y (t + 1 / 2) - u y t‖ ≤ C / 2 := by
      calc ‖u y (t + 1 / 2) - u y t‖ ≤ C * |(t + 1 / 2) - t| := hu y (t + 1 / 2) hmem
        _ = C / 2 := by
            rw [show (t + 1 / 2) - t = 1 / 2 by ring, abs_of_pos (by norm_num)]
            ring
    calc ‖u y t‖ = ‖u y (t + 1 / 2) - (u y (t + 1 / 2) - u y t)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u y (t + 1 / 2)‖ + ‖u y (t + 1 / 2) - u y t‖ := norm_sub_le _ _
      _ ≤ B + C / 2 := add_le_add h1 h2
  -- the two product estimates; the nonnegativity of `C * |s - t|` comes from the hypotheses
  have h1 : ‖u y s - u y t‖ * ‖ω y s‖ ≤ (C * |s - t|) * B :=
    mul_le_mul (hu y s hs) (hωb y s hs) (norm_nonneg _) (le_trans (norm_nonneg _) (hu y s hs))
  have h2 : ‖u y t‖ * ‖ω y s - ω y t‖ ≤ (B + C / 2) * (C * |s - t|) :=
    mul_le_mul hut (hω y s hs) (norm_nonneg _) (le_trans (norm_nonneg _) hut)
  calc ‖lamb u ω y s - lamb u ω y t‖
      ≤ ‖u y s - u y t‖ * ‖ω y s‖ + ‖u y t‖ * ‖ω y s - ω y t‖ := norm_lamb_sub_le u ω y s t
    _ ≤ (C * |s - t|) * B + (B + C / 2) * (C * |s - t|) := add_le_add h1 h2
    _ = (C * B + (B + C / 2) * C) * |s - t| := by ring

end Work.FTS.PressureOn.Connect
