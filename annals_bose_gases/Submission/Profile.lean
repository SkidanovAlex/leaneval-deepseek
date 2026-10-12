import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A concrete smooth profile for the cell partition of unity

`Submission.CellCutoffs` states the grid-cutoff lemmas (`axisFam`, `axis_pu`,
`axis_deriv`, `axis_grad_sum_le`, ...) abstractly over a smooth profile
`ρ : ℝ → ℝ` satisfying:

  * `profile_supp`      — `ρ` vanishes off the open interval `(0,2)`;
  * `profile_pu`        — `ρ(θ)² + ρ(θ+1)² = 1` for `θ ∈ [0,1]`;
  * `profile_deriv_supp`— `ρ′` vanishes off `(0,2)` (flatness at the seams);
  * `profile_contDiff`  — `ρ` is smooth.

This module provides such a profile.  CONSTRUCTION (standard): let
`s(t) := (∫ x in Iio t, φ x) / (∫ φ)` where `φ : ℝ → ℝ` is a smooth,
nonnegative bump symmetric about `1/2` with support inside `(0,1)` (e.g. a
`ContDiffBump` centred at `1/2` with radius `< 1/2`).  Then
`s` is a smooth step: `s = 0` on `(−∞,0]`, `s = 1` on `[1,∞)`, and
`s(t) + s(1−t) = 1` for `t ∈ [0,1]` (by the symmetry of `φ`).  Set
`w(t) := sin(π·s(t)/2)` (so `w(t)² + w(1−t)² = 1` for `t ∈ [0,1]`, since
`w(1−t) = cos(π·s(t)/2)`), and define the profile

    ρ(t) := w(t)       for t ∈ [0,1],
            w(2−t)     for t ∈ [1,2],
            0          otherwise.

Smoothness at the seams `0,1,2` holds because `s` (hence `w`) is constant — all
derivatives vanish — in neighbourhoods of `0` and `1`: indeed `φ` and all its
derivatives vanish outside its closed support inside `(0,1)`, so
`s = 0` near `0` and `s = 1` near `1` from both sides.  The profile satisfies
`ρ(θ)² + ρ(θ+1)² = w(θ)² + w(1−θ)² = 1` for `θ ∈ [0,1]`.

The exact internal construction (bump, integral step, piecewise profile,
ContDiffOn gluing at the seams) is left to the prover; the five statements
below are the required interface.
-/

namespace Submission

open Filter MeasureTheory
open scoped ContDiff Topology Real

namespace BoseGases

/-!
The concrete profile is built from `Real.smoothTransition` (the standard
infinitely-smooth flat step: `0` on `(-∞,0]`, `1` on `[1,∞)`, with the
complement identity `σ(x) + σ(1-x) = 1`).  Instead of the integral
construction above we use, directly, the smooth step

    s(t) := σ(2t - 1/2),

which is exactly `0` on `(-∞,1/4]` and exactly `1` on `[3/4,∞)` (open
plateaus, so every `t ≤ 0` and every `t ≥ 2` lies in the *interior* of the
zero set of the profile — this makes the seam flatness statements immediate).
Then `w(t) := sin(π·s(t)/2)` satisfies `w(t)² + w(1-t)² = 1` for all `t`
(because `s(t) + s(1-t) = 1` and `sin(π/2 - x) = cos x`), and the profile is
the closed (smooth) formula

    ρ(t) := w(t) · w(2−t),

equal to `w(t)` on `[0,1]`, to `w(2−t)` on `[1,2]` and to `0` outside.
-/

namespace ProfileAux

/-- Complement identity of the smooth transition: `σ(x) + σ(1-x) = 1`. -/
lemma smoothTransition_add_compl (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  unfold Real.smoothTransition
  rw [show 1 - (1 - x) = x by ring]
  rw [add_comm (expNegInvGlue (1 - x))]
  have hd : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [← add_mul]
  rw [mul_inv_cancel₀ hd]

/-- A smooth ramp: `0` on `(-∞, 1/4]`, `1` on `[3/4, ∞)`, smooth everywhere. -/
noncomputable def ramp (x : ℝ) : ℝ :=
  Real.smoothTransition (2 * x - 1 / 2)

lemma ramp_zero {x : ℝ} (hx : x ≤ 1 / 4) : ramp x = 0 := by
  unfold ramp
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma ramp_one {x : ℝ} (hx : 3 / 4 ≤ x) : ramp x = 1 := by
  unfold ramp
  exact Real.smoothTransition.one_of_one_le (by linarith)

lemma ramp_contDiff : ContDiff ℝ ∞ ramp := by
  unfold ramp
  have hlin : ContDiff ℝ ∞ (fun x : ℝ => 2 * x - 1 / 2) := by fun_prop
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp hlin

/-- Complementary symmetry of the ramp: `ramp(x) + ramp(1-x) = 1`. -/
lemma ramp_add_compl (x : ℝ) : ramp x + ramp (1 - x) = 1 := by
  unfold ramp
  have hargs : 2 * (1 - x) - 1 / 2 = 1 - (2 * x - 1 / 2) := by ring
  rw [hargs]
  exact smoothTransition_add_compl (2 * x - 1 / 2)

/-- `w(t) = sin(π · ramp(t) / 2)`, the smooth rising part of the profile. -/
noncomputable def rise (x : ℝ) : ℝ :=
  Real.sin (Real.pi / 2 * ramp x)

lemma rise_zero {x : ℝ} (hx : x ≤ 1 / 4) : rise x = 0 := by
  unfold rise
  have h := ramp_zero hx
  simp [h]

lemma rise_one {x : ℝ} (hx : 3 / 4 ≤ x) : rise x = 1 := by
  unfold rise
  have h := ramp_one hx
  rw [h]
  rw [mul_one]
  exact Real.sin_pi_div_two

lemma rise_contDiff : ContDiff ℝ ∞ rise := by
  unfold rise ramp
  fun_prop

/-- Partition identity for the rising part: `w(t)² + w(1-t)² = 1`. -/
lemma rise_sq_add (x : ℝ) : rise x ^ 2 + rise (1 - x) ^ 2 = 1 := by
  unfold rise
  have hcompl : ramp (1 - x) = 1 - ramp x := by
    have h := ramp_add_compl x
    linarith
  rw [hcompl]
  have hsin : Real.sin (Real.pi / 2 * (1 - ramp x)) =
      Real.cos (Real.pi / 2 * ramp x) := by
    have h : Real.pi / 2 * (1 - ramp x) = Real.pi / 2 - Real.pi / 2 * ramp x := by ring
    rw [h]
    exact Real.sin_pi_div_two_sub (Real.pi / 2 * ramp x)
  rw [hsin]
  exact Real.sin_sq_add_cos_sq (Real.pi / 2 * ramp x)

/-- A function which is constant in a whole neighbourhood of a point has zero
derivative there. -/
lemma deriv_eq_zero_of_eventually_eq {f : ℝ → ℝ} {x : ℝ}
    (hf : ∃ s ∈ 𝓝 x, ∀ y ∈ s, f y = f x) : deriv f x = 0 := by
  rcases hf with ⟨s, hs, hfs⟩
  have hc : HasDerivAt (fun _ : ℝ => f x) 0 x := hasDerivAt_const x (f x)
  have heq : f =ᶠ[𝓝 x] (fun _ : ℝ => f x) := by
    filter_upwards [hs] with y hy
    exact hfs y hy
  exact (hc.congr_of_eventuallyEq heq).deriv

end ProfileAux

open ProfileAux

/-- The concrete smooth profile with support in `(0,2)` and the two-term
partition identity. -/
noncomputable def rhoProfile (t : ℝ) : ℝ :=
  rise t * rise (2 - t)

/-- The profile vanishes on `(-∞, 1/4]` (in particular on `(-∞,0]`). -/
lemma rhoProfile_eq_zero_of_le_quarter {y : ℝ} (hy : y ≤ 1 / 4) : rhoProfile y = 0 := by
  unfold rhoProfile
  have h0 : rise y = 0 := rise_zero hy
  simp [h0]

/-- The profile vanishes on `[7/4, ∞)` (in particular on `[2,∞)`). -/
lemma rhoProfile_eq_zero_of_ge_seven_quarters {y : ℝ} (hy : 7 / 4 ≤ y) : rhoProfile y = 0 := by
  unfold rhoProfile
  have h0 : rise (2 - y) = 0 := rise_zero (by linarith : 2 - y ≤ 1 / 4)
  simp [h0]

/-- Smoothness of the profile. -/
lemma profile_contDiff : ContDiff ℝ ∞ rhoProfile := by
  unfold rhoProfile
  have h1 : ContDiff ℝ ∞ rise := rise_contDiff
  have hlin : ContDiff ℝ ∞ (fun t : ℝ => 2 - t) := by fun_prop
  exact h1.mul (h1.comp hlin)

/-- The profile vanishes off the open interval `(0,2)`. -/
lemma profile_supp (t : ℝ) (ht : t ≤ 0 ∨ 2 ≤ t) : rhoProfile t = 0 := by
  rcases ht with ht | ht
  · exact rhoProfile_eq_zero_of_le_quarter (by linarith : t ≤ 1 / 4)
  · exact rhoProfile_eq_zero_of_ge_seven_quarters (by linarith : 7 / 4 ≤ t)

/-- The two-term partition identity: `ρ(θ)² + ρ(θ+1)² = 1` for `θ ∈ [0,1]`. -/
lemma profile_pu (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (rhoProfile θ) ^ 2 + (rhoProfile (θ + 1)) ^ 2 = 1 := by
  have hθ1 : θ ≤ 1 := hθ.2
  have hθ0 : 0 ≤ θ := hθ.1
  -- `w(2−θ) = 1` and `w(θ+1) = 1` for `θ ∈ [0,1]`
  have hrise2 : rise (2 - θ) = 1 := rise_one (by linarith : 3 / 4 ≤ 2 - θ)
  have hriseB : rise (θ + 1) = 1 := rise_one (by linarith : 3 / 4 ≤ θ + 1)
  unfold rhoProfile
  rw [hrise2, hriseB]
  rw [show 2 - (θ + 1) = 1 - θ by ring]
  ring_nf
  exact rise_sq_add θ

/-- The derivative vanishes off the open interval `(0,2)` (flat at the seams). -/
lemma profile_deriv_supp (t : ℝ) (ht : t ≤ 0 ∨ 2 ≤ t) : deriv rhoProfile t = 0 := by
  rcases ht with ht | ht
  · have ht14 : t < 1 / 4 := by linarith
    apply deriv_eq_zero_of_eventually_eq
    refine ⟨Set.Iio (1 / 4), ?_, ?_⟩
    · exact isOpen_Iio.mem_nhds ht14
    · intro y hy
      rw [rhoProfile_eq_zero_of_le_quarter (le_of_lt hy),
        rhoProfile_eq_zero_of_le_quarter (le_of_lt ht14)]
  · have ht74 : 7 / 4 < t := by linarith
    apply deriv_eq_zero_of_eventually_eq
    refine ⟨Set.Ioi (7 / 4), ?_, ?_⟩
    · exact isOpen_Ioi.mem_nhds ht74
    · intro y hy
      rw [rhoProfile_eq_zero_of_ge_seven_quarters (le_of_lt hy),
        rhoProfile_eq_zero_of_ge_seven_quarters (le_of_lt ht74)]

/-- The derivative is bounded (existence form; any finite bound suffices for
the grid estimate, whose constant is absorbed later). -/
lemma profile_deriv_bdd : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |deriv rhoProfile t| ≤ A := by
  let f : ℝ → ℝ := fun t => |deriv rhoProfile t|
  have hcontD : Continuous (deriv rhoProfile) :=
    profile_contDiff.continuous_deriv (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hcont : Continuous f := hcontD.abs
  have hbdd := isCompact_Icc.bddAbove_image (K := (Set.Icc (0 : ℝ) 2)) hcont.continuousOn
  rcases hbdd with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · have hle : f t ≤ M := hM ⟨t, ht, rfl⟩
    exact le_trans hle (le_max_left M 0)
  · have hz : deriv rhoProfile t = 0 := by
      apply profile_deriv_supp
      rcases lt_or_ge t 0 with hneg | hnonneg
      · exact Or.inl (le_of_lt hneg)
      · have hnotle : ¬ t ≤ 2 := by
          intro hle
          exact ht ⟨hnonneg, hle⟩
        exact Or.inr (le_of_lt (lt_of_not_ge hnotle))
    simp [hz]

end BoseGases

end Submission
