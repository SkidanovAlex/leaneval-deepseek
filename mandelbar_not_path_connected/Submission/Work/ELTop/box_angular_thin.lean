/-
# The angular window `|Re - R| < a`, `|Im| < b` in the rotated Böttcher plane is thin

Fixing an angle `θ`, the rotation `rayRot θ w = w * exp (-2πiθ)` carries the point
`rayPoint θ R = R exp (2πiθ)` of the exterior disc to `R`.  Hence a point `c ∉ Mb` whose rotated
Böttcher coordinate lies in the small box `|Re - R| < a`, `|Im| < b` about `(R,0)` has its
Böttcher coordinate close to `rayPoint θ R`, so its external angle is close to `θ` *modulo*
`1`.  That is the content of `box_angular_thin`: there are `a, b > 0`, `a < R`, such that every
`z` whose rotated Böttcher coordinate lies in that box has its external angle within `η` of
`θ + k` for some `k : ℤ`.

The proof is the standard one, and it is carried out once for an arbitrary Nakane datum
(`exists_extAngle_close_int`), where the conclusion is phrased with the integral `k` so that
no reduction of `θ` modulo `1` is needed:

* the ratio `w = Φ z / rayPoint θ R` is close to `1`, so `Complex.arg w` is small;
* writing `A = arg (Φ z) / (2π)`, the congruence of the arguments modulo `2π`
  (`NakaneData.exists_int_arg_sub_arg_div`) gives an integer `n` with `|A - (θ + n)| < ε`;
* `extAngle Φ z` is the element of `[0,1)` congruent to `A` modulo `1`
  (`toIcoMod_eq_iff`), hence `A = extAngle Φ z + m` for some `m : ℤ`, and `k = n - m` works.

The dynamical statement follows by applying this to `Mb := K c`, `Φ := dynPhi c φ`; the box
hypothesis forces `z ∉ K c` because `dynPhi` vanishes on `K c` while `a < R`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.Top.Defs
import Submission.Work.Top.extAngle_close_of_Phi_close

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

/-! ## The rotation `rayRot` -/

theorem rayRot_sub (θ : ℝ) (u v : ℂ) :
    Work.Top.rayRot θ (u - v) = Work.Top.rayRot θ u - Work.Top.rayRot θ v := by
  simp only [Work.Top.rayRot_apply]
  ring

theorem rayRot_rayPoint_self (θ R : ℝ) :
    Work.Top.rayRot θ (Work.Top.NakaneData.rayPoint θ R) = (R : ℂ) := by
  rw [Work.Top.NakaneData.rayPoint, Work.Top.rayRot_apply]
  rw [mul_assoc, ← Complex.exp_add]
  rw [show 2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I +
      -(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) = 0 from by ring, Complex.exp_zero]
  ring

/-- The rotation `rayRot θ` is a Euclidean isometry and fixes `rayPoint θ R`, so the distance
to `rayPoint θ R` in the Böttcher plane is the distance to `R` in the rotated plane. -/
theorem norm_sub_rayPoint_eq_norm_rayRot_sub (θ R : ℝ) (w : ℂ) :
    ‖w - Work.Top.NakaneData.rayPoint θ R‖ = ‖Work.Top.rayRot θ w - (R : ℂ)‖ := by
  rw [← Work.Top.norm_rayRot θ (w - Work.Top.NakaneData.rayPoint θ R), rayRot_sub,
    rayRot_rayPoint_self]

/-- The box `|Re - R| < a`, `|Im| < b` about `(R,0)` is contained in the disc of radius
`a + b`: `‖w - R‖ ≤ |Re w - R| + |Im w|`. -/
theorem norm_sub_of_re_im_lt {R a b : ℝ} {w : ℂ} (hre : |w.re - R| < a) (him : |w.im| < b) :
    ‖w - (R : ℂ)‖ < a + b := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (w - (R : ℂ))
  rw [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero] at h1
  linarith

/-! ## The argument is small near `1` -/

theorem exists_arg_lt_of_norm_sub_one_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ w : ℂ, ‖w - 1‖ < δ₁ → |Complex.arg w| < 2 * Real.pi * ε := by
  have h2πε : (0 : ℝ) < 2 * Real.pi * ε :=
    mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi) hε
  have hmem : Complex.arg (1 : ℂ) ∈ Set.Ioo (-(2 * Real.pi * ε)) (2 * Real.pi * ε) := by
    simp only [Complex.arg_one]
    exact ⟨by linarith, h2πε⟩
  have h1slit : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_one, Complex.ofReal_mem_slitPlane]
    norm_num
  have hev : ∀ᶠ w in 𝓝 (1 : ℂ), |Complex.arg w| < 2 * Real.pi * ε := by
    have h1 := (Complex.continuousAt_arg h1slit).preimage_mem_nhds (isOpen_Ioo.mem_nhds hmem)
    filter_upwards [h1] with w hw using abs_lt.mpr hw
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hev
  exact ⟨δ₁, hδ₁pos, fun w hw => hδ₁ (by simpa [dist_eq_norm] using hw)⟩

/-! ## External angles close to `θ` modulo `1` -/

/-- If the Böttcher coordinate of `c ∉ Mb` is close to the point `rayPoint θ R` of the exterior
disc, then the external angle of `c` is close to `θ` modulo `1`.  The conclusion is phrased
with an integral `k`, so no reduction of `θ` modulo `1` is needed. -/
theorem exists_extAngle_close_int {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {θ R η : ℝ} (hR : 1 < R) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ∉ Mb →
      ‖Φ z - Work.Top.NakaneData.rayPoint θ R‖ < δ →
      ∃ k : ℤ, |Work.Top.NakaneData.extAngle Φ z - (θ + k)| < η := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  -- a tolerance `ε`, smaller than `η`
  set ε : ℝ := min η (1 / 4) / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    have h : (0 : ℝ) < min η (1 / 4) := lt_min hη (by norm_num)
    linarith
  have hεη : ε < η := by
    rw [hεdef]
    have h := min_le_left η (1 / 4 : ℝ)
    linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_arg_lt_of_norm_sub_one_lt hεpos
  refine ⟨R * δ₁, by positivity, ?_⟩
  intro z hz hdist
  have hz0 : Work.Top.NakaneData.rayPoint θ R ≠ 0 := by
    intro h
    have h1 := Work.Top.NakaneData.norm_rayPoint θ R
    rw [h, norm_zero] at h1
    have h2 : |R| = 0 := h1.symm
    rw [abs_eq_zero] at h2
    linarith
  have hnorm0 : ‖Work.Top.NakaneData.rayPoint θ R‖ = R := by
    rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos hRpos]
  have hΦz : Φ z ≠ 0 := hN.Phi_ne_zero hz
  set w : ℂ := Φ z / Work.Top.NakaneData.rayPoint θ R with hwdef
  have hw1 : w - 1 = (Φ z - Work.Top.NakaneData.rayPoint θ R) /
      Work.Top.NakaneData.rayPoint θ R := by
    rw [hwdef, sub_div, div_self hz0]
  have hwdist : ‖w - 1‖ < δ₁ := by
    rw [hw1, norm_div, hnorm0, div_lt_iff₀ hRpos]
    linarith
  have hargw : |Complex.arg w| < 2 * Real.pi * ε := hδ₁ w hwdist
  -- `|arg w / (2π)| < ε`
  have hargw2 : |Complex.arg w / (2 * Real.pi)| < ε := by
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [abs_div, abs_of_pos h2π, div_lt_iff₀ h2π]
    linarith
  -- the congruence of the arguments modulo `2π`
  obtain ⟨n, hn⟩ := Work.Top.NakaneData.exists_int_arg_sub_arg_div (z := Φ z)
    (z₀ := Work.Top.NakaneData.rayPoint θ R) hΦz hz0
    (Work.Top.NakaneData.arg_rayPoint_coe_angle hRpos)
  -- rewriting it as a statement about `A = arg (Φ z) / (2π)`
  have hA : Complex.arg (Φ z) / (2 * Real.pi) - θ - (n : ℝ) =
      Complex.arg w / (2 * Real.pi) := by
    have h1 : Complex.arg (Φ z) =
        Complex.arg w + 2 * Real.pi * θ + 2 * Real.pi * (n : ℝ) := by linarith [hn]
    rw [h1]
    field_simp
    ring
  have hAclose : |Complex.arg (Φ z) / (2 * Real.pi) - (θ + (n : ℝ))| < ε := by
    rw [show Complex.arg (Φ z) / (2 * Real.pi) - (θ + (n : ℝ)) =
      Complex.arg (Φ z) / (2 * Real.pi) - θ - (n : ℝ) from by ring, hA]
    exact hargw2
  -- `extAngle` is the element of `[0,1)` congruent to `A` modulo `1`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Complex.arg (Φ z) / (2 * Real.pi) =
      Work.Top.NakaneData.extAngle Φ z + (m : ℝ) := by
    have h := (toIcoMod_eq_iff (p := (1 : ℝ)) one_pos (a := (0 : ℝ))
      (b := Complex.arg (Φ z) / (2 * Real.pi))
      (c := Work.Top.NakaneData.extAngle Φ z)).mp
      (by rw [Work.Top.NakaneData.extAngle])
    obtain ⟨-, m, hm⟩ := h
    exact ⟨m, by simpa using hm⟩
  refine ⟨n - m, ?_⟩
  have hk : Work.Top.NakaneData.extAngle Φ z - (θ + ((n - m : ℤ) : ℝ)) =
      Complex.arg (Φ z) / (2 * Real.pi) - (θ + (n : ℝ)) := by
    have hcast : ((n - m : ℤ) : ℝ) = (n : ℝ) - (m : ℝ) := by push_cast; ring
    rw [hcast]
    linarith [hm]
  rw [hk]
  exact lt_trans hAclose hεη

/-! ## The statement for the dynamical plane -/

theorem box_angular_thin {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {R θ η : ℝ} (hR : 1 < R) (hη : 0 < η) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a < R ∧
      ∀ z : ℂ, |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).re - R| < a →
        |(Work.Top.rayRot θ (Work.EL.dynPhi c φ z)).im| < b →
        ∃ k : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - (θ + k)| < η := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_extAngle_close_int (Mb := Work.EL.K c)
    (Φ := Work.EL.dynPhi c φ) hN hR hη
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  refine ⟨min (R / 2) (δ / 4), δ / 4, lt_min (by linarith) (by linarith),
    by linarith, ?_, ?_⟩
  · have h := min_le_left (R / 2) (δ / 4)
    linarith
  · intro z hre him
    have hbox : ‖Work.Top.rayRot θ (Work.EL.dynPhi c φ z) - (R : ℂ)‖ < δ := by
      have h1 : ‖Work.Top.rayRot θ (Work.EL.dynPhi c φ z) - (R : ℂ)‖ <
          min (R / 2) (δ / 4) + δ / 4 := norm_sub_of_re_im_lt hre him
      have h2 : min (R / 2) (δ / 4) + δ / 4 ≤ δ := by
        have := min_le_right (R / 2) (δ / 4)
        linarith
      linarith
    by_cases hz : z ∈ Work.EL.K c
    · exfalso
      have hzero : Work.Top.rayRot θ (Work.EL.dynPhi c φ z) = 0 := by
        rw [Work.EL.dynPhi_of_mem hz, Work.Top.rayRot_apply, zero_mul]
      rw [hzero] at hre
      simp only [Complex.zero_re, zero_sub, abs_neg, abs_of_pos hRpos] at hre
      have := min_le_left (R / 2) (δ / 4)
      linarith
    · refine hδ z hz ?_
      rwa [norm_sub_rayPoint_eq_norm_rayRot_sub]

end Work.ELTop
