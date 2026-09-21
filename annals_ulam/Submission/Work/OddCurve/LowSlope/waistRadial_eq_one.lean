import Mathlib
import Submission.Work.OddCurve.LowSlope.exists_radialFunction_of_strictConcaveProfile
import Submission.Work.OddEnvelope.Main

/-!
# The waist of the radial function is the unit circle

Let `f = envelopeProfile h X Y` be the profile of the odd case (strictly concave on `[-1,1]`,
`f 0 = 1`, `f = √(1-t²)` on the unperturbed part `(-tStar, tStar)`, see
`Work.OddEnvelope.envelopeProfile_eq_semicircle`) and let `ρ` be a *radial function* of `f`,
i.e. a positive function with

  `ρ u * √(1-u²) = f (ρ u * u)`   for `-1 < u < 1`,

so that the ray of direction `(u, √(1-u²))` meets the graph of `f` at the point
`(ρ u · u, ρ u · √(1-u²))`.  Then `ρ u = 1` for `|u| < tStar`: the rays whose direction has
cosine `u` with `|u| < tStar` meet the graph **on the circular arc**, whose radial function is
identically `1`, and they meet it nowhere else.

The argument is a two-line consequence of strict concavity, and needs no differentiability.
Put `p := ρ u` and consider the function `G(λ) = f (λ u) - λ √(1-u²)` of the ray parameter.
`G` is strictly concave on `[0, 1/|u|]`, and `G 0 = f 0 = 1 > 0` while `G 1 = 0` because `f`
is the semicircle at `u`.  `G(p) = 0` by the radial-graph identity.  A strictly concave
function taking a positive value at `0` and vanishing at `1` cannot vanish anywhere else in
`(0, 1/|u|)`: `G(1) > (1-1/λ) G 0 + (1/λ) G λ`.  Hence `p = 1`.

This is the statement that on the circular part of the profile the radial function is the
constant `1` — the "waist" of the body of revolution is the unit circle there.
-/

namespace Work.OddCurve.LowSlope

open Set

/-- **Key elementary lemma.**  If `f` is strictly concave on `[-1,1]` with `f 0 = 1`, if `f u` is
the value of the semicircle at `u`, and if the point `ρ u · u` of the ray of direction
`(u, √(1-u²))` lies on the graph of `f` (`hgraph`) inside `[-1,1]`, then `ρ u = 1`.

The proof compares the strictly concave function `λ ↦ f (λ u) - λ √(1-u²)` at the three
parameters `0`, `1` (where it vanishes, by `hfu` and `hf0`) and `ρ u` (where it vanishes, by
`hgraph`). -/
private lemma radial_eq_one_of_strictConcaveOn {f ρ : ℝ → ℝ} {u : ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f) (hf0 : f 0 = 1)
    (hfu : f u = Real.sqrt (1 - u ^ 2)) (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (hρpos : 0 < ρ u) (hgraph : ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hbound : ρ u * u ∈ Set.Icc (-1 : ℝ) 1) : ρ u = 1 := by
  have hcc := hconc.2
  rcases eq_or_ne u 0 with rfl | hu0
  · simpa [hf0] using hgraph
  · have h0mem : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
    have hne : (0 : ℝ) ≠ u := Ne.symm hu0
    rcases lt_trichotomy (ρ u) 1 with hp1 | hp1 | hp1
    · -- `ρ u < 1`: concavity at the parameters `0`, `1`, `ρ u` would force `1 < ρ u`.
      have h := hcc h0mem hu hne (a := 1 - ρ u) (b := ρ u) (by linarith) hρpos (by ring)
      simp only [smul_eq_mul, mul_zero, zero_add] at h
      rw [hf0, hfu, ← hgraph] at h
      nlinarith
    · exact hp1
    · -- `1 < ρ u`: concavity at the parameters `0`, `ρ u`, `1` would force `ρ u < 1`.
      have hpne : ρ u ≠ 0 := ne_of_gt hρpos
      have hpu_ne : (0 : ℝ) ≠ ρ u * u := (mul_ne_zero hpne hu0).symm
      have ha1 : 0 < 1 - (ρ u)⁻¹ := by
        have := inv_lt_one_of_one_lt₀ hp1
        linarith
      have hb1 : 0 < (ρ u)⁻¹ := inv_pos.mpr hρpos
      have hab : 1 - (ρ u)⁻¹ + (ρ u)⁻¹ = 1 := by ring
      have h := hcc h0mem hbound hpu_ne (a := 1 - (ρ u)⁻¹) (b := (ρ u)⁻¹) ha1 hb1 hab
      simp only [smul_eq_mul, mul_zero, zero_add] at h
      have hcomb : (ρ u)⁻¹ * (ρ u * u) = u := by
        rw [inv_mul_cancel_left₀ hpne]
      rw [hcomb] at h
      rw [hf0, hfu, ← hgraph] at h
      have hsimp : (ρ u)⁻¹ * (ρ u * Real.sqrt (1 - u ^ 2)) = Real.sqrt (1 - u ^ 2) := by
        rw [inv_mul_cancel_left₀ hpne]
      rw [hsimp] at h
      have hlt : 1 < (ρ u)⁻¹ := by linarith
      have h2 : ρ u * 1 < ρ u * (ρ u)⁻¹ := mul_lt_mul_of_pos_left hlt hρpos
      rw [mul_one, mul_inv_cancel₀ hpne] at h2
      linarith

/-- **The radial function on the circular waist.**  If `ρ` is the radial function of the envelope
profile `f = envelopeProfile h X Y` of an envelope curve (`ρ u * √(1-u²) = f (ρ u · u)`,
`ρ > 0`), then `ρ u = 1` for every `|u| < tStar`, i.e. on the whole part of the body cut out by
directions whose cosine is below the threshold `tStar = profileX (1-τ)`: there the profile is the
unit semicircle and its radial function is the constant `1`. -/
theorem waistRadial_eq_one {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρ0 : ρ 0 = 1)
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    (hbound : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1)
    {u : ℝ} (hu : |u| < Work.OddEnvelope.tStar) : ρ u = 1 := by
  have hu_star : -Work.OddEnvelope.tStar < u ∧ u < Work.OddEnvelope.tStar := abs_lt.mp hu
  have huIoo : u ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [Work.OddEnvelope.tStar_lt_one, hu_star.1],
     by linarith [Work.OddEnvelope.tStar_lt_one, hu_star.2]⟩
  have huIcc : u ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt huIoo.1, le_of_lt huIoo.2⟩
  have hpuIcc : ρ u * u ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_of_lt (hbound u huIoo).1, le_of_lt (hbound u huIoo).2⟩
  have hfu : Work.OddEnvelope.envelopeProfile h X Y u = Real.sqrt (1 - u ^ 2) := by
    rw [Work.OddEnvelope.envelopeProfile_eq_semicircle H ⟨hu_star.1, hu_star.2⟩]
    rfl
  exact radial_eq_one_of_strictConcaveOn (Work.OddEnvelope.strictConcaveOn_envelopeProfile H)
    Work.OddEnvelope.envelopeProfile_zero hfu huIcc (hρpos u huIoo) (hgraph u huIoo) hpuIcc

end Work.OddCurve.LowSlope
