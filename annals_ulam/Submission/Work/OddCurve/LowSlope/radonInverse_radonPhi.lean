import Mathlib
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddRadon.RadonInversion

/-!
# The right inverse of the first Radon datum of a low-slope profile

The first Radon datum of the body of revolution with radial function `ρ` is
`radonPhi n ρ = radonProfile (2n+1) (u ↦ u² ρ(u)^{2n+2})`.  The point of this file is the
observation that the *spherical* Radon transform of a function of one coordinate only sees the
**even part** of the profile: an even weight times an odd function integrates to `0` over the
symmetric interval, so `radonProfile d γ = radonProfile d (fun u => (γ u + γ (-u))/2)`.

Consequently, for the *even* profile
`γ(u) = u²/2 (ρ(u)^{2n+2} + ρ(-u)^{2n+2})` we have `radonPhi n ρ = radonProfile (2n+1) γ`, and the
left-inverse theorem `Work.OddRadon.radonProfile_inv` gives the result of the file:

`radonInverse n (radonPhi n ρ) u = u²/2 (ρ(u)^{2n+2} + ρ(-u)^{2n+2})` for `u ∈ (0,1)`.

This is the "tautology" that replaces the paper's right-inverse step: for radial functions
`R, r` the pair `(R(|·|), r(|·|))` always solves the paper's system with the datum it defines,
because the datum is by construction the Radon profile of the even profile
`u²/2 (R(|u|)^{2n+2} + r(|u|)^{2n+2})`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **Averaging an integrand with its reflection does not change the integral against an even
weight.**  Both integrability hypotheses are needed (without them the Bochner integral is `0`
and additivity is lost); they are supplied by the concrete continuity of the profile below. -/
lemma integral_evenWeight_mul_evenPart (A γ : ℝ → ℝ) (c : ℝ) (hA : ∀ t, A (-t) = A t)
    (hf : IntervalIntegrable (fun s : ℝ => A s * γ (c * s)) volume (-1 : ℝ) 1)
    (hg : IntervalIntegrable (fun s : ℝ => A s * γ (-(c * s))) volume (-1 : ℝ) 1) :
    (∫ s in (-1 : ℝ)..1, A s * ((γ (c * s) + γ (-(c * s))) / 2))
      = ∫ s in (-1 : ℝ)..1, A s * γ (c * s) := by
  have hpoint : (fun s : ℝ => A s * ((γ (c * s) + γ (-(c * s))) / 2))
      = fun s => ((fun s => A s * γ (c * s)) s + (fun s => A s * γ (-(c * s))) s) / 2 := by
    funext s; ring
  rw [hpoint]
  have h2 : (∫ s in (-1 : ℝ)..1,
        ((fun s => A s * γ (c * s)) s + (fun s => A s * γ (-(c * s))) s) / 2)
      = (2 : ℝ)⁻¹ * ((∫ s in (-1 : ℝ)..1, A s * γ (c * s))
          + (∫ s in (-1 : ℝ)..1, A s * γ (-(c * s)))) := by
    have h1 : (∫ s in (-1 : ℝ)..1,
          ((fun s => A s * γ (c * s)) s + (fun s => A s * γ (-(c * s))) s) / 2)
        = ∫ s in (-1 : ℝ)..1,
            (2 : ℝ)⁻¹ * ((fun s => A s * γ (c * s)) s + (fun s => A s * γ (-(c * s))) s) := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [h1, intervalIntegral.integral_const_mul]
    rw [show (∫ x in (-1 : ℝ)..1,
          ((fun s => A s * γ (c * s)) x + (fun s => A s * γ (-(c * s))) x))
        = (∫ x in (-1 : ℝ)..1, A x * γ (c * x))
          + (∫ x in (-1 : ℝ)..1, A x * γ (-(c * x))) from
      intervalIntegral.integral_add hf hg]
  rw [h2]
  have h3 : (∫ s in (-1 : ℝ)..1, A s * γ (-(c * s)))
      = ∫ s in (-1 : ℝ)..1, A s * γ (c * s) := by
    have h4 : (fun s : ℝ => A s * γ (-(c * s)))
        = fun s => (fun t => A t * γ (c * t)) (-s) := by
      funext s
      simp only []
      rw [hA s, show c * (-s) = -(c * s) by ring]
    rw [h4]
    have := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => A t * γ (c * t)) (a := (-1 : ℝ)) (b := 1)
    simpa using this
  rw [h3]
  ring

/-- **`radonProfile` only sees the even part of the profile.** -/
lemma radonProfile_evenPart (d : ℕ) {γ : ℝ → ℝ} {c : ℝ}
    (hf : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * s))
      volume (-1 : ℝ) 1)
    (hg : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (-(c * s)))
      volume (-1 : ℝ) 1) :
    Work.OddRadon.radonProfile d γ c
      = Work.OddRadon.radonProfile d (fun u => (γ u + γ (-u)) / 2) c := by
  have hA : ∀ t : ℝ, (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2)) (-t)
      = (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2)) t := by
    intro t
    simp only []
    rw [neg_sq]
  have hkey := integral_evenWeight_mul_evenPart
    (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2)) γ c hA hf hg
  simp only [Work.OddRadon.radonProfile]
  rw [hkey]

/-- **The Radon kernel `(1-s²)^{(2n+1)/2-2} = (1-s²)^{n-1}/√(1-s²)` is interval integrable
against any function continuous on `[-1,1]`.** -/
lemma intervalIntegrable_radonKernel_mul (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Set.uIcc (-1 : ℝ) 1)) :
    IntervalIntegrable
      (fun s : ℝ => (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * G s)
      volume (-1 : ℝ) 1 := by
  -- the singular factor `(1-s²)^{-1/2}` is integrable
  have hb : IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) ^ (-(1 / 2 : ℝ))) volume (-1 : ℝ) 1 := by
    refine (Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv).congr ?_
    intro x hx
    simp only []
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Ioc] at hx
    have hx1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rw [Real.sqrt_eq_rpow, Real.inv_rpow hx1]
    exact (Real.rpow_neg hx1 (1 / 2)).symm
  have hcont : ContinuousOn (fun s : ℝ => (1 - s ^ 2) ^ (n - 1) * G s) (Set.uIcc (-1 : ℝ) 1) := by
    have h1 : ContinuousOn (fun s : ℝ => 1 - s ^ 2) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
    exact (h1.pow (n - 1)).mul hG
  refine (hb.mul_continuousOn hcont).congr ?_
  intro s hs
  simp only []
  rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Ioc] at hs
  have hs1 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hexp : (-(1 / 2 : ℝ)) + (((n - 1 : ℕ) : ℝ)) = (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) := by
    rw [Nat.cast_sub hn]; push_cast; ring
  have hE : (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) ≠ 0 := by
    intro h
    have h1 : (((2 * n + 1 : ℕ) : ℝ)) = 4 := by linarith
    have h2 : (2 * n + 1 : ℕ) = 4 := by exact_mod_cast h1
    omega
  rcases eq_or_lt_of_le hs1 with h0 | hpos
  · rw [← h0]
    rw [Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0), Real.zero_rpow hE]
    ring
  · rw [← mul_assoc, ← Real.rpow_natCast (1 - s ^ 2) (n - 1), ← Real.rpow_add hpos, hexp]

/-- The profile function `u ↦ u² ρ(u)^{2n+2}` composed with `s ↦ a s` is continuous on `[-1,1]`
whenever `|a| < 1` and `ρ` is continuous on `(-1,1)`. -/
lemma continuousOn_profile_comp_mul (n : ℕ) {ρ : ℝ → ℝ} {a : ℝ} (ha : |a| < 1)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (fun s : ℝ => (a * s) ^ 2 * ρ (a * s) ^ (2 * n + 2)) (Set.uIcc (-1 : ℝ) 1) := by
  have hlin : ContinuousOn (fun s : ℝ => a * s) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
  have hmaps : Set.MapsTo (fun s : ℝ => a * s) (Set.uIcc (-1 : ℝ) 1) (Set.Ioo (-1 : ℝ) 1) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at hs
    have hsabs : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hle : |a * s| ≤ |a| := by
      rw [abs_mul]
      calc |a| * |s| ≤ |a| * 1 := mul_le_mul_of_nonneg_left hsabs (abs_nonneg a)
        _ = |a| := mul_one _
    exact abs_lt.mp (lt_of_le_of_lt hle ha)
  exact (hlin.pow 2).mul ((hρ.continuousOn.comp hlin hmaps).pow (2 * n + 2))

/-- **The inverse of the first Radon datum of a low-slope profile.**
For a radial function `ρ` of class `C^∞` on `(-1,1)` whose even profile
`u ↦ u²/2 (ρ(u)^{2n+2} + ρ(-u)^{2n+2})` is `C¹` on `[-1,1]`, the inverse Radon transform of the
first datum `radonPhi n ρ` is that even profile on `(0,1)`. -/
theorem radonInverse_radonPhi (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hη : ContDiffOn ℝ 1 (fun u : ℝ => u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)))
      (Set.Icc (-1 : ℝ) 1))
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPhi n ρ) u
      = u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) := by
  set γ : ℝ → ℝ := fun u : ℝ => u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2))
    with hγdef
  change Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPhi n ρ) u = γ u
  have hγeven : ∀ t : ℝ, γ (-t) = γ t := by
    intro t
    simp only [hγdef]
    rw [neg_sq, neg_neg]
    ring
  have hγsm : ContDiffOn ℝ 1 γ (Set.Icc (-1 : ℝ) 1) := hη
  have hleft := Work.OddRadon.radonProfile_inv n hn hγsm hγeven hu
  rw [hleft]
  refine radonInverse_congr_of_eqOn n hu.1 hu.2 ?_
  intro c hc
  have hcabs : |c| < 1 := abs_lt.mpr ⟨by linarith [hc.1], hc.2⟩
  have hG₁ : ContinuousOn (fun s : ℝ => (c * s) ^ 2 * ρ (c * s) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) :=
    continuousOn_profile_comp_mul n hcabs hρsm
  have hG₂ : ContinuousOn (fun s : ℝ => (-(c * s)) ^ 2 * ρ (-(c * s)) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) := by
    have h := continuousOn_profile_comp_mul n (ρ := ρ) (a := -c) (by simpa using hcabs) hρsm
    refine h.congr ?_
    intro s _
    simp only []
    rw [show (-c) * s = -(c * s) by ring]
  have hf : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2)
      * ((fun v : ℝ => v ^ 2 * ρ v ^ (2 * n + 2)) (c * s))) volume (-1 : ℝ) 1 :=
    intervalIntegrable_radonKernel_mul n hn hG₁
  have hg : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2)
      * ((fun v : ℝ => v ^ 2 * ρ v ^ (2 * n + 2)) (-(c * s)))) volume (-1 : ℝ) 1 :=
    intervalIntegrable_radonKernel_mul n hn hG₂
  have h1 : Work.OddCurve.LowSlope.radonPhi n ρ c
      = Work.OddRadon.radonProfile (2 * n + 1)
          (fun v : ℝ => (v ^ 2 * ρ v ^ (2 * n + 2)
            + (fun w : ℝ => w ^ 2 * ρ w ^ (2 * n + 2)) (-v)) / 2) c := by
    unfold Work.OddCurve.LowSlope.radonPhi
    exact radonProfile_evenPart (2 * n + 1) hf hg
  have h2 : (fun v : ℝ => (v ^ 2 * ρ v ^ (2 * n + 2)
        + (fun w : ℝ => w ^ 2 * ρ w ^ (2 * n + 2)) (-v)) / 2) = γ := by
    funext v
    show (v ^ 2 * ρ v ^ (2 * n + 2) + (-v) ^ 2 * ρ (-v) ^ (2 * n + 2)) / 2
      = v ^ 2 / 2 * (ρ v ^ (2 * n + 2) + ρ (-v) ^ (2 * n + 2))
    ring
  rw [h1, h2]

end

end Work.OddCurve.LowSlope
