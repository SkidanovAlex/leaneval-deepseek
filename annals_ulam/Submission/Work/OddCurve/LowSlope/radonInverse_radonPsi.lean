import Mathlib
import Submission.Work.OddCurve.LowSlope.radonInverse_radonPhi
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddRadon.RadonInversion

/-!
# The left inverse of the second Radon datum of a low-slope profile

The second Radon datum of the body of revolution with radial function `ρ` is

    `radonPsi n ρ = radonProfile (2n+1) (u ↦ u · ρ(u)^{2n+1})`,

the spherical Radon transform of `w ↦ w₁ ρ^d`.  As in the companion file
`radonInverse_radonPhi`, the spherical Radon transform of a function of one coordinate only sees
the **even part** of the profile (`radonProfile_evenPart`), and the even part of the (generally
neither even nor odd) weight `γ(u) = u ρ(u)^{2n+1}` is

    `(γ u + γ (-u))/2 = u/2 (ρ(u)^{2n+1} - ρ(-u)^{2n+1})`.

Hence `radonPsi n ρ = radonProfile (2n+1) γ_e` with `γ_e` even, and the left-inverse theorem
`Work.OddRadon.radonProfile_inv` yields

`radonInverse n (radonPsi n ρ) u = u/2 (ρ u^{2n+1} - ρ (-u)^{2n+1})`   for `u ∈ (0,1)`.

This is the second half of the "tautology" replacing the paper's right-inverse step: for radial
functions `R, r` the pair `(R(|·|), r(|·|))` has Radon data
`φ = radonProfile (2n+1) (u ↦ u²/2 (R^{2n+2} + r^{2n+2})(|u|))` and
`ψ = radonProfile (2n+1) (u ↦ u/2 (R^{2n+1} - r^{2n+1})(|u|))`, and inverting these data recovers
`Φ/2 = (R^{2n+2}+r^{2n+2})cos²`, `Ψ/2 = (R^{2n+1}-r^{2n+1})cos` — the paper's system.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The odd weight `u ↦ u ρ(u)^{2n+1}` composed with `s ↦ a s` is continuous on `[-1,1]`
whenever `|a| < 1` and the weight is continuous on `[-1,1]`.  (Companion of
`continuousOn_profile_comp_mul` for the second Radon datum.) -/
lemma continuousOn_weight_comp_mul (n : ℕ) {ρ : ℝ → ℝ}
    (hcont : ContinuousOn (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Icc (-1 : ℝ) 1))
    {a : ℝ} (ha : |a| < 1) :
    ContinuousOn (fun s : ℝ => (a * s) * ρ (a * s) ^ (2 * n + 1)) (Set.uIcc (-1 : ℝ) 1) := by
  have hlin : ContinuousOn (fun s : ℝ => a * s) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
  have hmaps : Set.MapsTo (fun s : ℝ => a * s) (Set.uIcc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at hs
    have hsabs : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hle : |a * s| ≤ |a| := by
      rw [abs_mul]
      calc |a| * |s| ≤ |a| * 1 := mul_le_mul_of_nonneg_left hsabs (abs_nonneg a)
        _ = |a| := mul_one _
    have hlt : |a * s| < 1 := lt_of_le_of_lt hle ha
    rw [Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le (a * s)], by linarith [le_abs_self (a * s)]⟩
  exact hcont.comp hlin hmaps

/-- **The second Radon datum of a low-slope profile inverts to the odd (even-part) weight.**

For a radial function `ρ` of class `C^∞` on `(-1,1)` whose weight
`u ↦ u ρ(u)^{2n+1}` extends continuously to `[-1,1]` and whose even part
`u ↦ u/2 (ρ(u)^{2n+1} - ρ(-u)^{2n+1})` is `C¹` on `[-1,1]`, the inverse Radon transform of the
second datum `radonPsi n ρ` is that even part on `(0,1)`. -/
theorem radonInverse_radonPsi (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hcont : ContinuousOn (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Icc (-1 : ℝ) 1))
    (hη : ContDiffOn ℝ 1 (fun u : ℝ => u / 2 * (ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)))
      (Set.Icc (-1 : ℝ) 1))
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPsi n ρ) u
      = u / 2 * (ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) := by
  set γ : ℝ → ℝ := fun u : ℝ => u / 2 * (ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) with hγdef
  change Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPsi n ρ) u = γ u
  have hγeven : ∀ t : ℝ, γ (-t) = γ t := by
    intro t
    simp only [hγdef, neg_neg]
    ring
  have hγsm : ContDiffOn ℝ 1 γ (Set.Icc (-1 : ℝ) 1) := hη
  have hleft := Work.OddRadon.radonProfile_inv n hn hγsm hγeven hu
  rw [hleft]
  refine radonInverse_congr_of_eqOn n hu.1 hu.2 ?_
  intro c hc
  have hcabs : |c| < 1 := abs_lt.mpr ⟨by linarith [hc.1], hc.2⟩
  have hG₁ : ContinuousOn (fun s : ℝ => (c * s) * ρ (c * s) ^ (2 * n + 1))
      (Set.uIcc (-1 : ℝ) 1) := continuousOn_weight_comp_mul n hcont hcabs
  have hG₂ : ContinuousOn (fun s : ℝ => (-(c * s)) * ρ (-(c * s)) ^ (2 * n + 1))
      (Set.uIcc (-1 : ℝ) 1) := by
    simpa only [neg_mul] using continuousOn_weight_comp_mul n hcont (a := -c) (by simpa using hcabs)
  have hf : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2)
      * ((fun v : ℝ => v * ρ v ^ (2 * n + 1)) (c * s))) volume (-1 : ℝ) 1 :=
    intervalIntegrable_radonKernel_mul n hn hG₁
  have hg : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2)
      * ((fun v : ℝ => v * ρ v ^ (2 * n + 1)) (-(c * s)))) volume (-1 : ℝ) 1 :=
    intervalIntegrable_radonKernel_mul n hn hG₂
  have h1 : Work.OddCurve.LowSlope.radonPsi n ρ c
      = Work.OddRadon.radonProfile (2 * n + 1)
          (fun v : ℝ => (v * ρ v ^ (2 * n + 1)
            + (fun w : ℝ => w * ρ w ^ (2 * n + 1)) (-v)) / 2) c := by
    unfold Work.OddCurve.LowSlope.radonPsi
    exact radonProfile_evenPart (2 * n + 1) hf hg
  have h2 : (fun v : ℝ => (v * ρ v ^ (2 * n + 1)
        + (fun w : ℝ => w * ρ w ^ (2 * n + 1)) (-v)) / 2) = γ := by
    funext v
    simp only [hγdef]
    ring
  rw [h1, h2]

end

end Work.OddCurve.LowSlope
