import Mathlib
import Submission.Work.OddCurve.LowSlope.radonInverse_radonPhi
import Submission.Work.OddRadon.radonProfile_inv_local
import Submission.Work.OddCurve.LowSlope.Datum

namespace Work.OddRadon

open MeasureTheory Set
open scoped Topology ContDiff Interval

/-- **Locality in the profile variable of the inversion of the first Radon datum.**

`Work.OddCurve.LowSlope.radonInverse_radonPhi` identifies `radonInverse n (radonPhi n ρ)` with
the even profile `γ u = u²/2 (ρ u ^{2n+2} + ρ (-u)^{2n+2})`, but only under the hypothesis that
`γ` is `C¹` on the *whole* interval `[-1,1]`.  In the low-slope step the profile is only known on
`[-c₁,c₁]` for some `c₁ < 1`, and the identity is only needed at a point `u < c₁`.

Both obstructions are handled by locality:

* `radonInverse n F u` depends only on the datum `F` on `(0,c₀)` for any `c₀ > u`
  (`radonInverse_congr_of_eqOn`), and on `(0,c₀)` the first datum `radonPhi n ρ` only sees `ρ`
  on `(-c₀,c₀)`;
* the inversion of an *even* profile only needs `C¹` on `[-c₁,c₁]`
  (`radonProfile_inv_local`).

Interleaving the two gives the identity on `(0,c₁)` with no global regularity assumption. -/
lemma radonInverse_radonPhi_local (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {c₁ u : ℝ}
    (hc₁ : c₁ < 1) (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hu : 0 < u) (huc : u < c₁) :
    Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPhi n ρ) u
      = u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) := by
  have hc₁pos : 0 < c₁ := lt_trans hu huc
  set γ : ℝ → ℝ := fun u : ℝ => u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) with hγ
  -- an intermediate point of `(u, c₁)`, used both as the locality radius and the `C¹` radius
  set c₀ : ℝ := (u + c₁) / 2 with hc₀
  have huc₀ : u < c₀ := by rw [hc₀]; linarith
  have hc₀c₁ : c₀ < c₁ := by rw [hc₀]; linarith
  have hc₀pos : 0 < c₀ := lt_trans hu huc₀
  -- the even profile is even
  have hγeven : ∀ t : ℝ, γ (-t) = γ t := by
    intro t
    rw [hγ]
    simp only
    rw [neg_sq, neg_neg]
    ring
  -- and `C¹` on `[-c₁,c₁]`, since `ρ` is `C^∞` on `(-1,1) ⊇ [-c₁,c₁]`
  have hγsm : ContDiffOn ℝ 1 γ (Set.Icc (-c₁) c₁) := by
    rw [hγ]
    have hρ1 : ContDiffOn ℝ 1 ρ (Set.Icc (-c₁) c₁) :=
      (hρsm.of_le (by simp)).mono (by
        intro x hx
        rw [Set.mem_Icc] at hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hmap : Set.MapsTo (fun u : ℝ => -u) (Set.Icc (-c₁) c₁) (Set.Ioo (-1 : ℝ) 1) := by
      intro x hx
      rw [Set.mem_Icc] at hx
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hnegcont : ContDiffOn ℝ 1 (fun u : ℝ => -u) (Set.Icc (-c₁) c₁) := by fun_prop
    have hneg : ContDiffOn ℝ 1 (fun u : ℝ => ρ (-u)) (Set.Icc (-c₁) c₁) :=
      (hρsm.of_le (by simp)).comp hnegcont hmap
    exact ((contDiffOn_id (𝕜 := ℝ) (s := Set.Icc (-c₁) c₁)).pow 2).div_const 2 |>.mul
      ((hρ1.pow (2 * n + 2)).add (hneg.pow (2 * n + 2)))
  -- the local inversion of the even profile
  have hloc := radonProfile_inv_local n hn hc₀pos hc₀c₁ hc₁ hγsm hγeven (u := u) ⟨hu, huc₀⟩
  -- on `(0,c₀)` the first datum of `ρ` is the Radon profile of its even part, namely `γ`
  have hagree : ∀ c ∈ Set.Ioo (0 : ℝ) c₀,
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddRadon.radonProfile (2 * n + 1) γ c := by
    intro c hc
    have hcabs : |c| < 1 := by
      have hcc₀ : c < c₀ := hc.2
      rw [abs_of_pos hc.1]; linarith
    have hG₁ : ContinuousOn (fun s : ℝ => (c * s) ^ 2 * ρ (c * s) ^ (2 * n + 2))
        (Set.uIcc (-1 : ℝ) 1) :=
      Work.OddCurve.LowSlope.continuousOn_profile_comp_mul n hcabs hρsm
    have hG₂ : ContinuousOn (fun s : ℝ => (-(c * s)) ^ 2 * ρ (-(c * s)) ^ (2 * n + 2))
        (Set.uIcc (-1 : ℝ) 1) := by
      have h := Work.OddCurve.LowSlope.continuousOn_profile_comp_mul n (ρ := ρ) (a := -c)
        (by simpa using hcabs) hρsm
      refine h.congr ?_
      intro s _
      simp only []
      rw [show (-c) * s = -(c * s) by ring]
    have hf := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hG₁
    have hg := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hG₂
    have h1 : Work.OddCurve.LowSlope.radonPhi n ρ c
        = Work.OddRadon.radonProfile (2 * n + 1)
            (fun v : ℝ => (v ^ 2 * ρ v ^ (2 * n + 2)
              + (fun w : ℝ => w ^ 2 * ρ w ^ (2 * n + 2)) (-v)) / 2) c := by
      unfold Work.OddCurve.LowSlope.radonPhi
      exact Work.OddCurve.LowSlope.radonProfile_evenPart (2 * n + 1) hf hg
    have h2 : (fun v : ℝ => (v ^ 2 * ρ v ^ (2 * n + 2)
        + (fun w : ℝ => w ^ 2 * ρ w ^ (2 * n + 2)) (-v)) / 2) = γ := by
      rw [hγ]
      funext v
      simp only []
      ring
    rw [h1, h2]
  have hcongr := Work.OddCurve.LowSlope.radonInverse_congr_of_eqOn (n := n) hu huc₀ hagree
  rw [hcongr, ← hloc, hγ]

end Work.OddRadon
