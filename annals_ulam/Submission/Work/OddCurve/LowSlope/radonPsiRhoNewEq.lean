import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddCurve.LowSlope.radonPhiRhoNewEq
import Submission.Work.OddRadon.radonInverse_radonPsi_local
import Submission.Work.OddRadon.radonProfile_radonInverse_local

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The second datum of the reconstructed body is the glued second datum.**

`rhoNew R r` is built from the two radial functions `R, r` of the two-power system with data
`(GluePhi n ρa, GluePsi n ρa)`.  Its second Radon datum is then the glued datum itself on the
interval `(0,b)`:

  `radonPsi n (rhoNew R r) c = GlueG n ρa c`   (`c ∈ (0,b)`).

The proof has two halves, exactly as for the first datum (`radonPhiRhoNewEq`):

* the inverse Radon transform of the two data agree on `(0,b)`: the local inversion
  `radonInverse_radonPsi_local` turns `radonInverse n (radonPsi n (rhoNew R r))` at `u` into
  `u/2 (ρ_new u^{2n+1} - ρ_new (-u)^{2n+1}) = u/2 (R(arccos u)^{2n+1} - r(arccos u)^{2n+1})`,
  which is `radonInverse n (GlueG n ρa) u` by the *second* two-power equation
  `(R^{2n+1} - r^{2n+1}) cos α = GluePsi n ρa α` evaluated at `α = arccos u`, using that
  `GluePsi n ρa α = 2 𝓡^{-1}(GlueG n ρa)(cos α)`;
* both data are even (`radonPsi_neg`, `GlueG_even`) and `C^∞` on `[0,b]`, so the local
  right-inverse identity `radonProfile_radonInverse_local` recovers each datum from the inverse
  transform of the other. -/
theorem radonPsiRhoNewEq (n : ℕ) (hn : 1 ≤ n) {ρa R r : ℝ → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.rhoNew R r)
      (Set.Ioo (-1 : ℝ) 1))
    (hRsys : Work.OddRadon.RadialSystem n (Work.OddCurve.LowSlope.GluePhi n ρa)
      (Work.OddCurve.LowSlope.GluePsi n ρa) R r)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hsmPsi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.radonPsi n (Work.OddCurve.LowSlope.rhoNew R r)) (Set.Icc 0 b))
    (hsmG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.GlueG n ρa) (Set.Icc 0 b)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) b,
      Work.OddCurve.LowSlope.radonPsi n (Work.OddCurve.LowSlope.rhoNew R r) c =
        Work.OddCurve.LowSlope.GlueG n ρa c := by
  -- The two data have the same inverse Radon transform on `(0,b)`.
  have hkey : ∀ u ∈ Set.Ioo (0 : ℝ) b,
      Work.OddRadon.radonInverse n (radonPsi n (rhoNew R r)) u =
        Work.OddRadon.radonInverse n (GlueG n ρa) u := by
    intro u hu
    obtain ⟨c₁, huc₁, hc₁lt⟩ : ∃ c₁, u < c₁ ∧ c₁ < 1 :=
      ⟨(u + 1) / 2, by linarith [hu.2], by linarith [hu.2]⟩
    rw [Work.OddRadon.radonInverse_radonPsi_local n hn hc₁lt hsm hu.1 huc₁]
    -- evaluate the reconstructed profile at `u` and at `-u`
    have hpu : rhoNew R r u = R (Real.arccos u) := rhoNew_of_nonneg hu.1.le
    have hpn : rhoNew R r (-u) = r (Real.arccos u) := by
      rw [rhoNew_of_neg (by linarith [hu.1] : -u < 0), neg_neg]
    rw [hpu, hpn]
    -- the second two-power equation at the normal angle `arccos u`
    have hαmem : Real.arccos u ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨Real.arccos_nonneg u, (Real.arccos_le_pi_div_two).mpr hu.1.le⟩
    have hcos : Real.cos (Real.arccos u) = u :=
      Real.cos_arccos (by linarith [hu.1]) (by linarith [hu.2, hb1])
    have hsys := (hRsys (Real.arccos u) hαmem).2
    rw [hcos] at hsys
    have hGluePsi : GluePsi n ρa (Real.arccos u)
        = 2 * Work.OddRadon.radonInverse n (GlueG n ρa) u := by
      simp only [GluePsi, hcos]
    rw [hGluePsi] at hsys
    rw [show u / 2 * (R (Real.arccos u) ^ (2 * n + 1) - r (Real.arccos u) ^ (2 * n + 1))
          = (R (Real.arccos u) ^ (2 * n + 1) - r (Real.arccos u) ^ (2 * n + 1)) * u / 2
        by ring, hsys]
    ring
  intro c hc
  have h1 : Work.OddRadon.radonProfile (2 * n + 1)
      (fun u : ℝ => Work.OddRadon.radonInverse n
        (radonPsi n (rhoNew R r)) |u|) c = radonPsi n (rhoNew R r) c :=
    Work.OddRadon.radonProfile_radonInverse_local n hn hb hb1 hsmPsi
      (radonPsi_neg n (rhoNew R r)) c hc
  have h2 : Work.OddRadon.radonProfile (2 * n + 1)
      (fun u : ℝ => Work.OddRadon.radonInverse n (GlueG n ρa) |u|) c = GlueG n ρa c :=
    Work.OddRadon.radonProfile_radonInverse_local n hn hb hb1 hsmG
      (GlueG_even n ρa) c hc
  rw [← h1, ← h2]
  simp only [Work.OddRadon.radonProfile]
  congr 1
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({0} : Set ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr ((Set.finite_singleton (0 : ℝ)).measure_zero volume)
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hcompl] with s hs hmem
  have hs1 : |s| ≤ 1 := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h : (-1 : ℝ) < s := by
        simpa [min_eq_left (by norm_num : (-1 : ℝ) ≤ 1)] using hmem.1
      linarith
    · have h : s ≤ (1 : ℝ) := by
        simpa [max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] using hmem.2
      linarith
  have hsne : s ≠ 0 := by simpa using hs
  have habs : |c * s| < b := by
    rw [abs_mul, abs_of_pos hc.1]
    calc c * |s| ≤ c * 1 := mul_le_mul_of_nonneg_left hs1 hc.1.le
      _ = c := mul_one c
      _ < b := hc.2
  have hpos : 0 < |c * s| := abs_pos.mpr (mul_ne_zero (ne_of_gt hc.1) hsne)
  rw [hkey |c * s| ⟨hpos, habs⟩]

end

end Work.OddCurve.LowSlope
