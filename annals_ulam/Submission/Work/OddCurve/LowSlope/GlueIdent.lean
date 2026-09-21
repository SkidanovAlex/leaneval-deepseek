import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddRadon.radonInverse_radonPhi_local
import Submission.Work.OddRadon.radonInverse_radonPsi_local

/-!
# Identification of the glued-data deviations with the anchor's radial function

On the cap `cos α < 4/5` the glued datum is the anchor's (`gluedPhi_of_lt`, `gluedPsi_of_lt`), so
the two deviations `GlueA`, `GlueB` of the two-power system are the *anchor's* radial function's
two power combinations:

`GlueA α = ρ (cos α)^{2n+2} + ρ (-cos α)^{2n+2} - 2`,
`GlueB α = ρ (cos α)^{2n+1} - ρ (-cos α)^{2n+1}`,

(`Work.OddCurve.LowSlope.GlueA_eq`, `GlueB_eq`).  Consequently the smallness of `GlueA`, `GlueB`
in `C²` is exactly the `C²`-closeness of the anchor's radial function to `1` — i.e. of the
anchor's curve to the semicircle's chord function — on the cap.  This is the quantitative input of
the whole low-slope step (`radialSystem_exists_C2`).
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- `radonInverse` of the glued first datum on the cap is `radonInverse` of the anchor's own
datum: on `(0,4/5)` the two data coincide (and `radonInverse` is local). -/
theorem radonInverse_GlueF_eq (n : ℕ) {ρ : ℝ → ℝ} {α : ℝ}
    (hc0 : 0 < Real.cos α) (hc : Real.cos α < 4 / 5) :
    Work.OddRadon.radonInverse n (GlueF n ρ) (Real.cos α)
      = Work.OddRadon.radonInverse n (radonPhi n ρ) (Real.cos α) := by
  have h1 : Work.OddRadon.radonInverse n (GlueF n ρ) (Real.cos α)
      = Work.OddRadon.radonInverse n (gluedPhi n (radonPhi n ρ)) (Real.cos α) :=
    radonInverse_congr_of_eqOn (n := n) (u := Real.cos α) (b := 4 / 5) hc0 hc
      (fun c hcx => by
        simp only [GlueF]
        rw [abs_of_pos hcx.1])
  rw [h1, radonInverse_gluedPhi_eq_of_lt n hc0 hc]

/-- The same for the second datum. -/
theorem radonInverse_GlueG_eq (n : ℕ) {ρ : ℝ → ℝ} {α : ℝ}
    (hc0 : 0 < Real.cos α) (hc : Real.cos α < 4 / 5) :
    Work.OddRadon.radonInverse n (GlueG n ρ) (Real.cos α)
      = Work.OddRadon.radonInverse n (radonPsi n ρ) (Real.cos α) := by
  have h1 : Work.OddRadon.radonInverse n (GlueG n ρ) (Real.cos α)
      = Work.OddRadon.radonInverse n (gluedPsi (radonPsi n ρ)) (Real.cos α) :=
    radonInverse_congr_of_eqOn (n := n) (u := Real.cos α) (b := 4 / 5) hc0 hc
      (fun c hcx => by
        simp only [GlueG]
        rw [abs_of_pos hcx.1])
  rw [h1, radonInverse_gluedPsi_eq_of_lt n hc0 hc]

/-- **The first deviation is the anchor's radial function**, on the cap. -/
theorem GlueA_eq (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {α : ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hc0 : 0 < Real.cos α) (hc : Real.cos α < 4 / 5) :
    GlueA n ρ α = ρ (Real.cos α) ^ (2 * n + 2) + ρ (-Real.cos α) ^ (2 * n + 2) - 2 := by
  have hc1 : (4 : ℝ) / 5 < 1 := by norm_num
  rw [GlueA, GluePhi, radonInverse_GlueF_eq (n := n) hc0 hc,
    Work.OddRadon.radonInverse_radonPhi_local n hn (c₁ := 4 / 5) hc1 hρ hc0 hc]
  field_simp

/-- **The second deviation is the anchor's radial function**, on the cap. -/
theorem GlueB_eq (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {α : ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hc0 : 0 < Real.cos α) (hc : Real.cos α < 4 / 5) :
    GlueB n ρ α = ρ (Real.cos α) ^ (2 * n + 1) - ρ (-Real.cos α) ^ (2 * n + 1) := by
  have hc1 : (4 : ℝ) / 5 < 1 := by norm_num
  rw [GlueB, GluePsi, radonInverse_GlueG_eq (n := n) hc0 hc,
    Work.OddRadon.radonInverse_radonPsi_local n hn (c₁ := 4 / 5) hc1 hρ hc0 hc]
  field_simp

end

end Work.OddCurve.LowSlope
