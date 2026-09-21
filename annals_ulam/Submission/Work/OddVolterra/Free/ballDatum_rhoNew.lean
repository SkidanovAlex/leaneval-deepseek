import Mathlib
import Submission.Work.OddCurve.LowSlope.radonPhiRhoNewEq
import Submission.Work.OddCurve.LowSlope.radonPsiRhoNewEq
import Submission.Work.OddCurve.LowSlope.radonInverseRhoNewEq
import Submission.Work.OddVolterra.Free.glueDataContDiffOnIcc
import Submission.Work.OddCurve.Free.deltaCapAndSupport
import Submission.Work.OddCurve.LowSlope.GlueDefs

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **The glued data below the gap are the ball's.**  On the range
`c ∈ [1/√(1+(4/5)²), 1)` the glued first datum of the low-slope step equals the ball's first
datum and the glued second datum vanishes.  The range is the union of `[1/√(1+(4/5)²), 4/5)`,
where the glue is the anchor's data and `hgap` identifies those with the ball's, and `[4/5, 1)`,
where the glue is the ball's data by definition. -/
private lemma glueF_eq_ballPhiData_of_ge_inv {n : ℕ} {ρa : ℝ → ℝ}
    (hgap : ∀ c : ℝ, (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ ≤ c → c < 4 / 5 →
      Work.OddCurve.LowSlope.radonPhi n ρa c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρa c = 0)
    {c : ℝ} (hcge : (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ ≤ c) (_hclt : c < 1)
    (hcpos : 0 < c) :
    Work.OddCurve.LowSlope.GlueF n ρa c = Work.OddCurve.LowSlope.ballPhiData n c := by
  rw [Work.OddCurve.LowSlope.GlueF, abs_of_pos hcpos]
  rcases lt_or_ge c (4 / 5) with h | h
  · rw [Work.OddCurve.LowSlope.gluedPhi_of_lt hcpos.le h, (hgap c hcge h).1]
  · exact Work.OddCurve.LowSlope.gluedPhi_of_ge hcpos.le h

/-- The companion statement for the glued second datum. -/
private lemma glueG_eq_zero_of_ge_inv {n : ℕ} {ρa : ℝ → ℝ}
    (hgap : ∀ c : ℝ, (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ ≤ c → c < 4 / 5 →
      Work.OddCurve.LowSlope.radonPhi n ρa c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρa c = 0)
    {c : ℝ} (hcge : (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ ≤ c) (_hclt : c < 1)
    (hcpos : 0 < c) :
    Work.OddCurve.LowSlope.GlueG n ρa c = 0 := by
  rw [Work.OddCurve.LowSlope.GlueG, abs_of_pos hcpos]
  rcases lt_or_ge c (4 / 5) with h | h
  · rw [Work.OddCurve.LowSlope.gluedPsi_of_lt hcpos.le h, (hgap c hcge h).2]
  · exact Work.OddCurve.LowSlope.gluedPsi_of_ge hcpos.le h

theorem ballDatum_rhoNew (n : ℕ) (hn : 1 ≤ n) {ρa R r : ℝ → ℝ}
    (hρa : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρa (Set.Ioo (-1 : ℝ) 1))
    (hjun : ∀ c ∈ Set.Ioo ((4 : ℝ) / 5 - 1 / 100) ((4 : ℝ) / 5 + 1 / 100),
      Work.OddCurve.LowSlope.radonPhi n ρa c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρa c = 0)
    (hgap : ∀ c : ℝ, (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ ≤ c → c < 4 / 5 →
      Work.OddCurve.LowSlope.radonPhi n ρa c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρa c = 0)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.rhoNew R r)
      (Set.Ioo (-1 : ℝ) 1))
    (hRsys : Work.OddRadon.RadialSystem n (Work.OddCurve.LowSlope.GluePhi n ρa)
      (Work.OddCurve.LowSlope.GluePsi n ρa) R r) :
    ∀ c : ℝ, (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ ≤ c → c < 1 →
      Work.OddCurve.LowSlope.radonPhi n (Work.OddCurve.LowSlope.rhoNew R r) c =
        Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n (Work.OddCurve.LowSlope.rhoNew R r) c = 0 := by
  intro c hcge hclt
  -- the range is positive
  have hroot_pos : 0 < (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ := by
    rw [inv_pos]
    exact Real.sqrt_pos_of_pos (by norm_num)
  have hcpos : 0 < c := lt_of_lt_of_le hroot_pos hcge
  -- the glued data at `c` are the ball's
  have hGlueF := glueF_eq_ballPhiData_of_ge_inv (n := n) hgap hcge hclt hcpos
  have hGlueG := glueG_eq_zero_of_ge_inv (n := n) hgap hcge hclt hcpos
  -- work on `(0,b)` with `b := (c+1)/2`, a closed interval `[0,b] ⊆ [0,1)`
  set b : ℝ := (c + 1) / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have hb1 : b ≤ 1 := by rw [hbdef]; linarith
  have hblt1 : b < 1 := by rw [hbdef]; linarith
  have hcb : c < b := by rw [hbdef]; linarith
  have hcIoo : c ∈ Set.Ioo (0 : ℝ) b := ⟨hcpos, hcb⟩
  -- smoothness of the glued data on `[0,b]`
  obtain ⟨hFs, hGs⟩ := glueDataContDiffOnIcc n hn hρa hjun
  have hsub : Set.Icc (0 : ℝ) b ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc le_rfl hb1
  have hsmGlueF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.GlueF n ρa)
      (Set.Icc 0 b) := hFs.mono hsub
  have hsmGlueG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.GlueG n ρa)
      (Set.Icc 0 b) := hGs.mono hsub
  -- smoothness of the two Radon data of the reconstructed profile on `[0,b]`
  have hsmPhi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.radonPhi n (Work.OddCurve.LowSlope.rhoNew R r))
      (Set.Icc 0 b) :=
    Work.OddCurve.LowSlope.contDiffOn_radonPhi_Icc n hn hblt1 hsm
  have hsmPsi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.radonPsi n (Work.OddCurve.LowSlope.rhoNew R r))
      (Set.Icc 0 b) := by
    have hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => u * Work.OddCurve.LowSlope.rhoNew R r u ^ (2 * n + 1))
        (Set.Ioo (-1 : ℝ) 1) :=
      contDiffOn_id.mul (hsm.pow (2 * n + 1))
    exact Work.OddCurve.Free.contDiffOn_radonProfile_Icc_gen n hn hblt1 hγ
  -- the inverse Radon transforms of the two data agree on `(0,b)`
  have hkey : ∀ u ∈ Set.Ioo (0 : ℝ) b,
      Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.radonPhi n (Work.OddCurve.LowSlope.rhoNew R r)) u =
        Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρa) u :=
    fun u hu =>
      Work.OddCurve.LowSlope.radonInverseRhoNewEq n hn hsm hRsys hu.1 (lt_of_lt_of_le hu.2 hb1)
  refine ⟨?_, ?_⟩
  · rw [Work.OddCurve.LowSlope.radonPhiRhoNewEq n hn hb0 hb1 hsmPhi hsmGlueF hkey c hcIoo,
      hGlueF]
  · rw [Work.OddCurve.LowSlope.radonPsiRhoNewEq n hn hsm hRsys hb0 hb1 hsmPsi hsmGlueG c hcIoo,
      hGlueG]

end

end Work.OddVolterra.Free
