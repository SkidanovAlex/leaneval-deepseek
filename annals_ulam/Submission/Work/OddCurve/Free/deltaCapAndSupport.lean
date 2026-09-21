import Mathlib
import Submission.Work.OddCurve.LowSlope.QuantDefs
import Submission.Work.OddCurve.LowSlope.step3_anchor_data
import Submission.Work.OddCurve.LowSlope.radonInverse_radonPhi
import Submission.Work.OddCurve.LowSlope.contDiffOn_radonPhi_Icc
import Submission.Work.OddCurve.Free.deltaCapIdentityClean

namespace Work.OddCurve.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-!
# The glued deviation data: cap identity, support, and smoothness

`deltaA n ρ = GlueF n ρ - ballPhiData n` and `deltaB n ρ = GlueG n ρ` are the *deviations* of the
glued Radon data of the low-slope step from the ball's data.  This file collects the three
structural facts about them that the endgame consumes:

* **on the cap** `(0, 4/5)` they are the Radon profiles of the deviation profiles `gammaDev`,
  `gammaPsi` (`deltaCapIdentityClean`);
* **on the left** `(0, tStar)` they vanish: the deviation profiles do (`hz`, `hz'`), and the Radon
  profile of a function vanishing on `(-tStar, tStar)` vanishes there too;
* **on the right** `(cStar, 1)` they vanish: above `4/5` by the definition of the glue, and in
  `(cStar, 4/5)` because the anchor's Radon data coincide with the ball's there
  (`anchorData_junction_cap`);
* **both are `C^∞` on `(0,1)`**: below `4/5` they are (differences of) Radon profiles of smooth
  profiles, and above `cStar` they vanish, the two pieces agreeing on the overlap `(cStar, 4/5)`.
-/

/-! ## A generic smoothness statement for the one-variable Radon profile -/

/-- **The one-variable Radon profile of a profile smooth on `(-1,1)` is `C^∞` on the closed
interval `[0,b]`, `b < 1`.**  The point is the trigonometric form of the transform,
`radonProfile (2n+1) γ c = |S^{2n-2}| ∫_{-π/2}^{π/2} cos^{2n-2}θ · γ (c sin θ) dθ`, in which `γ`
is only ever evaluated at the points `c sin θ ∈ (-R,R) ⊂ (-1,1)`: the behaviour of `γ` at the
endpoints `±1` is irrelevant, so no continuity hypothesis at `±1` is needed. -/
lemma contDiffOn_radonProfile_Icc_gen (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ} {b : ℝ} (hb : b < 1)
    (hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => Work.OddRadon.radonProfile (2 * n + 1) γ c) (Set.Icc 0 b) := by
  rw [contDiffOn_infty]
  intro N
  -- at each point `x ∈ [0,b]` we work on an open neighbourhood `(-R,R)` with `|x| < R < 1`
  refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
  obtain ⟨hx0, hxb⟩ := hx
  have hx1 : x < 1 := lt_of_le_of_lt hxb hb
  set R : ℝ := (x + 1) / 2 with hR
  have hxR : x < R := by rw [hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith
  refine ⟨Set.Ioo (-R) R, isOpen_Ioo, ⟨by linarith, hxR⟩, ?_⟩
  have hsub : Set.Icc (-R) R ⊆ Set.Ioo (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1, hR1], by linarith [ht.2, hR1]⟩
  have hγR : ContDiffOn ℝ ((N : ℕ∞) : WithTop ℕ∞) γ (Set.Icc (-R) R) :=
    (hγ.mono hsub).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ (⊤ : ℕ∞)))
  -- a globally `C^N` function agreeing with the profile on `[-R,R]`
  obtain ⟨G, hGsm, hGeq⟩ : ∃ G : ℝ → ℝ, ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) G ∧
      Set.EqOn G γ (Set.Icc (-R) R) :=
    ⟨Commons.Analysis.Calculus.taylorExtend γ N (-R) R,
      Commons.Analysis.Calculus.contDiff_taylorExtend N (by linarith) hγR,
      Commons.Analysis.Calculus.taylorExtend_eqOn_Icc⟩
  set F : ℝ → ℝ → ℝ := fun c θ => Real.cos θ ^ (2 * n - 2) * G (c * Real.sin θ) with hF
  have hFsm : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) := by
    rw [hF]
    exact ((Real.contDiff_cos.comp contDiff_snd).pow (2 * n - 2)).mul
      (hGsm.comp (contDiff_fst.mul (Real.contDiff_sin.comp contDiff_snd)))
  have hK : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F c θ) :=
    Work.Analysis.Calculus.contDiff_intervalIntegral_fixed N hFsm
  -- the smooth integral coincides with the datum on `[0,b] ∩ (-R,R)`
  refine ((hK.const_smul (Work.OddRadon.sphereArea (2 * n - 2))).contDiffOn).congr
    (fun c hc => ?_)
  obtain ⟨hc1, hc2⟩ := hc
  have hc0 : 0 ≤ c := hc1.1
  have hcR : c < R := hc2.2
  rw [Work.OddCurve.LowSlope.radonProfile_eq_cos_any n hn γ c]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  rw [hF]
  simp only
  have hsin : |Real.sin θ| ≤ 1 := by
    rw [abs_le]; exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hle : |c * Real.sin θ| ≤ R := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |Real.sin θ| ≤ c * 1 := mul_le_mul_of_nonneg_left hsin hc0
      _ = c := by ring
      _ ≤ R := hcR.le
  have hmem : c * Real.sin θ ∈ Set.Icc (-R) R :=
    ⟨le_trans (neg_le_neg hle) (neg_abs_le _), le_trans (le_abs_self _) hle⟩
  rw [hGeq hmem]

/-- The second Radon datum `radonPsi n ρ = 𝓡 (w₁ ρ^d)` is `C^∞` on `(0, 4/5)` for `ρ` smooth on
`(-1,1)`. -/
lemma contDiffOn_radonPsi_Ioo (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.radonPsi n ρ)
      (Set.Ioo (0 : ℝ) (4 / 5)) := by
  have hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => u * ρ u ^ (2 * n + 1))
      (Set.Ioo (-1 : ℝ) 1) := contDiffOn_id.mul (hρsm.pow (2 * n + 1))
  have h := contDiffOn_radonProfile_Icc_gen n hn (b := (4 : ℝ) / 5) (by norm_num) hγ
  exact h.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

/-! ## The Radon profile of a profile vanishing near `0` -/

/-- **The Radon profile of a function vanishing on `(-T,T)` vanishes on `(-T,T)`**: the defining
integral only evaluates `γ` at the points `c · s` with `|s| ≤ 1`. -/
lemma radonProfile_eq_zero_of_vanish (n : ℕ) {γ : ℝ → ℝ} {c T : ℝ} (hT : |c| < T)
    (hγ : ∀ x : ℝ, |x| < T → γ x = 0) :
    Work.OddRadon.radonProfile (2 * n + 1) γ c = 0 := by
  have hint : ∀ s ∈ Set.uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * γ (c * s) = (0 : ℝ) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
    have hs1 : |s| ≤ 1 := abs_le.mpr hs
    have hcs : |c * s| < T := by
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (abs_nonneg c) hs1) hT
    rw [hγ (c * s) hcs, mul_zero]
  have hzero : (∫ s in (-1 : ℝ)..1,
      (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * γ (c * s)) = 0 := by
    rw [show (∫ s in (-1 : ℝ)..1,
        (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * γ (c * s))
        = ∫ s in (-1 : ℝ)..1, (0 : ℝ) from intervalIntegral.integral_congr hint]
    simp
  simp only [Work.OddRadon.radonProfile, hzero, mul_zero]

/-! ## The junction window -/

/-- `4/5 < (√(1+(7/10)²))⁻¹`: the junction interval `(cStar, (√(1+(7/10)²))⁻¹)` of the anchor's
Radon data contains the whole cap range `(cStar, 4/5)`. -/
private lemma four_fifths_lt_inv_c7 :
    (4 : ℝ) / 5 < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ := by
  rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 4 / 5) (Real.sqrt_pos.mpr (by norm_num))]
  rw [show ((4 : ℝ) / 5)⁻¹ = 5 / 4 by norm_num]
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5 / 4)]
  norm_num

/-- **The anchor's Radon data on the junction window `(cStar, 4/5)`**: there the bump vanishes
with its derivative and the anchor satisfies the ball's central-section conditions, so the
anchor's two Radon data are the ball's (`anchorData_junction_cap`). -/
private lemma junction_data (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0 := by
  intro c hc
  have hρsm1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) := hρsm.of_le (by simp)
  exact Work.OddCurve.LowSlope.anchorData_junction_cap n hn H hρpos hρsm1 hρmono hgraph hA hB
    ⟨hc.1, lt_trans hc.2 four_fifths_lt_inv_c7⟩

/-! ## The support of the two glued deviations -/

/-- **The first glued deviation vanishes below `tStar`.** -/
private lemma deltaA_eq_zero_of_lt_tStar (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hz : ∀ c : ℝ, |c| < Work.OddEnvelope.tStar → Work.OddCurve.LowSlope.gammaDev n ρ c = 0)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hct : c < Work.OddEnvelope.tStar) :
    Work.OddCurve.LowSlope.deltaA n ρ c = 0 := by
  have hc4 : c < 4 / 5 :=
    lt_trans hct (lt_trans Work.OddCurve.LowSlope.tStar_lt_cStar
      Work.OddCurve.LowSlope.cStar_lt_four_fifths)
  rw [(deltaCapIdentityClean n hn hρsm c ⟨hc.1, hc4⟩).1,
    radonProfile_eq_zero_of_vanish n (γ := Work.OddCurve.LowSlope.gammaDev n ρ)
      (T := Work.OddEnvelope.tStar) (by rw [abs_of_pos hc.1]; exact hct) hz]

/-- **The second glued deviation vanishes below `tStar`.** -/
private lemma deltaB_eq_zero_of_lt_tStar (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hz : ∀ c : ℝ, |c| < Work.OddEnvelope.tStar → Work.OddCurve.LowSlope.gammaPsi n ρ c = 0)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hct : c < Work.OddEnvelope.tStar) :
    Work.OddCurve.LowSlope.deltaB n ρ c = 0 := by
  have hc4 : c < 4 / 5 :=
    lt_trans hct (lt_trans Work.OddCurve.LowSlope.tStar_lt_cStar
      Work.OddCurve.LowSlope.cStar_lt_four_fifths)
  rw [(deltaCapIdentityClean n hn hρsm c ⟨hc.1, hc4⟩).2,
    radonProfile_eq_zero_of_vanish n (γ := Work.OddCurve.LowSlope.gammaPsi n ρ)
      (T := Work.OddEnvelope.tStar) (by rw [abs_of_pos hc.1]; exact hct) hz]

/-- **The first glued deviation vanishes above `cStar`.** -/
private lemma deltaA_eq_zero_of_gt_cStar (n : ℕ) {ρ : ℝ → ℝ}
    (hjunc : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c) :
    ∀ c : ℝ, Work.OddCurve.LowSlope.cStar < c → Work.OddCurve.LowSlope.deltaA n ρ c = 0 := by
  intro c hc
  have hcpos : 0 < c := lt_trans Work.OddCurve.LowSlope.cStar_pos hc
  rw [Work.OddCurve.LowSlope.deltaA_def, Work.OddCurve.LowSlope.GlueF, abs_of_pos hcpos]
  by_cases h4 : 4 / 5 ≤ c
  · rw [Work.OddCurve.LowSlope.gluedPhi_of_ge hcpos.le h4]
    ring
  · have hlt : c < 4 / 5 := lt_of_not_ge h4
    rw [Work.OddCurve.LowSlope.gluedPhi_of_lt hcpos.le hlt, hjunc c ⟨hc, hlt⟩]
    ring

/-- **The second glued deviation vanishes above `cStar`.** -/
private lemma deltaB_eq_zero_of_gt_cStar (n : ℕ) {ρ : ℝ → ℝ}
    (hjuncB : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0) :
    ∀ c : ℝ, Work.OddCurve.LowSlope.cStar < c → Work.OddCurve.LowSlope.deltaB n ρ c = 0 := by
  intro c hc
  have hcpos : 0 < c := lt_trans Work.OddCurve.LowSlope.cStar_pos hc
  rw [Work.OddCurve.LowSlope.deltaB_def, Work.OddCurve.LowSlope.GlueG, abs_of_pos hcpos]
  by_cases h4 : 4 / 5 ≤ c
  · rw [Work.OddCurve.LowSlope.gluedPsi_of_ge hcpos.le h4]
  · have hlt : c < 4 / 5 := lt_of_not_ge h4
    rw [Work.OddCurve.LowSlope.gluedPsi_of_lt hcpos.le hlt, hjuncB c ⟨hc, hlt⟩]

/-! ## Smoothness of the two glued deviations on `(0,1)` -/

/-- **The first glued deviation is `C^∞` on `(0,1)`**: on `(0,4/5)` it is the difference of the
two Radon profiles `radonPhi n ρ` and `ballPhiData n`, and on `(cStar,1)` it vanishes; the two
pieces agree on the overlap `(cStar, 4/5)`. -/
private lemma contDiffOn_deltaA_free (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hjunc : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.deltaA n ρ)
      (Set.Ioo (0 : ℝ) 1) := by
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => Work.OddCurve.LowSlope.radonPhi n ρ c
        - Work.OddCurve.LowSlope.ballPhiData n c) (Set.Ioo (0 : ℝ) (4 / 5)) :=
    ((Work.OddCurve.LowSlope.contDiffOn_radonPhi_Icc n hn (b := (4 : ℝ) / 5) (by norm_num)
        hρsm).mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).sub
      ((Work.OddCurve.LowSlope.contDiffOn_ballPhiData n hn).mono
        (fun x hx => ⟨hx.1, lt_trans hx.2 (by norm_num)⟩))
  have hconst : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (0 : ℝ))
      (Set.Ioo (0 : ℝ) 1) := contDiffOn_const
  refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
  rcases lt_or_ge x (4 / 5) with hlt | hge
  · refine ⟨Set.Ioo (0 : ℝ) (4 / 5), isOpen_Ioo, ⟨hx.1, hlt⟩, ?_⟩
    refine (hg.mono (fun c hc => hc.2)).congr (fun c hc => ?_)
    simp only [Work.OddCurve.LowSlope.deltaA_def, Work.OddCurve.LowSlope.GlueF]
    rw [abs_of_pos hc.2.1, Work.OddCurve.LowSlope.gluedPhi_of_lt hc.2.1.le hc.2.2]
  · refine ⟨Set.Ioo Work.OddCurve.LowSlope.cStar 1, isOpen_Ioo,
      ⟨lt_of_lt_of_le Work.OddCurve.LowSlope.cStar_lt_four_fifths hge, hx.2⟩, ?_⟩
    refine (hconst.mono (fun c hc => hc.1)).congr (fun c hc => ?_)
    exact deltaA_eq_zero_of_gt_cStar n hjunc c hc.2.1

/-- **The second glued deviation is `C^∞` on `(0,1)`**: on `(0,4/5)` it is the Radon profile
`radonPsi n ρ`, and on `(cStar,1)` it vanishes. -/
private lemma contDiffOn_deltaB_free (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hjuncB : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.deltaB n ρ)
      (Set.Ioo (0 : ℝ) 1) := by
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.radonPsi n ρ)
      (Set.Ioo (0 : ℝ) (4 / 5)) := contDiffOn_radonPsi_Ioo n hn hρsm
  have hconst : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (0 : ℝ))
      (Set.Ioo (0 : ℝ) 1) := contDiffOn_const
  refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
  rcases lt_or_ge x (4 / 5) with hlt | hge
  · refine ⟨Set.Ioo (0 : ℝ) (4 / 5), isOpen_Ioo, ⟨hx.1, hlt⟩, ?_⟩
    refine (hg.mono (fun c hc => hc.2)).congr (fun c hc => ?_)
    simp only [Work.OddCurve.LowSlope.deltaB_def, Work.OddCurve.LowSlope.GlueG]
    rw [abs_of_pos hc.2.1, Work.OddCurve.LowSlope.gluedPsi_of_lt hc.2.1.le hc.2.2]
  · refine ⟨Set.Ioo Work.OddCurve.LowSlope.cStar 1, isOpen_Ioo,
      ⟨lt_of_lt_of_le Work.OddCurve.LowSlope.cStar_lt_four_fifths hge, hx.2⟩, ?_⟩
    refine (hconst.mono (fun c hc => hc.1)).congr (fun c hc => ?_)
    exact deltaB_eq_zero_of_gt_cStar n hjuncB c hc.2.1

/-! ## The main theorem -/

theorem deltaCapAndSupport (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    (hz : ∀ c : ℝ, |c| < Work.OddEnvelope.tStar → Work.OddCurve.LowSlope.gammaDev n ρ c = 0)
    (hz' : ∀ c : ℝ, |c| < Work.OddEnvelope.tStar → Work.OddCurve.LowSlope.gammaPsi n ρ c = 0)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    (∀ c ∈ Set.Ioo (0:ℝ) (4/5),
        Work.OddCurve.LowSlope.deltaA n ρ c
          = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaDev n ρ) c ∧
        Work.OddCurve.LowSlope.deltaB n ρ c
          = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaPsi n ρ) c) ∧
      (∀ c ∈ Set.Ioo (0:ℝ) 1, c < Work.OddEnvelope.tStar →
          Work.OddCurve.LowSlope.deltaA n ρ c = 0 ∧ Work.OddCurve.LowSlope.deltaB n ρ c = 0) ∧
      (∀ c ∈ Set.Ioo (0:ℝ) 1, Work.OddCurve.LowSlope.cStar < c →
          Work.OddCurve.LowSlope.deltaA n ρ c = 0 ∧ Work.OddCurve.LowSlope.deltaB n ρ c = 0) ∧
      (ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.deltaA n ρ) (Set.Ioo (0:ℝ) 1) ∧
       ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.deltaB n ρ) (Set.Ioo (0:ℝ) 1)) := by
  have hjunc := junction_data n hn H hρpos hρsm hρmono hgraph hA hB
  have hjuncA : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c :=
    fun c hc => (hjunc c hc).1
  have hjuncB : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0 := fun c hc => (hjunc c hc).2
  refine ⟨fun c hc => deltaCapIdentityClean n hn hρsm c hc, ?_, ?_, ?_⟩
  · intro c hc hct
    exact ⟨deltaA_eq_zero_of_lt_tStar n hn hρsm hz hc hct,
      deltaB_eq_zero_of_lt_tStar n hn hρsm hz' hc hct⟩
  · intro c hc hcs
    exact ⟨deltaA_eq_zero_of_gt_cStar n hjuncA c hcs,
      deltaB_eq_zero_of_gt_cStar n hjuncB c hcs⟩
  · exact ⟨contDiffOn_deltaA_free n hn hρsm hjuncA, contDiffOn_deltaB_free n hn hρsm hjuncB⟩

end

end Work.OddCurve.Free
