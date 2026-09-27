import Mathlib
import Submission.Work.Drive.planeProfiles
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.dataR_dataD_spec
import Submission.Work.Drive.Neutral.stripDiskChordNe
import Submission.Work.Drive.Neutral.dataChordAux
import Submission.Work.Drive.Neutral.stripDiskValueClause
import Submission.Work.Drive.capSide_capPiece
import Submission.Work.Drive.Neutral.dataChord_spec

/-!
# The blended chord data and the band profile of the plane chart

Standalone module for the pieces of the plane chart of `Submission/Work/Drive/PLANE_CHART_FINAL.md`
that are shared by the descent lemma (`Submission/Work/Drive/chordAnnulusDescent.lean`) and by the
target `Work.Drive.exists_planeChart`:

* the smooth step `Work.Drive.pStep` and the band profile `Work.Drive.bandProf`/`bandTau`, with its
  sign pattern (`bandTau_eq`, `bandTau_neg`, `bandTau_pos`, `bandTau_eq_zero'`);
* the `Work.Drive.bandMu`-blend of the chord data with a constant
  (`Work.Drive.bandMidData`, `Work.Drive.bandWData`), which is globally `C^∞` and even in the
  opening, together with its values on the unit circle (`Work.Drive.bandDataCircle`);
* the one-sided clamp `Work.Drive.exists_oneSidedClamp`;
* the cap-clause lemmas in cap coordinates (`Work.Drive.capProjVecOf_isCapSide`,
  `Work.Drive.exists_capPiece_of_capForm`, `Work.Drive.exists_capPiece_of_capForm'`) and the
  non-vanishing criteria for the blends (`Work.Drive.blend_ne_zero_of_norm_ne`,
  `Work.Drive.blend_ne_zero_of_smul`, `Work.Drive.blend_rot_ne_zero`,
  `Work.Drive.exists_capPiece_of_capBlend`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Filter

noncomputable section

/-! ## The radial profiles of the plane chart -/

/-- A smooth step: `0` for `s ≤ a`, `1` for `s ≥ b`, when `a < b`. -/
def pStep (a b s : ℝ) : ℝ := Real.smoothTransition ((s - a) / (b - a))

lemma contDiff_pStep (a b : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pStep a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma pStep_nonneg (a b s : ℝ) : 0 ≤ pStep a b s := Real.smoothTransition.nonneg _

lemma pStep_le_one (a b s : ℝ) : pStep a b s ≤ 1 := Real.smoothTransition.le_one _

lemma pStep_eq_zero {a b s : ℝ} (hab : a < b) (h : s ≤ a) : pStep a b s = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

lemma pStep_eq_one {a b s : ℝ} (hab : a < b) (h : b ≤ s) : pStep a b s = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  exact (le_div_iff₀ (by linarith)).mpr (by linarith)

/-- The band profile: the linear profile `(π²/2)(ρ - 1/2)`, cut off below `1/2`. -/
def bandProf (a ρ : ℝ) : ℝ := pStep a (1 / 2) ρ * (Real.pi ^ 2 / 2 * (ρ - 1 / 2))

lemma contDiff_bandProf (a : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bandProf a) :=
  (contDiff_pStep _ _).mul (contDiff_const.mul (contDiff_id.sub contDiff_const))

lemma bandProf_eq {a ρ : ℝ} (ha : a < 1 / 2) (h : 1 / 2 ≤ ρ) :
    bandProf a ρ = Real.pi ^ 2 / 2 * (ρ - 1 / 2) := by
  unfold bandProf
  rw [pStep_eq_one ha h, one_mul]

lemma bandProf_eq_zero {a ρ : ℝ} (ha : a < 1 / 2) (h : ρ ≤ a) : bandProf a ρ = 0 := by
  unfold bandProf
  rw [pStep_eq_zero ha h, zero_mul]

lemma bandProf_nonpos {a ρ : ℝ} (hρ : ρ ≤ 1 / 2) : bandProf a ρ ≤ 0 := by
  unfold bandProf
  have h1 := pStep_nonneg a (1 / 2) ρ
  have h2 : Real.pi ^ 2 / 2 * (ρ - 1 / 2) ≤ 0 := by nlinarith [Real.pi_pos]
  exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- The band coordinate of the plane chart. -/
def bandTau (a : ℝ) (z : ℂ) : ℝ := bandProf a ‖z‖

lemma bandTau_contDiff {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bandTau a) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases lt_or_ge ‖z‖ a with h | h
  · have hopen : {w : ℂ | ‖w‖ < a} ∈ 𝓝 z :=
      isOpen_lt continuous_norm continuous_const |>.mem_nhds h
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hopen] with w hw
    show bandTau a w = 0
    unfold bandTau
    rw [bandProf_eq_zero ha' (le_of_lt hw)]
  · have hz : z ≠ 0 := fun hz => by rw [hz, norm_zero] at h; linarith
    have hns0 : Complex.normSq z ≠ 0 := fun h0 =>
      hz (by rw [← Complex.normSq_eq_zero, h0])
    have hns : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => Complex.normSq w) z :=
      Neutral.contDiff_complexNormSq.contDiffAt
    have hsqrt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : ℂ => Real.sqrt (Complex.normSq w)) z :=
      (Real.contDiffAt_sqrt hns0).comp z hns
    have hnorm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => ‖w‖) z := by
      refine hsqrt.congr_of_eventuallyEq ?_
      filter_upwards with w
      rw [Complex.normSq_eq_norm_sq w, Real.sqrt_sq (norm_nonneg w)]
    unfold bandTau
    exact (contDiff_bandProf a).contDiffAt.comp z hnorm

lemma bandTau_eq {a : ℝ} {z : ℂ} (ha : a < 1 / 2) (h : 1 / 2 ≤ ‖z‖) :
    bandTau a z = Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2) := bandProf_eq ha h

lemma bandTau_nonpos {a : ℝ} {z : ℂ} (h : ‖z‖ ≤ 1 / 2) : bandTau a z ≤ 0 :=
  bandProf_nonpos h

/-! ## The blended chord data -/

/-- The bump that kills the degeneracy of the chord data at `x = 0`: it is `0` for
`Complex.normSq x ≤ 1/8` and `1` for `Complex.normSq x ≥ 1/4`. -/
def bandMu (x : ℂ) : ℝ := Real.smoothTransition (8 * Complex.normSq x - 1)

lemma contDiff_bandMu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bandMu := by
  unfold bandMu
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul Neutral.contDiff_complexNormSq).sub contDiff_const))

lemma bandMu_nonneg (x : ℂ) : 0 ≤ bandMu x := Real.smoothTransition.nonneg _

lemma bandMu_le_one (x : ℂ) : bandMu x ≤ 1 := Real.smoothTransition.le_one _

lemma bandMu_eq_zero {x : ℂ} (h : Complex.normSq x ≤ 1 / 8) : bandMu x = 0 := by
  unfold bandMu
  refine Real.smoothTransition.zero_of_nonpos ?_
  linarith

lemma bandMu_eq_one {x : ℂ} (h : 1 / 4 ≤ Complex.normSq x) : bandMu x = 1 := by
  unfold bandMu
  refine Real.smoothTransition.one_of_one_le ?_
  linarith

/-- The even, potentially discontinuous chord midpoint data, blended with a constant near `x = 0`
so that it becomes globally `C^∞`. -/
def bandMidData (γ : Circle → ℝ × ℝ) (m₀ : ℂ) : ℂ × ℝ → ℂ :=
  fun p => (bandMu p.1 : ℝ) • Neutral.dataMid γ p.1 p.2 + (1 - bandMu p.1 : ℝ) • m₀

/-- The even chord-direction data, blended with a constant near `x = 0`. -/
def bandWData (γ : Circle → ℝ × ℝ) (w₀ : ℂ) : ℂ × ℝ → ℂ :=
  fun p => (bandMu p.1 : ℝ) • Neutral.dchW γ (p.1, p.2) + (1 - bandMu p.1 : ℝ) • w₀

lemma bandMidData_even (γ : Circle → ℝ × ℝ) (m₀ : ℂ) (p : ℂ × ℝ) :
    bandMidData γ m₀ (p.1, -p.2) = bandMidData γ m₀ p := by
  simp only [bandMidData, Neutral.dataMid_neg]

lemma bandWData_even (γ : Circle → ℝ × ℝ) (w₀ : ℂ) (p : ℂ × ℝ) :
    bandWData γ w₀ (p.1, -p.2) = bandWData γ w₀ p := by
  simp only [bandWData, Neutral.dchW_neg]

/-- Blending a function that is smooth off `x = 0` with a constant by the bump `bandMu` gives a
globally smooth function. -/
lemma contDiff_bandMu_blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ × ℝ → E} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f {p : ℂ × ℝ | p.1 ≠ 0}) (c : E) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => (bandMu p.1 : ℝ) • f p + (1 - bandMu p.1 : ℝ) • c) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 = 0
  · have hopen : {q : ℂ × ℝ | Complex.normSq q.1 < 1 / 8} ∈ 𝓝 p :=
      (isOpen_lt (Neutral.contDiff_complexNormSq.continuous.comp continuous_fst)
        continuous_const).mem_nhds (by
          simp only [Set.mem_ofPred_eq, Function.comp_apply]
          rw [hp]; norm_num)
    refine (contDiffAt_const (c := c)).congr_of_eventuallyEq ?_
    filter_upwards [hopen] with q hq
    rw [bandMu_eq_zero hq.le, zero_smul, sub_zero, one_smul, zero_add]
  · have hmem : {q : ℂ × ℝ | q.1 ≠ 0} ∈ 𝓝 p :=
      (isOpen_ne.preimage continuous_fst).mem_nhds hp
    have hfAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f p := hf.contDiffAt hmem
    have hmu : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℂ × ℝ => bandMu q.1) p :=
      contDiff_bandMu.contDiffAt.comp p contDiffAt_fst
    have hone : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℂ × ℝ => (1 - bandMu q.1) • c) p :=
      ((contDiffAt_const (c := (1 : ℝ))).sub hmu).smul (contDiffAt_const (c := c))
    exact (hmu.smul hfAt).add hone

lemma contDiff_bandMidData (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (m₀ : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bandMidData γ m₀) := by
  have hbase : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => Neutral.dataMid γ p.1 p.2)
      {p : ℂ × ℝ | p.1 ≠ 0} := Neutral.contDiffOn_dataMid_of_ne γ hγ
  exact contDiff_bandMu_blend hbase m₀

lemma contDiff_bandWData (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (w₀ : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bandWData γ w₀) := by
  have hbase : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => Neutral.dchW γ (p.1, p.2)) {p : ℂ × ℝ | p.1 ≠ 0} :=
    Neutral.contDiffOn_dchW γ hγ
  exact contDiff_bandMu_blend hbase w₀


/-! ## The direction profile and the bump on it -/

/-- Smoothness of `z ↦ pStep a b ‖z‖` when `a > 0` (the function vanishes in a neighbourhood of
`0`). -/
lemma contDiff_pStep_norm {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => pStep a b ‖z‖) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases lt_or_ge ‖z‖ a with h | h
  · have hopen : {w : ℂ | ‖w‖ < a} ∈ 𝓝 z :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds h
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hopen] with w hw
    exact pStep_eq_zero hab (le_of_lt hw)
  · have hz : z ≠ 0 := fun hz => by rw [hz, norm_zero] at h; linarith
    have hns0 : Complex.normSq z ≠ 0 := fun h0 => hz (Complex.normSq_eq_zero.mp h0)
    have hns : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => Complex.normSq w) z :=
      Neutral.contDiff_complexNormSq.contDiffAt
    have hsqrt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : ℂ => Real.sqrt (Complex.normSq w)) z :=
      (Real.contDiffAt_sqrt hns0).comp z hns
    have hnorm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => ‖w‖) z := by
      refine hsqrt.congr_of_eventuallyEq ?_
      filter_upwards with w
      rw [Complex.normSq_eq_norm_sq w, Real.sqrt_sq (norm_nonneg w)]
    exact (contDiff_pStep a b).contDiffAt.comp z hnorm

lemma bandMu_wCollapse_eq_one {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : bandMu (wCollapse z) = 1 := by
  refine bandMu_eq_one ?_
  rw [Complex.normSq_eq_norm_sq, wCollapse_eq hz, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg z), div_self (by positivity)]
  norm_num

lemma norm_wCollapse_eq {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : ‖wCollapse z‖ = 1 := by
  rw [wCollapse_eq hz, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
    div_self (by positivity)]

/-- The value of `smoothTransition` at `1/2`. -/
lemma smoothTransition_half : Real.smoothTransition (1 / 2) = 1 / 2 := by
  rw [Real.smoothTransition, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  have hpos : expNegInvGlue (1 / 2) ≠ 0 := by
    rw [expNegInvGlue, if_neg (by norm_num : ¬ (1 / 2 : ℝ) ≤ 0)]
    exact ne_of_gt (Real.exp_pos _)
  field_simp
  ring

/-- The cutoff at `1/4` takes the value at least `1/2` from `3/16` on. -/
lemma profCut_quarter_ge_half {s : ℝ} (hs : 3 / 16 ≤ s) : 1 / 2 ≤ profCut (1 / 4) s := by
  rw [Work.Drive.profCut]
  have h1 : Real.smoothTransition (1 / 2) ≤ Real.smoothTransition (2 * s / (1 / 4) - 1) :=
    Real.smoothTransition.monotone (by linarith)
  rwa [smoothTransition_half] at h1

/-- On `‖z‖ ≥ 7/16` the bump is still one: the collapsed direction has norm `≥ 1/2` there. -/
lemma bandMu_wCollapse_eq_one_of_ge {z : ℂ} (hz : 7 / 16 ≤ ‖z‖) : bandMu (wCollapse z) = 1 := by
  refine bandMu_eq_one ?_
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hval : ‖wCollapse z‖ = profCut (1 / 4) (‖z‖ ^ 2) := by
    unfold wCollapse
    rw [norm_mul, Work.Drive.norm_ofReal_complex, abs_of_nonneg (wProf_nonneg _)]
    have hne : ‖z‖ ≠ 0 := ne_of_gt hzpos
    rw [show wProf (‖z‖ ^ 2) * ‖z‖ = profCut (1 / 4) (‖z‖ ^ 2) from by
      unfold wProf
      rw [Real.sqrt_sq (norm_nonneg z)]
      exact div_mul_cancel₀ _ hne]
  have hs3 : (3 : ℝ) / 16 ≤ ‖z‖ ^ 2 := by nlinarith
  rw [Complex.normSq_eq_norm_sq, hval]
  have := profCut_quarter_ge_half hs3
  nlinarith

lemma bandMu_circle (σ : ℝ) : bandMu (Complex.exp ((σ : ℂ) * Complex.I)) = 1 := by
  refine bandMu_eq_one ?_
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have h : (((σ : ℂ) * Complex.I).re) = 0 := by simp
  rw [h, Real.exp_zero]
  norm_num

/-- **The blended data on the unit circle.** -/
theorem bandDataCircle (γ : Circle → ℝ × ℝ) (m₀ w₀ : ℂ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {σ s : ℝ} (hs : 0 < s) (hs2 : s ≤ Real.pi / 2) :
    bandMidData γ m₀ (Complex.exp ((σ : ℂ) * Complex.I), s)
        = Neutral.symmC (Neutral.symmMid γ σ s) ∧
      bandWData γ w₀ (Complex.exp ((σ : ℂ) * Complex.I), s)
        = ((2 : ℂ) * Neutral.symmWC γ σ s) ∧
      Neutral.dataR γ (Complex.exp ((σ : ℂ) * Complex.I)) s = Neutral.symmR γ σ s ∧
      Neutral.dataD γ (Complex.exp ((σ : ℂ) * Complex.I)) s = Neutral.symmD γ σ s := by
  have h1 : bandMidData γ m₀ (Complex.exp ((σ : ℂ) * Complex.I), s)
      = Neutral.dataMid γ (Complex.exp ((σ : ℂ) * Complex.I)) s := by
    unfold bandMidData
    rw [bandMu_circle σ]
    simp
  have h2 : bandWData γ w₀ (Complex.exp ((σ : ℂ) * Complex.I), s)
      = Neutral.dchW γ (Complex.exp ((σ : ℂ) * Complex.I), s) := by
    unfold bandWData
    rw [bandMu_circle σ]
    simp
  have h3 : Neutral.dchW γ (Complex.exp ((σ : ℂ) * Complex.I), s)
      = ((2 : ℂ) * Neutral.symmWC γ σ s) := by
    have hch : ((s : ℝ) : ℂ) * Neutral.dchW γ (Complex.exp ((σ : ℂ) * Complex.I), s)
        = ((s : ℝ) : ℂ) * ((2 : ℂ) * Neutral.symmWC γ σ s) := by
      have h5 : ((s : ℝ) : ℂ) * Neutral.dchW γ (Complex.exp ((σ : ℂ) * Complex.I), s)
          = (s : ℝ) • Neutral.dchW γ (Complex.exp ((σ : ℂ) * Complex.I), s) :=
        (Complex.real_smul).symm
      rw [h5, Neutral.dchW_smul γ hγ (Complex.exp_ne_zero _) s,
        Neutral.dataChord_exp_eq_two_smul hγ σ s hs hs2]
      push_cast
      ring
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hs)) hch
  exact ⟨by rw [h1]; exact Neutral.dataMid_exp_eq γ σ s hs hs2,
    by rw [h2, h3],
    Neutral.dataR_exp_eq γ σ s hs hs2,
    Neutral.dataD_exp_eq γ σ s hs hs2⟩



/-! ## The one-sided clamp of the band coordinate

The cap clause of the plane chart is obtained by continuing the chord data of the configuration strip
*across* the seam, i.e. by evaluating the `τ = s²` descent of the even chord data at *negative* `τ`.
Two devices make this work:

* the descent of the **data** `(M, W) = (chord midpoint, halved chord direction)` (and *not* of the
  assembled vector lift) — because then the disk coordinate is
  `D = M/√A` with `A = ‖M‖² + τ‖W‖²`, and `‖D‖² = ‖M‖²/A ≥ 1` **automatically** for `τ ≤ 0`
  (which is exactly the cap side, `Work.Drive.isCapVec_confProjVecOf`), with no side condition;
* the **one-sided clamp** below, which puts the band coordinate of the *inner* disk (where `τ` is
  forced negative by `Work.Drive.tauComp`) into the strip `|τ| ≤ δ` on which the descended data is
  known (uniformly in the direction) to be positive and non-vanishing, while leaving the band
  coordinate of the outer annulus — where the strip clause needs the *honest* value
  `(π²/2)(‖z‖ - 1/2)` — unchanged. -/

/-- **The diagonal of the chord data lies on the gluing torus.**  At opening `s = 0` the chord is
degenerate, so `dataChord = 0`, `dataMid` is (the complexification of) a point of `γ`, and the disk
coordinate `dataD = dataMid / dataR` therefore has norm one.  This is the torus hypothesis of the
collar lemma (`Work.Drive.collar_isCapVec`) in the form in which the plane chart needs it. -/
lemma norm_dataD_zero (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) {x : ℂ} (hx : x ≠ 0) :
    ‖Neutral.dataD γ x 0‖ = 1 := by
  have hsc : Neutral.sClamp (0 : ℝ) = 0 :=
    Neutral.sClamp_eq_self (by rw [abs_zero]; positivity)
  have hθ : (Circle.exp (Complex.arg x) : ℂ) = x / (‖x‖ : ℂ) := by
    rw [← Neutral.toCirc_eq_exp_arg x hx, Neutral.toCirc_coe]
  have hpt : Neutral.curvePtAt γ x 0 = Neutral.symmC (curve γ (Complex.arg x + 0)) := by
    have h := Neutral.curvePtAt_eq_exp γ x hx hθ 0
    simpa only [hsc, add_zero] using h
  have hchord : Neutral.dataChord γ x 0 = 0 := by
    show Neutral.endPlus γ x 0 - Neutral.endMinus γ x 0 = 0
    simp only [Neutral.endPlus, Neutral.endMinus, neg_zero, sub_self]
  have hmid : Neutral.dataMid γ x 0 = Neutral.curvePtAt γ x 0 := by
    show (Neutral.endPlus γ x 0 + Neutral.endMinus γ x 0) / 2 = Neutral.curvePtAt γ x 0
    simp only [Neutral.endPlus, Neutral.endMinus, neg_zero, add_self_div_two]
  have hmidne : Neutral.dataMid γ x 0 ≠ 0 := by
    rw [hmid, hpt, add_zero]
    intro h
    exact hγne (Circle.exp (Complex.arg x)) (Neutral.symmC_eq_zero_iff.mp h)
  have hR : Neutral.dataR γ x 0 = ‖Neutral.dataMid γ x 0‖ := by
    rw [Neutral.dataR, hchord, Complex.normSq_zero, add_zero,
      Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [Neutral.dataD, hR, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self]
  exact norm_ne_zero_iff.mpr hmidne

/-- **The one-sided clamp.**  A `C^∞` function which is the identity on `[0, ∞)` and whose negative
values are squeezed into `(-δ, 0)`: the convex combination of `t` and `-δ/2` with weight
`s = smoothTransition (2t/δ + 1)` (which is `1` for `t ≥ 0` and `0` for `t ≤ -δ/2`). -/
theorem exists_oneSidedClamp (δ : ℝ) (hδ : 0 < δ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ t : ℝ, 0 ≤ t → ψ t = t) ∧
      (∀ t : ℝ, t < 0 → -δ < ψ t ∧ ψ t < 0) := by
  refine ⟨fun t => Real.smoothTransition (2 * t / δ + 1) * t
      + (1 - Real.smoothTransition (2 * t / δ + 1)) * (-(δ / 2)), ?_, ?_, ?_⟩
  · fun_prop
  · intro t ht
    show Real.smoothTransition (2 * t / δ + 1) * t
        + (1 - Real.smoothTransition (2 * t / δ + 1)) * (-(δ / 2)) = t
    have h : (1 : ℝ) ≤ 2 * t / δ + 1 := by
      have h0 : 0 ≤ 2 * t / δ := div_nonneg (by linarith) hδ.le
      linarith
    have hs : Real.smoothTransition (2 * t / δ + 1) = 1 :=
      Real.smoothTransition.one_of_one_le h
    rw [hs]; ring
  · intro t ht
    show -δ < Real.smoothTransition (2 * t / δ + 1) * t
        + (1 - Real.smoothTransition (2 * t / δ + 1)) * (-(δ / 2)) ∧
      Real.smoothTransition (2 * t / δ + 1) * t
        + (1 - Real.smoothTransition (2 * t / δ + 1)) * (-(δ / 2)) < 0
    have hval : Real.smoothTransition (2 * t / δ + 1) * t
        + (1 - Real.smoothTransition (2 * t / δ + 1)) * (-(δ / 2))
        = -(δ / 2) + Real.smoothTransition (2 * t / δ + 1) * (t + δ / 2) := by ring
    rw [hval]
    by_cases h : t + δ / 2 ≤ 0
    · have hzero : 2 * t / δ + 1 ≤ 0 := by
        have h1 : 2 * t / δ ≤ -1 := by
          rw [div_le_iff₀ hδ]; linarith
        linarith
      have hs : Real.smoothTransition (2 * t / δ + 1) = 0 :=
        Real.smoothTransition.zero_of_nonpos hzero
      rw [hs]
      simp only [zero_mul, add_zero]
      constructor <;> linarith
    · have hlt : 0 < t + δ / 2 := not_le.mp h
      have hs0 : 0 ≤ Real.smoothTransition (2 * t / δ + 1) := Real.smoothTransition.nonneg _
      have hs1 : Real.smoothTransition (2 * t / δ + 1) ≤ 1 := Real.smoothTransition.le_one _
      constructor
      · have h1 : 0 ≤ Real.smoothTransition (2 * t / δ + 1) * (t + δ / 2) :=
          mul_nonneg hs0 (le_of_lt hlt)
        linarith
      · have h1 : Real.smoothTransition (2 * t / δ + 1) * (t + δ / 2) ≤ 1 * (t + δ / 2) :=
          mul_le_mul_of_nonneg_right hs1 (le_of_lt hlt)
        linarith






end

end Work.Drive
