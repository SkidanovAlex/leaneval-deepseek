import Mathlib
import Submission.Work.Drive.planeWrapData
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.planeProfiles
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.dataR_dataD_spec
import Submission.Work.Drive.Neutral.stripDiskChordNe
import Submission.Work.Drive.Neutral.dataChordAux
import Submission.Work.Drive.Neutral.stripDiskValueClause
import Submission.Work.Drive.Neutral.stripDiskAntipodal
import Submission.Work.Drive.Neutral.stripDiskSetup
import Submission.Work.Drive.Neutral.symmWC_ne_zero_le
import Submission.Work.Drive.exists_collar_ne_pos
import Submission.Work.Drive.seeleyDescent_ext
import Submission.Work.Drive.capSide_capPiece
import Submission.Work.Drive.Neutral.dataChord_spec
import Submission.Work.Drive.bandData
import Submission.Work.Drive.chordAnnulusDescentStrict
import Submission.Work.Drive.exists_planeChartDatum

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Filter

noncomputable section

/-! ## The value clause for the descent-based chart

The chart of `Submission/Work/Drive/PLANE_CHART_FINAL.md` evaluates the *descent* `(M, W)` of the
chord data at `(x, τ) = (wCollapse z, bandTau a z)`; on the annulus `x` is a unit complex number and
`τ = s²` with `s` the chord opening, so there the descent must reproduce the symmetric chord data.
The two lemmas below are the algebraic content of the strip clause in that presentation: the radius
`√(‖M‖² + τ‖W‖²)` is `symmR`, the disk coordinate `M/√(‖M‖² + τ‖W‖²)` is `symmD`, and the halving
`W/‖W‖` is `symmWC/‖symmWC‖`.  With them the strip clause is
`Work.Drive.planePt_symmD_eq_stripChart` (`Submission/Work/Drive/Neutral/stripDiskValueClause.lean`),
and no further identification is needed. -/

/-- **The radius of the descent data at the circle.**  If the descent reproduces the chord data at
`(x, s²)` with `‖x‖ = 1`, then `‖M‖² + s²‖W‖² = symmR²`: the capping radius of the descent is the
capping radius of the chord. -/
theorem dataR_desc_eq (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) {σ : ℝ} {M W : ℂ × ℝ → ℂ}
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ Real.pi / 2)
    (hM : M (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)
        = Neutral.dataMid γ (Complex.exp ((σ : ℂ) * Complex.I)) s)
    (hW : W (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)
        = Neutral.dchW γ (Complex.exp ((σ : ℂ) * Complex.I), s)) :
    ‖M (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)‖ ^ 2
        + s ^ 2 * ‖W (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)‖ ^ 2
      = (Neutral.symmR γ σ s) ^ 2 := by
  set x : ℂ := Complex.exp ((σ : ℂ) * Complex.I) with hxdef
  have hx1 : ‖x‖ = 1 := by rw [hxdef, Complex.norm_exp]; simp
  have hxe : x ≠ 0 := by rw [← norm_pos_iff, hx1]; norm_num
  have hch : Neutral.dataChord γ x s = s • Neutral.dchW γ (x, s) :=
    (Neutral.dchW_smul γ hγ hxe s).symm
  have hchord : ‖Neutral.dataChord γ x s‖ = s * ‖W (x, s ^ 2)‖ := by
    rw [hch, norm_smul, Real.norm_eq_abs, abs_of_pos hs, ← hW]
  have hmid : ‖Neutral.dataMid γ x s‖ = ‖M (x, s ^ 2)‖ := by rw [hM]
  have hR : Neutral.dataR γ x s = Neutral.symmR γ σ s := Neutral.dataR_exp_eq γ σ s hs hs2
  have hdataR : Neutral.dataR γ x s ^ 2
      = Complex.normSq (Neutral.dataMid γ x s) + Complex.normSq (Neutral.dataChord γ x s) := by
    rw [Neutral.dataR,
      Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
  rw [← hR, hdataR, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hmid, hchord]
  ring

/-- **The value clause data of the descent at the circle.**  Under the same hypotheses, the disk
coordinate and the halving of the descent are those of the symmetric chord data, so
`Work.Drive.planePt_symmD_eq_stripChart` identifies the plane point with the strip chart. -/
theorem chordData_desc_eq_stripData (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) {σ : ℝ} {M W : ℂ × ℝ → ℂ}
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ Real.pi / 2)
    (hM : M (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)
        = Neutral.dataMid γ (Complex.exp ((σ : ℂ) * Complex.I)) s)
    (hW : W (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)
        = Neutral.dchW γ (Complex.exp ((σ : ℂ) * Complex.I), s)) :
    (M (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)
        / ((Real.sqrt (‖M (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)‖ ^ 2
            + s ^ 2 * ‖W (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)‖ ^ 2) : ℝ) : ℂ)
      = Neutral.symmD γ σ s) ∧
    (W (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)
        / ((‖W (Complex.exp ((σ : ℂ) * Complex.I), s ^ 2)‖ : ℝ) : ℂ)
      = Neutral.symmWC γ σ s / ((‖Neutral.symmWC γ σ s‖ : ℝ) : ℂ)) := by
  set x : ℂ := Complex.exp ((σ : ℂ) * Complex.I) with hxdef
  have hx1 : ‖x‖ = 1 := by rw [hxdef, Complex.norm_exp]; simp
  have hxe : x ≠ 0 := by rw [← norm_pos_iff, hx1]; norm_num
  have hA := dataR_desc_eq γ hγ hs hs2 hM hW
  have hsqrt : Real.sqrt (‖M (x, s ^ 2)‖ ^ 2 + s ^ 2 * ‖W (x, s ^ 2)‖ ^ 2)
      = Neutral.dataR γ x s := by
    rw [hA, ← Neutral.dataR_exp_eq γ σ s hs hs2]
    exact Real.sqrt_sq (Real.sqrt_nonneg _)
  constructor
  · have hD : Neutral.dataMid γ x s / ((Neutral.dataR γ x s : ℝ) : ℂ)
        = Neutral.symmD γ σ s := Neutral.dataD_exp_eq γ σ s hs hs2
    rw [hsqrt, hM]
    exact hD
  · rw [hW]
    exact Neutral.halving_div_norm_eq hγ (Neutral.dchW γ) hs hs2
      (Neutral.dchW_smul γ hγ hxe s).symm

/-! ## The sign pattern of the band coordinate

The chart's evaluation region is `(x, τ) = (wCollapse z, bandTau a z)`.  The facts below record which
part of the `(x,τ)`-plane it meets, and hence which of the (necessarily restricted, see
`PLANE_CHART_FINAL.md` §4) band estimates of the chord data are needed:

* `‖z‖ ≥ 1/2`: `|x| = 1` and `τ ≥ 0` (the strip; the value clause of the data applies);
* `a < ‖z‖ < 1/2`: `|x| < 1` and `τ < 0` (the cap region proper);
* `‖z‖ ≤ a`: `|x| ≤ profCut (1/4) a² < 1` and `τ = 0` (the gluing-torus piece of the cap).
-/

lemma bandTau_eq_zero' {a : ℝ} (ha : a < 1 / 2) {z : ℂ} (h : ‖z‖ ≤ a) : bandTau a z = 0 := by
  unfold bandTau
  exact bandProf_eq_zero ha h

lemma bandTau_neg {a : ℝ} (ha : a < 1 / 2) {z : ℂ} (h1 : a < ‖z‖) (h2 : ‖z‖ < 1 / 2) :
    bandTau a z < 0 := by
  unfold bandTau bandProf
  have hpos : 0 < pStep a (1 / 2) ‖z‖ := by
    unfold pStep
    exact Real.smoothTransition.pos_of_pos (div_pos (by linarith) (by linarith))
  have hneg : Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  exact mul_neg_of_pos_of_neg hpos hneg

lemma bandTau_pos {a : ℝ} (ha : a < 1 / 2) {z : ℂ} (h : 1 / 2 < ‖z‖) : 0 < bandTau a z := by
  rw [bandTau_eq ha (le_of_lt h)]
  exact mul_pos (by positivity) (by linarith)

/-! ## The corrected assembly: cap coordinates, the collar cutoff, and non-vanishing

`Submission/Work/Drive/PLANE_CHART_ASSEMBLY.md` §7–§9 and the numerical experiments recorded there
left the construction of the plane chart stuck on a *class* obligation: the only known way to make the
chart smooth at `z = 0` is to kill the direction dependence of the chord data on a neighbourhood of
`z = 0`, and every blend device that was tried either cancels (the vector blends) or leaves the cap
side (the data blends with a constant anchor).

The three lemmas below are the algebraic core of the corrected architecture, which resolves this:

* **the chart is built in the cap coordinates** `(w, dc)` of the capping space (`capProjVecOf`): the
  point is a `CapPiece` point as soon as `‖dc‖ ≤ 1` (`exists_capPiece_of_capForm` below, an immediate
  corollary of `Work.Drive.capSide_capPiece`), and no side condition on `w` beyond `w ≠ 0` is needed.
  This is why the *disk* coordinate `dc` can be blended *convexly* between the honest datum and a
  constant anchor without ever leaving the cap side, and why the cap clause of `IsPlaneChart` then
  needs no inequality about the datum at all;
* **the only real remaining obligation is `w ≠ 0`**, and the two blend lemmas below show how to
  discharge it: the cancellation `λ W + (1-λ) a = 0` needs *both* moduli to match
  (`blend_ne_zero_of_norm_ne`), so making the modulus of the anchor disagree with the weight
  *everywhere* kills it without any side condition on the directions.  The special anchor "the datum
  rotated by `90°`" (`blend_rot_ne_zero`) has this property for free, because `i W` is never
  antiparallel to `W`.
-/

/-- **The cap-form point is on the cap side.**  For a non-zero halving datum `w` and a disk
coordinate `dc` in the closed unit disk, the sphere lift `capProjVecOf w dc` satisfies
`‖c₁‖ ≤ ‖c₂‖` — i.e. its projective class lies in the cap piece.  (This is the *non-strict* form
needed by `Work.Drive.capSide_capPiece`; the strict form on the unit circle is
`Work.Drive.isCapVec_capProjVecOf`.) -/
lemma capProjVecOf_isCapSide {w dc : ℂ} (hw : w ≠ 0) (hdc : ‖dc‖ ≤ 1) :
    ‖c₁ (capProjVecOf w dc)‖ ≤ ‖c₂ (capProjVecOf w dc)‖ := by
  rw [c₁_capProjVecOf, c₂_capProjVecOf]
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : ‖dc‖ ^ 2 ≤ 1 := by nlinarith [hdc, norm_nonneg dc]
  have hs2 : (0 : ℝ) ≤ 2 - ‖dc‖ ^ 2 := by linarith
  have hkey : Real.sqrt (1 - ‖dc‖ ^ 2 / 2) * Real.sqrt 2 = Real.sqrt (2 - ‖dc‖ ^ 2) := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 1 - ‖dc‖ ^ 2 / 2 by linarith),
      show (1 - ‖dc‖ ^ 2 / 2) * 2 = 2 - ‖dc‖ ^ 2 by ring]
  have hmain : ‖dc‖ ≤ Real.sqrt (2 - ‖dc‖ ^ 2) := by
    rw [Real.le_sqrt (norm_nonneg dc) hs2]
    linarith
  rw [norm_div, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg 2), norm_mul, norm_star,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), div_le_iff₀ h2pos]
  have h1 := mul_le_mul_of_nonneg_right hmain (le_of_lt hwn)
  have h3 : ‖w‖ * Real.sqrt (1 - ‖dc‖ ^ 2 / 2) * Real.sqrt 2
      = ‖w‖ * Real.sqrt (2 - ‖dc‖ ^ 2) := by rw [← hkey]; ring
  linarith [h1, h3]

/-- **The cap clause in cap coordinates.**  Any capping-space point whose projective class is the cap
lift `capProjVecOf w dc` of a *point of the cap solid torus* (`‖dc‖ ≤ 1`, `w ≠ 0`) is the class of an
explicit `CapPiece` element.  This is what turns the cap clause of `Work.Drive.IsPlaneChart` into the
scalar condition `‖dc‖ ≤ 1`. -/
theorem exists_capPiece_of_capForm {r : ℝ} (hr : 0 < r) {w dc : ℂ} (hw : ‖w‖ = 1)
    (hd : ‖dc‖ ≤ 1) :
    ∃ c : CapPiece, cappingSpaceHomeoProj.symm
        (⟨r, hr⟩, Projectivization.mk ℝ (capProjVecOf w dc) (capProjVecOf_ne_zero hw hd))
      = Quotient.mk'' (Sum.inr c) :=
  capSide_capPiece hr (capProjVecOf_ne_zero hw hd)
    (capProjVecOf_isCapSide (by intro h; rw [h, norm_zero] at hw; norm_num at hw) hd)

/-- **The modulus mismatch defeats the cancellation.**  If the two terms of the blend
`λ • W + A` have different moduli, the blend cannot vanish: a vanishing would force
`‖A‖ = λ ‖W‖ = λ`.  In the construction of the plane chart this is applied with `W` the unit halving
datum and `A = (1 - λ) • a` the anchor term, so that *no* condition on the directions is ever needed —
in particular no "the loop avoids a point" argument. -/
lemma blend_ne_zero_of_norm_ne {W A : ℂ} {lam : ℝ} (hW : ‖W‖ = 1) (hlam : 0 ≤ lam)
    (hA : ‖A‖ ≠ lam) : lam • W + A ≠ 0 := by
  intro h
  have h1 : A = -(lam • W) := by linear_combination h
  rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam, hW, mul_one] at hA
  exact hA rfl

/-- The modulus-mismatch criterion in the form in which the construction uses it: the anchor is a
weight `(1 - λ)` times a fixed vector `a`. -/
lemma blend_ne_zero_of_smul {W a : ℂ} {lam : ℝ} (hW : ‖W‖ = 1) (hlam : 0 ≤ lam)
    (hne : ‖(1 - lam) • a‖ ≠ lam) : lam • W + (1 - lam) • a ≠ 0 :=
  blend_ne_zero_of_norm_ne hW hlam hne

/-- **The `90°`-rotated anchor never cancels.**  Blending a unit datum `W` with its own rotation
`i W` cannot vanish, for *every* weight `λ ∈ [0,1]`: the two terms are never antiparallel.  This is the
anchor that makes the "kill the direction dependence at `z = 0`" step of the construction work without
any quantitative hypothesis on the curve. -/
lemma blend_rot_ne_zero {W : ℂ} (hW : ‖W‖ = 1) {lam : ℝ} (h0 : 0 ≤ lam) (_h1 : lam ≤ 1) :
    lam • W + (1 - lam) • (Complex.I * W) ≠ 0 := by
  have hfac : lam • W + (1 - lam) • (Complex.I * W)
      = W * (((lam : ℝ) : ℂ) + (((1 - lam : ℝ)) : ℂ) * Complex.I) := by
    simp only [Complex.real_smul]; ring
  rw [hfac]
  refine mul_ne_zero (fun h => by rw [h, norm_zero] at hW; norm_num at hW) ?_
  have hns : Complex.normSq (((lam : ℝ) : ℂ) + (((1 - lam : ℝ)) : ℂ) * Complex.I)
      = lam ^ 2 + (1 - lam) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hpos : 0 < Complex.normSq (((lam : ℝ) : ℂ) + (((1 - lam : ℝ)) : ℂ) * Complex.I) := by
    rw [hns]; nlinarith
  intro h
  rw [h] at hpos
  simpa using hpos

/-- **Non-vanishing of the cap lift for an arbitrary non-zero halving.**  `capProjVecOf w dc` is
zero exactly when `w = 0` (as long as `‖dc‖ ≤ 1`), so the cap coordinates may be used with any
non-zero `w` — in particular with the unnormalised blends of the construction. -/
lemma capProjVecOf_ne_zero_of_ne {w dc : ℂ} (hw : w ≠ 0) (hd : ‖dc‖ ≤ 1) :
    capProjVecOf w dc ≠ 0 := by
  intro h
  have h1 : c₁ (capProjVecOf w dc) = 0 := by rw [h]; simp [c₁]
  have h2 : c₂ (capProjVecOf w dc) = 0 := by rw [h]; simp [c₂]
  rw [c₁_capProjVecOf] at h1
  rw [c₂_capProjVecOf] at h2
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact hw (star_eq_zero.mp h')
  · have hs : Real.sqrt (1 - ‖dc‖ ^ 2 / 2) = 0 := Complex.ofReal_eq_zero.mp h'
    have hlow : 1 - ‖dc‖ ^ 2 / 2 ≤ 0 := Real.sqrt_eq_zero'.mp hs
    have hdc : ‖dc‖ ^ 2 = 1 := by nlinarith [hlow, hd, norm_nonneg dc, sq_nonneg (‖dc‖)]
    have hdcne : dc ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hdc
      norm_num at hdc
    have hsc : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    rw [div_eq_mul_inv] at h1
    rcases mul_eq_zero.mp h1 with h'' | h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · exact hdcne h3
      · exact hw h3
    · exact absurd h'' (inv_ne_zero hsc)

/-- **The cap clause, for an arbitrary non-zero halving.**  `Work.Drive.exists_capPiece_of_capForm`
without the normalisation `‖w‖ = 1` on the halving. -/
theorem exists_capPiece_of_capForm' {r : ℝ} (hr : 0 < r) {w dc : ℂ} (hw : w ≠ 0)
    (hd : ‖dc‖ ≤ 1) :
    ∃ c : CapPiece, cappingSpaceHomeoProj.symm
        (⟨r, hr⟩, Projectivization.mk ℝ (capProjVecOf w dc) (capProjVecOf_ne_zero_of_ne hw hd))
      = Quotient.mk'' (Sum.inr c) := by
  refine capSide_capPiece hr (capProjVecOf_ne_zero_of_ne hw hd) ?_
  rw [c₁_capProjVecOf, c₂_capProjVecOf]
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : ‖dc‖ ^ 2 ≤ 1 := by nlinarith [hd, norm_nonneg dc]
  have hs2 : (0 : ℝ) ≤ 2 - ‖dc‖ ^ 2 := by linarith
  have hkey : Real.sqrt (1 - ‖dc‖ ^ 2 / 2) * Real.sqrt 2 = Real.sqrt (2 - ‖dc‖ ^ 2) := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 1 - ‖dc‖ ^ 2 / 2 by linarith),
      show (1 - ‖dc‖ ^ 2 / 2) * 2 = 2 - ‖dc‖ ^ 2 by ring]
  have hmain : ‖dc‖ ≤ Real.sqrt (2 - ‖dc‖ ^ 2) := by
    rw [Real.le_sqrt (norm_nonneg dc) hs2]; linarith
  rw [norm_div, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg 2), norm_mul, norm_star,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), div_le_iff₀ h2pos]
  have h1 := mul_le_mul_of_nonneg_right hmain (norm_nonneg w)
  have h3 : ‖w‖ * Real.sqrt (1 - ‖dc‖ ^ 2 / 2) * Real.sqrt 2
      = ‖w‖ * Real.sqrt (2 - ‖dc‖ ^ 2) := by rw [← hkey]; ring
  linarith [h1, h3]

/-- **The cap clause for the blended cap coordinates**, which is the form in which the construction of
`PLANE_CHART_FINAL.md` uses it: the halving is blended with its own `90°`-rotation (never zero,
`Work.Drive.blend_rot_ne_zero`) and the disk coordinate is blended convexly with an anchor inside `D²`
(so `‖dc‖ ≤ 1`), and the resulting point is a `CapPiece` point — with no hypothesis relating the two
blend weights, no hypothesis on the curve, and no inequality on the datum. -/
theorem exists_capPiece_of_capBlend {r : ℝ} (hr : 0 < r) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {W dc dcC : ℂ} (hW : ‖W‖ = 1) (hd : ‖dc‖ ≤ 1) (hdC : ‖dcC‖ ≤ 1) :
    ∃ c : CapPiece, cappingSpaceHomeoProj.symm
        (⟨r, hr⟩, Projectivization.mk ℝ
          (capProjVecOf (lam • W + (1 - lam) • (Complex.I * W))
            (lam • dc + (1 - lam) • dcC))
          (capProjVecOf_ne_zero_of_ne (blend_rot_ne_zero hW h0 h1) (by
            calc ‖lam • dc + (1 - lam) • dcC‖
                ≤ ‖lam • dc‖ + ‖(1 - lam) • dcC‖ := norm_add_le _ _
              _ = lam * ‖dc‖ + (1 - lam) * ‖dcC‖ := by
                  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                    abs_of_nonneg h0, abs_of_nonneg (by linarith)]
              _ ≤ lam * 1 + (1 - lam) * 1 :=
                  add_le_add (mul_le_mul_of_nonneg_left hd h0)
                    (mul_le_mul_of_nonneg_left hdC (by linarith))
              _ = 1 := by ring)))
      = Quotient.mk'' (Sum.inr c) :=
  exists_capPiece_of_capForm' hr (blend_rot_ne_zero hW h0 h1) (by
    calc ‖lam • dc + (1 - lam) • dcC‖
        ≤ ‖lam • dc‖ + ‖(1 - lam) • dcC‖ := norm_add_le _ _
      _ = lam * ‖dc‖ + (1 - lam) * ‖dcC‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h0, abs_of_nonneg (by linarith)]
      _ ≤ lam * 1 + (1 - lam) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hd h0)
            (mul_le_mul_of_nonneg_left hdC (by linarith))
      _ = 1 := by ring)



/-! ## The evaluated region of the chart: the direction profile and the band coordinate

The chart of design V2 (`Submission/Work/Drive/PLANE_CHART_V2_DESIGN.md`) is

`Q z := cappingVecPoint (r z) (confProjVecOf (u z) (d z))`,
`x z := wCollapse z`, `τ z := ψ (tauComp τ₀ z)`, `M z := M (x z, τ z)`, `W z := W (x z, τ z)`,
`A z := ‖M z‖² + τ z ‖W z‖²`, `r z := √(A z)`, `d z := M z / √(A z)`, `u z := W z / ‖W z‖`,

with `(M, W, c)` the descended chord data of `Work.Drive.chordAnnulusDescentStrict` and `ψ` the
one-sided clamp of `Work.Drive.exists_oneSidedClamp c`.  The lemmas below are the region analysis the
four clauses need: the norms of the direction profile, the sign and size of the band coordinate, and
the resulting estimates. -/

/-- The norm of the collapsed direction is the radial cutoff `profCut (1/4)` (for `z ≠ 0`). -/
lemma norm_wCollapse_eq_profCut {z : ℂ} (hz : z ≠ 0) :
    ‖wCollapse z‖ = profCut (1 / 4) (‖z‖ ^ 2) := by
  have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  rw [wCollapse, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wProf_nonneg _)]
  unfold wProf
  rw [Real.sqrt_sq (norm_nonneg z), div_mul_cancel₀ _ (ne_of_gt hzpos)]

/-- On the circle `‖z‖ = 1` the collapsed direction is the point itself. -/
lemma wCollapse_eq_self_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : wCollapse z = z := by
  rw [wCollapse_eq (by rw [hz]; norm_num), hz, Complex.ofReal_one, div_one]

/-- **The direction profile stays outside the blend region below the chart's collar.**  For
`3/16 ≤ ρ₀²` and `ρ₀ ≤ ‖z‖`, the evaluated direction has norm at least `1/2`, so the chord data is
*not* blended there and the band estimates of the descent apply. -/
lemma half_le_norm_wCollapse (ρ₀ : ℝ) (hρ0 : 0 < ρ₀) (hρ : 3 / 16 ≤ ρ₀ ^ 2) {z : ℂ}
    (hz : ρ₀ ≤ ‖z‖) : 1 / 2 ≤ ‖wCollapse z‖ := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
  rw [norm_wCollapse_eq_profCut hz0]
  refine profCut_quarter_ge_half ?_
  have h2 : ρ₀ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [pow_two, pow_two]; exact mul_le_mul hz hz (le_of_lt hρ0) (norm_nonneg z)
  linarith

/-- **The chart's band coordinate is strictly negative inside the unit disk of radius `1/2`.** -/
lemma chartTau_neg {τ₀ : ℝ} (hτ₀ : τ₀ < 0) {ψ : ℝ → ℝ}
    (hψ : ∀ t : ℝ, t < 0 → ψ t < 0) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    ψ (tauComp τ₀ z) < 0 :=
  hψ _ (tauComp_neg hτ₀ hz)

/-- **The chart's band coordinate is the honest one on the outer annulus**: the clamp is the identity
on `[0, ∞)` and `tauComp` reproduces the strip profile there. -/
lemma chartTau_eq_outer {τ₀ : ℝ} {ψ : ℝ → ℝ} (hψ : ∀ t : ℝ, 0 ≤ t → ψ t = t)
    {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : ψ (tauComp τ₀ z) = Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2 := by
  rw [hψ _ (by rw [tauComp_eq hz]; positivity), tauComp_eq hz]
  ring

/-- **The chart's band coordinate is bounded by the clamp parameter.** -/
lemma abs_chartTau_lt {δ : ℝ} (hδ : 0 < δ) {ψ : ℝ → ℝ}
    (hψ : ∀ t : ℝ, t < 0 → -δ < ψ t ∧ ψ t < 0) {t : ℝ} (ht : t < 0) : |ψ t| < δ := by
  obtain ⟨h1, h2⟩ := hψ t ht
  rw [abs_of_neg h2]; linarith

end
/-! ## The assembly of the plane chart from the chart datum

`Submission/Work/Drive/PLANE_CHART_LIFT_DESIGN.md` §5: given the descended chord data `(M, W)`, the
band threshold `a`, a smooth positive radius `r` and a smooth nowhere-vanishing lift `V` with the
*strip values* on `1/2 < ‖z‖ ≤ 1` and the *cap form* on `‖z‖ < 1/2`, the capping-space point
`planeChartMap r V` is a plane chart of `γ`. -/

noncomputable section

/-- **The capping-space point presented by a radius and a sphere lift.** -/
def planeChartMap (r : ℂ → ℝ) (V : ℂ → Eucl 3) (hr : ∀ z : ℂ, 0 < r z)
    (hV : ∀ z : ℂ, V z ≠ 0) (z : ℂ) : CappingSpace :=
  cappingSpaceHomeoProj.symm (⟨r z, hr z⟩, Projectivization.mk ℝ (V z) (hV z))

/-- Negating the halving negates the configuration lift. -/
lemma confProjVecOf_neg (u d : ℂ) : confProjVecOf (-u) d = -confProjVecOf u d := by
  simp only [confProjVecOf]
  rw [show (-u) * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)
        = -(u * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)) by ring,
    show star (-u) * d / ((Real.sqrt 2 : ℝ) : ℂ)
        = -(star u * d / ((Real.sqrt 2 : ℝ) : ℂ)) by rw [star_neg]; ring]
  exact ofComplex_neg _ _

/-- The plane chart point depends only on the radius and the projective class. -/
lemma planeChartMap_congr_class {r r' : ℂ → ℝ} {V V' : ℂ → Eucl 3} (hr : ∀ z : ℂ, 0 < r z)
    (hV : ∀ z : ℂ, V z ≠ 0) (hr' : ∀ z : ℂ, 0 < r' z) (hV' : ∀ z : ℂ, V' z ≠ 0) {z z' : ℂ}
    (hz : r z = r' z')
    (hcl : Projectivization.mk ℝ (V z) (hV z) = Projectivization.mk ℝ (V' z') (hV' z')) :
    planeChartMap r V hr hV z = planeChartMap r' V' hr' hV' z' := by
  unfold planeChartMap
  exact congrArg cappingSpaceHomeoProj.symm (Prod.ext (Subtype.ext hz) hcl)

/-- **The assembly: the chart datum gives the plane chart.** -/
theorem isPlaneChart_of_datum (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (M W : ℂ × ℝ → ℂ) (a : ℝ) (r : ℂ → ℝ) (V : ℂ → Eucl 3)
    (ha : a < 1 / 2)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    (hrsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hVsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hrpos : ∀ z : ℂ, 0 < r z) (hVne : ∀ z : ℂ, V z ≠ 0)
    (hstrip : ∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ ≤ 1 →
      r z = Real.sqrt (‖M (wCollapse z, bandTau a z)‖ ^ 2
            + bandTau a z * ‖W (wCollapse z, bandTau a z)‖ ^ 2) ∧
      V z = confProjVecOf
        (W (wCollapse z, bandTau a z)
          / ((‖W (wCollapse z, bandTau a z)‖ : ℝ) : ℂ))
        (M (wCollapse z, bandTau a z)
          / ((Real.sqrt (‖M (wCollapse z, bandTau a z)‖ ^ 2
                + bandTau a z * ‖W (wCollapse z, bandTau a z)‖ ^ 2) : ℝ) : ℂ)))
    (hcap : ∀ z : ℂ, ‖z‖ < 1 / 2 →
      ∃ w dc : ℂ, w ≠ 0 ∧ ‖dc‖ ≤ 1 ∧ V z = capProjVecOf w dc) :
    IsPlaneChart γ hγne (planeChartMap r V hrpos hVne) := by
  letI := cappingCharted
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ## smoothness
    have hC : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin 2) => planeChartMap r V hrpos hVne (Neutral.sdCplxOf w)) := by
      intro w
      exact Neutral.contMDiffAt_cappingVecPoint (fun b : EuclideanSpace ℝ (Fin 2) =>
          r (Neutral.sdCplxOf b)) (fun b : EuclideanSpace ℝ (Fin 2) => V (Neutral.sdCplxOf b)) w
        (fun b => hrpos _) (fun b => hVne _)
        (contMDiff_iff_contDiff.mpr (hrsm.comp Neutral.sdContDiff_cplxOf) w)
        (contMDiff_iff_contDiff.mpr (hVsm.comp Neutral.sdContDiff_cplxOf) w)
    have hcomp := hC.comp (contMDiff_iff_contDiff.mpr Neutral.sdContDiff_euc2)
    simpa only [Function.comp_def, Neutral.sdCplxOf_euc2] using hcomp
  · -- ## the strip clause
    intro z h1 h2
    set s : ℝ := Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2) with hsdef
    have hzpos : (0 : ℝ) < ‖z‖ := by linarith
    have hzn : z ≠ 0 := fun h => by rw [h, norm_zero] at hzpos; exact lt_irrefl _ hzpos
    have hspos : 0 < s := by
      rw [hsdef]
      refine Real.sqrt_pos.mpr ?_
      have hpos : (0 : ℝ) < ‖z‖ - 1 / 2 := by linarith
      positivity
    have hs2 : s ≤ Real.pi / 2 := by
      have hsnn : 0 ≤ s := le_of_lt hspos
      have hsq : s ^ 2 ≤ (Real.pi / 2) ^ 2 := by
        rw [hsdef, Real.sq_sqrt (by positivity)]
        have hle : ‖z‖ - 1 / 2 ≤ 1 / 2 := by linarith
        nlinarith [Real.pi_pos, hle]
      have := (sq_le_sq.mp hsq)
      rwa [abs_of_nonneg hsnn, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at this
    have hτ : bandTau a z = s ^ 2 := by
      rw [bandTau_eq ha (le_of_lt h1), hsdef, Real.sq_sqrt (by positivity)]
      ring
    have hx : wCollapse z = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
      rw [wCollapse_eq (le_of_lt h1), ← Circle.coe_exp, Neutral.exp_arg_eq_div_norm z hzn]
    have hx1 : ‖wCollapse z‖ = 1 := norm_wCollapse_eq (le_of_lt h1)
    have hτpos : 0 < bandTau a z := bandTau_pos ha h1
    have hM : M (Complex.exp ((Complex.arg z : ℂ) * Complex.I), s ^ 2)
        = Neutral.dataMid γ (Complex.exp ((Complex.arg z : ℂ) * Complex.I)) s := by
      have hv := hMval (wCollapse z) (bandTau a z) (le_of_lt hτpos) hx1
      rw [hτ, Real.sqrt_sq hspos.le, hx] at hv
      exact hv
    have hW : W (Complex.exp ((Complex.arg z : ℂ) * Complex.I), s ^ 2)
        = Neutral.dchW γ (Complex.exp ((Complex.arg z : ℂ) * Complex.I), s) := by
      have hv := hWval (wCollapse z) (bandTau a z) (le_of_lt hτpos) hx1
      rw [hτ, Real.sqrt_sq hspos.le, hx] at hv
      exact hv
    have hsqrt : Real.sqrt (‖M (wCollapse z, bandTau a z)‖ ^ 2
          + bandTau a z * ‖W (wCollapse z, bandTau a z)‖ ^ 2)
        = Neutral.symmR γ (Complex.arg z) s := by
      have hA := dataR_desc_eq γ hγ hspos hs2 hM hW
      rw [hτ, hx]
      rw [hA, Real.sqrt_sq (le_of_lt (Neutral.symmR_pos hγne (Complex.arg z) s))]
    have hrz : r z = Neutral.symmR γ (Complex.arg z) s := by
      rw [(hstrip z h1 h2).1, hsqrt]
    have hVz : V z = confProjVecOf
        (Neutral.symmWC γ (Complex.arg z) s / ((‖Neutral.symmWC γ (Complex.arg z) s‖ : ℝ) : ℂ))
        (Neutral.symmD γ (Complex.arg z) s) := by
      have hpair := chordData_desc_eq_stripData γ hγ hspos hs2 hM hW
      rw [(hstrip z h1 h2).2, hτ, hx]
      rw [hpair.1, hpair.2]
    have hu1 : ‖Neutral.symmWC γ (Complex.arg z) s
        / ((‖Neutral.symmWC γ (Complex.arg z) s‖ : ℝ) : ℂ)‖ = 1 :=
      (Neutral.symmWC_ne_zero_le γ hγ).2 (Complex.arg z) s hspos hs2
    have hd1 : ‖Neutral.symmD γ (Complex.arg z) s‖ ≤ 1 := Neutral.symmD_norm_le_one γ _ _
    have hv1 : confProjVecOf (Neutral.symmWC γ (Complex.arg z) s
        / ((‖Neutral.symmWC γ (Complex.arg z) s‖ : ℝ) : ℂ))
        (Neutral.symmD γ (Complex.arg z) s) ≠ 0 := confProjVecOf_ne_zero hu1 hd1
    have hfinal : planeChartMap r V hrpos hVne z
        = planePt (Neutral.symmWC γ (Complex.arg z) s
            / ((‖Neutral.symmWC γ (Complex.arg z) s‖ : ℝ) : ℂ))
          (Neutral.symmR γ (Complex.arg z) s) (Neutral.symmR_pos hγne (Complex.arg z) s)
          (Neutral.symmD γ (Complex.arg z) s) hu1 hv1 := by
      unfold planeChartMap planePt
      refine congrArg cappingSpaceHomeoProj.symm (Prod.ext (Subtype.ext hrz) ?_)
      refine (Projectivization.mk_eq_mk_iff ℝ (V z)
        (confProjVecOf _ _) (hVne z) (confProjVecOf_ne_zero hu1 hd1)).mpr ⟨1, ?_⟩
      rw [one_smul, hVz]
    rw [hfinal]
    exact Neutral.planePt_symmD_eq_stripChart hγ hγne hspos hs2 rfl
      (Neutral.symmR_pos hγne (Complex.arg z) s) hu1 hv1
  · -- ## the seam clause
    intro z hz
    have hz1 : (1 : ℝ) / 2 < ‖z‖ := by rw [hz]; norm_num
    have hz1' : (1 : ℝ) / 2 < ‖-z‖ := by rw [norm_neg, hz]; norm_num
    have hz2 : ‖z‖ ≤ 1 := le_of_eq hz
    have hz2' : ‖-z‖ ≤ 1 := by rw [norm_neg, hz]
    have hx1 : ‖wCollapse z‖ = 1 := norm_wCollapse_eq (le_of_lt hz1)
    have hτpos : 0 < bandTau a z := bandTau_pos ha hz1
    have hτe : bandTau a (-z) = bandTau a z := by unfold bandTau; rw [norm_neg]
    have hwne : wCollapse z ≠ 0 := by
      intro h; rw [h, norm_zero] at hx1; norm_num at hx1
    have hs : Real.sqrt (bandTau a z) = Real.pi / 2 := by
      rw [bandTau_eq ha (le_of_lt hz1), hz]
      rw [show Real.pi ^ 2 / 2 * (1 - 1 / 2) = (Real.pi / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have hanti := Neutral.stripDiskAntipodal γ hγ
    have hMid : M (wCollapse (-z), bandTau a (-z)) = M (wCollapse z, bandTau a z) := by
      rw [hτe, wCollapse_neg,
        hMval (-wCollapse z) (bandTau a z) (le_of_lt hτpos) (by rw [norm_neg]; exact hx1),
        hMval (wCollapse z) (bandTau a z) (le_of_lt hτpos) hx1, hs]
      exact hanti.2.1 (wCollapse z) hwne
    have hWd : W (wCollapse (-z), bandTau a (-z)) = -W (wCollapse z, bandTau a z) := by
      rw [hτe, wCollapse_neg,
        hWval (-wCollapse z) (bandTau a z) (le_of_lt hτpos) (by rw [norm_neg]; exact hx1),
        hWval (wCollapse z) (bandTau a z) (le_of_lt hτpos) hx1, hs]
      exact hanti.2.2 (wCollapse z) hwne
    obtain ⟨hrz, hVz⟩ := hstrip z hz1 hz2
    obtain ⟨hrz', hVz'⟩ := hstrip (-z) hz1' hz2'
    have hAe : Real.sqrt (‖M (wCollapse (-z), bandTau a (-z))‖ ^ 2
          + bandTau a (-z) * ‖W (wCollapse (-z), bandTau a (-z))‖ ^ 2)
        = Real.sqrt (‖M (wCollapse z, bandTau a z)‖ ^ 2
          + bandTau a z * ‖W (wCollapse z, bandTau a z)‖ ^ 2) := by
      rw [hMid, hWd, hτe, norm_neg]
    have hrz'' : r (-z) = r z := by rw [hrz', hrz, hAe]
    have hVz'' : V (-z) = -V z := by
      rw [hVz', hVz, hAe, hMid, hWd, norm_neg, neg_div, confProjVecOf_neg]
    exact planeChartMap_congr_class hrpos hVne hrpos hVne hrz''
      (projectivizationMk_eq_of_eq_neg hVz'' (hVne z) (hVne (-z)))
  · -- ## the cap clause
    intro z hz
    obtain ⟨w, dc, hw, hdc, hVz⟩ := hcap z hz
    obtain ⟨c, hc⟩ := exists_capPiece_of_capForm' (hrpos z) hw hdc
    refine ⟨c, ?_⟩
    have hstep : planeChartMap r V hrpos hVne z
        = cappingSpaceHomeoProj.symm (⟨r z, hrpos z⟩,
            Projectivization.mk ℝ (capProjVecOf w dc) (capProjVecOf_ne_zero_of_ne hw hdc)) := by
      unfold planeChartMap
      refine congrArg cappingSpaceHomeoProj.symm (Prod.ext rfl ?_)
      exact (Projectivization.mk_eq_mk_iff ℝ (V z) (capProjVecOf w dc) (hVne z)
        (capProjVecOf_ne_zero_of_ne hw hdc)).mpr ⟨1, by rw [one_smul, hVz]⟩
    rw [hstep, hc]

end


/-! ## The target

The chart of `Submission/Work/Drive/PLANE_CHART_V2_DESIGN.md`:

`Q z := cappingVecPoint (r z) (confProjVecOf (u z) (d z))` with the data `(M, W)` of
`Work.Drive.chordAnnulusDescentStrict` evaluated at `(wCollapse z, ψ (tauComp τ₀ z))`, the clamp `ψ`
of `Work.Drive.exists_oneSidedClamp c`, `A z := ‖M z‖² + τ z ‖W z‖²`, `r z := √(A z)`,
`d z := M z / √(A z)`, `u z := W z / ‖W z‖`.  On `‖z‖ ≥ ρ₀` (`ρ₀² ≥ 3/16`) the evaluated direction
has norm `≥ 1/2`, so the band estimates of the descent give `W z ≠ 0` and
`‖M z‖² > 2|τ z|‖W z‖²`, hence `A z > 0` and `1 < ‖d z‖² < 2` — the *cap* half, which is exactly the
cap clause (`Work.Drive.exists_capPiece_of_capForm`); on `‖z‖ ≥ 1/2` the clamp is the identity and the
value clauses of the descent give the strip values; `x z = 0` for `‖z‖² ≤ 1/8` and `τ z` constant for
`‖z‖² ≤ 1/16` make the chart constant near `0`. -/
theorem exists_planeChart (hU : Submission.Drive.UmlaufProp) (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hW : Work.Drive.WrapData γ) :
    ∃ Q : ℂ → Work.Drive.CappingSpace, Work.Drive.IsPlaneChart γ hγne Q := by
  obtain ⟨M, W, c, a, r, V, hMsm, hWsm, hc, ha0, ha, hMval, hWval, hband, hWne, hM0, hW0,
    hrsm, hVsm, hrpos, hVne, hstrip, hcap⟩ :=
    exists_planeChartDatum hU γ hγ hγne hW
  exact ⟨planeChartMap r V hrpos hVne,
    isPlaneChart_of_datum γ hγ hγne M W a r V ha hMval hWval hrsm hVsm hrpos hVne
      hstrip hcap⟩

end Work.Drive
