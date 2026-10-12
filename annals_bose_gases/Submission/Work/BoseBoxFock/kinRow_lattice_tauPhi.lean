import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.kinRow_lattice
import Submission.Work.BoseBoxFock.labN_sum_le_tsum
import Submission.Work.BoseBoxFock.windowedDeficitResidual_of_band
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kinRow_lattice_tauPhi` — the kinetic row of the box↔model dictionary
at the explicit profile `tauPhi`

The target is the `Lab N`-sum kinetic row: the lattice sum of the smoothed kinetic symbol
`tauSmPhi` against the corpus's box coefficients `qCoeff` is dominated by the `(1−eT)`/`eT`
two-scale continuum kinetic energy `mainWord`, plus the Neumann word `neuWord`.

## Structure of this file

* `kinRow_lattice_tauPhi_lhs` — the left-hand side written with the single bridge state
  `winState ℓ ψ = χ_Λ·(ψ − m)` (`qCoeff_eq_winState`, proved in `kinRow_lattice.lean`);

* **`winState_row`** — THE CRUX (single scale `c`, `cℓ ≥ 4π`): for the windowed mean-free state
  `g = χ_Λ(ψ − m)`,
  `Σ_{k ∈ Lab N} ℓ⁻³(c²·τ̃_c(‖k‖))‖kinFT g k‖² ≤ (2π)⁻³∫[‖p‖−c]₊²‖kinFT g p‖²`.
  Equivalently (using the proved pointwise `τ̃_c ≤ F_c` and the moment identities
  `S₀ = R₀`, `S₂ = R₂`), this is the *sharp aliasing inequality*
  `Alias(τ̃_c) = L(τ̃_c) − C(τ̃_c) ≤ C(F_c − τ̃_c)`:
  the aliasing of the smoothed scale-`c` symbol is paid by the continuum mass of the pointwise
  deficit `F_c − τ̃_c = (‖p‖−c)₊² − c²τ̃(‖p‖/c)`.
  `FINDING_L5_numerics.md` §2bis records that the analogous row at the *envelope* profile
  (`tauEnvWorst`) is FALSE (two independent refutations), which is why the explicit `tauPhi`
  is used; at `tauPhi` the row is numerically true with margin ≥ 26 % over every tested state,
  and it is *asymptotically sharp* (states modulated at a large lattice momentum `K` give the
  ratio `1 − 2c/K + O(K⁻²)`), so a proof must be loss-free in the large-`K` regime.

* `neuWord_nonneg` — `0 ≤ neuWord ℓ d eT 0 ψ` (from the proved `neuFrac_nonneg_l2`);

* `kinRow_lattice_tauPhi` — the target, assembled from the crux at `c₁ = (2sℓ)⁻¹`,
  `c₂ = (2dsℓ)⁻¹` (both `≥ 4π/ℓ` by `s ≤ 1/(8π)`, `d ≤ 1`), the dictionary identities and
  `neuWord_nonneg`.

## Status (read `FINDING_kinRow_lattice_tauPhi_session4.md` — it supersedes the session-2/3 notes;
## §7 there corrects the session-4 route-(B) claim)

Everything above is PROVED and axiom-clean; the file's *single* remaining axiom is the imported
unfinished proof inside `Work.BoseBoxFock.sharpShiftRow` (line 176), because `winState_row` *is*
that row at `g = winState ℓ ψ`.  Session 5 **retracted** the session-4 claim that the χ_Λ-windowed
twin `Work.BoseBoxFock.tauPhiRowWindow` also applies here: it does **not**, because a witness `h`
with `winState ℓ ψ = χ_Λ·h`, `ContDiff ⊤ h`, `HasCompactSupport h`, `tsupport h ⊆ boxL ℓ` would
have to equal `ψ − m` on the open ball `‖z‖ < ℓ/2` (`chiScale_ne_zero_iff`) and vanish on
`∂(boxL ℓ)` (continuity + support), forcing `ψ = m` at the six face midpoints `(±ℓ/2)e_j` — a
constraint the node's statement does not impose (proof: `FINDING…session4.md` §7).  Hence the
node's crux is the **general** `sharpShiftRow` and nothing weaker.  Session 5 did prove the
scale-monotonicity `tauPhi_scale_anti` (`c ↦ c²·tauPhi(r/c)` is nonincreasing, via`sq_mul_tauH`
and `tauPhi_eq_integral`), giving `tauSmPhi_le_lowScale`: `tauSmPhi` is dominated by its
smaller-cutoff summand alone — a *negative* reduction result (the continuum side keeps both
scales, so both instances of the crux are needed).  Session 4 verified numerically, with a
validated toolkit
(`ScratchKR2/`), the exact identity
`L(W) − C(W_c) = c(2R₁ − 3S₁) + c²(b−1)R₀ + c²·L(φ(·/c)) + Π_c` and the exact equivalence of the
two forms of the crux
(`(ROW) 2R₁ ≤ 3S₁ − (b−1)cR₀ − c·L(φ) − Π_c/c` and
`(SHARP) D₀ ≤ R₁/5 − (9c/40)R₀ + (2/(5c))(L(Θ_{5c/4}) − Π_c)`), showed that the row has **no
uniform margin** (the tight families are honest modulated states, `g = χ_Λe^{iPx}` with `P` a
lattice vector, ratio `→ 1 − c/P`), and reduced the node's obligation to a *single* instance of
the row (at `c₁`; the present two-scale assembly is strictly stronger than necessary).
Session 3 had verified the exact equivalence chain of this node's crux
(`L(c²τ(·/c)) ≤ C((‖·‖−c)₊²)` ⟺ `Φ((‖·‖−c)₊²) ≤ L(Δ_c)` ⟺ the deficit form
`2R₁ ≤ 3S₁ + (1−b)cN − Π_c/c − c·L(φ(·/c))`), the identity `Φ(c²τ(·/c)) = 3cD + c²Φ(φ(·/c))`
(with `tauPhi r = r² − 3r + b + φ r`, `b = 9/4 + ∫t²tauKer`), and the fact that the row form is
the well-conditioned one while the deficit forms are near-cancellations; it also settled that the
cellwise-Jensen route is *not* a relaxation of the row.  See that FINDING for the numbers, the
dead ends, and the recommendation (do not re-dispatch the row in any of its equivalent forms).
Read **`FINDING_kinRow_lattice_tauPhi_session5.md`** for the newest quantitative record: the
correct `c₀ = 0.0121393548464217` of the Mathlib bump (three earlier notes used `0.0099`), the
*exact* ledger identities, the **binding family** (`g = e^{iQx}φ`, `φ = exp(−α/(1−u²))`,
`supp φ = B(ℓ/2)`, `Q = 0`, `α ≈ 2–3`) on which the `(D)`-spelling of the crux is tight to
`0.35 %` while the `(SE)`/`(KERM)` spelling keeps `60–82 %` relative slack (the two normalisations
differ by a factor `≈ 230`), the exact reduction of the row to the *single* hinge row at
`λ = 3c/2` (marginally easier than `λ = 5c/4` in the carrier regime, negligible gain in the
binding regime), and the negative results (cap-shell, cell-local, `D`-only) not to re-walk.

-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

/-- `kmomLab` is `kmomInt` at the centred integer vector `labVec` (definitional). -/
lemma kmomLab_eq_kmomInt (ℓ : ℝ) (N : ℕ) (k : Lab N) :
    kmomLab ℓ N k = kmomInt ℓ (labVec N k) := rfl

/-! ## 0. The bridge state `winState` and its regularity -/

/-- `χ_Λ` is smooth (`corpusBox.chiLam ℓ = chiScale ℓ`). -/
lemma chiLam_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ContDiff ℝ (⊤ : ENat) (Work.BoseK15.corpusBox.chiLam ℓ) := by
  have h : Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ := rfl
  rw [h]
  exact Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)

/-- `χ_Λ` has compact support. -/
lemma chiLam_hasCompactSupport_tauPhi {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasCompactSupport (Work.BoseK15.corpusBox.chiLam ℓ) := by
  have h : Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ := rfl
  rw [h]
  exact Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)

/-- `χ_Λ` is supported in the closed ball of radius `ℓ/2`. -/
lemma chiLam_tsupport_subset {ℓ : ℝ} (hℓ : 0 < ℓ) :
    tsupport (Work.BoseK15.corpusBox.chiLam ℓ) ⊆ Metric.closedBall 0 (ℓ / 2) := by
  have h : Function.support (Work.BoseK15.corpusBox.chiLam ℓ) ⊆ Metric.closedBall 0 (ℓ / 2) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Submission.BoseGases.chiScale_support_le hℓ hx
  exact closure_minimal h Metric.isClosed_closedBall

/-- The bridge state is smooth. -/
lemma winState_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ContDiff ℝ (⊤ : ENat) (winState ℓ ψ) := by
  have h1 : ContDiff ℝ (⊤ : ENat)
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (chiLam_contDiff hℓ)
  have h2 : ContDiff ℝ (⊤ : ENat)
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        (((ψ z - (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.acube ℓ, ψ x) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hψ.sub contDiff_const)
  exact h1.mul h2

/-- The bridge state has compact support. -/
lemma winState_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    HasCompactSupport (winState ℓ ψ) := by
  have hsub : tsupport (winState ℓ ψ) ⊆ tsupport (Work.BoseK15.corpusBox.chiLam ℓ) := by
    rw [tsupport, tsupport]
    refine closure_mono fun z hz => ?_
    intro hzero
    exact hz (by simp only [winState, hzero, Complex.ofReal_zero, zero_mul])
  exact (chiLam_hasCompactSupport_tauPhi hℓ).of_isClosed_subset (isClosed_tsupport _) hsub

/-- The bridge state is supported in the closed ball of radius `ℓ/2`. -/
lemma winState_tsupport_subset {ℓ : ℝ} (hℓ : 0 < ℓ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    tsupport (winState ℓ ψ) ⊆ Metric.closedBall 0 (ℓ / 2) := by
  have hsub : tsupport (winState ℓ ψ) ⊆ tsupport (Work.BoseK15.corpusBox.chiLam ℓ) := by
    rw [tsupport, tsupport]
    refine closure_mono fun z hz => ?_
    intro hzero
    exact hz (by simp only [winState, hzero, Complex.ofReal_zero, zero_mul])
  exact hsub.trans (chiLam_tsupport_subset hℓ)

/-! ## 0bis. The scale-monotonicity of the scaled profile (`c ↦ c²·tauPhi(r/c)`)

This is the one genuinely *provable* structural piece of the node's crux: it shows that the
*smaller* cutoff always carries the *larger* symbol, so `tauSmPhi` is dominated by its
`c₁ = (2sℓ)⁻¹` summand alone.  (It does **not** reduce the node's obligation to one instance of the
crux — the continuum side keeps both scales — see `FINDING_kinRow_lattice_tauPhi_session4.md`
§5a, corrected.) -/

/-- `c²·(max 0 x)² = (max 0 (c·x))²` for `c > 0`. -/
lemma sq_mul_tauH {c : ℝ} (hc : 0 < c) (x : ℝ) : c ^ 2 * tauH x = tauH (c * x) := by
  have hmax : max (0 : ℝ) (c * x) = c * max 0 x := by
    rw [mul_max_of_nonneg (a := c) 0 x hc.le, mul_zero]
  rw [tauH, tauH, hmax, mul_pow]

/-- **The scaled profile is antitone in the scale**: for `0 < c₁ ≤ c₂` and any `r`,
`c₂²·tauPhi(r/c₂) ≤ c₁²·tauPhi(r/c₁)`.

Proof: `tauPhi r = ∫t, tauH(r − 3/2 − t)·K(t)dt`, and `c²·tauH(x) = tauH(c·x)` for `c > 0`
(`sq_mul_tauH`), so `c²·tauPhi(r/c) = ∫t, tauH(r − c·(3/2+t))·K(t)dt`.  On `supp K ⊆ [−1/4,1/4]`
one has `3/2 + t ≥ 5/4 > 0`, whence `c₁ ≤ c₂` gives `r − c₂(3/2+t) ≤ r − c₁(3/2+t)` and
`tauH` is monotone; off the support both integrands vanish. -/
theorem tauPhi_scale_anti {c₁ c₂ r : ℝ} (h₁ : 0 < c₁) (h₁₂ : c₁ ≤ c₂) :
    c₂ ^ 2 * tauPhi (r / c₂) ≤ c₁ ^ 2 * tauPhi (r / c₁) := by
  have h₂ : 0 < c₂ := lt_of_lt_of_le h₁ h₁₂
  have key : ∀ c : ℝ, 0 < c →
      c ^ 2 * tauPhi (r / c) = ∫ t, tauH (r - c * (3 / 2 + t)) * tauKer t := by
    intro c hc
    rw [tauPhi_eq_integral, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have harg : c * (r / c - 3 / 2 - t) = r - c * (3 / 2 + t) := by
      field_simp
      ring
    show c ^ 2 * (tauH (r / c - 3 / 2 - t) * tauKer t)
        = tauH (r - c * (3 / 2 + t)) * tauKer t
    rw [← mul_assoc, sq_mul_tauH hc (r / c - 3 / 2 - t), harg]
  rw [key c₁ h₁, key c₂ h₂]
  refine MeasureTheory.integral_mono
    (tauKer_mul_integrable (fun t => tauH (r - c₂ * (3 / 2 + t)))
      (tauH_continuous.comp (by fun_prop)))
    (tauKer_mul_integrable (fun t => tauH (r - c₁ * (3 / 2 + t)))
      (tauH_continuous.comp (by fun_prop)))
    (fun t => ?_)
  rcases eq_or_ne (tauKer t) 0 with h0 | h0
  · rw [h0, mul_zero, mul_zero]
  · have ht : |t| < 1 / 4 := tauKer_abs_lt t h0
    have hpos : (0 : ℝ) < 3 / 2 + t := by
      have := (abs_lt.1 ht).1
      linarith
    have hle : r - c₂ * (3 / 2 + t) ≤ r - c₁ * (3 / 2 + t) := by
      have := mul_le_mul_of_nonneg_right h₁₂ hpos.le
      linarith
    exact mul_le_mul_of_nonneg_right (tauH_mono hle) (tauKer_nonneg t)

/-- `tauSmPhi` is dominated by its **smaller-cutoff** summand alone:
`tauSmPhi eT s d ℓ k ≤ ((2sℓ)⁻¹)²·tauPhi(‖k‖/(2sℓ)⁻¹)` for `0 < s`, `0 < d ≤ 1`, `0 ≤ eT`. -/
theorem tauSmPhi_le_lowScale {eT s d ℓ : ℝ} (hs : 0 < s) (hd : 0 < d) (hℓ : 0 < ℓ)
    (hd1 : d ≤ 1) (heT0 : 0 ≤ eT) (k : EuclideanSpace ℝ (Fin 3)) :
    tauSmPhi eT s d ℓ k ≤ ((2 * s * ℓ)⁻¹) ^ 2 * tauPhi (‖k‖ / ((2 * s * ℓ)⁻¹)) := by
  have hc₁ : (0 : ℝ) < (2 * s * ℓ)⁻¹ := by positivity
  have hc₂ : (0 : ℝ) < (2 * d * s * ℓ)⁻¹ := by positivity
  have ha : (0 : ℝ) < 2 * s * ℓ := by positivity
  have hb : (0 : ℝ) < 2 * d * s * ℓ := by positivity
  have hle : (2 * s * ℓ)⁻¹ ≤ (2 * d * s * ℓ)⁻¹ := by
    refine (inv_le_inv₀ ha hb).mpr ?_
    nlinarith [hs, hd, hℓ, hd1]
  have hB : ((2 * d * s * ℓ)⁻¹) ^ 2 * tauPhi (‖k‖ / ((2 * d * s * ℓ)⁻¹))
      ≤ ((2 * s * ℓ)⁻¹) ^ 2 * tauPhi (‖k‖ / ((2 * s * ℓ)⁻¹)) :=
    tauPhi_scale_anti hc₁ hle
  have hA := mul_le_mul_of_nonneg_left hB heT0
  rw [tauSmPhi]
  nlinarith [hA]

/-! ## 1. The crux: the single-scale kinetic row at `tauPhi` for the bridge state -/

/-- **The kinetic row at the explicit profile `tauPhi`** (the analytic content of the node).

For `cℓ ≥ 4π` and `ψ` smooth with `tsupport ψ ⊆ boxL ℓ`, the `Lab N`-truncated lattice sum of
`c²τ̃(‖k‖/c)` against the bridge state `winState ℓ ψ = χ_Λ(ψ − m)` is dominated by the continuum
integral of FS's sharp coefficient `[‖p‖−c]₊²`. -/
theorem winState_row {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    (N : ℕ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∑ k : Lab N, (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / c)) *
        ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2) := by
  exact le_trans
    (labN_sum_le_tsum hℓ hc N (winState_contDiff hℓ hψ) (winState_hasCompactSupport hℓ ψ))
    (tauPhi_row_closedBall hℓ hc hcℓ (winState_contDiff hℓ hψ) (winState_hasCompactSupport hℓ ψ)
      (winState_tsupport_subset hℓ ψ))

/-! ## 2. The Neumann word is nonnegative -/

/-- `0 ≤ neuWord ℓ d eT 0 ψ`: the defining trial functional of `neuFrac` is nonnegative
(completed square, `neuFrac_nonneg_l2`), and the prefactor `½eT(dℓ)⁻²` is nonnegative. -/
theorem neuWord_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) {d eT : ℝ} (hd : 0 < d) (heT : 0 ≤ eT)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    0 ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := by
  have hdℓ : (0 : ℝ) < d * ℓ := mul_pos hd hℓ
  have ha2 : (0 : ℝ) ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg hdℓ.le _
  have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ 0 ψ) :=
    hψ.continuous.sub continuous_const
  have hI : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ 0)) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • (0 : EuclideanSpace ℝ (Fin 3)))
      (2 * (|ℓ| + 1))) (hcont.pow 2).continuousOn).mono_set
        (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ 0)
  have hn := Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq (ℓ := ℓ)
    (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2 0 hI
  rw [Work.BoseKinLoc.neuWord]
  exact mul_nonneg (by positivity) hn

/-! ## 4. Wiring: the general row implies the bridge-state row -/

/-- **The crux at the bridge state, via the band-coupling route** (an alternative to
`winState_row`, which rests on `sharpShiftRow`): if the coupling inequality
`BandPlusLowGainGeHighDemand ℓ c (winState ℓ ψ)` holds, then the single-scale row at the bridge
state follows (through the proved assembly `Work.BoseBoxFock.windowedDeficitResidual_of_band` and
`tauPhi_row_lattice_of_deficit`).  So this node is implied by *either* of the two open cruxes
(`sharpShiftRow`, or `bandPlusLowGain_ge_highDemand`). -/
theorem winState_row_of_band {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    (hcℓ : 4 * Real.pi ≤ c * ℓ)
    (N : ℕ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hband : BandPlusLowGainGeHighDemand ℓ c (winState ℓ ψ)) :
    (∑ k : Lab N, (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / c)) *
        ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2) :=
  le_trans
    (labN_sum_le_tsum hℓ hc N (winState_contDiff hℓ hψ) (winState_hasCompactSupport hℓ ψ))
    (tauPhiRow_of_bandPlusLowGain hℓ hc hcℓ (winState_contDiff hℓ hψ)
      (winState_tsupport_subset hℓ ψ) hband)

/-- **The wiring**: the general closed-ball row (at the *full* lattice) implies the
bridge-state row over `Lab N` (`winState_row`), through the proved lattice truncation
`labN_sum_le_tsum` and the bridge-state facts.  So the only remaining input of this node is
`Work.BoseBoxFock.tauPhi_row_lattice` (the shared crux). -/
theorem winState_row_of_general
    (hgen : ∀ {ℓ c : ℝ}, 0 < ℓ → 0 < c → 4 * Real.pi ≤ c * ℓ →
      ∀ {g : EuclideanSpace ℝ (Fin 3) → ℂ}, ContDiff ℝ (⊤ : ENat) g → HasCompactSupport g →
        tsupport g ⊆ Metric.closedBall 0 (ℓ / 2) →
        (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
            (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ‖Submission.BoseGases.kinFT g p‖ ^ 2))
    {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ) (N : ℕ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∑ k : Lab N, (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / c)) *
        ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2) :=
  le_trans
    (labN_sum_le_tsum hℓ hc N (winState_contDiff hℓ hψ) (winState_hasCompactSupport hℓ ψ))
    (hgen hℓ hc hcℓ (winState_contDiff hℓ hψ) (winState_hasCompactSupport hℓ ψ)
      (winState_tsupport_subset hℓ ψ))

/-! ## 3. The assembly -/

/-- **The left-hand side at the bridge state**: the corpus box coefficient `∫conj(qVec)·ψ` is
`kinFT (winState ℓ ψ)` at the same momentum (`qCoeff_eq_winState`). -/
lemma kinRow_lattice_tauPhi_lhs {ℓ : ℝ} (hℓ : 0 < ℓ) {eT s d : ℝ} (N : ℕ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.tauSmPhi eT s d ℓ
        (Work.BoseBoxFock.kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖∫ z, (starRingEnd ℂ)
            (Work.BoseK15.corpusBox.qVec ℓ (Work.BoseBoxFock.kmomLab ℓ N k) z)
              * (ψ z : ℂ)‖ ^ 2))
      = ∑ k : Lab N, tauSmPhi eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ *
          ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  have hq : (∫ z, (starRingEnd ℂ)
        (Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k) z) * (ψ z : ℂ))
      = Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k) := by
    have h := qCoeff_eq_winState hℓ hψ hψsupp (labVec N k)
    simpa [qCoeff, kmomLab_eq_kmomInt] using h
  rw [hq]

/-- **The target**, assembled from the crux `winState_row` at the two scales
`c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹` and `neuWord_nonneg`. -/
theorem kinRow_lattice_tauPhi {ℓ : ℝ} (hℓ : 0 < ℓ) {eT s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hs8 : s ≤ 1 / (8 * Real.pi)) (hd1 : d ≤ 1) (N : ℕ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.tauSmPhi eT s d ℓ
        (Work.BoseBoxFock.kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖∫ z, (starRingEnd ℂ)
            (Work.BoseK15.corpusBox.qVec ℓ (Work.BoseBoxFock.kmomLab ℓ N k) z)
              * (ψ z : ℂ)‖ ^ 2))
      ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ
        + Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by
  -- `8πs ≤ 1`, used at both scales
  have h8 : 8 * Real.pi * s ≤ 1 := by
    have h8pos : (0 : ℝ) < 8 * Real.pi := by positivity
    have h := mul_le_mul_of_nonneg_left hs8 h8pos.le
    rw [mul_one_div, div_self (ne_of_gt h8pos)] at h
    exact h
  have hc1pos : (0 : ℝ) < (2 * s * ℓ)⁻¹ := by positivity
  have hc2pos : (0 : ℝ) < (2 * d * s * ℓ)⁻¹ := by positivity
  have hc1ℓ : 4 * Real.pi ≤ (2 * s * ℓ)⁻¹ * ℓ := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [h8, hℓ]
  have hc2ℓ : 4 * Real.pi ≤ (2 * d * s * ℓ)⁻¹ * ℓ := by
    have hds : d * s ≤ s := by nlinarith [hd, hs, hd1]
    have h2 : 8 * Real.pi * (d * s) ≤ 1 := by nlinarith [h8, hds, Real.pi_pos]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [h2, hℓ]
  have hrow1 := winState_row hℓ hc1pos hc1ℓ N hψ hψsupp
  have hrow2 := winState_row hℓ hc2pos hc2ℓ N hψ hψsupp
  have h1eT : (0 : ℝ) ≤ 1 - eT := by linarith
  -- the pointwise split of `tauSmPhi` into its two scales
  have hsplit : ∀ k : Lab N,
      tauSmPhi eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)
      = (1 - eT) * ((ℓ ^ 3)⁻¹ *
            (((2 * s * ℓ)⁻¹) ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / (2 * s * ℓ)⁻¹)) *
            ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)
        + eT * ((ℓ ^ 3)⁻¹ *
            (((2 * d * s * ℓ)⁻¹) ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / (2 * d * s * ℓ)⁻¹)) *
            ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2) := by
    intro k
    rw [tauSmPhi]
    ring
  have hmain := mainWord_eq_winState (ℓ := ℓ) (d := d) (s := s) (eT := eT) (ψ := ψ)
  have harg1 : (2 * (s * ℓ))⁻¹ = (2 * s * ℓ)⁻¹ := by ring
  have harg2 : (2 * (d * s * ℓ))⁻¹ = (2 * d * s * ℓ)⁻¹ := by ring
  have hneu := neuWord_nonneg hℓ hd heT0 hψ hψsupp
  -- the two-scale split of the whole sum
  have hsum : (∑ k : Lab N, tauSmPhi eT s d ℓ (kmomLab ℓ N k) *
        ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2))
      = (1 - eT) * (∑ k : Lab N, (ℓ ^ 3)⁻¹ *
            (((2 * s * ℓ)⁻¹) ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / (2 * s * ℓ)⁻¹)) *
            ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)
        + eT * (∑ k : Lab N, (ℓ ^ 3)⁻¹ *
            (((2 * d * s * ℓ)⁻¹) ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / (2 * d * s * ℓ)⁻¹)) *
            ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2) := by
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [kinRow_lattice_tauPhi_lhs hℓ N hψ hψsupp, hsum, hmain, harg1, harg2]
  have hb1 : (1 - eT) * (∑ k : Lab N, (ℓ ^ 3)⁻¹ *
        (((2 * s * ℓ)⁻¹) ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / (2 * s * ℓ)⁻¹)) *
        ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)
      ≤ (1 - eT) * (((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff ((2 * s * ℓ)⁻¹) ‖p‖ *
          ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hrow1 h1eT
  have hb2 : eT * (∑ k : Lab N, (ℓ ^ 3)⁻¹ *
        (((2 * d * s * ℓ)⁻¹) ^ 2 * tauPhi (‖kmomLab ℓ N k‖ / (2 * d * s * ℓ)⁻¹)) *
        ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)
      ≤ eT * (((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff ((2 * d * s * ℓ)⁻¹) ‖p‖ *
          ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hrow2 heT0
  linarith [hb1, hb2, hneu]

end Work.BoseBoxFock
