import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.moment_two_kinFT
import Submission.Work.BoseBoxFock.sharpShiftRow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sTailRow` — the reduced form `(S′)` of `sharpShiftRow`

## The statement

For `ℓ > 0`, `c > 0` with `4π ≤ cℓ`, and `g` smooth with `tsupport g ⊆ closedBall 0 (ℓ/2)`:

    (S′)  (2π)⁻³ ∫_p [‖p‖−c]₊²·‖ĉ(p)‖²  ≥  Σ_n (ℓ³)⁻¹·[‖k_n‖−5c/4]₊²·‖ĉ(k_n)‖²

(`ĉ = kinFT g`, `k_n = kmomInt ℓ n = (2π/ℓ)n`; the lattice sum runs over the **infinitely many**
shells with `‖k_n‖ ≥ 5c/4`.)

## Why this is the right node (read `FINDING_sharpShiftRow.md`)

* `(S′)` is *equivalent* to `sharpShiftRow` at its worst threshold `λ = 5c/4` — the equivalence
  uses only the two **proved** moment identities `latMass_closedBall` (`S0 = R0`) and
  `moment2LatticeComplex` (`S2 = R2`) together with
  `(r−c)² − (λ−c)(2r−λ−c) = (r−λ)²` for `r ≥ λ` and `S1 = R1 − D` (the deficit identity
  `aliasImageIdentity`).  So `(S′)` + `shiftRowLHS_antitone` gives the target for every
  `λ ≥ 5c/4`, hence for `λ ∈ [5c/4, 7c/4]`.
* **This is the form with slack.**  In the naive "majorant + hole" decomposition the two sides
  agree to `0.04 %` of the term scale at the extremiser; in the `(S′)` shape (equivalently
  `(S)`: `(2π)⁻³∫_{r≥c}(r−c)²ν + Σ_{r_n≥λ}ℓ⁻³(λ−c)(2r_n−λ−c)ν_n ≥ Σ_{r_n≥λ}ℓ⁻³(r_n−c)²ν_n`)
  the *relative* slack is `8 % – 76 %` on every state tested, so estimates with a few percent of
  error can close it.
* **The tail side is the safe side.**  Both sides of `(S′)` are sums/integrals over *infinitely*
  many momenta.  This matters: the aliasing lets `ĉ` be forced to vanish on any *finite* set of
  lattice points (the characters are independent), which refutes every sub-statement whose
  lattice side is finitely supported — that killed the two "hole/content domination" candidates
  of the first session (both reviewers).  `(S′)` is immune: no admissible `g ≠ 0` can make its
  lattice side vanish, since `kinFT g` is a nonzero entire function and the mass identity
  `Σ_n ℓ⁻³‖ĉ(k_n)‖² = ∫‖ĉ‖²` holds.  Concretely: over the subspace `kinFT g (k_n) = 0` for the
  six shells with `‖k_n‖ < λ` the `sharpShiftRow`-maximiser is `−137` (vs `−0.026` for the whole
  space), i.e. the "hidden" states are the *safest*.
* Two shortcuts are FALSE and must not be re-filed (see the finding §4, §4bis):
  `(S′)` with the continuum cut at `λ` instead of `c` (`(S″)`), and the "hole domination at `c`"
  (`(♡)`); both fail by `1 % – 3 %` on explicit smooth states.

## Status

`(S′)` is **not proved here** — it is the identified sharp Nyquist sampling inequality.  The
elementary comparison lemmas below (the truncation `[r−λ]₊² ≤ r²`, and the domination of the
`(S′)` lattice tail by the *global* second lattice moment `S2 = R2`) are proved; they are the
parts of the reduction that need no sampling input.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- The `(S′)` left-hand side: the continuum content with the truncated weight `[‖p‖−c]₊²`. -/
noncomputable def sTailCont (c : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The `(S′)` right-hand side: the lattice tail content beyond `λ`. -/
noncomputable def sTailLat (ℓ lam : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff lam ‖kmomInt ℓ n‖ *
    ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `[r−λ]₊² ≤ r²` for `λ ≥ 0`: the truncated weight is dominated by the quadratic one. -/
lemma fsKinCoeff_le_sq {lam r : ℝ} (hlam : 0 ≤ lam) :
    Submission.BoseGases.fsKinCoeff lam r ≤ r ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff]
  have h1 : max (r - lam) 0 ≤ |r| :=
    max_le (by linarith [le_abs_self r, hlam]) (abs_nonneg r)
  have h2 : (max (r - lam) 0) ^ 2 ≤ |r| ^ 2 := pow_le_pow_left₀ (le_max_right _ _) h1 2
  rwa [sq_abs] at h2

/-- **(S′) — the reduced form of `sharpShiftRow` at its worst threshold `λ = 5c/4`.**
See the module docstring: this is *equivalent* to the target (via the two proved moment
identities), and it is the form that carries `8 % – 76 %` of relative slack while both of its
sides run over infinitely many momenta (so the "`ĉ`-vanishes-on-a-finite-set" mechanism cannot
empty it). -/
theorem sTailRow {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    sTailLat ℓ (5 * c / 4) g ≤ sTailCont c g := by
  sorry

/-- **Elementary half of the reduction.**  The `(S′)` lattice tail is dominated by the *global*
second lattice moment `S2 = Σ_n ℓ⁻³‖k_n‖²‖ĉ(k_n)‖²`; by the proved identity
`moment2LatticeComplex` (the complex second-moment identity, for ball-supported states) the
latter equals `(2π)⁻³∫‖p‖²‖ĉ(p)‖²dp`.  So the `(S′)` left-hand side is a *tail-restricted*
version of the global second moment, and the whole content of `(S′)` is that the restriction to
the tail from `c`, combined with the shift `λ = 5c/4`, is enough. -/
theorem sTailLat_le_latticeSecondMoment {ℓ lam : ℝ} (hℓ : 0 < ℓ) (hlam : 0 ≤ lam)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    sTailLat ℓ lam g ≤
      ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
  have hsum : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (2:ℕ) *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) :=
    summable_lattice_kinFT_weight hℓ hg hgc 2
  have hpt : ∀ n : Fin 3 → ℤ,
      (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff lam ‖kmomInt ℓ n‖ *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        ≤ (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (2:ℕ) *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
    intro n
    have h1 : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
    have hb := fsKinCoeff_le_sq hlam (r := ‖kmomInt ℓ n‖)
    calc (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff lam ‖kmomInt ℓ n‖ *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        ≤ (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb h2) h1
      _ = (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (2:ℕ) *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by push_cast; ring
  have hsum' : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ *
      Submission.BoseGases.fsKinCoeff lam ‖kmomInt ℓ n‖ *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
    · have h1 : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
      have h2 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
      exact mul_nonneg (mul_nonneg h2 (Submission.BoseGases.fsKinCoeff_nonneg lam _)) h1
    · exact hpt n
  simpa only [sTailLat] using Summable.tsum_le_tsum hpt hsum' hsum

end Work.BoseBoxFock
