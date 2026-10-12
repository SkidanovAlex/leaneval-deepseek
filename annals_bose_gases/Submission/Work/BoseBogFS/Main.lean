import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.Reserve
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Main` — FS `eq:Combined1` at one datum

This module assembles the chapter into the inequality FS `eq:Combined1` needs:

  `(4π·lhyC·ρ²aℓ³√(ρa³) − C·(§11 bracket))·‖f‖² + ⟨f, dNumOpR_{RHi} f⟩`
  `≤ ⟨f, 𝒦^Bog f⟩ + (½ρ²ℓ³Ŵ₁ω(0) + ½(ρ−μ)²ℓ³ĝ(0))·‖f‖²`,

from

* `qw_KzBogFS_ge` (the finite-sum Bogoliubov step, FS `thm:BogHamDiag`) — the zero point
  and the `κ`-sum are supplied as the two scalar estimates `hZP`/`hKAP` in the shapes
  produced by `Work.BoseB6Est.fsZeroPoint_le` and `Work.BoseB6Est.kappaSum_le`;
* `hRes`: the control of the *unshifted* `Work.BoseB7.FockData.dNumOpR` by the shifted
  diagonal up to the scalar `Res` (the only place where FS's shift `c_k` of `eq:Defb_k`
  has to be traded for the corpus's unshifted `b_k`; see `README.md` §"the reserve");
* the arithmetic `hArith`, absorbing FS's §7–§11 error display into the free constant of
  the §11 bracket; the close threshold `closeThresholdFS` (`μK_ℓ⁻²/(2¹⁴π)`, `F9`) is what
  makes the `(ρ−μ)²` of the `𝒞`-sum land on the `(R/a)²√(μa³)` slot.

The main statements are `bogOpBound_at` (one chemical potential) and `bogOpBoundFS_of_at`
(the `BogOpBoundFS` shape, with the per-`μ` estimates as hypotheses).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The §11 error bracket of `BogOpBoundFS`, as the free-constant factor of the error:
`μ²aℓ³√(μa³)·(X² + (R/a)²√(μa³) + X^{1/1615})`. -/
def errBracket (v : ℝ³ → ℝ) (R μ : ℝ) : ℝ :=
  μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
    * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ)

lemma errBracket_eq (v : ℝ³ → ℝ) (R μ : ℝ) :
    errBracket v R μ = μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
      * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ) := rfl

/-- The per-mode Fock datum of one `KzDatum` satisfies FS §10's numeric side conditions:
the diagonalisation hypotheses `0 < 𝒜`, `|ℬ| ≤ 𝒜`, `0 < 𝒜+ℬ`, the evenness of `𝒜, ℬ, 𝒞`
(needed for the pair `(k,−k)`), and the commutator bound
`[a_k,a_k†] + [a_{−k},a_{−k}†] ≤ 2` (which the box kernel
`[a_k,a_k†] = χ̂²(0) − χ̂(kℓ)²` with `|χ̂²| ≤ 1`, `|χ̂| ≤ 1` gives). -/
structure BogNumeric {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) : Prop where
  hA : ∀ k, 0 < bogA E ρ k
  hB : ∀ k, |bogB E ρ k| ≤ bogA E ρ k
  hAB : ∀ k, 0 < bogA E ρ k + bogB E ρ k
  hAe : ∀ k, bogA E ρ k = bogA E ρ (-k)
  hBe : ∀ k, bogB E ρ k = bogB E ρ (-k)
  hCe : ∀ k, bogC E ρ k = bogC E ρ (-k)
  hccr : ∀ k, bogCcr2 F k ≤ 2


/-- Cauchy–Schwarz control of the *unshifted* squeezed number by the shifted one:
`‖b_k x‖² ≤ (1+σ)‖b̂_k x‖² + (1+σ⁻¹)γ_k²‖x‖²` for `σ > 0` (`b̂_k = b_k + γ_k`).  The free
`σ` is what makes the reserve's scalar cost absorbable in the §11 bracket (see
`README.md` §4, F8): `σ` has to be chosen small compared with `X²` but large compared with
the (super-polynomially small) `γ_k²` on `RHi`. -/
theorem normSq_bOp_le (F : FockData Mode) (E : Q3Env Mode) (ρ σ : ℝ) (k : Mode) (x : F.H)
    (hσ : 0 < σ) :
    F.normSq ((F.bOp (bogAlpha E ρ) k) x)
      ≤ (1 + σ) * F.normSq ((bogBShift F E ρ k) x)
        + (1 + σ⁻¹) * (bogGamma E ρ k) ^ 2 * F.normSq x := by
  have h1 : (F.bOp (bogAlpha E ρ) k) x
      = (bogBShift F E ρ k) x - (bogGamma E ρ k) • x := by
    simp only [bogBShift, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    abel
  rw [h1, FockData.normSq, FockData.normSq, FockData.normSq]
  have hexp : F.bp ((bogBShift F E ρ k) x - (bogGamma E ρ k) • x)
      ((bogBShift F E ρ k) x - (bogGamma E ρ k) • x)
      = F.bp ((bogBShift F E ρ k) x) ((bogBShift F E ρ k) x)
        - 2 * (bogGamma E ρ k) * F.bp ((bogBShift F E ρ k) x) x
        + (bogGamma E ρ k) ^ 2 * F.bp x x := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
    rw [F.bp_symm x ((bogBShift F E ρ k) x)]
    ring
  rw [hexp]
  have habs := Work.BoseB7.bp_cauchy_abs F ((bogBShift F E ρ k) x) x
  have hY := Work.BoseB7.two_mul_le_eps_inv (ε := σ) hσ
    (Real.sqrt (F.bp ((bogBShift F E ρ k) x) ((bogBShift F E ρ k) x)))
    (|bogGamma E ρ k| * Real.sqrt (F.bp x x))
  have hnn1 : 0 ≤ F.bp ((bogBShift F E ρ k) x) ((bogBShift F E ρ k) x) := F.bp_nonneg _
  have hnn2 : 0 ≤ F.bp x x := F.bp_nonneg x
  rw [Real.sq_sqrt hnn1, mul_pow, sq_abs, Real.sq_sqrt hnn2] at hY
  have h1' : Real.sqrt (F.bp ((bogBShift F E ρ k) x) ((bogBShift F E ρ k) x)) ^ 2
      = F.bp ((bogBShift F E ρ k) x) ((bogBShift F E ρ k) x) := Real.sq_sqrt hnn1
  have h2' : Real.sqrt (F.bp ((bogBShift F E ρ k) x) ((bogBShift F E ρ k) x))
      * (|bogGamma E ρ k| * Real.sqrt (F.bp x x))
      = |bogGamma E ρ k| * (Real.sqrt (F.bp ((bogBShift F E ρ k) x)
            ((bogBShift F E ρ k) x)) * Real.sqrt (F.bp x x)) := by ring
  have h2'' : |bogGamma E ρ k| * (Real.sqrt (F.bp ((bogBShift F E ρ k) x)
          ((bogBShift F E ρ k) x)) * Real.sqrt (F.bp x x))
      = Real.sqrt (F.bp ((bogBShift F E ρ k) x) ((bogBShift F E ρ k) x))
        * (|bogGamma E ρ k| * Real.sqrt (F.bp x x)) := by ring
  have h3' : |bogGamma E ρ k| * |F.bp ((bogBShift F E ρ k) x) x|
      ≤ |bogGamma E ρ k| * (Real.sqrt (F.bp ((bogBShift F E ρ k) x)
          ((bogBShift F E ρ k) x)) * Real.sqrt (F.bp x x)) :=
    mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  have h4' : -2 * (bogGamma E ρ k) * F.bp ((bogBShift F E ρ k) x) x
      ≤ 2 * (|bogGamma E ρ k| * |F.bp ((bogBShift F E ρ k) x) x|) := by
    have hab := le_abs_self (-(bogGamma E ρ k) * F.bp ((bogBShift F E ρ k) x) x)
    rw [abs_mul, abs_neg] at hab
    nlinarith [hab]
  nlinarith [hY, h1', h2', h2'', h3', h4', hnn1, hnn2]

/-- **The reserve control** (with the free Cauchy–Schwarz parameter `σ > 0`): the corpus's
`dNumOpR` (the *unshifted* `b_k`) on `RHi` is dominated by `(1+σ)𝒦^Bog` plus
`(1+σ)Σ_k½(𝒵_k+κ_k) + (1+σ⁻¹)G`, where `G` bounds `Σ_{RHi}𝒟_kγ_k²`. -/
theorem qw_dNumOpR_le (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    (ρ σ G : ℝ) (hσ : 0 < σ) (hnum : BogNumeric F E ρ)
    (hG : (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
        (bogD E ρ k) * (bogGamma E ρ k) ^ 2) ≤ G) :
    ∀ f : F.H, T.NWindow E.bigM f →
      F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
        ≤ (1 + σ) * F.qw f (KzBogFS F E ρ)
          + ((1 + σ) * (∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k)
                (bogB E ρ k) + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k)
                  (bogC E ρ k)))
              + (1 + σ⁻¹) * G) * F.normSq f := by
  intro f hf
  have hDnn : ∀ k : Mode, 0 ≤ bogD E ρ k := fun k => by
    simp only [bogD]
    exact le_of_lt (Submission.BoseGases.bogD_pos (A := bogA E ρ k) (B := bogB E ρ k)
      (hnum.hA k) (hnum.hB k))
  have hbase : F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
      = ∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
          (bogD E ρ k) * F.normSq ((F.bOp (bogAlpha E ρ) k) f) := by
    have hDl : (KzEnvAt E ρ).D = bogD E ρ := funext fun k => rfl
    have hAl : (KzEnvAt E ρ).alpha = bogAlpha E ρ := funext fun k => rfl
    simp only [Work.BoseB7.FockData.dNumOpR, Work.BoseB7.FockData.regionSum]
    rw [qw_sum_finset]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hDl, hAl, Work.BoseB7.FockData.bNumOp, FockData.qw, LinearMap.comp_apply,
      Work.BoseB7.bOpDag_bp, FockData.normSq]
  have hstep : (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
        (bogD E ρ k) * F.normSq ((F.bOp (bogAlpha E ρ) k) f))
      ≤ (1 + σ) * (∑ k : Mode, (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f))
        + (1 + σ⁻¹) * G * F.normSq f := by
    have hs1 : (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
          (bogD E ρ k) * F.normSq ((F.bOp (bogAlpha E ρ) k) f))
        ≤ ∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
            ((1 + σ) * ((bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f))
              + (1 + σ⁻¹) * ((bogD E ρ k) * (bogGamma E ρ k) ^ 2) * F.normSq f) :=
      Finset.sum_le_sum fun k _ => by
        nlinarith [mul_le_mul_of_nonneg_left (normSq_bOp_le F E ρ σ k f hσ) (hDnn k)]
    refine le_trans hs1 ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    have hsub : (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
          (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f))
        ≤ ∑ k : Mode, (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        ((Finset.filter_subset _ _).trans (Finset.subset_univ _))
        (fun k _ _ => mul_nonneg (hDnn k) (F.bp_nonneg _))
    have h1σ : 0 ≤ 1 + σ⁻¹ := by positivity
    have hnn : 0 ≤ F.normSq f := F.bp_nonneg f
    have hmul1 : (1 + σ) * (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
          (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f))
        ≤ (1 + σ) * ∑ k : Mode, (bogD E ρ k) * F.normSq ((bogBShift F E ρ k) f) :=
      mul_le_mul_of_nonneg_left hsub (by positivity)
    have hmul2 : (1 + σ⁻¹) *
          (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
            (bogD E ρ k) * (bogGamma E ρ k) ^ 2) * F.normSq f
        ≤ (1 + σ⁻¹) * G * F.normSq f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG h1σ) hnn
    linarith [hmul1, hmul2]
  have hkz := qw_KzBogFS_eq F E ρ f hnum.hA hnum.hB hnum.hAB hnum.hAe hnum.hBe hnum.hCe
  have hTle : (∑ k : Mode, (1 / 2 : ℝ) * ((bogD E ρ k) * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k
        + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)))
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
          + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (add_le_add (bogD_alpha_sq_ccr_le E ρ k F (hnum.hA k) (hnum.hB k) (hnum.hccr k)) le_rfl)
      (by norm_num)
  have hnn : 0 ≤ F.normSq f := F.bp_nonneg f
  have h1σ : 0 ≤ 1 + σ := by positivity
  have hmulT : (1 + σ) * (∑ k : Mode, (1 / 2 : ℝ) * ((bogD E ρ k) * (bogAlpha E ρ k) ^ 2
        * bogCcr2 F k + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)))
      ≤ (1 + σ) * ∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
          + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)) :=
    mul_le_mul_of_nonneg_left hTle h1σ
  rw [hbase]
  nlinarith [hstep, hkz, hmulT, hnn, hG]

/-- **`qw_dNumOpR_le` in the `hRes` shape of `bogOpBound_at`**: the reserve is `S + Res`
with `S = Σ_k ½(𝒵_k+κ_k)` and `Res = σ·Kbar + σ·S + (1+σ⁻¹)G`, where `Kbar` bounds `𝒦^Bog`
on the window. -/
theorem qw_dNumOpR_le_res (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    (ρ Kbar G σ : ℝ) (hσ : 0 < σ) (hnum : BogNumeric F E ρ)
    (hKbar : ∀ f : F.H, T.NWindow E.bigM f → F.qw f (KzBogFS F E ρ) ≤ Kbar * F.normSq f)
    (hG : (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
        (bogD E ρ k) * (bogGamma E ρ k) ^ 2) ≤ G) :
    ∀ f : F.H, T.NWindow E.bigM f →
      F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
        ≤ F.qw f (KzBogFS F E ρ)
          + ((∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
                + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)))
              + (σ * Kbar
                  + σ * (∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k)
                      (bogB E ρ k) + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k)
                        (bogC E ρ k)))
                  + (1 + σ⁻¹) * G)) * F.normSq f := by
  intro f hf
  have h := qw_dNumOpR_le F T E ρ σ G hσ hnum hG f hf
  have hK' := hKbar f hf
  nlinarith [h, hK', F.bp_nonneg f]

/-- **FS `eq:Combined1` at one chemical potential**, from the two scalar estimates, the
reserve control and the §11 arithmetic. -/
theorem bogOpBound_at (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : KzDatum) (μ ρ : ℝ)
    (hnum : BogNumeric D.F D.E ρ)
    (hmu : D.E.mu = μ) (hell : D.E.ell = ell v μ)
    (Ezero Res δ Capp : ℝ) (hδ : 0 ≤ δ)
    (hZP : (∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA D.E ρ k) (bogB D.E ρ k))
      ≤ -(4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * D.E.W1omega0 + Ezero)
    (hKAP : (∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA D.E ρ k) (bogB D.E ρ k)
        (bogC D.E ρ k))
      ≤ (ρ - μ) ^ 2 * (D.gHat0 / 2) * ell3 v μ * (1 + δ))
    (hRes : ∀ f : D.F.H, D.T.NWindow D.E.bigM f →
      D.F.qw f (D.F.dNumOpR (KzEnvAt D.E ρ) (RHi D.F (KzEnvAt D.E ρ)))
        ≤ D.F.qw f (KzBogFS D.F D.E ρ)
          + ((∑ k : D.Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA D.E ρ k) (bogB D.E ρ k)
                + Work.BoseB6.bogKappaErr (bogA D.E ρ k) (bogB D.E ρ k) (bogC D.E ρ k)))
              + Res) * D.F.normSq f)
    (hArith : Ezero + Res + (ρ - μ) ^ 2 * (D.gHat0 / 2) * ell3 v μ * δ ≤ Capp * errBracket v R μ)
    (f : D.F.H) (hf : D.T.NWindow D.E.bigM f) :
    (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3) - Capp * errBracket v R μ)
        * D.F.normSq f
      + D.F.qw f (D.F.dNumOpR (KzEnvAt D.E ρ) (RHi D.F (KzEnvAt D.E ρ)))
      ≤ D.F.qw f (KzBogFS D.F D.E ρ)
        + ((1 / 2) * ρ ^ 2 * ell3 v μ * D.E.W1omega0
            + (1 / 2) * (ρ - μ) ^ 2 * ell3 v μ * D.gHat0) * D.F.normSq f := by
  have hKz := qw_KzBogFS_ge D.F D.E ρ f hnum.hA hnum.hB hnum.hAB hnum.hAe hnum.hBe hnum.hCe
    hnum.hccr
  have hd := hRes f hf
  have hnf : 0 ≤ D.F.normSq f := D.F.bp_nonneg f
  have hsplit : (∑ k : D.Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA D.E ρ k)
        (bogB D.E ρ k) + Work.BoseB6.bogKappaErr (bogA D.E ρ k) (bogB D.E ρ k) (bogC D.E ρ k)))
      = (∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA D.E ρ k) (bogB D.E ρ k))
        + ∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA D.E ρ k) (bogB D.E ρ k)
            (bogC D.E ρ k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hKap2 : (ρ - μ) ^ 2 * (D.gHat0 / 2) * ell3 v μ * (1 + δ)
      = (ρ - μ) ^ 2 * (D.gHat0 / 2) * ell3 v μ
        + (ρ - μ) ^ 2 * (D.gHat0 / 2) * ell3 v μ * δ := by ring
  have hKz' : -((∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA D.E ρ k)
          (bogB D.E ρ k))
        + (∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA D.E ρ k) (bogB D.E ρ k)
            (bogC D.E ρ k))) * D.F.normSq f ≤ D.F.qw f (KzBogFS D.F D.E ρ) := by
    rw [hsplit] at hKz
    exact hKz
  have hd' : D.F.qw f (D.F.dNumOpR (KzEnvAt D.E ρ) (RHi D.F (KzEnvAt D.E ρ)))
      ≤ D.F.qw f (KzBogFS D.F D.E ρ)
        + ((∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA D.E ρ k) (bogB D.E ρ k))
            + (∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA D.E ρ k) (bogB D.E ρ k)
                (bogC D.E ρ k)) + Res) * D.F.normSq f := by
    rw [hsplit] at hd
    exact hd
  have hKAP' : (∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA D.E ρ k) (bogB D.E ρ k)
        (bogC D.E ρ k))
      ≤ (ρ - μ) ^ 2 * (D.gHat0 / 2) * ell3 v μ
        + (ρ - μ) ^ 2 * (D.gHat0 / 2) * ell3 v μ * δ := by
    rw [hKap2] at hKAP
    exact hKAP
  nlinarith [hKz', hd', hZP, hKAP', hArith, hnf]

/-- `BogOpBoundFS` at the corrected close threshold `closeThresholdFS` (`F9`): the design's
`BogOpBoundFS` with `CloseCond` replaced by `CloseCondFS`.  `BogOpBoundAtFS.toBogOpBoundFS`
converts it back to the design's statement as soon as `closeThreshold` *is*
`μK_ℓ⁻²/(2¹⁴π)` — which is the `F9` edit the `D-FS` node prescribes. -/
abbrev BogOpBoundAtFS (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ →
      ∀ ρ : ℝ, 0 ≤ ρ → CloseCondFS v μ ρ →
        ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
          (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
              - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
                  * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ))
              * (D μ).F.normSq f
            + (D μ).F.qw f ((D μ).F.dNumOpR (KzEnvAt (D μ).E ρ)
                (RHi (D μ).F (KzEnvAt (D μ).E ρ)))
          ≤ (D μ).F.qw f (KzBogFS (D μ).F (D μ).E ρ)
            + ((1 / 2) * ρ ^ 2 * (D μ).E.ell ^ 3 * (D μ).E.W1omega0
                + (1 / 2) * (ρ - μ) ^ 2 * (D μ).E.ell ^ 3 * (D μ).gHat0)
              * (D μ).F.normSq f

/-- The `F9` edit turns the chapter's statement into the design's `BogOpBoundFS`. -/
theorem BogOpBoundAtFS.toBogOpBoundFS {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ} {D : ℝ → KzDatum}
    (hthr : ∀ μ : ℝ, Work.BoseFixR.closeThreshold v μ = closeThresholdFS v μ)
    (hbound : BogOpBoundAtFS v h R D) : BogOpBoundFS v h R D := by
  obtain ⟨ε₀, C, hε, hC, hmain⟩ := hbound
  exact ⟨ε₀, C, hε, hC, fun μ h1 h2 ρ h3 hclose f hf =>
    hmain μ h1 h2 ρ h3 (by simpa only [CloseCond, CloseCondFS, hthr μ] using hclose) f hf⟩

/-- **`BogOpBoundAtFS` from the per-`μ` estimates.**  The design's `BogOpBoundFS` at the
corrected close threshold `closeThresholdFS` (`F9`), with the two scalar estimates
(`ZP`, `KAP`), the reserve control (`Res`) and the arithmetic (one absolute `Capp`)
carried as hypotheses.  `BogNumeric` collects exactly the rows the gate
`Work.BoseB7AK.C3Q.Q3KernelFS` supplies. -/
theorem bogOpBoundFS_of_at (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum)
    (Ezero δ : ℝ → ℝ) (Res : ℝ → ℝ → ℝ) (Capp : ℝ) (hδ : ∀ μ, 0 ≤ δ μ) (hCapp : 0 ≤ Capp)
    (hnum : ∀ μ ρ, CloseCondFS v μ ρ → BogNumeric (D μ).F (D μ).E ρ)
    (hZP : ∀ μ ρ, CloseCondFS v μ ρ → (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
        (bogA (D μ).E ρ k) (bogB (D μ).E ρ k))
      ≤ -(4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * (D μ).E.W1omega0 + Ezero μ)
    (hKAP : ∀ μ ρ, CloseCondFS v μ ρ → (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr
        (bogA (D μ).E ρ k) (bogB (D μ).E ρ k) (bogC (D μ).E ρ k))
      ≤ (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ * (1 + δ μ))
    (hRes : ∀ μ ρ, CloseCondFS v μ ρ → ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
      (D μ).F.qw f ((D μ).F.dNumOpR (KzEnvAt (D μ).E ρ) (RHi (D μ).F (KzEnvAt (D μ).E ρ)))
        ≤ (D μ).F.qw f (KzBogFS (D μ).F (D μ).E ρ)
          + ((∑ k : (D μ).Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA (D μ).E ρ k)
                (bogB (D μ).E ρ k)
                + Work.BoseB6.bogKappaErr (bogA (D μ).E ρ k) (bogB (D μ).E ρ k)
                    (bogC (D μ).E ρ k))) + Res μ ρ) * (D μ).F.normSq f)
    (hArith : ∀ μ ρ, CloseCondFS v μ ρ → Ezero μ + Res μ ρ
        + (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ * δ μ ≤ Capp * errBracket v R μ) :
    BogOpBoundAtFS v h R D := by
  refine ⟨1, Capp, one_pos, hCapp, ?_⟩
  intro μ _ hview ρ hρ hclose f hf
  have hell : (D μ).E.ell = ell v μ := hview.2.2.2.1
  have hmu : (D μ).E.mu = μ := hview.2.1
  have hmain := bogOpBound_at v h R (D μ) μ ρ (hnum μ ρ hclose) hmu hell (Ezero μ) (Res μ ρ)
    (δ μ) Capp (hδ μ) (hZP μ ρ hclose) (hKAP μ ρ hclose) (hRes μ ρ hclose)
    (hArith μ ρ hclose) f hf
  simpa only [errBracket, mul_assoc, hell, ell3] using hmain

end Work.BoseBogFS
