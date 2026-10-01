/-
# ZeroFreeTables/OffAxis — `RectLam0`

**The height-`L` `λ₀`-bound**: for the off-axis rectangle bookkeeping `IsRectStrip L χ₁ ρ₁`
(the HB Lemma 6.1 minimiser at height `L`), every zero `ρ` of `χ₁` of height `≤ L` other than
`ρ₁` (and `conj ρ₁` when `χ₁` is real) has `λ(ρ) ≥ 0.695`, and `λ₁ ≥ 0.695` whenever `ρ₁` is a
multiple zero.  This is HB's Table 4 / Table 8 statement run at rectangle height `L`.

## Structure

Write `λ₁ = lamOf q ρ₁`.  If `λ₁ ≥ 0.695` both conjuncts are the minimality clause of
`IsRectStrip` (`IsMinWideAt L (10L)`).  Otherwise `λ₁ < 0.695 < 2`, so the zero-free strip
upgrades the bookkeeping to `IsMinWideAt L (10L)`, and the height-`L` engines of HB §§8–9 give
the contradiction with a certified table row:

* `χ₁` or `ρ₁` complex: HB Lemma 9.1 at height `L` with the diagonal row `(0.695, 0.695)` of
  Table 8 (the engine `HBLemma9_1_engine_H`, `OffAxis/HBLemma9_1_engine_H.lean`);
* multiplicity (`2 ≤ zeroMult χ₁ ρ₁`) outside the real-real case: HB Lemma 9.1 at the repeated
  zero (`HBLemma9_1_rep_engine_H`) with the certified diagonal `(0.696, 0.696)`;
* real-real (`χ₁² = 1`, `ρ₁` real) with `|Im ρ| ≤ 1`: the on-axis HB Table 4
  (`HBTable4_proof`), whose row `(0.7, 1.724)` applies since `λ₁ < 0.695 < 0.7`;
* real-real with `|Im ρ| > 1` (hence `ρ` non-real): HB Lemma 8.3 at height `L`
  (`HBLemma8_3_engine_H`, the `P₃` engine of HB §8.2) together with the certified rows of
  Table 4 (`Table4Cert`), on the interval of `λ₁`;
* real-real multiplicity: HB Lemma 8.2's repeated-zero case (`HBRepZero_proof`).

The `q₀` produced is the maximum of the finitely many thresholds, enlarged by `⌈e^{3L}⌉ + 1` so
that the engines' hypothesis `L ≤ Real.log q` holds.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.RectDefs
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_rep_engine_H3
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma8_3_engine_H
import Submission.Work.ZeroFreeTables.Table8CertExt
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.ZeroFreeTables.HBRepZeroC_defs
import Submission.Work.ZeroFreeTables.Table4Cert
import Submission.Work.ZeroFreeTables.Table4Derive
import Submission.Work.ZeroFreeTables.HBTable4_proof
import Submission.Work.ZeroFreeTables.HBRepZero_proof

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract
open Work.ZeroFreeTables

/-! ## The height-`L` engines of HB §§8–9 as `Prop`s -/

/-- **HB Lemma 9.1 at rectangle height `H` with room `W`**, all cases except the real-real one
(the statement proved in `OffAxis/HBLemma9_1_engine_H.lean`). -/
def HB91Stmt : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ H → ρ₁ ≠ ρ₀ →
      (χ₁ ^ 2 = 1 → ρ₀ ≠ starRingEnd ℂ ρ₁) →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K ε

/-- **HB Lemma 9.1 at a repeated zero, at rectangle height `H` with room `W`**
(the statement proved in `OffAxis/HBLemma9_1_rep_engine_H.lean`). -/
def HB91RepStmt : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε

/-- **HB Lemma 8.3 at rectangle height `H` with room `W`**, real-real case, non-real second
zero (the statement proved in `OffAxis/HBLemma8_3_engine_H.lean`). -/
def HB83Stmt : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 1 / 4 ≤ K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ H → ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 →
      Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ →
      Work.ZeroFreeTables.cond86 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a →
      0 ≤ Work.ZeroFreeTables.p83 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K
        + (K + 1) ^ 2 * (a + Work.LinnikContract.lamOf q ρ₁) * ε

theorem hb91Stmt_proven : HB91Stmt := HBLemma9_1_engine_H
theorem hb91RepStmt_proven : HB91RepStmt := HBLemma9_1_rep_engine_H3
theorem hb83Stmt_proven : HB83Stmt := HBLemma8_3_engine_H

/-! ## The certified rows at height `L`

`p913`/`ineq913` and `cond913` are HB's (9.13) at `φ = 1/3` (Table 8); `p83`/`cond86` and
`cond88` are HB's (8.7)/(8.6)/(8.8) (Table 4).  The two certified rows used for the `λ₀`-bound
are the diagonal `(0.695, 0.695, 129/50)` of the extended Table 8 and the rows of
`Table4Cert`. -/

/-- The certified diagonal row of HB Table 8 at `0.695`. -/
theorem t8cert_695 :
    Work.ZeroFreeTables.cond913 ((695:ℝ)/1000) ((695:ℝ)/1000) ((129:ℝ)/50)
        (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) ∧
      Work.ZeroFreeTables.p913 ((695:ℝ)/1000) ((695:ℝ)/1000) ((129:ℝ)/50)
        (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) < 0 :=
  Work.ZeroFreeTables.Table8CertExt
    ((695:ℝ)/1000, (695:ℝ)/1000, (695:ℝ)/1000, (129:ℝ)/50)
    (by simp [Work.ZeroFreeTables.t8certRowsExt])

/-- **The second conjunct of `Lam0Bound` for the non-real-real cases, at rectangle height
`L`**: the certified row `(0.695, 0.695)` of Table 8 fed into the height-`L` HB Lemma 9.1. -/
theorem rectLam0_other_of_hb91 (h9 : HB91Stmt) {L : ℝ} (hL : 1 ≤ L) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsRectStrip L χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      Work.LinnikContract.lamOf q ρ₁ ≤ (695:ℝ)/1000 →
      ∀ ρ : ℂ, Work.ZeroFreeTables.IsZAt L χ₁ ρ → ρ ≠ ρ₁ →
        (χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) →
        (695:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨hcond, hp⟩ := t8cert_695
  have ha : (0:ℝ) < 129/50 := by norm_num
  have hKpos : 0 < Work.ZeroFreeTables.Kaff ((695:ℝ)/1000) := by
    norm_num [Work.ZeroFreeTables.Kaff]
  set ε : ℝ := - Work.ZeroFreeTables.p913 ((695:ℝ)/1000) ((695:ℝ)/1000) (129/50)
      (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) / (2 * (129/50 + (695:ℝ)/1000)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) (by norm_num)
  obtain ⟨q₀, hq₀⟩ := h9 (129/50) (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) ε ha hKpos hε
    L (10 * L) hL (by linarith)
  refine ⟨max q₀ (Nat.ceil (Real.exp (3 * L)) + 1),
    fun q hq _inst χ₁ ρ₁ hR hnr hlam1 ρ hZ hne hconj => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hq₀' : q₀ ≤ q := (le_max_left _ _).trans hq
  have h3Lle : 3 * L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le (by omega)
  have hLle : L ≤ Real.log (q : ℝ) := by linarith [hL]
  have hmin : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
    Work.ZeroFreeTables.isMinWideAt_of_isRectStrip hR (by linarith)
  have hρ0 : |ρ.im| ≤ L := hZ.2.2
  have hne' : ρ₁ ≠ ρ := fun h => hne h.symm
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    lamOf_nonneg_of_zeroMult hR.1.2.1
  have hlam0nn : 0 ≤ Work.LinnikContract.lamOf q ρ := lamOf_nonneg_of_zeroMult hZ.2.1
  have hcond' : Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
      (Work.LinnikContract.lamOf q ρ) (129/50) (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) := by
    have ha1 : 0 < 129/50 + Work.LinnikContract.lamOf q ρ₁ := by linarith
    have ha4 : 0 < 129/50 + Work.LinnikContract.lamOf q ρ := by linarith
    have hKnn : 0 ≤ Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have h3 : Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000))
          / (129/50 + (695:ℝ)/1000) ^ 3
        ≤ Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000))
          / (129/50 + Work.LinnikContract.lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left hKnn (pow_pos ha1 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    have h4 : 1 / (129/50 + (695:ℝ)/1000) ^ 3
        ≤ 1 / (129/50 + Work.LinnikContract.lamOf q ρ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos ha4 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    unfold Work.ZeroFreeTables.cond913 at hcond ⊢
    linarith
  have hineq := hq₀ q hq₀' χ₁ ρ₁ ρ hLle hmin hnr hZ.2.1 hρ0 hne' hconj hcond'
  have hineq' : 0 ≤ Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ) (129/50) (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000))
      + (129/50 + Work.LinnikContract.lamOf q ρ₁) * ε := hineq
  have h1 : Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ) (129/50) (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000))
      ≤ Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁) ((695:ℝ)/1000) (129/50)
        (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) :=
    Work.ZeroFreeTables.p913_mono_lam₀ ha (by linarith) (by linarith) (by linarith) (le_of_lt hlt)
  have h2 : Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁) ((695:ℝ)/1000) (129/50)
        (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000))
      ≤ Work.ZeroFreeTables.p913 ((695:ℝ)/1000) ((695:ℝ)/1000) (129/50)
        (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) :=
    Work.ZeroFreeTables.p913_mono_lam₁ hlam1nn hlam1 le_rfl ha hKpos
  have hεval : (129/50 + (695:ℝ)/1000) * ε
      = - Work.ZeroFreeTables.p913 ((695:ℝ)/1000) ((695:ℝ)/1000) (129/50)
          (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) / 2 := by
    rw [hεdef]
    field_simp
  have h5 : (129/50 + Work.LinnikContract.lamOf q ρ₁) * ε
      ≤ (129/50 + (695:ℝ)/1000) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', h1, h2, h5, hεval, hp]

/-- **The multiplicity conjunct outside the real-real case, at rectangle height `L`.** -/
theorem rectLam0_repRow_of_hb91rep (hrep : HB91RepStmt) {L : ℝ} (hL : 1 ≤ L) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsRectStrip L χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      Work.LinnikContract.lamOf q ρ₁ ≤ (696:ℝ)/1000 →
      (696:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨hcond, hp⟩ := Work.ZeroFreeTables.hbRZC_t8diag_cert
  have ha : (0:ℝ) < 269/100 := by norm_num
  have hKpos : 0 < Work.ZeroFreeTables.Kaff ((696:ℝ)/1000) := by
    norm_num [Work.ZeroFreeTables.Kaff]
  set ε : ℝ := - Work.ZeroFreeTables.p913 ((696:ℝ)/1000) ((696:ℝ)/1000) (269/100)
      (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) / (2 * (269/100 + (696:ℝ)/1000)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) (by norm_num)
  obtain ⟨q₀, hq₀⟩ := hrep (269/100) (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) ε ha hKpos hε
    L (10 * L) hL (by linarith)
  refine ⟨max q₀ (Nat.ceil (Real.exp (3 * L)) + 1),
    fun q hq _inst χ₁ ρ₁ hR hnr hmult hlam => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hq₀' : q₀ ≤ q := (le_max_left _ _).trans hq
  have h3Lle : 3 * L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le (by omega)
  have hLle : L ≤ Real.log (q : ℝ) := by linarith [hL]
  have hmin : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
    Work.ZeroFreeTables.isMinWideAt_of_isRectStrip hR (by linarith)
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := lamOf_nonneg_of_zeroMult hR.1.2.1
  have hcond' : Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
      (Work.LinnikContract.lamOf q ρ₁) (269/100) (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) := by
    have ha1 : 0 < 269/100 + Work.LinnikContract.lamOf q ρ₁ := by linarith
    have hKnn : 0 ≤ Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have h3 : Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000))
          / (269/100 + (696:ℝ)/1000) ^ 3
        ≤ Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000))
          / (269/100 + Work.LinnikContract.lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left hKnn (pow_pos ha1 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    have h4 : 1 / (269/100 + (696:ℝ)/1000) ^ 3
        ≤ 1 / (269/100 + Work.LinnikContract.lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos ha1 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    unfold Work.ZeroFreeTables.cond913 at hcond ⊢
    linarith
  have hineq := hq₀ q hq₀' χ₁ ρ₁ hLle hmin hnr hmult hcond'
  have hineq' : 0 ≤ Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) (269/100) (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000))
      + (269/100 + Work.LinnikContract.lamOf q ρ₁) * ε := hineq
  have hmono : Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) (269/100) (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000))
      ≤ Work.ZeroFreeTables.p913 ((696:ℝ)/1000) ((696:ℝ)/1000) (269/100)
        (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) :=
    Work.ZeroFreeTables.hbRZC_p913_diag_mono (by linarith) hlam ha hKpos.le
  have hεval : (269/100 + (696:ℝ)/1000) * ε
      = - Work.ZeroFreeTables.p913 ((696:ℝ)/1000) ((696:ℝ)/1000) (269/100)
          (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) / 2 := by
    rw [hεdef]
    field_simp
  have h5 : (269/100 + Work.LinnikContract.lamOf q ρ₁) * ε
      ≤ (269/100 + (696:ℝ)/1000) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', hmono, h5, hεval, hp]


/-! ## The real-real case: `IsMinWideAt` gives the on-axis numbering -/

/-- From the height-`L` numbering with a **real** zero `ρ₁`, the on-axis numbering
`IsMin1WideAt 10` (the hypothesis of HB Table 4 and of HB Lemma 8.2). -/
theorem isMin1WideAt_of_isMinWideAt_im_zero {q : ℕ} [NeZero q] {L : ℝ} (hL : 1 ≤ L)
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁)
    (him : ρ₁.im = 0) : Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ := by
  have h10 : (10:ℝ) ≤ 10 * L := by linarith
  have h110 : (1:ℝ) ≤ 10 * L := by linarith
  refine ⟨⟨⟨h.1, h.2.1, ?_⟩, ?_⟩, ?_⟩
  · rw [him]; norm_num
  · intro χ u hu
    exact h.2.2.2 χ u hu.1 hu.2.1 (hu.2.2.trans h110)
  · intro χ u hχ hzm himu
    exact h.2.2.2 χ u hχ hzm (himu.trans h10)

/-! ## The real-real case with a non-real second zero: Table 4 at height `L` -/

/-- **A single certified row of Table 4 at height `L`**: HB Lemma 8.3 at height `L` together
with the row's certificate gives `T4v r ≤ λ(ρ₀)` whenever `λ₁` lies in the row's interval and
`ρ₀` is a non-real zero of height `≤ L` with `λ(ρ₀) < T4v r`. -/
theorem rectLam0_row_of_hb83 (h83 : HB83Stmt) {L : ℝ} (hL : 1 ≤ L) (r : T4Row)
    (hr : r ∈ Work.ZeroFreeTables.t4certRows) (hv : (695:ℝ)/1000 ≤ T4v r) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ L → ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 →
      T4lo r ≤ Work.LinnikContract.lamOf q ρ₁ → Work.LinnikContract.lamOf q ρ₁ ≤ T4hi r →
      Work.LinnikContract.lamOf q ρ₀ < (695:ℝ)/1000 →
      False := by
  obtain ⟨ha, hK, hK4, hlo0, hlohi, hvle, hhiv, hc88, hc86, hp83⟩ :=
    Work.ZeroFreeTables.t4certRows_facts r hr
  set e : ℝ := -(Work.ZeroFreeTables.p83 (T4hi r) (T4v r) (T4a r) (T4K r))
      / (2 * (T4K r + 1) ^ 2 * (T4a r + T4hi r)) with he
  have hden : 0 < 2 * (T4K r + 1) ^ 2 * (T4a r + T4hi r) := by
    have h1 : 0 < T4a r + T4hi r := by linarith
    positivity
  have hepos : 0 < e := by
    rw [he]
    exact div_pos (by linarith) hden
  obtain ⟨q₀, hq₀⟩ := h83 (T4a r) (T4K r) e ha hK4 hepos L (10 * L) hL (by linarith)
  refine ⟨max q₀ (Nat.ceil (Real.exp (3 * L)) + 1), fun q hq _inst χ₁ ρ₁ ρ₀ hw hsq him hzm him0
    hne0 himne hlo hhi hlt => ?_⟩
  have hq₀' : q₀ ≤ q := (le_max_left _ _).trans hq
  have h3Lle : 3 * L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le (by omega)
  have hLle : L ≤ Real.log (q : ℝ) := by linarith [hL]
  have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := le_trans hlo0 hlo
  have hlamle : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
    hw.2.2.2 χ₁ ρ₀ hw.1 hzm (by
      have h10 : (10:ℝ) * L = 10 * L := rfl
      linarith [him0, hL])
  have hcon : Work.LinnikContract.lamOf q ρ₀ ≤ T4v r := by linarith
  have hcond : Work.ZeroFreeTables.cond86 (Work.LinnikContract.lamOf q ρ₁)
      (Work.LinnikContract.lamOf q ρ₀) (T4a r) :=
    Work.ZeroFreeTables.cond86_mono hc86 hhi hcon (by linarith) (by linarith)
  have hineq := hq₀ q hq₀' χ₁ ρ₁ ρ₀ hLle hw hsq him hzm him0 hne0 himne hlamle hcond
  have hmono0 : Work.ZeroFreeTables.p83 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) (T4a r) (T4K r)
      ≤ Work.ZeroFreeTables.p83 (Work.LinnikContract.lamOf q ρ₁) (T4v r) (T4a r) (T4K r) :=
    Work.ZeroFreeTables.p83_mono_lam₀ ha hK.le (by linarith) (by linarith) (by linarith) hcon
  have hc88' : Work.ZeroFreeTables.cond88 (Work.LinnikContract.lamOf q ρ₁) (T4a r) (T4K r) :=
    Work.ZeroFreeTables.cond88_mono_lam₁ hc88 hlo ha (by linarith) hK
  have hmono1 : Work.ZeroFreeTables.p83 (Work.LinnikContract.lamOf q ρ₁) (T4v r) (T4a r) (T4K r)
      ≤ Work.ZeroFreeTables.p83 (T4hi r) (T4v r) (T4a r) (T4K r) :=
    Work.ZeroFreeTables.p83_mono_lam₁ hlamnn hhi hhiv ha hK hc88'
  have heval : (T4K r + 1) ^ 2 * (T4a r + T4hi r) * e
      = -(Work.ZeroFreeTables.p83 (T4hi r) (T4v r) (T4a r) (T4K r)) / 2 := by
    rw [he]
    have h1 : (0:ℝ) < T4K r + 1 := by linarith
    have h2 : (0:ℝ) < T4a r + T4hi r := by linarith
    field_simp
  have hterm : (T4K r + 1) ^ 2 * (T4a r + Work.LinnikContract.lamOf q ρ₁) * e
      ≤ (T4K r + 1) ^ 2 * (T4a r + T4hi r) * e := by
    have h1 : 0 < (T4K r + 1) ^ 2 := by positivity
    have h2 : T4a r + Work.LinnikContract.lamOf q ρ₁ ≤ T4a r + T4hi r := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h1.le) hepos.le
  linarith [hineq, hmono0, hmono1, heval, hterm, hp83]

/-- **The real-real case of the second conjunct at height `L`**, for a **non-real** second zero:
the certified rows of Table 4 cover the interval `[0, 0.7]` of `λ₁`. -/
theorem rectLam0_realreal_row (h83 : HB83Stmt) {L : ℝ} (hL : 1 ≤ L) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ L → ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 →
      Work.LinnikContract.lamOf q ρ₁ < (695:ℝ)/1000 →
      (695:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₀ := by
  obtain ⟨q1, hq1⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨0, 26/100, 2293/1000, 41/10, 116/100⟩ : T4Row) Work.ZeroFreeTables.memT4_1 (by norm_num)
  obtain ⟨q2, hq2⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨26/100, 3/10, 2293/1000, 19/5, 22/25⟩ : T4Row) Work.ZeroFreeTables.memT4_2 (by norm_num)
  obtain ⟨q3, hq3⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨3/10, 35/100, 2195/1000, 4, 88/100⟩ : T4Row) Work.ZeroFreeTables.memT4_3 (by norm_num)
  obtain ⟨q4, hq4⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨35/100, 4/10, 2108/1000, 41/10, 88/100⟩ : T4Row) Work.ZeroFreeTables.memT4_4 (by norm_num)
  obtain ⟨q5, hq5⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨4/10, 45/100, 2030/1000, 42/10, 87/100⟩ : T4Row) Work.ZeroFreeTables.memT4_5 (by norm_num)
  obtain ⟨q6, hq6⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨45/100, 5/10, 1958/1000, 43/10, 87/100⟩ : T4Row) Work.ZeroFreeTables.memT4_6 (by norm_num)
  obtain ⟨q7, hq7⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨5/10, 55/100, 1893/1000, 44/10, 86/100⟩ : T4Row) Work.ZeroFreeTables.memT4_7 (by norm_num)
  obtain ⟨q8, hq8⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨55/100, 6/10, 1832/1000, 44/10, 86/100⟩ : T4Row) Work.ZeroFreeTables.memT4_8 (by norm_num)
  obtain ⟨q9, hq9⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨6/10, 65/100, 1776/1000, 45/10, 85/100⟩ : T4Row) Work.ZeroFreeTables.memT4_9 (by norm_num)
  obtain ⟨q10, hq10⟩ := rectLam0_row_of_hb83 h83 hL
    (⟨65/100, 7/10, 1724/1000, 45/10, 85/100⟩ : T4Row) Work.ZeroFreeTables.memT4_10 (by norm_num)
  refine ⟨({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ).sup id, ?_⟩
  intro q hq _inst χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne hlt
  have hS : ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ).sup id ≤ q := hq
  have h1' : q1 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h2' : q2 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h3' : q3 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h4' : q4 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h5' : q5 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h6' : q6 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h7' : q7 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h8' : q8 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h9' : q9 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  have h10' : q10 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q1, q2, q3, q4, q5, q6, q7, q8, q9, q10} : Finset ℕ)) (by simp)) hS
  by_contra hconl
  push_neg at hconl
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := lamOf_nonneg_of_zeroMult hw.2.1
  by_cases h1 : Work.LinnikContract.lamOf q ρ₁ ≤ 26/100
  · exact False.elim (hq1 q h1' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne hlam1nn h1 hconl)
  · rw [not_le] at h1
    by_cases h2 : Work.LinnikContract.lamOf q ρ₁ ≤ 3/10
    · exact False.elim (hq2 q h2' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) h2 hconl)
    · rw [not_le] at h2
      by_cases h3 : Work.LinnikContract.lamOf q ρ₁ ≤ 35/100
      · exact False.elim (hq3 q h3' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) h3 hconl)
      · rw [not_le] at h3
        by_cases h4 : Work.LinnikContract.lamOf q ρ₁ ≤ 4/10
        · exact False.elim (hq4 q h4' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) h4 hconl)
        · rw [not_le] at h4
          by_cases h5 : Work.LinnikContract.lamOf q ρ₁ ≤ 45/100
          · exact False.elim (hq5 q h5' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) h5 hconl)
          · rw [not_le] at h5
            by_cases h6 : Work.LinnikContract.lamOf q ρ₁ ≤ 5/10
            · exact False.elim (hq6 q h6' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) h6 hconl)
            · rw [not_le] at h6
              by_cases h7 : Work.LinnikContract.lamOf q ρ₁ ≤ 55/100
              · exact False.elim (hq7 q h7' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) h7 hconl)
              · rw [not_le] at h7
                by_cases h8 : Work.LinnikContract.lamOf q ρ₁ ≤ 6/10
                · exact False.elim (hq8 q h8' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) h8 hconl)
                · rw [not_le] at h8
                  by_cases h9 : Work.LinnikContract.lamOf q ρ₁ ≤ 65/100
                  · exact False.elim (hq9 q h9' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) h9 hconl)
                  · rw [not_le] at h9
                    exact False.elim (hq10 q h10' χ₁ ρ₁ ρ₀ hw hsq him hzm him0 hne0 himne (by linarith) (by linarith) hconl)
/-- **The real-real multiplicity conjunct at height `L`** (HB Lemma 8.2 / Table 4's entry
`(0.7, 1.724)`). -/
theorem rectLam0_realreal_mult {L : ℝ} (hL : 1 ≤ L) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      (695:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨q₀, hq₀⟩ := Work.ZeroFreeTables.HBRepZero_proof
  refine ⟨max q₀ 3, fun q hq _inst χ₁ ρ₁ hw hsq him hmult => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hmin : Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ :=
    isMin1WideAt_of_isMinWideAt_im_zero hL hw him
  have h1724 := hq₀ q ((le_max_left _ _).trans hq) χ₁ ρ₁ hmin hsq him hmult (by linarith)
  linarith

/-! ## The assembly -/

/-- **The height-`L` `λ₀`-bound**: HB's Table 4 / Table 8 statement at rectangle height `L`,
for the off-axis bookkeeping `IsRectStrip L χ₁ ρ₁`. -/
theorem RectLam0 : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), Work.ZeroFreeTables.IsRectStrip L χ₁ ρ₁ →
      Work.ZeroFreeTables.Lam0BoundH L χ₁ ρ₁ (695/1000) := by
  intro L hL
  obtain ⟨q9, hq9⟩ := rectLam0_other_of_hb91 hb91Stmt_proven hL
  obtain ⟨q9r, hq9r⟩ := rectLam0_repRow_of_hb91rep hb91RepStmt_proven hL
  obtain ⟨q83, hq83⟩ := rectLam0_realreal_row hb83Stmt_proven hL
  obtain ⟨q83m, hq83m⟩ := rectLam0_realreal_mult hL
  obtain ⟨q4, hq4⟩ := Work.ZeroFreeTables.HBTable4_proof
  obtain ⟨qrz, hqrz⟩ := Work.ZeroFreeTables.HBRepZero_proof
  refine ⟨({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ).sup id, ?_⟩
  intro q hq _inst χ₁ ρ₁ hR
  have hS : ({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ).sup id ≤ q := hq
  have hq9' : q9 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ))
    (by simp)) hS
  have hq9r' : q9r ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ))
    (by simp)) hS
  have hq83' : q83 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ))
    (by simp)) hS
  have hq83m' : q83m ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ))
    (by simp)) hS
  have hq4' : q4 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ))
    (by simp)) hS
  have hqrz' : qrz ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ))
    (by simp)) hS
  have hqceil : Nat.ceil (Real.exp (3 * L)) + 1 ≤ q := le_trans (Finset.le_sup (f := id)
    (s := ({q9, q9r, q83, q83m, q4, qrz, Nat.ceil (Real.exp (3 * L)) + 1} : Finset ℕ))
    (by simp)) hS
  have h3Lle : 3 * L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le (T := 3 * L) hqceil
  have hLle : L ≤ Real.log (q : ℝ) := by linarith [h3Lle, hL]
  refine ⟨?_, ?_⟩
  · intro hmult
    by_cases hlam : Work.LinnikContract.lamOf q ρ₁ < (695:ℝ)/1000
    · have hmin : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
        Work.ZeroFreeTables.isMinWideAt_of_isRectStrip hR (by linarith)
      by_cases hrr : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0
      · have := hq83m q hq83m' χ₁ ρ₁ hmin hrr.1 hrr.2 hmult
        linarith
      · have := hq9r q hq9r' χ₁ ρ₁ hR hrr hmult (by linarith)
        linarith
    · push_neg at hlam
      exact hlam
  · intro ρ hZ hne hconj
    by_cases hlam : Work.LinnikContract.lamOf q ρ₁ < (695:ℝ)/1000
    · have hmin : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
        Work.ZeroFreeTables.isMinWideAt_of_isRectStrip hR (by linarith)
      by_cases hrr : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0
      · by_cases him : ρ.im = 0
        · have hmin1 : Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ :=
            isMin1WideAt_of_isMinWideAt_im_zero hL hmin hrr.2
          have hZ1 : Work.LinnikContract.IsZ χ₁ ρ :=
            ⟨hZ.1, hZ.2.1, by rw [him]; norm_num⟩
          have hb := hq4 q hq4' χ₁ ρ₁ hmin1 hrr.1 hrr.2
            ((70:ℝ)/100, (1724:ℝ)/1000)
            (by norm_num [Work.ZeroFreeTables.tableR, Work.ZeroFreeTables.hbTable4]) (by linarith)
          have hb2 := (Work.ZeroFreeTables.lam0Bound_iff.mp hb).2 ρ hZ1 hne
            (fun _ => by rw [Complex.conj_eq_iff_im.mpr hrr.2]; exact hne)
          linarith
        · have := hq83 q hq83' χ₁ ρ₁ ρ hmin hrr.1 hrr.2 hZ.2.1 hZ.2.2 hne him (by linarith)
          linarith
      · exact hq9 q hq9' χ₁ ρ₁ hR hrr (by linarith) ρ hZ hne hconj
    · push_neg at hlam
      exact le_trans hlam (hR.2.1 χ₁ ρ hZ)

end Work.ZeroFreeTables.OffAxis
