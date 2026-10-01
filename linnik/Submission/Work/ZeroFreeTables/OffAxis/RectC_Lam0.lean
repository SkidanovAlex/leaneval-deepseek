import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.Table8Cert
import Submission.Work.ZeroFreeTables.Table8CertExt
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.ZeroFreeTables.HBRepZeroC_defs
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H_cplx
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_rep_engine_H3

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-! ## The two rectangle-height (`IsMinWideAt H W`) engines of HB's §9

`RectC_Lam0` is the `λ₀ ≥ 0.695` clause of `Z3` at rectangle height `L`
(`Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁`, `1 < |Im ρ₁|`).  As in the on-axis assembly
(`lam0_0695_of_props`), the two conjuncts of `Lam0Bound` come from

* the certified Table 8 row `(λ₁ ≤ 0.695 ⟹ λ₀ ≥ 0.695)` (`Table8CertExt`) fed into HB
  Lemma 9.1, and
* the multiplicity conjunct, from HB Lemma 9.1 run at the repeated zero (`Rep9`).

Both engines are run at the rectangle height: `IsMin1WideAt 10 χ₁ ρ₁` becomes
`IsMinWideAt H W χ₁ ρ₁`, and the second zero `ρ₀` is only required to satisfy
`zeroMult χ₁ ρ₀ ≠ 0` and `|Im ρ₀| ≤ H`.  These are the statements delegated as
`Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H` and
`...HBLemma9_1_rep_engine_H`; the present file does the row reductions and the assembly,
so that the only inputs are those two theorems. -/

/-- **HB Lemma 9.1 at rectangle height `H` with room `W`** (the height-parametric form of
`Work.ZeroFreeTables.HBLemma9_1`): `ρ₁` is a non-principal zero of `χ₁` with `|Im ρ₁| ≤ H`
and `λ₁` minimal over the zeros of all non-principal characters at height `≤ W`; `ρ₀ ≠ ρ₁`
is a second zero of `χ₁` of height `≤ H`; `χ₁` or `ρ₁` is complex; the side condition
`cond913` holds; then HB's inequality (9.13) holds. -/
def HBLemma9_1EngineHStmt : Prop :=
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

/-- **HB Lemma 9.1 at a repeated zero, at rectangle height `H` with room `W`** (the
height-parametric form of `Work.ZeroFreeTables.HBLemma9_1_rep`, the `Rep9` core). -/
def HBLemma9_1RepEngineHStmt : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      3 * H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε

/-- The χ₁² ≠ 1 case of the height-`H` engine (see `HBLemma9_1_engine_H_cplx`). -/
def HBLemma9_1EngineHStmtCplx : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      χ₁ ^ 2 ≠ 1 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ H → ρ₁ ≠ ρ₀ →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K ε

/-- The χ₁² = 1 case of the height-`H` engine (see `HBLemma9_1_engine_H_real`). -/
def HBLemma9_1EngineHStmtReal : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ H → ρ₁ ≠ ρ₀ →
      ρ₀ ≠ starRingEnd ℂ ρ₁ →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K ε

/-- The general height-`H` engine from its two character cases. -/
theorem HBLemma9_1EngineHStmt_of_parts (hc : HBLemma9_1EngineHStmtCplx)
    (hr : HBLemma9_1EngineHStmtReal) : HBLemma9_1EngineHStmt := by
  intro a K ε ha hK hε H W hH hHW
  obtain ⟨qc, hc'⟩ := hc a K ε ha hK hε H W hH hHW
  obtain ⟨qr, hr'⟩ := hr a K ε ha hK hε H W hH hHW
  refine ⟨max qc qr, fun q hq _inst χ₁ ρ₁ ρ₀ hlog hmin hnr hzm him hne hconj hcond => ?_⟩
  by_cases h1 : χ₁ ^ 2 = 1
  · have hγ : ρ₁.im ≠ 0 := fun h0 => hnr ⟨h1, h0⟩
    exact hr' q (by omega) χ₁ ρ₁ ρ₀ hlog hmin h1 hγ hzm him hne (hconj h1) hcond
  · exact hc' q (by omega) χ₁ ρ₁ ρ₀ hlog hmin h1 hzm him hne hcond

/-- The complex case, from the proved engine `HBLemma9_1_engine_H_cplx`. -/
theorem HBLemma9_1EngineHStmtCplx_proven : HBLemma9_1EngineHStmtCplx :=
  Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H_cplx

/-- The general engine, from the proved `HBLemma9_1_engine_H`. -/
theorem HBLemma9_1EngineHStmt_proven : HBLemma9_1EngineHStmt :=
  Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H

/-- The repeated-zero engine, from the proved `HBLemma9_1_rep_engine_H3` (which assumes the
weaker `H ≤ log q`, hence implies the shape used here, `3H ≤ log q`). -/
theorem HBLemma9_1RepEngineHStmt_proven : HBLemma9_1RepEngineHStmt := by
  intro a K ε ha hK hε H W hH hHW
  obtain ⟨q₀, hq₀⟩ :=
    Work.ZeroFreeTables.OffAxis.HBLemma9_1_rep_engine_H3 a K ε ha hK hε H W hH hHW
  exact ⟨q₀, fun q hq _inst χ₁ ρ₁ h3H hmin hnr hmult hcond =>
    hq₀ q hq χ₁ ρ₁ (by linarith) hmin hnr hmult hcond⟩

/-! ## Elementary helpers -/

/-- `IsRectMin L` is `IsMinWideAt L (10L)` (same conjunction, `IsZAt` unfolded). -/
theorem isMinWideAt_of_isRectMin_rectC {q : ℕ} [NeZero q] {L : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁) :
    Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
  ⟨h.1.1, h.1.2.1, h.1.2.2, fun χ u hχ hzm him => h.2 χ u ⟨hχ, hzm, him⟩⟩

/-- `λ(ρ) = (1 - Re ρ) log q ≥ 0` for a zero of non-zero multiplicity. -/
theorem lamOf_nonneg_of_zeroMult_rectC {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 ≤ Work.LinnikContract.lamOf q ρ := by
  have hre : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ h
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  rw [Work.LinnikContract.lamOf]
  exact mul_nonneg (by linarith) hlog

/-- The threshold `⌈e^T⌉ + 1` makes `T ≤ Real.log q` available. -/
theorem le_log_of_ceil_exp_le {T : ℝ} {q : ℕ} (hq : Nat.ceil (Real.exp T) + 1 ≤ q) :
    T ≤ Real.log (q : ℝ) := by
  have h1 : Real.exp T ≤ (Nat.ceil (Real.exp T) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp T) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have h3 : Real.exp T ≤ (q : ℝ) := by linarith
  calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos T) h3

/-! ## The row reduction: the certified row `(λ₁ ≤ 0.695 ⟹ λ₀ ≥ 0.695)` at height `L` -/

/-- **The certified row `(0.695, 0.695, 0.695, 129/50)` of HB Table 8, at rectangle height
`L`.**  Given the height-`L` engine of HB Lemma 9.1, the row forces the *second* conjunct of
`Lam0Bound χ₁ ρ₁ 0.695` whenever `λ₁ ≤ 0.695`.  This is the height-`L` version of
`Work.ZeroFreeTables.lam0_row_of_lemma9_1_of_facts`. -/
theorem rectCLam0_boundOther_of_engine (h9 : HBLemma9_1EngineHStmt) {L : ℝ} (hL : 1 ≤ L) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      Work.LinnikContract.lamOf q ρ₁ ≤ (695:ℝ)/1000 →
      Work.ZeroFreeTables.Lam0BoundOther χ₁ ρ₁ ((695:ℝ)/1000) := by
  obtain ⟨hcond, hp⟩ := Work.ZeroFreeTables.Table8CertExt
    ((695:ℝ)/1000, (695:ℝ)/1000, (695:ℝ)/1000, (129:ℝ)/50)
    (by simp [Work.ZeroFreeTables.t8certRowsExt])
  have ha : (0:ℝ) < 129/50 := by norm_num
  have hKpos : 0 < Work.ZeroFreeTables.Kaff ((695:ℝ)/1000) := by norm_num [Work.ZeroFreeTables.Kaff]
  set ε : ℝ := - Work.ZeroFreeTables.p913 ((695:ℝ)/1000) ((695:ℝ)/1000) (129/50)
      (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) / (2 * (129/50 + (695:ℝ)/1000)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) (by norm_num)
  obtain ⟨q₀, hq₀⟩ := h9 (129/50) (Work.ZeroFreeTables.Kaff ((695:ℝ)/1000)) ε ha hKpos hε
    L (10 * L) hL (by linarith)
  refine ⟨max q₀ (max (Nat.ceil (Real.exp (3 * L)) + 1) 3),
    fun q hq _inst χ₁ ρ₁ hR hnr hlam1 => ?_⟩
  intro ρ hZ hne hconj
  by_contra hlt
  push_neg at hlt
  have hq₀' : q₀ ≤ q := by omega
  have h3Lle : 3 * L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le (by omega)
  have hLle : L ≤ Real.log (q : ℝ) := by linarith [hL]
  have hmin : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
    isMinWideAt_of_isRectMin_rectC hR
  have hρ0 : |ρ.im| ≤ L := by
    have := hZ.2.2
    linarith
  have hne' : ρ₁ ≠ ρ := fun h => hne h.symm
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    lamOf_nonneg_of_zeroMult_rectC hR.1.2.1
  have hlam0nn : 0 ≤ Work.LinnikContract.lamOf q ρ := lamOf_nonneg_of_zeroMult_rectC hZ.2.1
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
    have h4 : 1 / (129/50 + (695:ℝ)/1000) ^ 3 ≤ 1 / (129/50 + Work.LinnikContract.lamOf q ρ) ^ 3 :=
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

/-! ## The multiplicity conjunct at height `L` -/

/-- **The diagonal row `(0.696, 0.696, 0.696, 269/100)` of HB Table 8, at rectangle height
`L`.**  If `ρ₁` is a zero of `χ₁` of multiplicity `≥ 2` and `λ₁ ≤ 0.696`, then
`λ₁ = 0.696`: the height-`L` repeated-zero engine (`Rep9`) and the certified diagonal row
give `ineq913 λ₁ λ₁`, hence `λ₁ ≥ 0.696`.  This is the height-`L` version of
`Work.ZeroFreeTables.hbRZC_repZero_row`. -/
theorem rectCLam0_repRow_of_engine (hrep : HBLemma9_1RepEngineHStmt) {L : ℝ} (hL : 1 ≤ L) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      Work.LinnikContract.lamOf q ρ₁ ≤ (696:ℝ)/1000 →
      (696:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨hcond, hp⟩ := Work.ZeroFreeTables.hbRZC_t8diag_cert
  have ha : (0:ℝ) < 269/100 := by norm_num
  have hKpos : 0 < Work.ZeroFreeTables.Kaff ((696:ℝ)/1000) := by norm_num [Work.ZeroFreeTables.Kaff]
  set ε : ℝ := - Work.ZeroFreeTables.p913 ((696:ℝ)/1000) ((696:ℝ)/1000) (269/100)
      (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) / (2 * (269/100 + (696:ℝ)/1000)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) (by norm_num)
  obtain ⟨q₀, hq₀⟩ := hrep (269/100) (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) ε ha hKpos hε
    L (10 * L) hL (by linarith)
  refine ⟨max q₀ (max (Nat.ceil (Real.exp (3 * L)) + 1) 3),
    fun q hq _inst χ₁ ρ₁ hR hnr hmult hlam => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hq₀' : q₀ ≤ q := by omega
  have h3Lle : 3 * L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le (by omega)
  have hLle : L ≤ Real.log (q : ℝ) := by linarith [hL]
  have hmin : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
    isMinWideAt_of_isRectMin_rectC hR
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    lamOf_nonneg_of_zeroMult_rectC hR.1.2.1
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
  have hineq := hq₀ q hq₀' χ₁ ρ₁ h3Lle hmin hnr hmult hcond'
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

/-! ## The assembly -/

/-- **`RectC_Lam0` from the two height-`L` engines.**  `Lam0Bound χ₁ ρ₁ 0.695` at a
rectangle-height-`L` minimiser with `1 < |Im ρ₁|`: the multiplicity conjunct is the repeated
zero engine (`rectCLam0_repRow_of_engine`), and the second conjunct is either minimality
(`λ₁ ≥ 0.695`) or the certified Table 8 row (`rectCLam0_boundOther_of_engine`). -/
theorem rectCLam0_of_engines (h9 : HBLemma9_1EngineHStmt) (hrep : HBLemma9_1RepEngineHStmt) :
    ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
        Work.LinnikContract.Lam0Bound χ₁ ρ₁ 0.695 := by
  have h695 : (0.695:ℝ) = (695:ℝ)/1000 := by norm_num
  rw [h695]
  intro L hL
  obtain ⟨qA, hA⟩ := rectCLam0_boundOther_of_engine h9 hL
  obtain ⟨qB, hB⟩ := rectCLam0_repRow_of_engine hrep hL
  refine ⟨max (max qA qB) (max (Nat.ceil (Real.exp (3 * L)) + 1) 3), ?_⟩
  intro q hq _inst χ₁ ρ₁ hR hoff
  have hqA : qA ≤ q := by omega
  have hqB : qB ≤ q := by omega
  have hoff0 : ρ₁.im ≠ 0 := by
    intro h0
    rw [h0] at hoff
    norm_num at hoff
  have hnr : ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) := fun h => hoff0 h.2
  refine ⟨?_, ?_⟩
  · intro hmult
    by_cases hle : Work.LinnikContract.lamOf q ρ₁ ≤ (696:ℝ)/1000
    · exact le_trans (by norm_num) (hB q hqB χ₁ ρ₁ hR hnr hmult hle)
    · push_neg at hle
      linarith
  · intro ρ hZ hne hconj
    by_cases h : (695:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ
    · exact h
    · push_neg at h
      have hle1 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ :=
        hR.2 χ₁ ρ ⟨hZ.1, hZ.2.1, hZ.2.2.trans (by linarith)⟩
      have hlam1 : Work.LinnikContract.lamOf q ρ₁ ≤ (695:ℝ)/1000 := by linarith
      exact absurd (hA q hqA χ₁ ρ₁ hR hnr hlam1 ρ hZ hne hconj) (not_le.mpr h)

-- The `λ₀ ≥ 0.695` clause of `Z3` at rectangle height L.  Recipe: HB Table 8 (= Lemma 9.1,
-- the P₃ engine) in the complex case and Table 4 (Lemmas 8.2/8.3) + `HBRepZeroC` (the Rep9
-- core) in the real case, run at rectangle height L.  The height-free rational certificates
-- (`Table8CertPrinted`, `Table8CertExtPrinted`) are reused verbatim; the row reduction is
-- `Work.ZeroFreeTables.lam0_row_of_lemma9_1_of_facts` (Table8Derive.lean), whose only engine
-- input `HBLemma9_1` is replaced by a height-L version: `IsMin1WideAt 10 χ₁ ρ₁` ↦
-- `IsRectMin L χ₁ ρ₁`, and `IsZ χ₁ ρ₀` (|Im ρ₀| ≤ 1) ↦ `zeroMult χ₁ ρ₀ ≠ 0 ∧ |ρ₀.im| ≤ 2L`.
-- The transcription template is `HB94/Lam0GeEngine.lean` (`HBLemma9_1Wide_proof`) together
-- with `HB94/Lam0GeOfEngine.lean`.
theorem RectC_Lam0 : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      Work.LinnikContract.Lam0Bound χ₁ ρ₁ 0.695 :=
  rectCLam0_of_engines HBLemma9_1EngineHStmt_proven HBLemma9_1RepEngineHStmt_proven

end Work.ZeroFreeTables.OffAxis
