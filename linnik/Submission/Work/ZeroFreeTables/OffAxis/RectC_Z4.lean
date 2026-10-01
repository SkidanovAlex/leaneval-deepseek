/-
# ZeroFreeTables/OffAxis — `RectC_Z4`

The `Z4` clause at rectangle height `L` (HB §15 rows): for every row `r` of `rows15` whose
`λ₁`-interval contains `λ₁ = lamOf q ρ₁`, the three bounds of that row hold — for a pair
`(χ₁, ρ₁)` carrying the height-`L` numbering `IsRectMin L χ₁ ρ₁` (`|Im ρ₁| ≤ L` and `λ₁`
minimal over *all* non-principal zeros of height `≤ 10L`) with `1 < |Im ρ₁|`.

The assembly follows the on-axis `Submission/Work/ZeroFreeTables/Assemble.lean`
(`rows15_t8cert_route`, `rows15_t10_route`, `rows15_t9_route`, `Z4_source`) verbatim, with
`IsMin1WideAt 10 χ₁ ρ₁ ↦ IsRectMin L χ₁ ρ₁`; the rational routing tables and the
certificates are height-free and reused.  The three columns are

* `λ₀` — HB Table 8: the height-`L` P₃ engine `OffAxis/RectP3EngineH` (HB Lemma 9.1 with the
  second zero at height `≤ L`, itself the transcription of `HB94/Lam0GeEngine`) plus the
  certified rows `t8certRows` (`Table8Cert`); the row reduction is carried out here
  (`lam0Rows8_of_engine`), a height-`L` version of `HBTable8_certified_other`;
* `λ₂` — HB Table 10 at height `L` (`OffAxis/RectT10H`);
* `λ₃` — HB Table 9 at height `L` (`OffAxis/RectT9H`), the cap `6/7 - 1/1000` provided by
  `rect10_3H_cap` below, and, in the real-character case (`χ₁ ^ 2 = 1`), the strict off-axis
  bound `56/100 < λ₁` (`OffAxis/RectZ2Strict`), which makes rows `1`–`11` of `rows15`
  unreachable (they would need `λ₃ ≥ 0.865 > 6/7`, which HB's Lemma 10.3 cannot give and
  Table 9 provides only for complex `χ₁`).

The cap `rect10_3H_cap` is the selection argument of HB §6/§9 plus his §10 case analysis at
height `L`: Lemma 10.1 (no principal signed triple, `OffAxis/Rect10_3H_F1`) and Lemma 10.2 (a
principal signed triple, `rectF2H_cap`, assembled here from the height-`L` (10.6) engine
`OffAxis/Rect10_3EngineH` and the `tf72G`-free endgame `Work.OffAxis.Rect10_3EndgameClean`).

The multiplicity conjunct of `λ₀` is vacuous on `rows15`: a repeated zero forces
`λ₁ ≥ 696/1000` (`repRow_of_engine`, the height-`L` Rep9 engine `OffAxis/RectP3RepEngineH`),
while every `rows15` row has `λ₁ ≤ 6/10`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.Table8Cert
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.ZeroFreeTables.HBRepZeroC_defs
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.ZeroFreeTables.Assemble
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.OffAxis.RectT9H
import Submission.Work.ZeroFreeTables.OffAxis.RectP3EngineH
import Submission.Work.ZeroFreeTables.OffAxis.RectT10H
import Submission.Work.ZeroFreeTables.OffAxis.RectZ2Strict
import Submission.Work.ZeroFreeTables.OffAxis.RectP3RepEngineH
import Submission.Work.ZeroFreeTables.OffAxis.Rect10_3H_F1
import Submission.Work.ZeroFreeTables.OffAxis.Rect10_3EngineH
import Submission.Work.ZeroFreeTables.OffAxis.tf72Fc_ten_eight
import Submission.Work.ZeroFreeTables.OffAxis.tf72f_moment_step
import Submission.Work.ZeroFreeTables.OffAxis.L52SupplyGen
import Submission.Work.OffAxis.Rect10_3EndgameClean
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
import Submission.Work.LinnikContract2.NumZero.exists_wideMin

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables Work.LinnikContract

/-! ## The two height-`L` `P₃` engines as `Prop`s -/

/-- **HB Lemma 9.1 at rectangle height `H` with room `W`** (the statement proved in
`OffAxis/HBLemma9_1_engine_H`). -/
def RectP3EngineStmt : Prop :=
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

/-- **HB Lemma 9.1 at a repeated zero, at rectangle height `H` with room `W`.**  The room
needed is `3H + 1`: the diagonal (9.1) combination runs at the points `σ`, `σ+iγ`, `σ+2iγ`,
`σ+3iγ`, and the near sums at `σ+2iγ` and `σ+3iγ` are dropped by minimality, whose window
reaches `3γ + δ ≤ 3H + δ` (`OffAxis/HBLemma9_1_rep_engine_H` states `2H+1`, which is too
weak to drop the `σ+3iγ` window; the corrected statement is delegated as
`OffAxis/RectP3RepEngineH`). -/
def RectRepEngineStmt : Prop :=
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

/-! ## Elementary helpers -/

/-- `IsRectMin L χ₁ ρ₁` is the height-`(10L)` numbering `IsMinWideAt L (10L)`. -/
theorem isMinWideAt_of_isRectMin_z4 {q : ℕ} [NeZero q] {L : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsRectMin L χ₁ ρ₁) :
    Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
  ⟨h.1.1, h.1.2.1, h.1.2.2, fun χ u hχ hzm him => h.2 χ u ⟨hχ, hzm, him⟩⟩

/-- `λ(ρ) = (1 - Re ρ) log q ≥ 0` for a zero of non-zero multiplicity. -/
theorem lamOf_nonneg_of_zeroMult_z4 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 ≤ Work.LinnikContract.lamOf q ρ := by
  have hre : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ h
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  rw [Work.LinnikContract.lamOf]
  exact mul_nonneg (by linarith) hlog

/-- The threshold `⌈e^L⌉ + 1` makes `H ≤ Real.log q` available at `H = L`. -/
theorem le_log_of_ceil_exp_le_z4 {L : ℝ} {q : ℕ} (hq : Nat.ceil (Real.exp L) + 1 ≤ q) :
    L ≤ Real.log (q : ℝ) := by
  have h1 : Real.exp L ≤ (Nat.ceil (Real.exp L) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp L) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have h3 : Real.exp L ≤ (q : ℝ) := by linarith
  calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos L) h3

/-! ## The `λ₀` column: HB Table 8 at rectangle height `L` -/

/-- **One certified row of HB Table 8 at rectangle height `L`.**  Given the height-`L` P₃
engine, a certified row `r ∈ t8certRows` forces the second conjunct of `Lam0Bound χ₁ ρ₁ r.λ₀`
whenever `λ₁ ≤ r.λ₁` — the height-`L` version of
`Work.ZeroFreeTables.lam0_row_of_lemma9_1_of_facts`. -/
theorem lam0Row8_of_engine (h9 : RectP3EngineStmt) {L : ℝ} (hL : 1 ≤ L)
    {r0 : ℝ × ℝ × ℝ × ℝ} (hr0 : r0 ∈ Work.ZeroFreeTables.t8certRows) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      Work.LinnikContract.lamOf q ρ₁ ≤ r0.2.1 →
      Work.ZeroFreeTables.Lam0BoundOther χ₁ ρ₁ r0.2.2.1 := by
  obtain ⟨hcond, hp⟩ := Work.ZeroFreeTables.Table8Cert r0 hr0
  obtain ⟨ha, hK, hhiv, hhipos⟩ := Work.ZeroFreeTables.t8certRows_facts r0 hr0
  set ε : ℝ := -Work.ZeroFreeTables.p913 r0.2.1 r0.2.2.1 r0.2.2.2
      (Work.ZeroFreeTables.Kaff r0.2.1) / (2 * (r0.2.2.2 + r0.2.1)) with hεdef
  have hεden : 0 < 2 * (r0.2.2.2 + r0.2.1) := by linarith
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) hεden
  obtain ⟨q₀, hq₀⟩ := h9 r0.2.2.2 (Work.ZeroFreeTables.Kaff r0.2.1) ε ha hK hε
    L (10 * L) hL (by linarith)
  refine ⟨max q₀ (max (Nat.ceil (Real.exp L) + 1) 3),
    fun q hq _inst χ₁ ρ₁ hR hcx hlam ρ hZ hne hconj => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hq₀' : q₀ ≤ q := by omega
  have hLle : L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le_z4 (by omega)
  have hmin : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
    isMinWideAt_of_isRectMin_z4 hR
  have hρ0 : |ρ.im| ≤ L := by have := hZ.2.2; linarith
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    lamOf_nonneg_of_zeroMult_z4 hR.1.2.1
  have hlam0nn : 0 ≤ Work.LinnikContract.lamOf q ρ :=
    lamOf_nonneg_of_zeroMult_z4 hZ.2.1
  have hcond' : Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
      (Work.LinnikContract.lamOf q ρ) r0.2.2.2 (Work.ZeroFreeTables.Kaff r0.2.1) := by
    have ha1 : 0 < r0.2.2.2 + Work.LinnikContract.lamOf q ρ₁ := by linarith
    have ha4 : 0 < r0.2.2.2 + Work.LinnikContract.lamOf q ρ := by linarith
    have hKnn : 0 ≤ Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff r0.2.1) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have h3 : Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff r0.2.1)
          / (r0.2.2.2 + r0.2.1) ^ 3
        ≤ Work.ZeroFreeTables.Kond (Work.ZeroFreeTables.Kaff r0.2.1)
          / (r0.2.2.2 + Work.LinnikContract.lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left hKnn (pow_pos ha1 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    have h4 : 1 / (r0.2.2.2 + r0.2.2.1) ^ 3
        ≤ 1 / (r0.2.2.2 + Work.LinnikContract.lamOf q ρ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos ha4 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    unfold Work.ZeroFreeTables.cond913 at hcond ⊢
    linarith
  have hineq := hq₀ q hq₀' χ₁ ρ₁ ρ hLle hmin hcx hZ.2.1 hρ0 (Ne.symm hne) hconj hcond'
  have hineq' : 0 ≤ Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ) r0.2.2.2 (Work.ZeroFreeTables.Kaff r0.2.1)
      + (r0.2.2.2 + Work.LinnikContract.lamOf q ρ₁) * ε := hineq
  have h1 : Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ) r0.2.2.2 (Work.ZeroFreeTables.Kaff r0.2.1)
      ≤ Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁) r0.2.2.1 r0.2.2.2
        (Work.ZeroFreeTables.Kaff r0.2.1) :=
    Work.ZeroFreeTables.p913_mono_lam₀ ha (by linarith) (by linarith) (by linarith)
      (le_of_lt hlt)
  have h2 : Work.ZeroFreeTables.p913 (Work.LinnikContract.lamOf q ρ₁) r0.2.2.1 r0.2.2.2
        (Work.ZeroFreeTables.Kaff r0.2.1)
      ≤ Work.ZeroFreeTables.p913 r0.2.1 r0.2.2.1 r0.2.2.2
        (Work.ZeroFreeTables.Kaff r0.2.1) :=
    Work.ZeroFreeTables.p913_mono_lam₁ hlam1nn hlam hhiv ha hK
  have hεval : (r0.2.2.2 + r0.2.1) * ε
      = -(Work.ZeroFreeTables.p913 r0.2.1 r0.2.2.1 r0.2.2.2
          (Work.ZeroFreeTables.Kaff r0.2.1)) / 2 := by
    rw [hεdef]
    field_simp
  have h5 : (r0.2.2.2 + Work.LinnikContract.lamOf q ρ₁) * ε
      ≤ (r0.2.2.2 + r0.2.1) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', h1, h2, h5, hεval, hp]

/-- **HB Table 8 at rectangle height `L`**: the thirteen certified rows `t8certRows` give the
`λ₀`-column of `rows15`, uniformly in `q` above a threshold.  Height-`L` version of
`HBTable8_certified_other`. -/
theorem lam0Rows8_of_engine (h9 : RectP3EngineStmt) :
    ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      ∀ r ∈ Work.ZeroFreeTables.t8certRows, Work.LinnikContract.lamOf q ρ₁ ≤ r.2.1 →
        Work.ZeroFreeTables.Lam0BoundOther χ₁ ρ₁ r.2.2.1 := by
  intro L hL
  obtain ⟨N, hN⟩ := Work.ZeroFreeTables.exists_threshold_of_forall_mem
    Work.ZeroFreeTables.t8certRows
    (fun r N => ∀ q : ℕ, N ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → Work.LinnikContract.lamOf q ρ₁ ≤ r.2.1 →
      Work.ZeroFreeTables.Lam0BoundOther χ₁ ρ₁ r.2.2.1)
    (fun r hr => lam0Row8_of_engine h9 hL hr)
    (fun r hr n n' hn hn' q hq => hn' q (le_trans hn hq))
  exact ⟨N, fun q hq _ χ₁ ρ₁ hR hcx r hr hlam => hN r hr q hq χ₁ ρ₁ hR hcx hlam⟩

/-! ## The multiplicity conjunct: the height-`L` Rep9 row `(0.696, 0.696)` -/

/-- **The diagonal row `(0.696, 0.696, 0.696, 269/100)` of HB Table 8 at rectangle height
`L`.**  The height-`L` repeated-zero engine (Rep9) and the certified diagonal row give
`λ₁ ≥ 696/1000` when `ρ₁` is a multiple zero and `λ₁ ≤ 696/1000`. -/
theorem repRow_of_engine (hrep : RectRepEngineStmt) {L : ℝ} (hL : 1 ≤ L) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      Work.LinnikContract.lamOf q ρ₁ ≤ (696:ℝ)/1000 →
      (696:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨hcond, hp⟩ := Work.ZeroFreeTables.hbRZC_t8diag_cert
  have ha : (0:ℝ) < 269/100 := by norm_num
  have hKpos : 0 < Work.ZeroFreeTables.Kaff ((696:ℝ)/1000) := by
    norm_num [Work.ZeroFreeTables.Kaff]
  set ε : ℝ := -Work.ZeroFreeTables.p913 ((696:ℝ)/1000) ((696:ℝ)/1000) (269/100)
      (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) / (2 * (269/100 + (696:ℝ)/1000)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) (by norm_num)
  obtain ⟨q₀, hq₀⟩ := hrep (269/100) (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000)) ε ha hKpos hε
    L (10 * L) hL (by linarith)
  refine ⟨max q₀ (max (Nat.ceil (Real.exp L) + 1) 3),
    fun q hq _inst χ₁ ρ₁ hR hnr hmult hlam => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hq₀' : q₀ ≤ q := by omega
  have hLle : L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le_z4 (by omega)
  have hmin : Work.ZeroFreeTables.IsMinWideAt L (10 * L) χ₁ ρ₁ :=
    isMinWideAt_of_isRectMin_z4 hR
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    lamOf_nonneg_of_zeroMult_z4 hR.1.2.1
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
      = -(Work.ZeroFreeTables.p913 ((696:ℝ)/1000) ((696:ℝ)/1000) (269/100)
          (Work.ZeroFreeTables.Kaff ((696:ℝ)/1000))) / 2 := by
    rw [hεdef]
    field_simp
  have h5 : (269/100 + Work.LinnikContract.lamOf q ρ₁) * ε
      ≤ (269/100 + (696:ℝ)/1000) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', hmono, h5, hεval, hp]

/-! ## Arithmetic facts about `rows15` -/

theorem rows15_lo_ge_z4 : ∀ r ∈ Work.LinnikContract.rows15, (348:ℝ)/1000 ≤ r.1 := by
  intro r hr
  fin_cases hr <;> norm_num

theorem rows15_hi_le_z4 : ∀ r ∈ Work.LinnikContract.rows15, r.2.1 ≤ (6:ℝ)/10 := by
  intro r hr
  fin_cases hr <;> norm_num

/-- Rows of `rows15` whose `λ₁`-right-end exceeds `0.56` (i.e. rows `12` and `13`) have
`λ₃ ≤ 6/7 - 1/1000` (the cap of HB Lemma 10.3). -/
theorem rows15_lam3_of_hi_gt_z4 : ∀ r ∈ Work.LinnikContract.rows15,
    (56:ℝ)/100 < r.2.1 → r.2.2.2.2 ≤ 6/7 - 1/1000 := by
  intro r hr h
  simp only [Work.LinnikContract.rows15, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · exfalso; rw [h1] at h; norm_num at h
  · rw [h1]; norm_num
  · rw [h1]; norm_num



/-! ## The cap: HB Lemma 10.3 at rectangle height `L`

For an off-axis rectangle minimiser, `Lam3BoundH L χ₁ (6/7 - 1/1000)`.  The proof is the
*selection* argument of HB §6/§9 together with his §10 case analysis at height `L`: take the
`λ`-minimal pair `(χ₂,ρ₂)` outside `{χ₁^{±1}}` and then `(χ₃,ρ₃)` outside
`{χ₁^{±1}, χ₂^{±1}}`; if `λ₃ < 6/7 - 1/1000`, HB's Lemma 10.1 (no principal signed triple,
`Rect10_3H_F1`) or Lemma 10.2 (a principal signed triple, `rectF2H_cap`) gives the
contradiction.

The `F`-method case (HB Lemma 10.2) `rectF2H_cap` is assembled here from the height-`L`
(10.6) engine `Rect10_3EngineH`, the (`tf72G`-free) endgame of
`Work.OffAxis.Rect10_3EndgameClean`, the numerics `tf72Fc_ten_eight`, the moment step
`tf72f_moment_step` and the Burgess supply `L52SupplyGen`.
-/

/-- **A `λ`-minimal zero at height `L` outside a set of characters.**  The height-`L` version
of `exists_min_lam_avoiding`: the candidate set is the finite `zeroSetH L χ`. -/
theorem exists_min_lam_avoiding_z4 {q : ℕ} [NeZero q] (L : ℝ) (S : Set (DirichletCharacter ℂ q))
    (hne : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZAt L χ ρ ∧ χ ∉ S) :
    ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZAt L χ ρ ∧ χ ∉ S ∧
      ∀ (χ' : DirichletCharacter ℂ q) (ρ' : ℂ), IsZAt L χ' ρ' → χ' ∉ S →
        Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamOf q ρ' := by
  classical
  set cands : Finset (DirichletCharacter ℂ q × ℂ) :=
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ∉ S)).biUnion
      (fun χ => (Work.LinnikContract2.NumZero.zeroSetH L χ).image (fun ρ => (χ, ρ))) with hcands
  have hmem : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      (χ, ρ) ∈ cands ↔ χ ∉ S ∧ IsZAt L χ ρ := by
    intro χ ρ
    rw [hcands, Finset.mem_biUnion]
    constructor
    · rintro ⟨χ', hχ', hmem'⟩
      rw [Finset.mem_filter] at hχ'
      obtain ⟨-, hχ'S⟩ := hχ'
      rw [Finset.mem_image] at hmem'
      obtain ⟨ρ', hρ', heq⟩ := hmem'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨hχ'S, Work.LinnikContract2.NumZero.mem_zeroSetH.mp hρ'⟩
    · rintro ⟨hχS, hZ⟩
      refine ⟨χ, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ χ, hχS⟩
      · rw [Finset.mem_image]
        exact ⟨ρ, Work.LinnikContract2.NumZero.mem_zeroSetH.mpr hZ, rfl⟩
  have hne' : cands.Nonempty := by
    obtain ⟨χ₀, ρ₀, hZ, hS⟩ := hne
    exact ⟨(χ₀, ρ₀), (hmem χ₀ ρ₀).mpr ⟨hS, hZ⟩⟩
  obtain ⟨p, hp_mem, hp_min⟩ := Finset.exists_min_image cands
    (fun p : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q p.2) hne'
  obtain ⟨hpS, hpZ⟩ := (hmem p.1 p.2).mp hp_mem
  exact ⟨p.1, p.2, hpZ, hpS, fun χ' ρ' hZ' hS' =>
    hp_min (χ', ρ') ((hmem χ' ρ').mpr ⟨hS', hZ'⟩)⟩

/-- **HB §10, Lemma 10.2 (the `F`-method case) at rectangle height `L`.**  If one of the four
signed triple products of the three characters is principal and `λ₂ ≤ λ₃ ≤ 6/7`, then
`λ₃ ≥ 6/7 - ε`. -/
theorem rectF2H_cap : ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      IsZAt L χ₂ ρ₂ → IsZAt L χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 →
      (χ₁ * χ₂ * χ₃ = 1 ∨ χ₁ * χ₂ = χ₃ ∨ χ₁ * χ₃ = χ₂ ∨ χ₂ * χ₃ = χ₁) →
      6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  intro ε hε L hL
  by_cases hbig : (126 : ℝ) ≤ ε
  · refine ⟨1, fun q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ _hR _him _hZ2 hZ3 _ _ _ _ _ _ _ _ _ => ?_⟩
    have hnn : 0 ≤ Work.LinnikContract.lamOf q ρ₃ := lamOf_nonneg_of_zeroMult_z4 hZ3.2.1
    linarith
  push_neg at hbig
  -- HB Lemma 7.2's test function at `λ = 6/7`
  set T : Work.ZeroFreeTables.TestFn := Work.ZeroFreeTables.tf72T (6/7) (by norm_num) with hTdef
  have hT0 : T.x₀ = 7/3 := by rw [hTdef]; norm_num [Work.ZeroFreeTables.tf72T]
  have hTf : T.f = Work.ZeroFreeTables.tf72f (6/7) := rfl
  have hTFc : ∀ z : ℂ, T.Fc z = Work.ZeroFreeTables.tf72Fc (6/7) z := by
    intro z; rw [hTdef]; rfl
  have hTf0 : T.f 0 = 32/35 := by
    rw [hTf, Work.ZeroFreeTables.tf72f_at_zero (6/7) (by norm_num)]; norm_num
  have hTF0 : T.F 0 = 8/9 := by
    rw [hTdef]
    show (Work.ZeroFreeTables.tf72Fc (6/7) ((0:ℝ) : ℂ)).re = 8/9
    exact Work.ZeroFreeTables.tf72Fc_zero_re (6/7) (by norm_num)
  have hTF6 : T.F (-(6/7)) = 8/5 := by
    rw [hTdef]
    show (Work.ZeroFreeTables.tf72Fc (6/7) ((-(6/7) : ℝ) : ℂ)).re = 8/5
    exact Work.ZeroFreeTables.tf72Fc_neglam_re (6/7) (by norm_num)
  have hL75 : T.f 0 * (7/6) = 3 * T.F 0 - T.F (-(6/7)) := by
    rw [hTf0, hTF0, hTF6]; norm_num
  -- the slack
  set ε' : ℝ := ε / 100000 with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; linarith
  set s : ℝ := 8 * ε' * T.f 0 with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hse : s ≤ ε / 10000 := by rw [hsdef, hε'def, hTf0]; nlinarith [hε]
  have hs83 : s < 83/9000 := by rw [hsdef, hε'def, hTf0]; nlinarith [hbig]
  -- the two numerical hypotheses of the engine, from the `λ = 6/7` numerics
  have hnum : ∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → |μ| ≤ 4 →
      (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        - 2 * (T.Fc ((μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a μ ha0 ha6 hμ
    have h := tf72Fc_ten_eight.1 a μ ha0 ha6 hμ
    rw [hTFc, hTFc, hTf0]
    linarith
  have hnum2 : ∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → 4 ≤ |μ| →
      (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a μ ha0 ha6 hμ
    have h := tf72Fc_ten_eight.2 a μ ha0 ha6 hμ
    rw [hTFc, hTf0]
    linarith
  -- the moment step, in the integral form of `tf72f_moment_step`
  have hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + s →
        l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
    intro l hl0 hl67 hl
    have hA : T.F (-(6/7)) = ∫ t in (0:ℝ)..(7/3),
        Real.exp ((6/7:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT0 hTf]
      simp only [neg_mul, neg_neg]
    have hB : T.F (-l) = ∫ t in (0:ℝ)..(7/3),
        Real.exp (l * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT0 hTf]
      simp only [neg_mul, neg_neg]
    have hC : T.F 0 = ∫ t in (0:ℝ)..(7/3),
        Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT0 hTf]
      simp
    have hD : T.F (6/7 - l) = ∫ t in (0:ℝ)..(7/3),
        Real.exp (-((6/7 - l) * t)) * Work.ZeroFreeTables.tf72f (6/7) t :=
      Work.ZeroFreeTables.F_eq_tf72f_int T hT0 hTf (6/7 - l)
    rw [hA, hB, hC, hD] at hl
    exact tf72f_moment_step ε s hε hs0 hse l hl0 hl67 hl
  -- the engine and the endgame
  obtain ⟨δ, hδ0, hδ1, qS, hS⟩ := L52SupplyGen ε' hε'
  obtain ⟨qE, hE⟩ := Rect10_3EngineH T ε' δ hε' hδ0 hδ1
  refine ⟨max qE (max qS (Nat.ceil (Real.exp L) + 1)),
    fun q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
      hlam23 hlam3 hcase => ?_⟩
  have hqE : qE ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hqL : Nat.ceil (Real.exp L) + 1 ≤ q := by omega
  have hLlog : L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le_z4 (by omega)
  have h106 := hE q hqE L χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ (fun χ _ hχ => hS q hqS χ hχ) hL hLlog
    hR him hZ2 hZ3 h21 h2i h31 h3i h32 h3ii hlam23 hlam3 hnum hnum2
  have h01 : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := lamOf_nonneg_of_zeroMult_z4 hR.1.2.1
  have h13 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₃ :=
    hR.2 χ₃ ρ₃ (Work.ZeroFreeTables.isZAt_mono (by linarith) hZ3)
  exact Work.OffAxis.rect10_3_endgame_clean T ε' ε s
    (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₂)
    (Work.LinnikContract.lamOf q ρ₃) hε hT0 hTf hTF0 hTF6 hL75 hs0 hse
    (by rw [hsdef]) hs83 hmom
    (Work.OffAxis.tf72f_refute_quant_clean T hT0 hTf hTF0 hTF6) h106 h01 h13 hlam23 hlam3

/-- **The cap: `Lam3BoundH L χ₁ (6/7 - 1/1000)` at an off-axis rectangle minimiser.**  The
selection argument of HB §6/§9, with the two cases of his §10 (Lemmas 10.1 and 10.2). -/
theorem rect10_3H_cap : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ →
      Work.ZeroFreeTables.Lam3BoundH L χ₁ (6/7 - 1/1000) := by
  intro L hL
  have hL10 : L ≤ 10 * L := by linarith
  obtain ⟨q₁, hq₁⟩ := Rect10_3H_F1 (1/1000) (by norm_num) L hL
  obtain ⟨q₂, hq₂⟩ := rectF2H_cap (1/1000) (by norm_num) L hL
  refine ⟨max q₁ q₂, fun q hq _inst χ₁ ρ₁ hm him _h348 => ?_⟩
  have hq₁' : q₁ ≤ q := by omega
  have hq₂' : q₂ ≤ q := by omega
  have hmono : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZAt L χ u →
      Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u :=
    fun χ u hu => hm.2 χ u (Work.ZeroFreeTables.isZAt_mono hL10 hu)
  classical
  by_cases hge : (6/7 - 1/1000 : ℝ) ≤ Work.LinnikContract.lamOf q ρ₁
  · exact ⟨χ₁, fun χ ρ hZ _ _ _ _ => hge.trans (hmono χ ρ hZ)⟩
  · push_neg at hge
    by_cases hex : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZAt L χ ρ ∧
        χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹ ∧ Work.LinnikContract.lamOf q ρ < (6/7 - 1/1000 : ℝ)
    · obtain ⟨χ₂, ρ₂, hZ₂, hout₂, hmin₂⟩ :=
        exists_min_lam_avoiding_z4 L ({χ₁, χ₁⁻¹} : Set (DirichletCharacter ℂ q))
          (by obtain ⟨χa, ρa, hZa, hχa1, hχa2, -⟩ := hex
              exact ⟨χa, ρa, hZa, by simp [hχa1, hχa2]⟩)
      have hchi21 : χ₂ ≠ χ₁ := fun h => hout₂ (by simp [h])
      have hchi22 : χ₂ ≠ χ₁⁻¹ := fun h => hout₂ (by simp [h])
      have hlam2lt : Work.LinnikContract.lamOf q ρ₂ < (6/7 - 1/1000 : ℝ) := by
        obtain ⟨χa, ρa, hZa, hχa1, hχa2, hlama⟩ := hex
        exact lt_of_le_of_lt (hmin₂ χa ρa hZa (by simp [hχa1, hχa2])) hlama
      refine ⟨χ₂, fun χ₃ ρ₃ hZ₃ h31 h32 h33 h34 => ?_⟩
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨χ₃', ρ₃', hZ₃', hout₃', hmin₃⟩ :=
        exists_min_lam_avoiding_z4 L
          (({χ₁, χ₁⁻¹} : Set (DirichletCharacter ℂ q)) ∪ {χ₂, χ₂⁻¹})
          ⟨χ₃, ρ₃, hZ₃, by simp [h31, h32, h33, h34]⟩
      have hchi31 : χ₃' ≠ χ₁ := fun h => hout₃' (by simp [h])
      have hchi32 : χ₃' ≠ χ₁⁻¹ := fun h => hout₃' (by simp [h])
      have hchi33 : χ₃' ≠ χ₂ := fun h => hout₃' (by simp [h])
      have hchi34 : χ₃' ≠ χ₂⁻¹ := fun h => hout₃' (by simp [h])
      have hlam3lt : Work.LinnikContract.lamOf q ρ₃' < (6/7 - 1/1000 : ℝ) :=
        lt_of_le_of_lt (hmin₃ χ₃ ρ₃ hZ₃ (by simp [h31, h32, h33, h34])) hcon
      have hle23 : Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃' :=
        hmin₂ χ₃' ρ₃' hZ₃' (by simp [hchi31, hchi32])
      have hle67 : Work.LinnikContract.lamOf q ρ₃' ≤ 6/7 := by norm_num at hlam3lt ⊢; linarith
      have hcontr : (6/7 - 1/1000 : ℝ) ≤ Work.LinnikContract.lamOf q ρ₃' := by
        by_cases hcase : χ₁ * χ₂ * χ₃' = 1 ∨ χ₁ * χ₂ = χ₃' ∨ χ₁ * χ₃' = χ₂ ∨ χ₂ * χ₃' = χ₁
        · exact hq₂ q hq₂' χ₁ χ₂ χ₃' ρ₁ ρ₂ ρ₃' hm him hZ₂ hZ₃' hchi21 hchi22
            hchi31 hchi32 hchi33 hchi34 hle23 hle67 hcase
        · push_neg at hcase
          exact hq₁ q hq₁' χ₁ χ₂ χ₃' ρ₁ ρ₂ ρ₃' hm him hZ₂ hZ₃' hchi21 hchi22
            hchi31 hchi32 hchi33 hchi34 hle23 hle67
            hcase.1 hcase.2.1 hcase.2.2.1 hcase.2.2.2
      linarith
    · refine ⟨χ₁, fun χ ρ hZ h1 h2 _ _ => ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      exact hex ⟨χ, ρ, hZ, h1, h2, hlt⟩

/-! ## The assembly -/

/-- **`(Z4)` at rectangle height `L`**: for every row `r` of `rows15` containing `λ₁`, the
three bounds of the row hold.  The three columns are assembled from the height-`L` tables
exactly as in the on-axis `Z4_source`, with the rational routing tables `rows15_t8cert_route`,
`rows15_t10_route`, `rows15_t9_route` used verbatim. -/
theorem RectC_Z4 : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      ∀ r ∈ Work.ZeroFreeTables.rows15, r.1 ≤ Work.LinnikContract.lamOf q ρ₁ →
        Work.LinnikContract.lamOf q ρ₁ ≤ r.2.1 →
        Work.LinnikContract.Lam0Bound χ₁ ρ₁ r.2.2.1 ∧
        Work.LinnikContract.Lam2Bound χ₁ r.2.2.2.1 ∧
        Work.LinnikContract.Lam3Bound χ₁ r.2.2.2.2 := by
  intro L hL
  -- the height-`L` `P₃` engine (HB Lemma 9.1 at rectangle height `H` with room `W`)
  obtain ⟨q8, h8⟩ := lam0Rows8_of_engine RectP3EngineH L hL
  -- the height-`L` repeated-zero engine (Rep9)
  obtain ⟨qrep, hrep⟩ := repRow_of_engine RectP3RepEngineH hL
  -- HB Table 10 at rectangle height `L` (height-`L` Lemma 9.4/9.3/6.2)
  obtain ⟨q10, h10⟩ := RectT10H L hL
  obtain ⟨q9, h9⟩ := RectT9H L hL
  -- HB Lemma 10.3 at rectangle height `L` (the cap `6/7 - 1/1000`)
  obtain ⟨qcap, hcap⟩ := rect10_3H_cap L hL
  -- the strict off-axis bound for a real `χ₁` with non-real `ρ₁`
  obtain ⟨qreal, hreal⟩ := RectZ2Strict L hL
  refine ⟨max (max (max q8 qrep) (max q10 q9)) (max qcap qreal), ?_⟩
  intro q hq _inst χ₁ ρ₁ hR hIm r hr hlo hhi
  obtain ⟨⟨⟨hq8, hqrep⟩, hq10, hq9⟩, hqcap, hqreal⟩ :
      ((q8 ≤ q ∧ qrep ≤ q) ∧ q10 ≤ q ∧ q9 ≤ q) ∧ qcap ≤ q ∧ qreal ≤ q := by
    simpa only [max_le_iff] using hq
  have hcx : ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) := by
    intro h
    have h0 : ρ₁.im = 0 := h.2
    rw [h0, abs_zero] at hIm
    linarith
  have h348 : (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    le_trans (rows15_lo_ge_z4 r hr) hlo
  refine ⟨?_, ?_, ?_⟩
  · -- `λ₀`: the multiplicity conjunct is vacuous on `rows15`, the second conjunct is Table 8
    rw [Work.ZeroFreeTables.lam0Bound_iff]
    refine ⟨?_, ?_⟩
    · intro hmult
      exfalso
      have hle696 : Work.LinnikContract.lamOf q ρ₁ ≤ (696:ℝ)/1000 := by
        have := rows15_hi_le_z4 r hr
        linarith
      have h696 := hrep q hqrep χ₁ ρ₁ hR hcx hmult hle696
      have := rows15_hi_le_z4 r hr
      linarith
    · obtain ⟨p, hp, hp1, hp2⟩ := Work.ZeroFreeTables.rows15_t8cert_route r hr
      have hp' := h8 q hq8 χ₁ ρ₁ hR hcx p hp (by rw [hp1]; exact hhi)
      exact hp'.mono' hp2
  · -- `λ₂`: HB Table 10
    obtain ⟨p, hp, hp1, hp2⟩ := Work.ZeroFreeTables.rows15_t10_route r hr
    have hb := h10 q hq10 χ₁ ρ₁ hR hIm h348 p hp (le_trans hhi hp1)
    exact lam2Bound_mono (Work.ZeroFreeTables.Lam2BoundH.toIsZ hL hb) hp2
  · -- `λ₃`: Table 9 in the complex case, Lemma 10.3 otherwise; `χ₁` real is unreachable
    by_cases hsq : χ₁ ^ 2 = 1
    · have h56 := hreal q hqreal χ₁ ρ₁ hR hIm hsq
      have hhi56 : (56:ℝ)/100 < r.2.1 := lt_of_lt_of_le h56 hhi
      have hle := rows15_lam3_of_hi_gt_z4 r hr hhi56
      have hcap' := hcap q hqcap χ₁ ρ₁ hR hIm h348
      exact lam3Bound_mono (Work.ZeroFreeTables.Lam3BoundH.toIsZ hL hcap') hle
    · rcases Work.ZeroFreeTables.rows15_t9_route r hr with hcap9 | ⟨p, hp, hp1, hp2⟩
      · have hcap' := hcap q hqcap χ₁ ρ₁ hR hIm h348
        exact lam3Bound_mono (Work.ZeroFreeTables.Lam3BoundH.toIsZ hL hcap') hcap9
      · have hb := h9 q hq9 χ₁ ρ₁ hR hIm h348 hsq p hp (le_trans hhi hp1)
        exact lam3Bound_mono (Work.ZeroFreeTables.Lam3BoundH.toIsZ hL hb) hp2

end Work.ZeroFreeTables.OffAxis
