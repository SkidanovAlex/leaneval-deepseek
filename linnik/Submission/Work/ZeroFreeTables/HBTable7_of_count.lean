/-
# ZeroFreeTables — HBTable7_of_count

The **assembly of Heath-Brown's Table 7 from two inputs**: a near-line zero *count* and the
`λ₀`-bounds for the character `χ₁`.

`Work.ZeroFreeTables.HBTable7` (HB (1992), Table 7, p. 47) says: for a *real* character `χ₁` with
real zero `ρ₁` (`IsMin1WideAt 10`, `χ₁² = 1`, `ρ₁.im = 0`, `λ₁ < 0.696`), every zero `ρ` of a
character `χ ∉ {χ₁, χ₁⁻¹}` in the working region `IsZ χ ρ` satisfies `λ(ρ) ≥ p.2` for every row
`p ∈ tableR hbTable7` with `λ₁ ≤ p.1`.

## The two inputs

* `OtherLamCountBounded`: the bad zeros with `λ ≤ Λ ≤ 3` in the strip `|Im| ≤ H ≤ 10 log q` are
  bounded by a constant, uniformly in `q` and `H` (and in the excluded character `χ₁`).  This is
  the counting content of HB's Lemma 6.1, hence of Jutila's log-free family zero-density estimate;
  the reduction from the project's node `Work.LinnikAreas.FamilyZeroDensityJutila` is
  `OtherLamCountBounded_of_jutila` (delegated).
* `Lam0Table7`: the `λ₀`-rows of Table 7 for `χ₁` itself, i.e. every *other* zero `u` of `χ₁` with
  `|Im u| ≤ 2` satisfies `λ(u) ≥ p.2` for every row `p` with `λ₁ ≤ p.1`.  This is HB's Tables 2,
  3 and 4; in this workspace it is `Work.ZeroFreeTables.lam0_table7_wide` (whose *assembly* is in
  place; the interface is stated here to keep the dependency optional).

## The argument (HB §6 + §8)

Let `ρ` be a bad zero with `λ(ρ) < p.2 ≤ 3`, and `λ₁ ≤ p.1`.

1. **The second number.**  `second_pair_wide` (with the count) produces `(χ₂,ρ₂)` with
   `χ₂ ∉ {1, χ₁, χ₁⁻¹}`, `zeroMult χ₂ ρ₂ ≠ 0`, `λ₂ ≤ λ(ρ)`, `2|γ₂| + 1 ≤ 10 log q`, `λ₂` minimal
   over the strip `|Im| ≤ 2|γ₂| + 1` among all bad pairs:

   `∀ ψ ∉ {1,χ₁,χ₁⁻¹}, ∀ u, zeroMult ψ u ≠ 0 → |u.im| ≤ 2|γ₂|+1 → λ₂ ≤ λ(u)`.

   This is HB's §6 numbering at stage 2, with the count replacing Lemma 6.1's far-range input;
   the self-consistency `2|γ₂| + 1 ≤ 10 log q` is exactly the condition under which the engine's
   window hypotheses are covered by the minimality.
2. **Case split on `χ₂`.**
   * *Case A* (`χ₂² ≠ 1`, `χ₁χ₂² ≠ 1`): HB's **third method** (Lemma 8.7): the four window
     characters `χ₂, χ₁χ₂, χ₂², χ₁χ₂²` are `∉ {1,χ₁,χ₁⁻¹}`, so all four window hypotheses of
     `RowBodyA` follow from the minimality; the certificate is `CertRow p.1 p.2 kA lamA εA`.
   * *Case B* (`χ₂² = 1` or `χ₁χ₂² = 1`): then `χ₂⁴ = 1` (since `χ₁² = 1`) and HB's **first
     method** (Lemma 8.5, five-term, `ψ ≤ 3/8`) applies: `RowBodyB`, certificate
     `CertRow85 p.1 p.2 lamB εB`.
3. **The `χ₁`-window.**  The engine's last hypothesis is about the zeros of `χ₁` itself
   (`|Im u| ≤ 1`): they are `ρ₁` or have `u.re ≤ ρ₂.re`; this is `Lam0Table7` together with
   `λ₂ ≤ λ(ρ) < p.2`.
4. **The `δ`-conditions.**  `|1 - ρᵢ.re| ≤ δ` for the *fixed* `δ` of the `L52Hyp` supply is
   `λᵢ ≤ δ log q` (available since `λ₁ < 0.696`, `λ₂ ≤ 3`, `q` large), and
   `|1 - ρ₂.re| ≤ √(log log q)/log q` likewise.
5. **The side conditions** `hzero₁`, `hzero₂` (the `zeroMult` → `L`-bridge) and the two divisor
   conditions follow from `zeroMult χᵢ ρᵢ ≠ 0` and the strip containing them.

The per-row data (`k, ε, δ` of the two certificates, the `L52Hyp` supplies at `1/6`/`1/8` and the
two engine thresholds) is packaged in `RowData`; `HBTable7_rowData` (delegated) produces it for
each row of `tableR hbTable7`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.HBTable7_defs
import Submission.Work.ZeroFreeTables.HBTable7_defs2
import Submission.Work.ZeroFreeTables.HBTable7_defs85
import Submission.Work.ZeroFreeTables.second_pair_wide
import Submission.Work.ZeroFreeTables.maximalityAt
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine
import Submission.Work.LinnikAreas.LFunction_eq_zero_of_zeroMult
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000

namespace Work.ZeroFreeTables

/-! ## 1. The two inputs -/

/-- **The single *analytic* input of Table 7**: the bad zeros with `λ ≤ Λ ≤ 3` in the strip
`|Im| ≤ H ≤ 10 log q` are bounded by a constant, uniformly in `q`, `H` and the excluded
character `χ₁`.

Jutila's log-free family zero-density estimate (`Work.LinnikAreas.FamilyZeroDensityJutila`) gives
`Σ_{χ ≠ 1} N(1 - Λ/log q, H, χ) ≪ (qH)^{(2+ε)Λ/log q} ≤ C` for `Λ ≤ 3`, `H ≤ 10 log q`
(`OtherLamCountBounded_of_jutila`). -/
def OtherLamCountBounded : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ),
    Λ ≤ 3 → H ≤ 10 * Real.log (q : ℝ) → Work.ZeroFreeTables.otherLamCount χ₁ Λ H ≤ C

/-- **The `λ₀`-rows of Table 7 for `χ₁`**: every zero `u ≠ ρ₁` of `χ₁` with `|Im u| ≤ 2` lies at
`λ(u) ≥ p.2` for every row `p` of Table 7 with `λ₁ ≤ p.1`.

This is `Work.ZeroFreeTables.lam0_table7_wide` (HB's Tables 2, 3, 4 for `χ₁`); it is stated here
as an interface so that the assembly does not depend on that module's proof chain. -/
def Lam0Table7 : Prop :=
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ * χ₁ = 1 → ρ₁.im = 0 →
    ∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable7,
      Work.LinnikContract.lamOf q ρ₁ ≤ p.1 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₁ →
        p.2 ≤ Work.LinnikContract.lamOf q u

/-! ## 2. The row bodies (the interfaces of the two row cores) -/

/-- **The body of the third-method row core** (HB Lemma 8.7; `row_contra_general_weak` with the
unused hypothesis `|ρ₂.im| ≤ 1` deleted): the hypotheses of `lemma8_7_region` at a pair
`(χ₁,ρ₁)`, `(χ₂,ρ₂)`, together with the two row bounds `λ₁ ≤ b`, `λ₂ ≤ c`, imply `False`. -/
def RowBodyA (q : ℕ) (b c k lam ε δ : ℝ) : Prop :=
  ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ) (χ₂ : DirichletCharacter ℂ q)
    [NeZero χ₁.conductor] [NeZero χ₂.conductor],
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ * χ₁ = 1 → ρ₁.im = 0 →
    χ₂ ≠ 1 → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ * χ₂ ≠ 1 → χ₁ * (χ₂ * χ₂) ≠ 1 →
    Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 →
    Work.LinnikContract.lamOf q ρ₁ ≤ b →
    Work.LinnikContract.lamOf q ρ₂ ≤ c → 2 * |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) →
    (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
    DirichletCharacter.LFunction χ₁ ((ρ₁.re : ℂ)) = 0 →
    DirichletCharacter.LFunction χ₂ (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = 0 →
    |1 - ρ₁.re| ≤ δ → |1 - ρ₂.re| ≤ δ →
    |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₂.im| + 2))) (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0 →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₂.im| + 2))) ((ρ₁.re : ℂ)) ≠ 0 →
    (∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
      |u.im| ≤ 1 → u = ((ρ₁.re : ℂ)) ∨ u.re ≤ ρ₂.re) →
    False

/-- **The body of the five-term row core** (HB Lemma 8.5; `row_contra_degenerate_weak` with the
unused hypothesis `|ρ₂.im| ≤ 1` deleted). -/
def RowBodyB (q : ℕ) (b c lam ε δ : ℝ) : Prop :=
  ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ) (χ₂ : DirichletCharacter ℂ q)
    [NeZero χ₁.conductor] [NeZero χ₂.conductor],
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ * χ₁ = 1 → ρ₁.im = 0 →
    χ₂ ≠ 1 → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 4 = 1 →
    Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 →
    Work.LinnikContract.lamOf q ρ₁ ≤ b →
    Work.LinnikContract.lamOf q ρ₂ ≤ c → |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) →
    (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
    DirichletCharacter.LFunction χ₁ ((ρ₁.re : ℂ)) = 0 →
    DirichletCharacter.LFunction χ₂ (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = 0 →
    |1 - ρ₁.re| ≤ δ → |1 - ρ₂.re| ≤ δ →
    |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
    |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₂.im| + 2))) ((ρ₁.re : ℂ)) ≠ 0 →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₂.im| + 2))) (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0 →
    (∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
      |u.im| ≤ 1 → u = ((ρ₁.re : ℂ)) ∨ u.re ≤ ρ₂.re) →
    False

/-! ## 3. The per-row data -/

/-- **The data attached to one row `(b,c)` of Table 7**: the two certificates (third method and
five-term), the window radius and slack of the two `L52Hyp` supplies, the thresholds of those
supplies and of the two row cores, and the supplies themselves. -/
structure RowData (b c : ℝ) where
  /-- the parameter `k` of the third-method certificate -/
  k : ℝ
  /-- the test-function parameter of the third-method certificate -/
  lamA : ℝ
  /-- the slack of the third-method certificate -/
  εA : ℝ
  /-- the window radius of the `L52Hyp` supply of the third method -/
  δA : ℝ
  /-- the test-function parameter of the five-term certificate -/
  lamB : ℝ
  /-- the slack of the five-term certificate -/
  εB : ℝ
  /-- the window radius of the `L52Hyp` supply of the five-term route -/
  δB : ℝ
  hεA : 0 < εA
  hδA0 : 0 < δA
  hδA1 : δA < 1
  /-- the strict failure of HB (8.11) at the row -/
  hcertA : Work.ZeroFreeTables.CertRow b c k lamA εA
  hεB : 0 < εB
  hδB0 : 0 < δB
  hδB1 : δB < 1
  /-- the strict failure of HB Lemma 8.5 at the row -/
  hcertB : Work.ZeroFreeTables.CertRow85 b c lamB εB
  /-- the threshold of the two `L52Hyp` supplies -/
  Qsup : ℕ
  hL6 : ∀ q : ℕ, Qsup ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
    χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/6) εA δA
  hL8A : ∀ q : ℕ, Qsup ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
    χ ≠ 1 → χ ^ 2 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/8) εA δA
  hL8B : ∀ q : ℕ, Qsup ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
    χ ≠ 1 → χ ^ 4 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/8) εB δB
  /-- the threshold of the third-method row core -/
  QEA : ℕ
  hcoreA : ∀ q : ℕ, QEA ≤ q → RowBodyA q b c k lamA εA δA
  /-- the threshold of the five-term row core -/
  QEB : ℕ
  hcoreB : ∀ q : ℕ, QEB ≤ q → RowBodyB q b c lamB εB δB

/-- The row `p` of Table 7 is *served* at the level `q`: its data exists, all thresholds are met,
and the arithmetic conditions the assembly needs at `q` hold (`δ`-conditions of the engine and the
region condition `λ₂ · log q ≤ √(log log q)`). -/
def RowOK (q : ℕ) (p : ℝ × ℝ) : Prop :=
  ∃ D : RowData p.1 p.2, D.Qsup ≤ q ∧ D.QEA ≤ q ∧ D.QEB ≤ q ∧
    696 / 1000 ≤ D.δA * Real.log (q : ℝ) ∧
    3 ≤ D.δA * Real.log (q : ℝ) ∧
    3 ≤ D.δB * Real.log (q : ℝ) ∧
    3 ≤ Real.sqrt (Real.log (Real.log (q : ℝ)))

/-! ## 4. Elementary helpers -/

/-- For `δ > 0` and any `c`: `c ≤ δ log q` for all large `q`. -/
theorem exists_log_mul_ge (c δ : ℝ) (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → c ≤ δ * Real.log (q : ℝ) := by
  refine ⟨⌈Real.exp (max c 0 / δ)⌉₊ + 2, ?_⟩
  intro q hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    have h' : (1 : ℕ) < q := by
      have h2 : (2 : ℕ) ≤ ⌈Real.exp (max c 0 / δ)⌉₊ + 2 := Nat.le_add_left 2 _
      omega
    exact_mod_cast h'
  have hexp : Real.exp (max c 0 / δ) ≤ (q : ℝ) := by
    have h1 : Real.exp (max c 0 / δ) ≤ (⌈Real.exp (max c 0 / δ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp (max c 0 / δ)⌉₊ : ℝ) ≤ ((⌈Real.exp (max c 0 / δ)⌉₊ + 2 : ℕ) : ℝ) := by
      push_cast; linarith only []
    have h3 : ((⌈Real.exp (max c 0 / δ)⌉₊ + 2 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith only [h1, h2, h3]
  have hlog : max c 0 / δ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp (max c 0 / δ)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have h1 : c ≤ δ * (max c 0 / δ) := by
    rw [mul_div_cancel₀ _ hδ.ne']
    exact le_max_left _ _
  have h2 : δ * (max c 0 / δ) ≤ δ * Real.log (q : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hδ.le
  linarith only [h1, h2]

/-- For any `c`: `c ≤ √(log log q)` for all large `q`. -/
theorem exists_sqrt_loglog_ge (c : ℝ) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → c ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
  refine ⟨⌈Real.exp (Real.exp (max c 0 ^ 2))⌉₊ + 2, ?_⟩
  intro q hq
  have h1 : Real.exp (Real.exp (max c 0 ^ 2)) ≤ (q : ℝ) := by
    have ha : Real.exp (Real.exp (max c 0 ^ 2)) ≤ (⌈Real.exp (Real.exp (max c 0 ^ 2))⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hb : (⌈Real.exp (Real.exp (max c 0 ^ 2))⌉₊ : ℝ)
        ≤ ((⌈Real.exp (Real.exp (max c 0 ^ 2))⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith only []
    have hc : ((⌈Real.exp (Real.exp (max c 0 ^ 2))⌉₊ + 2 : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq
    linarith only [ha, hb, hc]
  have h2 : Real.exp (max c 0 ^ 2) ≤ Real.log (q : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have h3 : max c 0 ^ 2 ≤ Real.log (Real.log (q : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at this
  have h4 : max c 0 ≤ Real.sqrt (max c 0 ^ 2) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have h5 : Real.sqrt (max c 0 ^ 2) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) :=
    Real.sqrt_le_sqrt h3
  have h6 : c ≤ max c 0 := le_max_left _ _
  linarith only [h4, h5, h6]

/-- **Uniform threshold over a finite list**: if every element of `l` has a threshold, then one
threshold serves all of them (monotone in the threshold). -/
theorem exists_uniform_of_forall {α : Type*} (l : List α) (P : α → ℕ → Prop)
    (h : ∀ a ∈ l, ∃ Q, P a Q)
    (hmono : ∀ a Q Q', Q ≤ Q' → P a Q → P a Q') : ∃ Q, ∀ a ∈ l, P a Q := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
    have ha : ∃ Q, P a Q := h a (by simp)
    have ht : ∀ b ∈ t, ∃ Q, P b Q := fun b hb => h b (by simp [hb])
    obtain ⟨Qa, hQa⟩ := ha
    obtain ⟨Qt, hQt⟩ := ih ht
    refine ⟨max Qa Qt, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hbt
    · exact hmono b Qa (max Qa Qt) (le_max_left _ _) hQa
    · exact hmono b Qt (max Qa Qt) (le_max_right _ _) (hQt b hbt)

/-- Every row of `tableR hbTable7` has `p.2 ≤ 3` (the largest entry is `2.76`). -/
theorem tableR_hbTable7_snd_le_three {p : ℝ × ℝ} (hp : p ∈ tableR hbTable7) : p.2 ≤ 3 := by
  simp only [tableR, hbTable7, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num

/-- Every row of `tableR hbTable7` has `0 < p.2`. -/
theorem tableR_hbTable7_snd_pos {p : ℝ × ℝ} (hp : p ∈ tableR hbTable7) : 0 < p.2 := by
  simp only [tableR, hbTable7, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num

/-- Every row of `tableR hbTable7` has `p.1 ≤ 745/1000`. -/
theorem tableR_hbTable7_fst_le {p : ℝ × ℝ} (hp : p ∈ tableR hbTable7) : p.1 ≤ 745 / 1000 := by
  simp only [tableR, hbTable7, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num

/-- The complex form of the `zeroMult` → `L`-function bridge
(`Work.LinnikAreas.LFunction_eq_zero_of_zeroMult` is the real-`β` case). -/
theorem LFunction_eq_zero_of_zeroMult_complex {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {u : ℂ} (hre0 : 0 < u.re) (hre1 : u.re < 1)
    (hzm : Work.LinnikContract.zeroMult χ u ≠ 0) :
    DirichletCharacter.LFunction χ u = 0 := by
  have hχc : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχc' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter u = 0 :=
    Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero χ hχ hzm
  have hprod : (∏ p ∈ q.primeFactors,
      (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hpos : (0 : ℝ) < p := by linarith only [hre0, hre1, hp1]
    have hnorm : ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)‖ < 1 := by
      have h1 : ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-u.re) := by
        have := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-u)
        simpa using this
      calc ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)‖
          ≤ ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-u)‖ := norm_mul_le _ _
        _ ≤ 1 * ((p : ℝ) ^ (-u.re)) := by
              rw [h1]
              exact mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (by positivity)
        _ < 1 := by
              rw [one_mul, Real.rpow_neg hpos.le]
              exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp1 hre0)
    intro h
    have ha : χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u) = 1 :=
      (sub_eq_zero.mp h).symm
    rw [ha, norm_one] at hnorm
    exact absurd hnorm (lt_irrefl 1)
  have hcl := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level χ.primitiveCharacter (s := u) (Or.inl hχc')
  rw [changeLevel_primitiveCharacter] at hcl
  rw [hcl, hL, zero_mul]



theorem HBTable7_of_count (hcount : OtherLamCountBounded) (hlam0 : Lam0Table7)
    (hrowdata : ∀ p ∈ tableR hbTable7, ∃ D : RowData p.1 p.2, True) :
    Work.ZeroFreeTables.HBTable7 := by
  obtain ⟨C, hCpos, QC, hQC⟩ := hcount
  obtain ⟨Qsp, hsp⟩ := second_pair_wide ⟨C, hCpos, QC, hQC⟩
  obtain ⟨QL, hL0⟩ := hlam0
  -- the per-row data and its arithmetic threshold
  have hper : ∀ p ∈ tableR hbTable7, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → RowOK q p := by
    intro p hp
    obtain ⟨D, -⟩ := hrowdata p hp
    obtain ⟨Q₁, hQ₁⟩ := exists_log_mul_ge (696 / 1000) D.δA D.hδA0
    obtain ⟨Q₂, hQ₂⟩ := exists_log_mul_ge 3 D.δA D.hδA0
    obtain ⟨Q₃, hQ₃⟩ := exists_log_mul_ge 3 D.δB D.hδB0
    obtain ⟨Q₄, hQ₄⟩ := exists_sqrt_loglog_ge 3
    refine ⟨D.Qsup + D.QEA + D.QEB + Q₁ + Q₂ + Q₃ + Q₄, fun q hq => ?_⟩
    exact ⟨D, by omega, by omega, by omega, hQ₁ q (by omega), hQ₂ q (by omega),
      hQ₃ q (by omega), hQ₄ q (by omega)⟩
  obtain ⟨QW, hQW⟩ := exists_uniform_of_forall (tableR hbTable7)
    (fun p Q => ∀ q : ℕ, Q ≤ q → RowOK q p) hper
    (fun p Q Q' hle h q hq => h q (le_trans hle hq))
  refine ⟨max (max (max Qsp QW) QL) 100, ?_⟩
  intro q hq hqne χ₁ ρ₁ hmin hsq him hlam1 p hp hlep
  intro χ ρ hZ hχne hχneInv
  have hsq' : χ₁ * χ₁ = 1 := by rw [← pow_two]; exact hsq
  by_contra hcon
  rw [not_le] at hcon
  have hqsp : Qsp ≤ q := by omega
  have hqW : QW ≤ q := by omega
  have hqL : QL ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hp2le3 : p.2 ≤ 3 := tableR_hbTable7_snd_le_three hp
  have hχne1 : χ ≠ 1 := hZ.1
  have hzmρ : Work.LinnikContract.zeroMult χ ρ ≠ 0 := hZ.2.1
  have hlamρ3 : Work.LinnikContract.lamOf q ρ ≤ 3 := le_of_lt (lt_of_lt_of_le hcon hp2le3)
  have hchi1strip := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hmin.1.1.1 hmin.1.1.2.1
  -- the second pair (HB's §6 numbering at stage 2)
  obtain ⟨χ₂, ρ₂, hchi2ne1, hchi2chi1, hchi2inv, hzm2, hlam2rho, hgamma2, hball⟩ :=
    hsp q hqsp χ₁ ρ₁ χ ρ 3 hmin hsq him hlam1 hZ hχne hχneInv (by linarith only [hcon, hp2le3]) (by norm_num)
  have hlam2c : Work.LinnikContract.lamOf q ρ₂ ≤ p.2 := le_trans hlam2rho (le_of_lt hcon)
  have hlam2le3 : Work.LinnikContract.lamOf q ρ₂ ≤ 3 := le_trans hlam2c hp2le3
  have hchi2strip := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hchi2ne1 hzm2
  -- the row data
  obtain ⟨D, hQsup, hQEA, hQEB, harith1, harith2, harith3, harith4⟩ := hQW p hp q hqW
  haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  -- the point `ρ₂` as a complex number (for the divisor statements)
  have hptrho2 : (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = ρ₂ := by
    refine Complex.ext ?_ ?_ <;> simp
  have hptrho1 : ((ρ₁.re : ℂ)) = ρ₁ := by
    refine Complex.ext ?_ ?_ <;> simp [him]
  -- the `χ₁`-window
  have hmaxE : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
      |u.im| ≤ 1 → u = ((ρ₁.re : ℂ)) ∨ u.re ≤ ρ₂.re := by
    intro u hu himu
    by_cases huρ : u = (ρ₁.re : ℂ)
    · exact Or.inl huρ
    refine Or.inr ?_
    by_cases h0 : u.re ≤ 0
    · linarith only [hchi2strip.1, hchi2strip, h0]
    push_neg at h0
    by_cases h1 : u.re < 1
    · have hzm : Work.LinnikContract.zeroMult χ₁ u ≠ 0 :=
        zeroMult_ne_zero_of_LFunction_zero χ₁ hmin.1.1.1 hu h0 h1
      have hle := hL0 q hqL χ₁ ρ₁ hmin hsq' him p hp hlep u hzm himu
        (by rw [← hptrho1]; exact huρ)
      exact re_le_of_lamOf_le hlogq (le_trans hlam2c hle)
    · push_neg at h1
      exact absurd hu (LFunction_ne_zero_of_one_le_re' χ₁ hmin.1.1.1 h1)
  -- the zero bridges
  have hzero₁ : DirichletCharacter.LFunction χ₁ ((ρ₁.re : ℂ)) = 0 := by
    have hzm1 : Work.LinnikContract.zeroMult χ₁ ((ρ₁.re : ℂ)) ≠ 0 := by
      rw [hptrho1]; exact hmin.1.1.2.1
    exact Work.LinnikAreas.LFunction_eq_zero_of_zeroMult χ₁ hmin.1.1.1 hchi1strip.1
      hchi1strip.2.1 hzm1
  have hzero₂ : DirichletCharacter.LFunction χ₂
      (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = 0 := by
    rw [hptrho2]
    exact LFunction_eq_zero_of_zeroMult_complex χ₂ hchi2ne1 hchi2strip.1 hchi2strip.2.1 hzm2
  -- the divisor conditions
  have hdivB : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction
      (χ₂).primitiveCharacter) (Metric.closedBall 0 (|ρ₂.im| + 2)))
      (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0 := by
    have hzm2' : Work.LinnikContract.zeroMult χ₂
        (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0 := by rw [hptrho2]; exact hzm2
    refine divisor_ne_zero_of_zeroMult χ₂ hchi2ne1 ?_ hzm2'
    rw [Metric.mem_closedBall, dist_zero_right, hptrho2]
    have h2 : ‖ρ₂‖ ^ 2 = ρ₂.re ^ 2 + ρ₂.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h3 : |ρ₂.re| ≤ 1 := by rw [abs_of_pos hchi2strip.1]; linarith only [hchi2strip.2.1, hchi2strip]
    have h9 : ρ₂.re ^ 2 + ρ₂.im ^ 2 ≤ (|ρ₂.im| + 2) ^ 2 := by
      have h10 : ρ₂.re ^ 2 ≤ 1 := by nlinarith only [h3, abs_nonneg ρ₂.re, sq_abs ρ₂.re, hchi2strip, hchi1strip]
      have h12 : (|ρ₂.im| + 2) ^ 2 = |ρ₂.im| ^ 2 + (4 * |ρ₂.im| + 4) := by ring
      rw [h12, sq_abs ρ₂.im]
      linarith only [h10, abs_nonneg ρ₂.im, hchi1strip]
    have h8 : ‖ρ₂‖ ≤ |ρ₂.im| + 2 := by
      rw [← Real.sqrt_sq (norm_nonneg ρ₂), ← Real.sqrt_sq (show (0:ℝ) ≤ |ρ₂.im| + 2 by positivity)]
      apply Real.sqrt_le_sqrt
      rw [h2]
      exact h9
    exact h8
  have hdivE : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction
      (χ₁).primitiveCharacter) (Metric.closedBall 0 (|ρ₂.im| + 2))) ((ρ₁.re : ℂ)) ≠ 0 := by
    have hzm1' : Work.LinnikContract.zeroMult χ₁ ((ρ₁.re : ℂ)) ≠ 0 := by
      rw [hptrho1]; exact hmin.1.1.2.1
    refine divisor_ne_zero_of_zeroMult χ₁ hmin.1.1.1 ?_ hzm1'
    rw [Metric.mem_closedBall, dist_zero_right, hptrho1]
    have h2 : ‖ρ₁‖ ^ 2 = ρ₁.re ^ 2 + ρ₁.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h3 : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hchi1strip.1]; linarith only [hchi1strip.2.1, hchi1strip]
    have h9 : ρ₁.re ^ 2 + ρ₁.im ^ 2 ≤ (|ρ₂.im| + 2) ^ 2 := by
      have h10 : ρ₁.re ^ 2 ≤ 1 := by nlinarith only [h3, abs_nonneg ρ₁.re, sq_abs ρ₁.re, hchi1strip]
      have h10' : ρ₁.im ^ 2 ≤ 1 := by
        nlinarith only [hmin.1.1.2.2, abs_nonneg ρ₁.im, sq_abs ρ₁.im, hchi1strip, him]
      have h12 : (|ρ₂.im| + 2) ^ 2 = |ρ₂.im| ^ 2 + (4 * |ρ₂.im| + 4) := by ring
      rw [h12, sq_abs ρ₂.im]
      nlinarith only [h10, h10', abs_nonneg ρ₂.im, hchi1strip]
    have h8 : ‖ρ₁‖ ≤ |ρ₂.im| + 2 := by
      rw [← Real.sqrt_sq (norm_nonneg ρ₁), ← Real.sqrt_sq (show (0:ℝ) ≤ |ρ₂.im| + 2 by positivity)]
      apply Real.sqrt_le_sqrt
      rw [h2]
      exact h9
    exact h8
  -- the `δ`-conditions
  have hδA₁ : |1 - ρ₁.re| ≤ D.δA := by
    have h : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [abs_of_nonneg (by linarith only [hchi1strip.2.1, hchi1strip] : (0:ℝ) ≤ 1 - ρ₁.re), h]
    rw [div_le_iff₀ hlogq]
    linarith only [harith1, hlam1, hchi1strip, harith2]
  have hδA₂ : |1 - ρ₂.re| ≤ D.δA := by
    have h : 1 - ρ₂.re = Work.LinnikContract.lamOf q ρ₂ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [abs_of_nonneg (by linarith only [hchi2strip.2.1, hchi2strip] : (0:ℝ) ≤ 1 - ρ₂.re), h]
    rw [div_le_iff₀ hlogq]
    linarith only [harith2, hlam2le3, hcon, hp2le3, hlam2rho]
  have hδB₁ : |1 - ρ₁.re| ≤ D.δB := by
    have h : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [abs_of_nonneg (by linarith only [hchi1strip.2.1, hchi1strip] : (0:ℝ) ≤ 1 - ρ₁.re), h]
    rw [div_le_iff₀ hlogq]
    linarith only [harith3, hlam1, hchi1strip]
  have hδB₂ : |1 - ρ₂.re| ≤ D.δB := by
    have h : 1 - ρ₂.re = Work.LinnikContract.lamOf q ρ₂ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [abs_of_nonneg (by linarith only [hchi2strip.2.1, hchi2strip] : (0:ℝ) ≤ 1 - ρ₂.re), h]
    rw [div_le_iff₀ hlogq]
    linarith only [harith3, hlam2le3, hcon, hp2le3, hlam2rho]
  have hβreg : |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h : 1 - ρ₂.re = Work.LinnikContract.lamOf q ρ₂ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [abs_of_nonneg (by linarith only [hchi2strip.2.1, hchi2strip] : (0:ℝ) ≤ 1 - ρ₂.re), h]
    rw [div_le_div_iff_of_pos_right hlogq]
    exact le_trans hlam2le3 harith4
  have hrho1reg : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [abs_of_nonneg (by linarith only [hchi1strip.2.1, hchi1strip] : (0:ℝ) ≤ 1 - ρ₁.re), h]
    rw [div_le_div_iff_of_pos_right hlogq]
    exact le_trans (le_of_lt hlam1) (le_trans (by norm_num) harith4)
  -- the case split on `χ₂`
  rcases eq_or_ne (χ₂ * χ₂) 1 with hcase | hcase
  · -- `χ₂² = 1`: the five-term route
    have hcase' : χ₂ ^ 2 = 1 := by rw [pow_two]; exact hcase
    have hchi24 : χ₂ ^ 4 = 1 := by
      rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, hcase']; simp
    exact D.hcoreB q hQEB χ₁ ρ₁ ρ₂ χ₂ hmin hsq' him hchi2ne1 hchi2chi1 hchi2inv hchi24 hzm2
      hlep hlam2c (by linarith only [abs_nonneg ρ₂.im, hgamma2]) hball hzero₁ hzero₂ hδB₁ hδB₂
      hrho1reg hβreg hdivE hdivB hmaxE
  · rcases eq_or_ne (χ₁ * (χ₂ * χ₂)) 1 with hcase2 | hcase2
    · -- `χ₁χ₂² = 1`: again `χ₂⁴ = 1`
      have hchi24 : χ₂ ^ 4 = 1 := by
        have h2eq : χ₂ ^ 2 = χ₁ := by
          have h := congrArg (fun x : DirichletCharacter ℂ q => χ₁⁻¹ * x) hcase2
          rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h
          rw [pow_two, h, inv_eq_of_mul_eq_one_left hsq']
        rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, h2eq, pow_two, hsq']
      exact D.hcoreB q hQEB χ₁ ρ₁ ρ₂ χ₂ hmin hsq' him hchi2ne1 hchi2chi1 hchi2inv hchi24 hzm2
        hlep hlam2c (by linarith only [abs_nonneg ρ₂.im, hgamma2]) hball hzero₁ hzero₂ hδB₁ hδB₂
        hrho1reg hβreg hdivE hdivB hmaxE
    · -- the third method
      exact D.hcoreA q hQEA χ₁ ρ₁ ρ₂ χ₂ hmin hsq' him hchi2ne1 hchi2chi1 hchi2inv hcase
        hcase2 hzm2 hlep hlam2c hgamma2 hball hzero₁ hzero₂ hδA₁ hδA₂ hβreg hdivB hdivE hmaxE

end Work.ZeroFreeTables
