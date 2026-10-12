import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseBogFS.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Gate` — the numeric rows of `BogNumeric` from the §10 gate

`BogNumeric` (the numeric side conditions of `bogPairOp_eq_shifted`/`bogPairOp_ground`) is
supplied at the honest datum by the §10 gate `Q3KernelFS` evaluated at `KzEnvAt E ρ`:

* `𝒜`-evenness, `ℬ`-evenness from the gate's `A_even`, `B_even` (`KzEnvAt` only changes
  `z`, `A`, `B`);
* `|ℬ| ≤ 𝒜` from the gate's `AB`;
* the commutator bound `[a_k,a_k†] + [a_{−k},a_{−k}†] ≤ 2` from the gate's
  `hasKernel_noWrap` at the pairs `(k,k)`, `(−k,−k)` (`NoWrap` there is `kmom 0 = 0`),
  with `|χ̂²| ≤ 1` and `χ̂² ≥ 0`.

The one row **not** in `Q3KernelFS` is `0 < 𝒜(k)+ℬ(k)`, i.e. `τ(k) + 2ρŴ₁(k) > 0`: the
gate carries no sign information on `Ŵ₁` below `P_H^q`, and `𝒜+ℬ = 0` would make the
squeezing parameter `α_k = −1` degenerate.  It has to be added as an extra row of the
gate (or derived from the view's `Ŵ₁` pin); see `README.md` §"what is missing".
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The label `0` has zero momentum (from the oddness `kmom (-i) = -kmom i`). -/
theorem kmom_zero (F : FockData Mode) : F.kmom 0 = 0 := by
  have h := F.kmom_neg 0
  rw [neg_zero] at h
  have h2 : (2 : ℝ) • F.kmom 0 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- `NoWrap` at the diagonal pair `(k,k)`: `kmom 0 = 0`. -/
theorem noWrap_self (F : FockData Mode) (k : Mode) :
    Work.BoseK15.NoWrap F.kmom k k := by
  simp only [Work.BoseK15.NoWrap, sub_self, kmom_zero F, sub_self]

/-- `[a_k,a_k†] ≤ 1` at the honest datum: the box kernel at the diagonal pair is
`χ̂²(0) − χ̂(kℓ)²` with `|χ̂²(0)| ≤ 1`. -/
theorem ccrK_self_le_one (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    {K₀ : ℝ} (h : Q3KernelFS K₀ F T E) (k : Mode) : F.ccrK k k ≤ 1 := by
  have hh := h.hasKernel_noWrap k k (noWrap_self F k)
  rw [sub_self] at hh
  have h1 : E.hatChiSq 0 ≤ 1 := (abs_le.mp (h.hatChiSq_le 0)).2
  have h2 : 0 ≤ E.hatChi k * E.hatChi k := mul_self_nonneg _
  linarith [hh, h1, h2]

/-- `[a_k,a_k†] + [a_{−k},a_{−k}†] ≤ 2` at the honest datum: the `BogNumeric.hccr` row. -/
theorem bogCcr2_le_two (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    {K₀ : ℝ} (h : Q3KernelFS K₀ F T E) (k : Mode) : bogCcr2 F k ≤ 2 := by
  have h1 := ccrK_self_le_one F T E h k
  have h2 := ccrK_self_le_one F T E h (-k)
  simp only [bogCcr2]
  linarith

/-- `𝒜` is even at the honest datum (the gate's `A_even` at `KzEnvAt E ρ`). -/
theorem bogA_even_of_gate (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    (ρ : ℝ) {K₀ : ℝ} (h : Q3KernelFS K₀ F T (Work.BoseFixR.KzEnvAt E ρ)) (k : Mode) :
    bogA E ρ (-k) = bogA E ρ k := by
  have hh := h.A_even k
  simpa only [bogA, Work.BoseFixR.KzEnvAt] using hh

/-- `ℬ` is even at the honest datum (the gate's `B_even` at `KzEnvAt E ρ`). -/
theorem bogB_even_of_gate (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    (ρ : ℝ) {K₀ : ℝ} (h : Q3KernelFS K₀ F T (Work.BoseFixR.KzEnvAt E ρ)) (k : Mode) :
    bogB E ρ (-k) = bogB E ρ k := by
  have hh := h.B_even k
  simpa only [bogB, Work.BoseFixR.KzEnvAt] using hh

/-- `𝒞` is even at the honest datum (χ̂ is even). -/
theorem bogC_even_of_gate (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    (ρ : ℝ) {K₀ : ℝ} (h : Q3KernelFS K₀ F T (Work.BoseFixR.KzEnvAt E ρ)) (k : Mode) :
    bogC E ρ (-k) = bogC E ρ k := by
  have hh := h.hatChi_even
  simp only [Work.BoseFixR.KzEnvAt] at hh
  simp only [bogC, hh]

/-- `|ℬ| ≤ 𝒜` at the honest datum (the gate's `AB` at `KzEnvAt E ρ`). -/
theorem bogAB_of_gate (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    (ρ : ℝ) {K₀ : ℝ} (h : Q3KernelFS K₀ F T (Work.BoseFixR.KzEnvAt E ρ)) (k : Mode) :
    |bogB E ρ k| ≤ bogA E ρ k := by
  have hh := h.AB k
  simpa only [bogA, bogB, Work.BoseFixR.KzEnvAt] using hh

/-- **`BogNumeric` from the gate.**  All rows but `0 < 𝒜(k)` and `0 < 𝒜(k)+ℬ(k)` come from
`Q3KernelFS` at `KzEnvAt E ρ`; the two positivity rows are the extra input (the honest data
has them from the `Ŵ₁` pin and `τ̃ ≥ 0`). -/
theorem BogNumeric.of_gate (F : FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Q3Env Mode) (ρ : ℝ) {K₀ : ℝ}
    (h : Q3KernelFS K₀ F T (Work.BoseFixR.KzEnvAt E ρ))
    (hA : ∀ k, 0 < bogA E ρ k) (hAB : ∀ k, 0 < bogA E ρ k + bogB E ρ k) :
    BogNumeric F E ρ where
  hA := hA
  hB := fun k => bogAB_of_gate F T E ρ h k
  hAB := hAB
  hAe := fun k => (bogA_even_of_gate F T E ρ h k).symm
  hBe := fun k => (bogB_even_of_gate F T E ρ h k).symm
  hCe := fun k => (bogC_even_of_gate F T E ρ h k).symm
  hccr := fun k => bogCcr2_le_two F T (Work.BoseFixR.KzEnvAt E ρ) h k

/-- **The two positivity rows of `BogNumeric`.**  With `τ̃ ≥ 0`, `τ̃` large above a
threshold `c₁`, and `−w₁ ≤ Ŵ₁` everywhere while `Ŵ₁ ≥ w₀ > 0` below `c₁`, the combinations
`𝒜_k = τ̃_k + ρŴ₁_k` and `𝒜_k + ℬ_k = τ̃_k + 2ρŴ₁_k` are positive.  (At the honest data
`τ̃_k > 0` for `|k| > (2dsℓ)⁻¹` and `Ŵ₁(k) > 0` for the low momenta; see `README.md` §5.1.
The gate gives only `|Ŵ₁| ≤ K₀a`, hence the `w₁` slot.) -/
theorem bogA_pos_and_add_pos (F : FockData Mode) (E : Q3Env Mode) (ρ c₁ w₀ w₁ : ℝ)
    (hρ : 0 < ρ) (hw₀ : 0 < w₀) (hw₁ : 0 ≤ w₁)
    (htau0 : ∀ k : Mode, 0 ≤ E.tau k)
    (htau : ∀ k : Mode, c₁ < ‖F.kmom k‖ → 2 * ρ * w₁ < E.tau k)
    (hWlo : ∀ k : Mode, -w₁ ≤ E.W1 k)
    (hW : ∀ k : Mode, ‖F.kmom k‖ ≤ c₁ → w₀ ≤ E.W1 k) :
    (∀ k : Mode, 0 < bogA E ρ k) ∧ (∀ k : Mode, 0 < bogA E ρ k + bogB E ρ k) := by
  have hρw : 0 ≤ ρ * w₁ := mul_nonneg hρ.le hw₁
  constructor
  · intro k
    by_cases h : ‖F.kmom k‖ ≤ c₁
    · have h1 : w₀ ≤ E.W1 k := hW k h
      have h2 := htau0 k
      simp only [bogA]
      nlinarith
    · have h1 : 2 * ρ * w₁ < E.tau k := htau k (lt_of_not_ge h)
      have h2 : -w₁ ≤ E.W1 k := hWlo k
      simp only [bogA]
      nlinarith
  · intro k
    by_cases h : ‖F.kmom k‖ ≤ c₁
    · have h1 : w₀ ≤ E.W1 k := hW k h
      have h2 := htau0 k
      simp only [bogA, bogB]
      nlinarith
    · have h1 : 2 * ρ * w₁ < E.tau k := htau k (lt_of_not_ge h)
      have h2 : -w₁ ≤ E.W1 k := hWlo k
      simp only [bogA, bogB]
      nlinarith

end Work.BoseBogFS
