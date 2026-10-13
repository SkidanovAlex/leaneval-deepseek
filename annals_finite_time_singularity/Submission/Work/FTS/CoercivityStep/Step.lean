/-
# The induction step of the `ℋ^k` coercivity (tex 661–707)

This is the paper's Proposition `prop:HkCoercivity`, formalised as the induction step
`HkIPStep_isHkIP_fts`: from one level of `StepInputs` (an admissible inner product on
`ℋ^n` with named coercivity and Cauchy–Schwarz constants, the regularity package
`StepReg α n`, the commutator bounds `CommutBounds α n κ`, and the balance `CC√κ ≤ cc/2`),
together with the *next* level's regularity and commutator data, one obtains `StepInputs`
at level `n+1` for the paper's recursion `HkIPStep 1 1 IP`.

The two halves are proved separately:

* `Step/Coercive.lean` (`HkIPStep_coercive`), the paper's coercivity computation
  (tex 690–705);
* `Step/HkIPStep_core.lean`, the constructive clauses of the new pairing.

The constants: the new coercivity constant is `cc/4`, the new Cauchy–Schwarz constant is
`9·CC`, and the balance required at the *next* level is `9·CC·√κ' ≤ cc/8` — i.e.
`CC'√κ' ≤ cc'/2` with `cc' = cc/4`, `CC' = 9CC`.  This is exactly the paper's
"`c_{1,k}C̄_k = (1/2)c_{k-1}²`", with the constants made explicit.
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Coercivity.HkMem_dth
import Submission.Work.Coercivity.HkAdm_dth
import Submission.Work.Coercivity.HkSq_succ_le
import Submission.Work.Coercivity.HkSq_succ_le
import Submission.Work.FTS.CoercivityStep.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dz_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Norm.HkAdm_mono
import Submission.Work.FTS.CoercivityStep.Step.Coercive
import Submission.Work.FTS.CoercivityStep.Step.HkIPStep_core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep

set_option autoImplicit false

open Work.FTS.CoercivityStep.Norm (HkAdm_mono HkSq_Dth_le HkSq_Dz_le HkSq_mono_le)

/-! ## Descending the regularity class -/

theorem HkReg.mono {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (h : HkReg α (k + 1) f) :
    HkReg α k f :=
  ⟨h.1, Work.Coercivity.HkMem_mono α k h.1 h.2⟩

theorem HkReg.dth {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : HkReg α (k + 1) f) : HkReg α k (Work.Spaces.Dth f) :=
  ⟨h.1.Dth, (Work.Coercivity.HkMem_dth α hα k h.1 h.2).1⟩

theorem HkReg.dz {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (h : HkReg α (k + 1) f) :
    HkReg α k (Work.Spaces.Dz f) :=
  ⟨h.1.Dz, Work.Coercivity.HkMem_dz_free α k h.1 h.2⟩

/-! ## The Cauchy–Schwarz bound of the new pairing, with its explicit constant -/

/-- **The Cauchy–Schwarz constant of `HkIPStep 1 1 IP` is `9·CC`.**  Each of the three
pairings is bounded by `CC·|f|_{ℋ^{n+1}}|g|_{ℋ^{n+1}}` (because `|·|_{ℋ^n} ≤ |·|_{ℋ^{n+1}}`
for `f`, `D_θf`, `D_zf`), and there are three of them. -/
theorem HkIPStep_cs (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {CC : ℝ} (hCC : 0 < CC)
    (hcs : ∀ f g : ℝ → ℝ → ℝ, HkReg α n f → HkReg α n g →
      |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g) :
    ∀ f g : ℝ → ℝ → ℝ, HkReg α (n + 1) f → HkReg α (n + 1) g →
      |Work.Coercivity.HkIPStep 1 1 IP f g|
        ≤ (9 * CC) * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
  intro f g hf hg
  set A : ℝ := Work.Spaces.HkNorm α (n + 1) f with hA
  set B : ℝ := Work.Spaces.HkNorm α (n + 1) g with hB
  set A0 : ℝ := Work.Spaces.HkNorm α n f with hA0
  set B0 : ℝ := Work.Spaces.HkNorm α n g with hB0
  set A1 : ℝ := Work.Spaces.HkNorm α n (Work.Spaces.Dth f) with hA1
  set B1 : ℝ := Work.Spaces.HkNorm α n (Work.Spaces.Dth g) with hB1
  set A2 : ℝ := Work.Spaces.HkNorm α n (Work.Spaces.Dz f) with hA2
  set B2 : ℝ := Work.Spaces.HkNorm α n (Work.Spaces.Dz g) with hB2
  have hNA : 0 ≤ A := by rw [hA]; exact Work.Spaces.HkNorm_nonneg α (n + 1) f
  have hNB : 0 ≤ B := by rw [hB]; exact Work.Spaces.HkNorm_nonneg α (n + 1) g
  have hNA0 : 0 ≤ A0 := by rw [hA0]; exact Work.Spaces.HkNorm_nonneg α n f
  have hNB0 : 0 ≤ B0 := by rw [hB0]; exact Work.Spaces.HkNorm_nonneg α n g
  have hNA1 : 0 ≤ A1 := by rw [hA1]; exact Work.Spaces.HkNorm_nonneg α n _
  have hNB1 : 0 ≤ B1 := by rw [hB1]; exact Work.Spaces.HkNorm_nonneg α n _
  have hNA2 : 0 ≤ A2 := by rw [hA2]; exact Work.Spaces.HkNorm_nonneg α n _
  have hNB2 : 0 ≤ B2 := by rw [hB2]; exact Work.Spaces.HkNorm_nonneg α n _
  have hA0A : A0 ≤ A := by
    rw [hA0, hA, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_mono_le α (Nat.le_succ n) hf.2)
  have hB0B : B0 ≤ B := by
    rw [hB0, hB, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_mono_le α (Nat.le_succ n) hg.2)
  have hA1A : A1 ≤ A := by
    rw [hA1, hA, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_Dth_le α hα n hf.2)
  have hB1B : B1 ≤ B := by
    rw [hB1, hB, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_Dth_le α hα n hg.2)
  have hA2A : A2 ≤ A := by
    rw [hA2, hA, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_Dz_le α n hf.1 hf.2)
  have hB2B : B2 ≤ B := by
    rw [hB2, hB, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_Dz_le α n hg.1 hg.2)
  have hRf0 : HkReg α n f := HkReg.mono hf
  have hRg0 : HkReg α n g := HkReg.mono hg
  have hRf1 : HkReg α n (Work.Spaces.Dth f) := HkReg.dth hα hf
  have hRg1 : HkReg α n (Work.Spaces.Dth g) := HkReg.dth hα hg
  have hRf2 : HkReg α n (Work.Spaces.Dz f) := HkReg.dz hf
  have hRg2 : HkReg α n (Work.Spaces.Dz g) := HkReg.dz hg
  have hs1 : |IP f g| ≤ CC * A0 * B0 := by rw [hA0, hB0]; exact hcs f g hRf0 hRg0
  have hs2 : |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)| ≤ CC * A1 * B1 := by
    rw [hA1, hB1]; exact hcs _ _ hRf1 hRg1
  have hs3 : |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| ≤ CC * A2 * B2 := by
    rw [hA2, hB2]; exact hcs _ _ hRf2 hRg2
  have habs : |Work.Coercivity.HkIPStep 1 1 IP f g|
      ≤ |IP f g| + |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
        + |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := by
    rw [Work.Coercivity.HkIPStep]
    simp only [one_mul]
    have hAB := abs_add_le (IP f g + IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
      (IP (Work.Spaces.Dz f) (Work.Spaces.Dz g))
    have hCD := abs_add_le (IP f g) (IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
    linarith
  have e1 : CC * A0 * B0 ≤ CC * A * B :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA0A hCC.le) hB0B hNB0 (mul_nonneg hCC.le hNA)
  have e2 : CC * A1 * B1 ≤ CC * A * B :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA1A hCC.le) hB1B hNB1 (mul_nonneg hCC.le hNA)
  have e3 : CC * A2 * B2 ≤ CC * A * B :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA2A hCC.le) hB2B hNB2 (mul_nonneg hCC.le hNA)
  have t1 : |IP f g| ≤ CC * A * B := le_trans hs1 e1
  have t2 : |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)| ≤ CC * A * B := le_trans hs2 e2
  have t3 : |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| ≤ CC * A * B := le_trans hs3 e3
  have hN : 0 ≤ CC * A * B := mul_nonneg (mul_nonneg hCC.le hNA) hNB
  have hsum : |IP f g| + |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
      + |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| ≤ 9 * CC * A * B := by
    nlinarith [t1, t2, t3, hN]
  refine le_trans habs hsum


/-! ## The induction step -/

/-- **The induction step of the paper's Proposition `prop:HkCoercivity`** (tex 661–707).

From the level-`n` input package `StepInputs α n IP cc CC κ` and the level-`(n+1)` data
which the step cannot produce itself (the regularity `StepReg α (n+1)` and the commutator
bounds `CommutBounds α (n+1) κ'`, with the balance `9·CC·√κ' ≤ cc/8`), one obtains the
level-`(n+1)` input package for the paper's recursion:

  `HkIPStep 1 1 IP`, with coercivity constant `cc/4` and Cauchy–Schwarz constant `9·CC`. -/
theorem HkIPStep_isHkIP_fts (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 1 ≤ n)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {cc CC κ κ' : ℝ}
    (h : StepInputs α n IP cc CC κ)
    (hCm' : CommutBounds α (n + 1) κ') (hreg' : StepReg α (n + 1))
    (hbal' : 9 * CC * Real.sqrt κ' ≤ cc / 8) :
    StepInputs α (n + 1) (Work.Coercivity.HkIPStep 1 1 IP) (cc / 4) (9 * CC) κ' := by
  have hcc0 : 0 < cc := h.1
  have hCC0 : 0 < CC := h.2.1
  have hIPc : IsHkIPc_fts α n IP cc := h.2.2.1
  have hcs : ∀ f g : ℝ → ℝ → ℝ, HkReg α n f → HkReg α n g →
      |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g :=
    h.2.2.2.1
  have hcc0' : (0:ℝ) < cc / 4 := by linarith
  have hCC0' : (0:ℝ) < 9 * CC := by linarith
  have hcore : IsHkIPCore_fts α (n + 1) (Work.Coercivity.HkIPStep 1 1 IP) :=
    { Work.FTS.CoercivityStep.Step.HkIPStep_core α hα n hn hIPc.prop.core with
      cs := ⟨9 * CC, hCC0', HkIPStep_cs α hα n hCC0 hcs⟩ }
  have hcoer : ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α (n + 1) f →
      (cc / 4) * Work.Spaces.HkSq α (n + 1) f
        ≤ Work.Coercivity.HkIPStep 1 1 IP (Work.Coercivity.LGammaT α f) f :=
    HkIPStep_coercive α hα n hn h
  have hprop : IsHkIP_fts α (n + 1) (Work.Coercivity.HkIPStep 1 1 IP) :=
    ⟨hcore, ⟨cc / 4, hcc0', hcoer⟩⟩
  have hbal'' : 9 * CC * Real.sqrt κ' ≤ cc / 4 / 2 := by linarith [hbal']
  exact ⟨hcc0', hCC0', ⟨hcc0', hprop, hcoer⟩, HkIPStep_cs α hα n hCC0 hcs, hreg', hCm', hbal''⟩

end Work.FTS.CoercivityStep
