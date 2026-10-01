/-
# ZeroFreeTables/OffAxis/RectRepPoint

`OffAxis.pointBoundWide`: HB §9's point bound `Σ(s,χ) ≤ −P3NearSumL(s) + (a+λ₁)(1/6 + e)` for an
arbitrary non-principal character `χ` mod `q`, at every point `s` of the line `Re s = 1 + a/log q`
with `|Im s| ≤ 3H` (`1 ≤ H ≤ log q`) — the height range needed by the diagonal (repeated-zero)
argument, where the four points `σ, σ+iγ, σ+2iγ, σ+3iγ` reach height `3|γ| ≤ 3H`.

It is the height-`H`/wide counterpart of `Rep9.pointBound` (height `4`, `1/4` in place of `1/6`),
and composes the same three ingredients:

* `RectRepMaster` — the `P₃` master bound for a *primitive* character on the wide range
  `|Im s| ≤ 10 log q`, whose log-derivative input is supplied by `RectRepInput`
  (`l31free.lemma3_1_free_gen` with `φ = 1/3`, i.e. the constant `1/6`);
* `Rep9.imprimCorrBoundedH` — the passage from `χ` to `χ.primitiveCharacter`;
* `Rep9.nearSum_primitive_le` — the near sums agree between `χ` and `χ.primitiveCharacter`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.OffAxis.RectRepInput
import Submission.Work.ZeroFreeTables.OffAxis.RectRepMaster
import Submission.Work.ZeroFreeTables.OffAxis.RepHMisc
import Submission.Work.ZeroFreeTables.Rep9.nearSum_primitive_le
import Submission.Work.LinnikAreas2.D2Aux

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables Work.LinnikContract

/-- **HB §9's point bound at height `≤ 3H`.**  For positive `a`, `e` and any bound `M` on `λ₁`,
`1 ≤ H`, there are `q₀` and `δ ∈ (0,1)` such that for `q ≥ q₀`, every non-principal `χ` mod `q`,
`0 ≤ λ₁ ≤ M` and every `s` with `Re s = 1 + a/log q`, `|Im s| ≤ 3H` (and `H ≤ log q`):
`Σ(s,χ) ≤ −P3NearSumL q (log q) χ s a λ₁ δ + (a + λ₁)(1/6 + e)`. -/
theorem pointBoundWide {a e M H : ℝ} (ha : 0 < a) (he : 0 < e) (hM : 0 ≤ M) (hH1 : 1 ≤ H) :
    ∃ q₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {lam₁ : ℝ}, 0 ≤ lam₁ → lam₁ ≤ M →
      H ≤ Real.log (q : ℝ) →
      ∀ s : ℂ, s.re = 1 + a / Real.log (q : ℝ) → |s.im| ≤ 3 * H →
        Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ s a lam₁
          ≤ -Work.ZeroFreeTables.P3NearSumL q (Real.log q) χ s a lam₁ δ + (a + lam₁) * (1 / 6 + e) := by
  obtain ⟨L₀i, δ, hδ0, hδ1, hin⟩ := RectRepInput (e / 3) (by positivity)
  obtain ⟨L₀m, hmast⟩ := RectRepMaster (a := a) (δ := δ) (c := 1 / 6 + e / 3) (e := e / 3) (M := M)
    ha hδ0 hδ1 (by positivity)
  obtain ⟨L₀c, himp⟩ := Work.ZeroFreeTables.Rep9.imprimCorrBoundedH (a := a) (H := 3 * H)
    (e := e / 3) (M := M) ha (by positivity) hM
  refine ⟨max (max (Nat.ceil (Real.exp L₀i)) (Nat.ceil (Real.exp L₀m)))
      (max (Nat.ceil (Real.exp L₀c)) 5) + 1, δ, hδ0, hδ1, ?_⟩
  intro q hq inst χ hχ lam₁ hlam0 hlamM hHL s hsre hsim
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hceL : Nat.ceil (Real.exp L₀i) ≤ q := by omega
  have hceM : Nat.ceil (Real.exp L₀m) ≤ q := by omega
  have hceI : Nat.ceil (Real.exp L₀c) ≤ q := by omega
  have hexpL : Real.exp L₀i ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceL)
  have hexpM : Real.exp L₀m ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceM)
  have hexpI : Real.exp L₀c ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceI)
  have hLL : L₀i ≤ L := by
    rw [hLdef]
    calc L₀i = Real.log (Real.exp L₀i) := (Real.log_exp L₀i).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexpL
  have hLm : L₀m ≤ L := by
    rw [hLdef]
    calc L₀m = Real.log (Real.exp L₀m) := (Real.log_exp L₀m).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexpM
  have hLi : L₀c ≤ L := by
    rw [hLdef]
    calc L₀c = Real.log (Real.exp L₀c) := (Real.log_exp L₀c).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexpI
  have hHL' : H ≤ L := by rw [hLdef]; exact hHL
  have hχprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hχprimne : χ.primitiveCharacter ≠ 1 := by
    intro h1
    refine hχ ?_
    have h2 := χ.changeLevel_primitiveCharacter
    rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
    exact h2.symm
  have hlogN : Real.log ((χ.conductor : ℕ) : ℝ) ≤ L := by
    have hle : χ.conductor ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    rw [hLdef]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor))
      (by exact_mod_cast hle)
  have hN3 : 3 ≤ χ.conductor := Work.LinnikAreas2.three_le_conductor χ hχ
  have hlogd : WideLogDerivHyp χ.primitiveCharacter δ L (1 / 6 + e / 3) :=
    hin χ.primitiveCharacter hχprimne hχprim hN3 hLL hlogN
  have hsim10 : |s.im| ≤ 10 * L := by
    have h1 : 3 * H ≤ 3 * L := by linarith
    linarith
  have hm := hmast χ.primitiveCharacter hχprimne hχprim hLm hlogN hlam0 hlamM hlogd s hsre hsim10
  have hi := himp χ hχ hLi (le_of_eq hLdef.symm) hlam0 hlamM s hsre (by
    have : H ≤ 3 * H := by linarith
    linarith)
  have hn := Work.ZeroFreeTables.Rep9.nearSum_primitive_le hq2 χ hχ L s a lam₁ δ hδ0.le hδ1
  have hkey : (a + lam₁) * ((1 / 6 + e / 3) + e / 3) + (a + lam₁) * (e / 3)
      = (a + lam₁) * (1 / 6 + e) := by ring
  linarith [hm, hi, hn, hkey]

end Work.ZeroFreeTables.OffAxis
