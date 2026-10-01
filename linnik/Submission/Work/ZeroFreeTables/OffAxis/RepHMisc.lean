/-
# ZeroFreeTables/OffAxis/RepHMisc

Height-parametric pieces of the repeated-zero engine at rectangle height `H`
(`OffAxis/HBLemma9_1_rep_engine_H.lean`):

* `Rep9.imprimCorrBoundedH` — the imprimitive correction of `Rep9.imprimCorrBounded` with
  `|s.im| ≤ 4` weakened to `|s.im| ≤ H` (that hypothesis is unused in the original proof);
* `Rep9.nearSumDoubleH` — the aligned double zero contributes `2·P₃(1)` to the near sum at
  `σ + i·Im ρ₁`, for the height-`H` numbering `IsMinWideAt H W`;
* `OffAxis.pointBoundH` — HB §9's point bound at height `H`: for a non-principal `χ` and a point
  of the line `1 + a/log q` with `|Im s| ≤ H` (and `H ≤ log q`),
  `Σ(s,χ) ≤ −P3NearSumL(δ) + (a+λ₁)(1/4 + e)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Rep9.imprimCorrBounded
import Submission.Work.ZeroFreeTables.Rep9.masterP3M
import Submission.Work.ZeroFreeTables.Rep9.logDerivHyp_quarter
import Submission.Work.ZeroFreeTables.Rep9.nearSum_bounds
import Submission.Work.ZeroFreeTables.Rep9.nearSum_primitive_le
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.RepHMaster
import Submission.Work.LinnikAreas.boxMaxZero

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.Rep9

open Work.ZeroFreeTables Work.LinnikContract

/-- **The imprimitive correction at height `H`.**  `Rep9.imprimCorrBounded` with the (unused)
hypothesis `|s.im| ≤ 4` replaced by `|s.im| ≤ H`. -/
theorem imprimCorrBoundedH {a e M H : ℝ} (ha : 0 < a) (he : 0 < e) (hM : 0 ≤ M) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {L lam₁ : ℝ},
      L₀ ≤ L → Real.log (q : ℝ) ≤ L → 0 ≤ lam₁ → lam₁ ≤ M →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ H →
        Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
          ≤ @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L
              χ.primitiveCharacter s a lam₁ + (a + lam₁) * e := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
  obtain ⟨L₀, hL₀1, hAbs⟩ := imprimAbsorb (C := C) (a := a) (e := e) (A := a + M) hCpos ha he
  refine ⟨L₀, ?_⟩
  intro q _inst χ hχ L lam₁ hL0 hlogq hlam0 hlamM s hsre him
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := le_trans hL₀1 hL0
  have hsre' : 1 < s.re := by
    rw [hsre]
    have : 0 < a / L := div_pos ha hLpos
    linarith
  have hdiff := hC (N := χ.conductor) (q := q) (χ.conductor_dvd_level) χ.primitiveCharacter
    hL1 hsre' ha hlam0
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at hdiff
  have habs := hAbs (q := q) hL0 hlogq hlam0 (by linarith)
  have hkey : Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
      - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L
          χ.primitiveCharacter s a lam₁ ≤ (a + lam₁) * e :=
    le_trans (le_trans (le_abs_self _) hdiff) habs
  linarith

end Work.ZeroFreeTables.Rep9

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables Work.LinnikContract

/-- **HB §9's point bound at height `H`.**  The composition of `Rep9.masterP3H` (the `P₃` master
bound at height `H`), `Rep9.imprimCorrBoundedH` (passage to the primitive character) and
`Rep9.nearSum_primitive_le`, exactly as `Rep9.pointBound` composes the height-`4` versions. -/
theorem pointBoundH {a e M H : ℝ} (ha : 0 < a) (he : 0 < e) (hM : 0 ≤ M) :
    ∃ q₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {lam₁ : ℝ}, 0 ≤ lam₁ → lam₁ ≤ M →
      H ≤ Real.log (q : ℝ) →
      ∀ s : ℂ, s.re = 1 + a / Real.log (q : ℝ) → |s.im| ≤ H →
        Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ s a lam₁
          ≤ -Work.ZeroFreeTables.P3NearSumL q (Real.log q) χ s a lam₁ δ + (a + lam₁) * (1 / 4 + e) := by
  obtain ⟨L₀L, δ, hδ0, hδ1, hlog⟩ := Work.ZeroFreeTables.Rep9.logDerivHyp_quarter (e := e / 3) (by positivity)
  obtain ⟨L₀m, hmast⟩ := Work.ZeroFreeTables.P9.prim.masterP3H (a := a) (H := H) (δ := δ)
    (c := 1 / 4 + e / 3) (e := e / 3) (M := M) ha hδ0 hδ1 (by positivity)
  obtain ⟨L₀i, himp⟩ := Work.ZeroFreeTables.Rep9.imprimCorrBoundedH (a := a) (H := H) (e := e / 3) (M := M)
    ha (by positivity) hM
  refine ⟨max (max (Nat.ceil (Real.exp L₀L)) (Nat.ceil (Real.exp L₀m)))
      (max (Nat.ceil (Real.exp L₀i)) 5) + 1, δ, hδ0, hδ1, ?_⟩
  intro q hq inst χ hχ lam₁ hlam0 hlamM hHL s hsre hsim
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hceL : Nat.ceil (Real.exp L₀L) ≤ q := by omega
  have hceM : Nat.ceil (Real.exp L₀m) ≤ q := by omega
  have hceI : Nat.ceil (Real.exp L₀i) ≤ q := by omega
  have hexpL : Real.exp L₀L ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceL)
  have hexpM : Real.exp L₀m ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceM)
  have hexpI : Real.exp L₀i ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceI)
  have hLL : L₀L ≤ L := by
    rw [hLdef]
    calc L₀L = Real.log (Real.exp L₀L) := (Real.log_exp L₀L).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexpL
  have hLm : L₀m ≤ L := by
    rw [hLdef]
    calc L₀m = Real.log (Real.exp L₀m) := (Real.log_exp L₀m).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexpM
  have hLi : L₀i ≤ L := by
    rw [hLdef]
    calc L₀i = Real.log (Real.exp L₀i) := (Real.log_exp L₀i).symm
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
  have hlogd : Work.ZeroFreeTables.LogDerivHyp χ.primitiveCharacter δ L (1 / 4 + e / 3) :=
    hlog χ.primitiveCharacter hχprimne hχprim hLL hlogN
  have hm := hmast χ.primitiveCharacter hχprimne hχprim hLm hlogN hlam0 hlamM hHL' hlogd
    s hsre hsim
  have hi := himp χ hχ hLi (le_of_eq hLdef.symm) hlam0 hlamM s hsre hsim
  have hn := Work.ZeroFreeTables.Rep9.nearSum_primitive_le hq2 χ hχ L s a lam₁ δ hδ0.le hδ1
  have hkey : (a + lam₁) * ((1 / 4 + e / 3) + e / 3) = (a + lam₁) * (1 / 4 + 2 * e / 3) := by ring
  linarith [hm, hi, hn, hkey]

end Work.ZeroFreeTables.OffAxis
