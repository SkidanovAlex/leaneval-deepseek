/-
# `ZeroFreeTables/OffAxis/RectC/RectSelfMin`

HB Table 8 (the `P₃`/Lemma 9.1 row) at **rectangle height `L`**, complex case: the
height-`L` version of `Work.ZeroFreeTables.HB94.Lam0Ge`.

If `ρ₁` is the `λ`-minimal zero of `χ₁` in the height-`L` rectangle with room `10L`
(`Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁`), `χ₁` is complex (`χ₁ ^ 2 ≠ 1`) and `λ₁ ≤ 348/1000`,
then every *other* zero `ρ` of `χ₁` of height `≤ 2L` satisfies `λ(ρ) ≥ 82/100`.

The engine is the height-parametric `HBLemma9_1_engine_H_cplx` at `H = 2L`, `W = 10L`; the row
reduction uses the certified row `(λ₁ ≤ 36/100 ⟹ λ₀ ≥ 1309/1000)` with witness `a = 1161/500`
(`Table8CertPrinted`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H_cplx
import Submission.Work.ZeroFreeTables.Table8Printed

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis.RectC

open Work.LinnikContract Work.ZeroFreeTables

/-- The threshold `⌈e^L⌉ + 1` makes `L ≤ log q` available (local copy of
`Work.ZeroFreeTables.OffAxis.le_log_of_ceil_exp_le`, to avoid importing the `sorry`-carrying
`OffAxis/RectC_Lam0.lean`). -/
theorem le_log_of_ceil_exp_le_rectC {L : ℝ} {q : ℕ} (hq : Nat.ceil (Real.exp L) + 1 ≤ q) :
    L ≤ Real.log (q : ℝ) := by
  have h1 : Real.exp L ≤ (Nat.ceil (Real.exp L) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp L) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have h3 : Real.exp L ≤ (q : ℝ) := by linarith
  calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos L) h3

/-- **HB Table 8 at rectangle height `L`, complex case.** -/
theorem RectSelfMin : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 →
      Work.LinnikContract.lamOf q ρ₁ ≤ (348:ℝ)/1000 →
    ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ₁ ρ ≠ 0 → |ρ.im| ≤ 2 * L → ρ ≠ ρ₁ →
      (82:ℝ)/100 ≤ Work.LinnikContract.lamOf q ρ := by
  intro L hL
  -- the certified Table 8 row `(λ₁ ≤ 0.36, λ₀ ≥ 1.309)`
  have hcert : cond913 ((36:ℝ)/100) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) ∧
      p913 ((36:ℝ)/100) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) < 0 :=
    Table8CertPrinted ((348/1000 : ℝ), (36/100 : ℝ), (1309/1000 : ℝ), (1161/500 : ℝ))
      (by simp [t8certRowsP])
  obtain ⟨hcond, hp⟩ := hcert
  set ε : ℝ := -p913 ((36:ℝ)/100) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100))
    / (2 * ((1161:ℝ)/500 + (36:ℝ)/100)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) (by norm_num)
  -- the height-`L` `P₃` engine at `H = 2L`, `W = 10L`
  obtain ⟨q₀, hq₀⟩ := HBLemma9_1_engine_H_cplx ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) ε
    (by norm_num) (by norm_num [Kaff]) hε (2 * L) (10 * L) (by linarith) (by linarith)
  refine ⟨max q₀ (max (Nat.ceil (Real.exp (2 * L)) + 1) 3), ?_⟩
  intro q hq _inst χ₁ ρ₁ hR hsq hlam1 ρ hzm him hne
  have hq₀' : q₀ ≤ q := by omega
  have hqexp : Nat.ceil (Real.exp (2 * L)) + 1 ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hlog2L : 2 * L ≤ Real.log (q : ℝ) := le_log_of_ceil_exp_le_rectC hqexp
  by_contra hcon
  push_neg at hcon
  have hltv : lamOf q ρ ≤ (1309:ℝ)/1000 := by linarith
  have hχ1 : χ₁ ≠ 1 := hR.1.1
  have hq2 : 2 ≤ q := by omega
  have hmin : IsMinWideAt (2 * L) (10 * L) χ₁ ρ₁ :=
    ⟨hR.1.1, hR.1.2.1, le_trans hR.1.2.2 (by linarith),
      fun χ u hχ hzm him => hR.2 χ u ⟨hχ, hzm, him⟩⟩
  have hlam1nn : 0 ≤ lamOf q ρ₁ := Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hR.1.2.1
  have hlam1' : lamOf q ρ₁ ≤ (36:ℝ)/100 := by linarith
  have hlam0nn : 0 ≤ lamOf q ρ := Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hzm
  -- the side condition, transported to the pair `(λ₁, λ₀)`
  have hcondA : cond913 (lamOf q ρ₁) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) :=
    cond913_mono_lam₁ (lam₁ := lamOf q ρ₁) (lam₁' := (36:ℝ)/100)
      (lam₀ := (1309:ℝ)/1000) (a := (1161:ℝ)/500) (K := Kaff ((36:ℝ)/100))
      hlam1' (by norm_num [Kaff]) (by norm_num) (by linarith) hcond
  have hcond' : cond913 (lamOf q ρ₁) (lamOf q ρ) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) := by
    unfold cond913 at hcondA ⊢
    have hle : ((1161:ℝ)/500 + lamOf q ρ) ^ 3 ≤ ((1161:ℝ)/500 + (1309:ℝ)/1000) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hpos : 0 < ((1161:ℝ)/500 + lamOf q ρ) ^ 3 := by positivity
    have h1 : 1 / ((1161:ℝ)/500 + (1309:ℝ)/1000) ^ 3
        ≤ 1 / ((1161:ℝ)/500 + lamOf q ρ) ^ 3 :=
      one_div_le_one_div_of_le hpos hle
    linarith
  have hineq := hq₀ q hq₀' χ₁ ρ₁ ρ hlog2L hmin hsq hzm him hne.symm hcond'
  have hineq' : 0 ≤ p913 (lamOf q ρ₁) (lamOf q ρ) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100))
      + ((1161:ℝ)/500 + lamOf q ρ₁) * ε := hineq
  -- monotonicity in `λ₀` and then in `λ₁`, and the value of `ε`
  have h1 : p913 (lamOf q ρ₁) (lamOf q ρ) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100))
      ≤ p913 (lamOf q ρ₁) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) :=
    p913_mono_lam₀ (lam₁ := lamOf q ρ₁) (lam₀ := lamOf q ρ) (lam₀' := (1309:ℝ)/1000)
      (a := (1161:ℝ)/500) (K := Kaff ((36:ℝ)/100))
      (by norm_num) (by linarith) (by linarith) (by linarith) hltv
  have h2 : p913 (lamOf q ρ₁) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100))
      ≤ p913 ((36:ℝ)/100) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) :=
    p913_mono_lam₁ (lam₁ := lamOf q ρ₁) (lam₁' := (36:ℝ)/100)
      (lam₀ := (1309:ℝ)/1000) (a := (1161:ℝ)/500) (K := Kaff ((36:ℝ)/100))
      hlam1nn hlam1' (by norm_num) (by norm_num) (by norm_num [Kaff])
  have hεval : ((1161:ℝ)/500 + (36:ℝ)/100) * ε
      = -(p913 ((36:ℝ)/100) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100))) / 2 := by
    rw [hεdef]
    field_simp
  have h5 : ((1161:ℝ)/500 + lamOf q ρ₁) * ε ≤ ((1161:ℝ)/500 + (36:ℝ)/100) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', h1, h2, h5, hεval, hp]

end Work.ZeroFreeTables.OffAxis.RectC
