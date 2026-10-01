import Mathlib
import Submission.Work.ZeroFreeTables.HBTable8StrictLast
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.ZeroFreeTables.Table8Printed
import Submission.Work.ZeroFreeTables.Table8Cert
import Submission.Work.ZeroFreeTables.Table8CertExtPrinted
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P9.pointEngine_prim
import Submission.Work.ZeroFreeTables.HB94.Lam0GeEngine

open scoped Classical BigOperators

namespace Work.ZeroFreeTables.HB94

open Work.LinnikContract Work.ZeroFreeTables

/-- **HB Table 8 (complex case) at the wide height `|Im ρ| ≤ 2`.**  If `χ₁` is complex
(`χ₁ ^ 2 ≠ 1`) and `λ₁ ≤ 0.348`, then every zero `ρ ≠ ρ₁` of `χ₁` (non-zero multiplicity) of
height `|Im ρ| ≤ 2` satisfies `λ(ρ) ≥ 0.82` — HB Table 8 gives `λ₀ ≥ 1.309` for `λ₁ ≤ 0.36` (row
`(0.36, 1.309)`), which covers the intended use (`λ(ρ) ≥ λ₁ + 0.472`, and `λ₁ ≤ 0.348`).

Route.  (i) The `P₃` engine `HBLemma9_1` (`Submission/Work/ZeroFreeTables/HBLemma9_1_proof.lean`)
is proved there in **all cases except** `χ₁ ^ 2 = 1` (case C, its only `sorry`, line 945); its
remaining hypotheses are `IsMin1WideAt 10 χ₁ ρ₁`, `¬(χ₁ ^ 2 = 1 ∧ ρ₁.im = 0)`, `IsZ χ₁ ρ₁`,
`IsZ χ₁ ρ₀`, `ρ₁ ≠ ρ₀`, `cond913` → `ineq913`.  Copy that file, delete the case-C branch, and
relax `IsZ χ₁ ρ₀` to `zeroMult χ₁ ρ₀ ≠ 0 ∧ |ρ₀.im| ≤ 2` (in that file `|γ₀| ≤ 1` is used only to
get `|t| ≤ 3` in the `k1_input` windows and `‖sPt a L t‖ ≤ 5`; `k1_input`'s `|t| ≤ 3` is itself
used only to derive `|t| ≤ 10 * L` (`L ≥ 1`), so `|t| ≤ 10` works, and `|γ₀| ≤ 2` gives
`‖sPt a L t‖ ≤ 4 + a/L`).  (ii) Then apply the row reduction
`Work.ZeroFreeTables.lam0_row_of_lemma9_1_of_facts` (`Table8Derive.lean`) — the template of
`HBTable8StrictLast.lam0_strict_of_lemma9_1` — with a certified Table 8 row: the printed rows and
their certificates are `t8certRowsP`, `t8certRowsExtP` and `Table8CertPrinted`,
`Table8CertExtPrinted` (`Table8Printed.lean`, both proved), e.g. the row
`(λ₁ ≤ 0.36, λ₀ ≥ 1.309)`; monotonicity `p913_mono_lam₁`/`p913_mono_lam₀` upgrades `λ₁ ≤ 0.348`
to the row's `0.36` and the conclusion `λ₀ ≥ 1.309` down to `0.82`. -/
theorem Lam0Ge : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 →
    Work.LinnikContract.lamOf q ρ₁ ≤ (348:ℝ)/1000 →
    ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ₁ ρ ≠ 0 → |ρ.im| ≤ 2 → ρ ≠ ρ₁ →
      (82:ℝ)/100 ≤ Work.LinnikContract.lamOf q ρ := by
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
    apply div_pos
    · linarith
    · norm_num
  obtain ⟨q₀, hq₀⟩ := Lam0GeEngine.HBLemma9_1Wide_proof ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) ε
    (by norm_num) (by norm_num [Kaff]) hε
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ hm hsq hlam1 ρ hzm him hne => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hltv : lamOf q ρ ≤ (1309:ℝ)/1000 := by linarith
  have hmZ : IsZ χ₁ ρ₁ := isMin1_isZ hm.1
  have hχ1 : χ₁ ≠ 1 := hmZ.1
  have hlam1' : lamOf q ρ₁ ≤ (36:ℝ)/100 := by linarith
  have hq2 : 2 ≤ q := two_le_modulus_of_char_ne_one hχ1
  have hlam1nn : 0 ≤ lamOf q ρ₁ := Work.LinnikContract.API.isZ_lambda_nonneg hq2 hmZ
  have hlam0nn : 0 ≤ lamOf q ρ := Lam0GeEngine.lamOf_nonneg_of_zeroMult hzm
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
  have hineq := hq₀ q hq χ₁ ρ₁ ρ hm hsq hmZ hzm him hne.symm hcond'
  have hineq' : 0 ≤ p913 (lamOf q ρ₁) (lamOf q ρ) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100))
      + ((1161:ℝ)/500 + lamOf q ρ₁) * ε := hineq
  -- monotonicity in `λ₀` and then in `λ₁`, and the value of `ε`
  have h1 : p913 (lamOf q ρ₁) (lamOf q ρ) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100))
      ≤ p913 (lamOf q ρ₁) ((1309:ℝ)/1000) ((1161:ℝ)/500) (Kaff ((36:ℝ)/100)) :=
    p913_mono_lam₀ (lam₁ := lamOf q ρ₁) (lam₀ := lamOf q ρ) (lam₀' := (1309:ℝ)/1000)
      (a := (1161:ℝ)/500) (K := Kaff ((36:ℝ)/100))
      (by norm_num) (by linarith) (by linarith) (by norm_num) hltv
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


end Work.ZeroFreeTables.HB94
