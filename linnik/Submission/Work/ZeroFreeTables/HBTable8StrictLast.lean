/-
# ZeroFreeTables — HBTable8StrictLast

The **strict** form of the last printed row of HB's Table 8.

The frozen statement asks for the last row of Table 8 in the shape in which the
`rows15`-consumer (the `Z4` clause of the contract) needs it: below `λ₁ ≤ 0.696`
in the complex case, every *other* zero `ρ ≠ ρ₁` of `χ₁` (with the real-character
conjugate excluded, as in `Lam0Bound`) has `λ(ρ) > 0.696` **strictly**.

The strict inequality is what the non-strict certificate `lam0_certified_printed`
does *not* deliver: that lemma proves `v ≤ λ(ρ)`, i.e. it rules out `λ(ρ) < v`
from the engine (9.13).  Here the argument is run at the tangency row
`(hi, v, a) = (0.696, 0.696, 269/100)` of `t8certRowsExtP`, the only row with
`hi = v`.  Assuming instead `λ(ρ) ≤ v` and `λ(ρ₁) ≤ v`:

* the side condition `cond913 (λ(ρ₁)) (λ(ρ)) a K` follows from
  `cond913 v v a K` by monotonicity (both arguments are `≤ v`);
* HB Lemma 9.1 (9.13) gives `0 ≤ p913 (λ(ρ₁)) (λ(ρ)) a K + (a + λ(ρ₁)) ε`;
* `p913` is non-decreasing in both arguments, and `λ(ρ₁) ≤ v = hi ≤ v`, so with
  `ε = -p913 v v a K / (2(a+v)) > 0` the right hand side is bounded by
  `p913 v v a K + (a+v)ε = p913 v v a K / 2 < 0` — a contradiction.

(The general row lemma `lam0_row_of_lemma9_1_of_facts` cannot be reused directly:
its assumption is `λ(ρ) < v`, and its conclusion `v ≤ λ(ρ)` is precisely the
non-strict statement.  The only new ingredient is `hi = v`, which makes
`p913_mono_lam₁` available with `lam₁' = hi = v`.)
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.Table8CertPrinted
import Submission.Work.ZeroFreeTables.Table8CertExtPrinted
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.ZeroFreeTables.API

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The last printed row of Table 8 -/

/-- The last printed entry of HB Table 8, `(lo, hi, v, a) = (0.696, 0.696, 0.696, 269/100)`:
the only row with `hi = v`, i.e. the `λ₁ = λ₀` *tangency* row. -/
def t8lastRow : ℝ × ℝ × ℝ × ℝ := ((696/1000:ℝ), (696/1000:ℝ), (696/1000:ℝ), (269/100:ℝ))

theorem t8lastRow_mem : t8lastRow ∈ t8certRowsExtP := by
  simp only [t8lastRow, t8certRowsExtP, List.mem_cons, List.not_mem_nil, or_false]
  norm_num

/-- The certificate of `Table8CertExtPrinted` at the tangency row `t8lastRow`,
in the reduced form used below. -/
theorem t8lastRow_cert :
    cond913 ((696:ℝ)/1000) ((696:ℝ)/1000) ((269:ℝ)/100) (Kaff ((696:ℝ)/1000)) ∧
      p913 ((696:ℝ)/1000) ((696:ℝ)/1000) ((269:ℝ)/100) (Kaff ((696:ℝ)/1000)) < 0 :=
  Table8CertExtPrinted t8lastRow t8lastRow_mem

/-! ## The strict row lemma -/

/-- The strict form of `lam0_row_of_lemma9_1_of_facts` at a row with `hi = v`.

If (9.13) is certified *at the pair* `(v, v)` — i.e. `cond913 v v a (Kaff v)` holds
and `p913 v v a (Kaff v) < 0` — then below `λ₁ ≤ v` in the complex case every other
zero `ρ ≠ ρ₁` of `χ₁` (conjugate excluded when `χ₁` is real) satisfies
`v < λ(ρ)` strictly. -/
theorem lam0_strict_of_lemma9_1 (h9 : HBLemma9_1) {v a : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hK : 0 < Kaff v)
    (hcert : cond913 v v a (Kaff v) ∧ p913 v v a (Kaff v) < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → lamOf q ρ₁ ≤ v →
      ∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ →
        (χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) →
        v < lamOf q ρ := by
  obtain ⟨hcond, hp⟩ := hcert
  set ε : ℝ := -p913 v v a (Kaff v) / (2 * (a + v)) with hεdef
  have hεden : 0 < 2 * (a + v) := by linarith
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) hεden
  obtain ⟨q₀, hq₀⟩ := h9 a (Kaff v) ε ha hK hε
  refine ⟨q₀, ?_⟩
  intro q hq _ χ₁ ρ₁ hm hcx hlam ρ hZ hne hconj
  by_contra hlt
  push_neg at hlt
  have hmem : IsZ χ₁ ρ₁ := isMin1_isZ hm.1
  have hq2 : 2 ≤ q := two_le_modulus_of_char_ne_one (isZ_ne_one hmem)
  have hlam1nn : 0 ≤ lamOf q ρ₁ := Work.LinnikContract.API.isZ_lambda_nonneg hq2 hmem
  have hlam0nn : 0 ≤ lamOf q ρ := Work.LinnikContract.API.isZ_lambda_nonneg hq2 hZ
  have hcond' : cond913 (lamOf q ρ₁) (lamOf q ρ) a (Kaff v) := by
    have hKnn : 0 ≤ Kond (Kaff v) := le_of_lt (lt_min (by positivity) (by positivity))
    have h3 : Kond (Kaff v) / (a + v) ^ 3 ≤ Kond (Kaff v) / (a + lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left hKnn (pow_pos (by linarith) 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    have h4 : 1 / (a + v) ^ 3 ≤ 1 / (a + lamOf q ρ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos (by linarith) 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    unfold cond913 at hcond ⊢
    linarith
  have hineq := hq₀ q hq χ₁ ρ₁ ρ hm hcx hmem hZ hne.symm hconj hcond'
  have hineq' : 0 ≤ p913 (lamOf q ρ₁) (lamOf q ρ) a (Kaff v)
      + (a + lamOf q ρ₁) * ε := hineq
  have h1 : p913 (lamOf q ρ₁) (lamOf q ρ) a (Kaff v)
      ≤ p913 (lamOf q ρ₁) v a (Kaff v) :=
    p913_mono_lam₀ ha (by linarith) (by linarith) (by linarith) hlt
  have h2 : p913 (lamOf q ρ₁) v a (Kaff v) ≤ p913 v v a (Kaff v) :=
    p913_mono_lam₁ hlam1nn hlam le_rfl ha hK
  have hεval : (a + v) * ε = -(p913 v v a (Kaff v)) / 2 := by
    rw [hεdef]; field_simp
  have h5 : (a + lamOf q ρ₁) * ε ≤ (a + v) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', h1, h2, h5, hεval, hp]

/-- **The strict form of the last row of HB Table 8** (the frozen target). -/
theorem HBTable8StrictLast (h9 : Work.ZeroFreeTables.HBLemma9_1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      Work.LinnikContract.lamOf q ρ₁ ≤ 696/1000 →
      ∀ ρ : ℂ, Work.LinnikContract.IsZ χ₁ ρ → ρ ≠ ρ₁ →
        (χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) →
        (696 : ℝ)/1000 < Work.LinnikContract.lamOf q ρ := by
  obtain ⟨hcond, hp⟩ := t8lastRow_cert
  exact lam0_strict_of_lemma9_1 h9 (by norm_num) (by norm_num) (by norm_num [Kaff])
    ⟨hcond, hp⟩

end Work.ZeroFreeTables
