/-
# ZeroFreeTables — Table4Cert

The rational certificate for **HB Table 4** (p. 43), together with the monotonicity
of the `P₃`-inequality (8.7) of Lemma 8.3 that lets the certificate at a right end
`λ₁ = hi` cover the whole interval `[lo, hi]`.

The certificate rows `(lo, hi, v, a, K)` mean: for `lo ≤ λ₁ ≤ hi`, with `λ₀ < v`,
with this `a` and `K`, the side condition (8.6) holds at `(hi, v)` and the left hand
side of (8.7) is *strictly negative* at `(hi, v)`; monotonicity in `λ₀` (always) and
in `λ₁` (from (8.8), which holds at `lo`) then gives the contradiction
`λ₀ < v ∧ (8.6) ∧ (8.7)`.  The witness values `a` are HB's own table values where
they can be used (the intervals `[0.3, 0.35], …, [1.275, 1.294]`); for the two
intervals covering `[0, 0.3]` (where HB's `a = 3.9` does not satisfy (8.8) at the
left end) explicit rational witnesses were found by exact arithmetic.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The certificate data -/

/-- Abbreviation for the certificate rows `(lo, hi, v, a, K)`. -/
abbrev T4Row := ℝ × ℝ × ℝ × ℝ × ℝ

/-- The left end of the interval of a certificate row. -/
abbrev T4lo (r : T4Row) : ℝ := r.1
/-- The right end. -/
abbrev T4hi (r : T4Row) : ℝ := r.2.1
/-- The target `λ₀ ≥ v`. -/
abbrev T4v (r : T4Row) : ℝ := r.2.2.1
/-- HB's parameter `a`. -/
abbrev T4a (r : T4Row) : ℝ := r.2.2.2.1
/-- HB's parameter `K`. -/
abbrev T4K (r : T4Row) : ℝ := r.2.2.2.2

/-- The certificate rows of Table 4: `(lo, hi, v, a, K)`.  The intervals cover
`[0, 1.294]` and the targets `v` decrease along the list, so that the first row
whose interval contains `λ₁` gives a `v` at least as large as any later one. -/
def t4certRows : List T4Row :=
  [((0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)),
   ((26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)),
   ((3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)),
   ((35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)),
   ((4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)),
   ((45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)),
   ((5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)),
   ((55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)),
   ((6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)),
   ((65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)),
   ((7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)),
   ((75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)),
   ((8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)),
   ((85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)),
   ((9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)),
   ((95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)),
   ((1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)),
   ((105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)),
   ((11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)),
   ((115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)),
   ((1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)),
   ((12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)),
   ((1225/1000 : ℝ), (125/100 : ℝ), (1318/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)),
   ((125/100 : ℝ), (1275/1000 : ℝ), (1304/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)),
   ((1275/1000 : ℝ), (1294/1000 : ℝ), (1294/1000 : ℝ), (5 : ℝ), (83/100 : ℝ))]

/-- **The certificate.**  Every row satisfies the elementary side conditions, the
(8.8) monotonicity condition at its left end, the side condition (8.6) at
`(hi, v)`, and the strict negativity of (8.7)'s left hand side at `(hi, v)`. -/
theorem t4certRows_facts : ∀ r ∈ t4certRows,
    0 < T4a r ∧ 0 < T4K r ∧ 1/4 ≤ T4K r ∧ 0 ≤ T4lo r ∧ T4lo r ≤ T4hi r ∧
    T4v r ≤ 2293/1000 ∧ T4hi r ≤ T4v r ∧
    cond88 (T4lo r) (T4a r) (T4K r) ∧ cond86 (T4hi r) (T4v r) (T4a r) ∧
    p83 (T4hi r) (T4v r) (T4a r) (T4K r) < 0 := by
  intro r hr
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    | h | h | h | h | h <;>
    · subst h
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, ?_, ?_, ?_⟩ <;> norm_num [cond88, cond86, p83, P3R]

/-! ## Monotonicity of (8.7) -/

/-- (8.7)'s left hand side is non-decreasing in `λ₀` (for `K ≥ 0`). -/
theorem p83_mono_lam₀ {lam₁ lam₀ lam₀' a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (h1 : -a < lam₁) (h2 : -a < lam₀) (h2' : -a < lam₀') (h : lam₀ ≤ lam₀') :
    p83 lam₁ lam₀ a K ≤ p83 lam₁ lam₀' a K := by
  have hden : 0 < a + lam₀ := by linarith
  have hden' : 0 < a + lam₀' := by linarith
  have hn : 0 < a + lam₁ := by linarith
  have hle : (a + lam₁) / (a + lam₀') ≤ (a + lam₁) / (a + lam₀) :=
    div_le_div_of_nonneg_left hn.le hden (by linarith)
  have hmono : P3R ((a + lam₁) / (a + lam₀')) ≤ P3R ((a + lam₁) / (a + lam₀)) :=
    P3R_mono hle
  have h2K : (0 : ℝ) ≤ 2 * K := by linarith
  have hmain : 2 * K * P3R ((a + lam₁) / (a + lam₀')) ≤ 2 * K * P3R ((a + lam₁) / (a + lam₀)) :=
    mul_le_mul_of_nonneg_left hmono h2K
  unfold p83
  linarith [hmain]

/-- `P₃(x') - P₃(x) ≥ (x'-x)(1+2x+2x²)` for `0 ≤ x ≤ x'`. -/
theorem P3R_sub_ge {x x' : ℝ} (h0 : 0 ≤ x) (hx : x ≤ x') :
    (x' - x) * (1 + 2 * x + 2 * x ^ 2) ≤ P3R x' - P3R x := by
  rw [P3R_sub_eq]
  have h1 : 0 ≤ x' - x := by linarith
  have h2 : 1 + 2 * x + 2 * x ^ 2 ≤ 1 + x' + x + (2/3) * (x'^2 + x'*x + x^2) := by nlinarith
  exact mul_le_mul_of_nonneg_left h2 h1

/-- `P₃(y') - P₃(y) ≤ 5(y'-y)` for `0 ≤ y ≤ y' ≤ 1`. -/
theorem P3R_sub_le {y y' : ℝ} (h0 : 0 ≤ y) (hy : y ≤ y') (hy1 : y' ≤ 1) :
    P3R y' - P3R y ≤ 5 * (y' - y) := by
  rw [P3R_sub_eq]
  have h1 : 0 ≤ y' - y := by linarith
  have h2 : 1 + y' + y + (2/3) * (y'^2 + y'*y + y^2) ≤ 5 := by nlinarith
  calc (y' - y) * (1 + y' + y + (2/3) * (y'^2 + y'*y + y^2)) ≤ (y' - y) * 5 :=
        mul_le_mul_of_nonneg_left h2 h1
    _ = 5 * (y' - y) := by ring

/-- (8.7)'s left hand side is non-decreasing in `λ₁`, under the monotonicity
condition (8.8) at the left end. -/
theorem p83_mono_lam₁ {lam₁ lam₁' lam₀ a K : ℝ} (h0 : 0 ≤ lam₁) (h : lam₁ ≤ lam₁')
    (h2 : lam₁' ≤ lam₀) (ha : 0 < a) (hK : 0 < K) (hc : cond88 lam₁ a K) :
    p83 lam₁ lam₀ a K ≤ p83 lam₁' lam₀ a K := by
  have ha1 : 0 < a + lam₁ := by linarith
  have hden : 0 < a + lam₀ := by linarith
  have hd0 : 0 ≤ lam₁' - lam₁ := by linarith
  have hx0 : 0 ≤ (a + lam₁) / a := div_nonneg (by linarith) ha.le
  have hxx : (a + lam₁) / a ≤ (a + lam₁') / a := div_le_div_of_nonneg_right (by linarith) ha.le
  have hy0 : 0 ≤ (a + lam₁) / (a + lam₀) := div_nonneg (by linarith) hden.le
  have hyy : (a + lam₁) / (a + lam₀) ≤ (a + lam₁') / (a + lam₀) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have hy1 : (a + lam₁') / (a + lam₀) ≤ 1 := by
    rw [div_le_one hden]; linarith
  have hA : (lam₁' - lam₁) / a * (1 + 2 * ((a + lam₁)/a) + 2 * ((a + lam₁)/a)^2)
      ≤ P3R ((a + lam₁')/a) - P3R ((a + lam₁)/a) := by
    have hxx' : (a + lam₁')/a - (a + lam₁)/a = (lam₁' - lam₁)/a := by field_simp; ring
    have := P3R_sub_ge hx0 hxx
    rwa [hxx'] at this
  have hB : P3R ((a + lam₁')/(a + lam₀)) - P3R ((a + lam₁)/(a + lam₀))
      ≤ 5 * ((lam₁' - lam₁) / (a + lam₁)) := by
    have hyy' : (a + lam₁')/(a + lam₀) - (a + lam₁)/(a + lam₀) = (lam₁' - lam₁)/(a + lam₀) := by
      field_simp; ring
    have h1 : P3R ((a + lam₁')/(a + lam₀)) - P3R ((a + lam₁)/(a + lam₀))
        ≤ 5 * ((a + lam₁')/(a + lam₀) - (a + lam₁)/(a + lam₀)) := by
      have := P3R_sub_le hy0 hyy hy1
      linarith [this]
    have h2 : (lam₁' - lam₁) / (a + lam₀) ≤ (lam₁' - lam₁) / (a + lam₁) :=
      div_le_div_of_nonneg_left hd0 ha1 (by linarith)
    rw [hyy'] at h1
    nlinarith [h1, h2]
  have hK2 : (0:ℝ) ≤ K^2 + 1/2 := by positivity
  have hmain : (K^2 + 1/2) * ((lam₁' - lam₁) / a * (1 + 2 * ((a + lam₁)/a) + 2 * ((a + lam₁)/a)^2))
      - 2 * K * (5 * ((lam₁' - lam₁) / (a + lam₁))) + (K + 1)^2 * (lam₁' - lam₁) / 8 ≤
      p83 lam₁' lam₀ a K - p83 lam₁ lam₀ a K := by
    have h1 : (K^2 + 1/2) * ((lam₁' - lam₁) / a * (1 + 2 * ((a + lam₁)/a) + 2 * ((a + lam₁)/a)^2))
        ≤ (K^2 + 1/2) * (P3R ((a + lam₁')/a) - P3R ((a + lam₁)/a)) :=
      mul_le_mul_of_nonneg_left hA hK2
    have h2 : 2 * K * (P3R ((a + lam₁')/(a + lam₀)) - P3R ((a + lam₁)/(a + lam₀)))
        ≤ 2 * K * (5 * ((lam₁' - lam₁) / (a + lam₁))) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    unfold p83
    linarith [h1, h2]
  have hcond : 0 ≤ (K^2 + 1/2) * ((lam₁' - lam₁) / a * (1 + 2 * ((a + lam₁)/a) + 2 * ((a + lam₁)/a)^2))
      - 2 * K * (5 * ((lam₁' - lam₁) / (a + lam₁))) + (K + 1)^2 * (lam₁' - lam₁) / 8 := by
    have hc' : ((K ^ 2 + 1/2) / a) * (1 + 2 * (a + lam₁) / a + 2 * ((a + lam₁) / a) ^ 2)
        + (K + 1) ^ 2 / 8 - 10 * K / (a + lam₁) ≥ 0 := by
      have := hc; unfold cond88 at this; linarith
    have hfac : (K^2 + 1/2) * ((lam₁' - lam₁) / a * (1 + 2 * ((a + lam₁)/a) + 2 * ((a + lam₁)/a)^2))
        - 2 * K * (5 * ((lam₁' - lam₁) / (a + lam₁))) + (K + 1)^2 * (lam₁' - lam₁) / 8
        = (lam₁' - lam₁) * (((K ^ 2 + 1/2) / a) * (1 + 2 * (a + lam₁) / a
            + 2 * ((a + lam₁) / a) ^ 2) + (K + 1) ^ 2 / 8 - 10 * K / (a + lam₁)) := by
      field_simp; ring
    rw [hfac]
    exact mul_nonneg hd0 hc'
  linarith [hmain, hcond]

/-- The side condition (8.6) is monotone: it becomes easier as `λ₁`, `λ₀` decrease. -/
theorem cond86_mono {l₁ l₁' l₀ l₀' a : ℝ} (h : cond86 l₁ l₀ a) (h1 : l₁' ≤ l₁) (h2 : l₀' ≤ l₀)
    (ha1 : 0 < a + l₁') (ha0 : 0 < a + l₀') : cond86 l₁' l₀' a := by
  have h₁ : 0 < a + l₁ := by linarith
  have h₀ : 0 < a + l₀ := by linarith
  have e1 : 1 / (a + l₁) ^ 3 ≤ 1 / (a + l₁') ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos ha1 3)
      (pow_le_pow_left₀ ha1.le (by linarith) 3)
  have e0 : 1 / (a + l₀) ^ 3 ≤ 1 / (a + l₀') ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos ha0 3)
      (pow_le_pow_left₀ ha0.le (by linarith) 3)
  unfold cond86 at h ⊢
  linarith

/-- The monotonicity condition (8.8) is monotone: it becomes easier as `λ₁` increases. -/
theorem cond88_mono_lam₁ {lam₁ lam₁' a K : ℝ} (h : cond88 lam₁ a K) (hle : lam₁ ≤ lam₁')
    (ha : 0 < a) (ha1 : 0 < a + lam₁) (hK : 0 < K) : cond88 lam₁' a K := by
  have hb : ((K^2 + 1/2)/a) * (1 + 2*(a+lam₁)/a + 2*((a+lam₁)/a)^2)
      ≤ ((K^2 + 1/2)/a) * (1 + 2*(a+lam₁')/a + 2*((a+lam₁')/a)^2) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) ha.le)
    have hu : (2 * (a + lam₁)) / a ≤ (2 * (a + lam₁')) / a :=
      div_le_div_of_nonneg_right (by linarith) ha.le
    have hsq : ((a + lam₁) / a) ^ 2 ≤ ((a + lam₁') / a) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (by linarith) ha.le)
        (div_le_div_of_nonneg_right (by linarith) ha.le) 2
    have h2 : 2 * ((a + lam₁) / a) ^ 2 ≤ 2 * ((a + lam₁') / a) ^ 2 := by linarith
    linarith
  have hr : 10*K/(a+lam₁') ≤ 10*K/(a+lam₁) :=
    div_le_div_of_nonneg_left (by linarith) ha1 (by linarith)
  unfold cond88 at h ⊢
  linarith

end Work.ZeroFreeTables
