/-
# ZeroFreeTables — Lam0Table7_of_table2and3

The `λ₀`-rows of **HB Table 7** for the character `χ₁` itself, derived from
**HB Tables 2 and 3** (`HBTable2and3`, the `F`-method of HB §7 with the optimal test
function) together with the closing row of **HB Table 4** (available in the workspace
as `HBTable4_proof`).

`Lam0Table7` says: for a real `χ₁` with real zero `ρ₁` (`IsMin1WideAt 10`, `χ₁ * χ₁ = 1`,
`ρ₁.im = 0`), every *other* zero `u` of `χ₁` with `|Im u| ≤ 1` satisfies `λ(u) ≥ p.2` for
every row `p` of HB Table 7 with `λ₁ ≤ p.1`.

Two analytic inputs cover the seventeen rows, split at `λ₁ = 2/5`:

* **`λ₁ ≤ 2/5`** — the ε-free half of `HBTable2and3` (Tables 2, 3) gives, for every other
  zero of the working region, `λ(u) ≥ max ((3/2) log (1/λ₁), 1.294)`;
* **`λ₁ ≥ 2/5`** — the last row `(1.294, 1.294)` of HB Table 4 (`HBTable4_proof`), applied
  at `λ₁ ≤ p.1 ≤ 745/1000 ≤ 1294/1000`, gives `λ(u) ≥ 1.294`.

The matching numerical fact about Table 7 is proved here as well (`table7_row_bound_max`):
every row `(b,c)` of the table satisfies `c ≤ max ((3/2) log (1/x)) 1.294` for every
`0 < x ≤ b`.  For the ten rows with `b ≤ 2/5` this is the elementary lower bound
`m log 2 + (1 - 2^m/r) ≤ log r` (`2^m ≤ r`) at `r = 1/b`; for the seven rows with
`b ≥ 2/5` it is just `c ≤ 1.294`.

The conversion of the `zeroMult`/`|Im| ≤ 1` hypotheses of `Lam0Table7` into the `IsZ`
hypotheses of `Lam0BoundOther` is immediate; the positivity `0 < λ₁` needed to compare
`log (1/λ₁)` with `log (1/p.1)` is `zeroMultStripPos` (the non-trivial zeros of a
non-principal character lie in the open critical strip).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_of_count
import Submission.Work.ZeroFreeTables.HBTable4_proof
import Submission.Work.ZeroFreeTables.HB8Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## Elementary analytic and numeric facts -/

/-- The conjugate of a complex number with zero imaginary part is itself. -/
lemma conj_eq_self_of_im_zero_lam0 {z : ℂ} (h : z.im = 0) : starRingEnd ℂ z = z := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, h]

/-- **Lower bound for `log`.**  For `2 ^ m ≤ r`,
`m · 0.6931471803 + (1 - 2^m/r) ≤ log r`, from `log 2 > 0.6931471803`
(`Real.log_two_gt_d9`) and `1 - 1/y ≤ log y` (`Real.one_sub_inv_le_log_of_pos`). -/
lemma log_ge_pow (m : ℕ) {r : ℝ} (hr : (2 : ℝ) ^ m ≤ r) :
    (m : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ m / r) ≤ Real.log r := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le h2 hr
  have hsplit : Real.log r = Real.log ((2 : ℝ) ^ m) + Real.log (r / (2 : ℝ) ^ m) := by
    rw [← Real.log_mul (by positivity) (ne_of_gt (div_pos hr0 h2))]
    congr 1
    field_simp
  rw [hsplit, Real.log_pow]
  have h1 : (m : ℝ) * 0.6931471803 ≤ (m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_gt_d9) (Nat.cast_nonneg m)
  have h2' : 1 - (r / (2 : ℝ) ^ m)⁻¹ ≤ Real.log (r / (2 : ℝ) ^ m) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hr0 h2)
  have h3 : (r / (2 : ℝ) ^ m)⁻¹ = (2 : ℝ) ^ m / r := by field_simp
  rw [h3] at h2'
  linarith

/-- The same bound for `log (1/x)`, from `2 ^ m ≤ r ≤ 1/x`. -/
lemma log_inv_ge (m : ℕ) {x r : ℝ} (hr : (2 : ℝ) ^ m ≤ r) (hrx : r ≤ 1 / x) :
    (m : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ m / r) ≤ Real.log (1 / x) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  exact le_trans (log_ge_pow m hr) (Real.log_le_log (lt_of_lt_of_le h2 hr) hrx)

/-! ## The numerical content of the seventeen rows of HB Table 7 -/

/-- **The rows of HB Table 7 versus `max ((3/2) log (1/x)) 1.294`.**  For every row
`p = (b,c)` of the table and every `0 < x ≤ b`, `c ≤ max ((3/2) log (1/x)) (1294/1000)`.

This is a finite computation: the ten rows with `b ≤ 2/5` are compared with
`(3/2) log (1/x) ≥ (3/2) log (1/b)` via the lower bounds of `log_inv_ge` at
`r = 1/b` (using `2^3 ≤ 10`, `2^3 ≤ 25/3`, `2^2 ≤ 50/7`, …), and the seven rows with
`b ≥ 2/5` satisfy `c ≤ 1.294 ≤ max …`. -/
theorem table7_row_bound_max :
    ∀ p ∈ tableR hbTable7, ∀ x : ℝ, 0 < x → x ≤ p.1 →
      p.2 ≤ max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) := by
  intro p hp x hx0 hxp
  simp only [tableR, hbTable7, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
    or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · -- `(0.10, 2.76)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 3 (x := x) (r := 1 / ((10 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((276 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((3 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 3 / (1 / ((10 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.12, 2.56)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 3 (x := x) (r := 1 / ((12 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((256 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((3 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 3 / (1 / ((12 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.14, 2.39)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 2 (x := x) (r := 1 / ((14 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((239 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((2 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 2 / (1 / ((14 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.16, 2.25)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 2 (x := x) (r := 1 / ((16 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((225 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((2 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 2 / (1 / ((16 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.18, 2.12)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 2 (x := x) (r := 1 / ((18 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((212 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((2 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 2 / (1 / ((18 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.20, 2.01)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 2 (x := x) (r := 1 / ((20 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((201 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((2 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 2 / (1 / ((20 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.25, 1.77)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 2 (x := x) (r := 1 / ((25 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((177 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((2 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 2 / (1 / ((25 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.30, 1.58)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 1 (x := x) (r := 1 / ((30 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((158 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((1 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 1 / (1 / ((30 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.35, 1.42)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 1 (x := x) (r := 1 / ((35 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((142 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((1 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 1 / (1 / ((35 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.40, 1.29)`
    refine le_trans ?_ (le_max_left _ _)
    have hrec := log_inv_ge 1 (x := x) (r := 1 / ((40 / 100 : ℚ) : ℝ)) (by norm_num)
      (one_div_le_one_div_of_le hx0 hxp)
    have hnum : ((129 / 100 : ℚ) : ℝ) ≤
        (3 / 2) * ((1 : ℝ) * 0.6931471803 + (1 - (2 : ℝ) ^ 1 / (1 / ((40 / 100 : ℚ) : ℝ)))) := by
      norm_num
    have hA := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  · -- `(0.45, 1.18)`
    refine le_trans ?_ (le_max_right _ _)
    norm_num
  · -- `(0.50, 1.08)`
    refine le_trans ?_ (le_max_right _ _)
    norm_num
  · -- `(0.55, 1.00)`
    refine le_trans ?_ (le_max_right _ _)
    norm_num
  · -- `(0.60, 0.92)`
    refine le_trans ?_ (le_max_right _ _)
    norm_num
  · -- `(0.65, 0.85)`
    refine le_trans ?_ (le_max_right _ _)
    norm_num
  · -- `(0.70, 0.79)`
    refine le_trans ?_ (le_max_right _ _)
    norm_num
  · -- `(0.745, 0.745)`
    refine le_trans ?_ (le_max_right _ _)
    norm_num

/-- **The tail of HB Table 7.**  Every row `(b,c)` with `b ≥ 2/5` satisfies `c ≤ 1.294`. -/
theorem table7_row_bound_big {p : ℝ × ℝ} (hp : p ∈ tableR hbTable7) (h : 2 / 5 ≤ p.1) :
    p.2 ≤ 1294 / 1000 := by
  simp only [tableR, hbTable7, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
    or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (try norm_num at h) <;> norm_num

/-! ## The main theorem -/

theorem Lam0Table7_of_table2and3 (h23 : Work.ZeroFreeTables.HBTable2and3)
    (lamS : ℝ) (hS : 0 < lamS) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ * χ₁ = 1 → ρ₁.im = 0 →
      lamS ≤ Work.LinnikContract.lamOf q ρ₁ →
      ∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable7,
        Work.LinnikContract.lamOf q ρ₁ ≤ p.1 →
        ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₁ →
          p.2 ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨Q23, h23'⟩ := h23 (1 / 2) (by norm_num) lamS hS
  obtain ⟨Q4, h4⟩ := HBTable4_proof
  refine ⟨max Q23 Q4, ?_⟩
  intro q hq hqne χ₁ ρ₁ hmin hsq him hSle p hp hlep u hzu himu hne
  have hq23 : Q23 ≤ q := le_trans (le_max_left _ _) hq
  have hq4 : Q4 ≤ q := le_trans (le_max_right _ _) hq
  have hχ1 : χ₁ ≠ 1 := hmin.1.1.1
  have hsq' : χ₁ ^ 2 = 1 := by rw [pow_two]; exact hsq
  -- `q ≥ 2`, since the only character of level `1` is principal
  have hq2 : 2 ≤ q := by
    have hq0 : q ≠ 0 := NeZero.ne q
    by_contra h
    have hq1 : q = 1 := by omega
    subst hq1
    exact hχ1 (MulChar.ext (fun x => by simp [Subsingleton.elim x 1]))
  -- the zero `ρ₁` of `χ₁` lies in the open critical strip, so `λ₁ > 0`
  have hstrip := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hmin.1.1.2.1
  have hlampos : 0 < lamOf q ρ₁ := hstrip.2.2
  have hZu : IsZ χ₁ u := ⟨hχ1, hzu, himu⟩
  -- `ρ₁` is real, so `u ≠ ρ₁` excludes the conjugate as well
  have hconj : χ₁ ^ 2 = 1 → u ≠ starRingEnd ℂ ρ₁ := by
    intro _
    rw [conj_eq_self_of_im_zero_lam0 him]
    exact hne
  rcases lt_or_ge (lamOf q ρ₁) (2 / 5) with hsmall | hbig
  · -- `λ₁ < 2/5`: the ε-free half of HB Tables 2 and 3
    have hb := (h23' q hq23 χ₁ ρ₁ hmin hsq' him hSle).2 (le_of_lt hsmall)
    have hle := hb u hZu hne hconj
    have hpm := table7_row_bound_max p hp (lamOf q ρ₁) hlampos hlep
    linarith
  · -- `λ₁ ≥ 2/5`: the closing row `(1.294, 1.294)` of HB Table 4
    have hlamle : lamOf q ρ₁ ≤ 1294 / 1000 :=
      le_trans hlep (le_trans (tableR_hbTable7_fst_le hp) (by norm_num))
    have hb := h4 q hq4 χ₁ ρ₁ hmin hsq' him ((1294 / 1000 : ℝ), (1294 / 1000 : ℝ))
      (by simp [tableR, hbTable4]) hlamle
    have hle : (1294 / 1000 : ℝ) ≤ lamOf q u := hb.2 u hZu hne hconj
    have hpc : p.2 ≤ 1294 / 1000 := table7_row_bound_big hp (le_trans hbig hlep)
    linarith

end Work.ZeroFreeTables
