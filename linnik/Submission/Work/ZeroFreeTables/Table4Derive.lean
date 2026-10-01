/-
# ZeroFreeTables — Table4Derive

**HB Table 4** (p. 43) from the two engine inequalities of `Table4Defs` and the
rational certificate of `Table4Cert`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.Table4Cert
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.LinnikAreas.exists_minLam_zero

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## One certificate row + HB Lemma 8.3 -/

/-- **A certificate row of Table 4 at work.** -/
theorem lam0_row_of_hb83 (h83 : HBLemma8_3)
    (r : T4Row) (ha : 0 < T4a r) (hK : 0 < T4K r) (hK4 : 1/4 ≤ T4K r)
    (hlo0 : 0 ≤ T4lo r) (hlohi : T4lo r ≤ T4hi r) (hhiv : T4hi r ≤ T4v r)
    (hc88 : cond88 (T4lo r) (T4a r) (T4K r))
    (hc86 : cond86 (T4hi r) (T4v r) (T4a r))
    (hp83 : p83 (T4hi r) (T4v r) (T4a r) (T4K r) < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 → T4lo r ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ T4hi r → T4v r ≤ lamOf q ρ₀ := by
  set e : ℝ := -(p83 (T4hi r) (T4v r) (T4a r) (T4K r))
      / (2 * (T4K r + 1) ^ 2 * (T4a r + T4hi r)) with he
  have hden : 0 < 2 * (T4K r + 1) ^ 2 * (T4a r + T4hi r) := by
    have h1 : 0 < T4a r + T4hi r := by linarith
    positivity
  have hepos : 0 < e := by rw [he]; exact div_pos (by linarith) hden
  obtain ⟨q₀, hq₀⟩ := h83 (T4a r) (T4K r) e ha hK4 hepos
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ ρ₀ hw hsq hne him hZ₁ hZ₀ hne0 him0 hlo hhi => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlamnn : 0 ≤ lamOf q ρ₁ := le_trans hlo0 hlo
  have hlamle : lamOf q ρ₁ ≤ lamOf q ρ₀ :=
    hw.2 χ₁ ρ₀ hne hZ₀.2.1 (by linarith [hZ₀.2.2])
  have hcond : cond86 (lamOf q ρ₁) (lamOf q ρ₀) (T4a r) :=
    cond86_mono hc86 hhi hcon.le (by linarith) (by linarith)
  have hineq := hq₀ q hq χ₁ ρ₁ ρ₀ hw hsq hne him hZ₁ hZ₀ hne0 him0 hlamle hcond
  have hmono0 : p83 (lamOf q ρ₁) (lamOf q ρ₀) (T4a r) (T4K r)
      ≤ p83 (lamOf q ρ₁) (T4v r) (T4a r) (T4K r) :=
    p83_mono_lam₀ ha hK.le (by linarith) (by linarith) (by linarith) hcon.le
  have hc88' : cond88 (lamOf q ρ₁) (T4a r) (T4K r) :=
    cond88_mono_lam₁ hc88 hlo ha (by linarith) hK
  have hmono1 : p83 (lamOf q ρ₁) (T4v r) (T4a r) (T4K r)
      ≤ p83 (T4hi r) (T4v r) (T4a r) (T4K r) :=
    p83_mono_lam₁ hlamnn hhi hhiv ha hK hc88'
  have heval : (T4K r + 1) ^ 2 * (T4a r + T4hi r) * e
      = -(p83 (T4hi r) (T4v r) (T4a r) (T4K r)) / 2 := by
    rw [he]
    have h1 : (0:ℝ) < T4K r + 1 := by linarith
    have h2 : (0:ℝ) < T4a r + T4hi r := by linarith
    field_simp
  have hterm : (T4K r + 1) ^ 2 * (T4a r + lamOf q ρ₁) * e
      ≤ (T4K r + 1) ^ 2 * (T4a r + T4hi r) * e := by
    have h1 : 0 < (T4K r + 1) ^ 2 := by positivity
    have h2 : T4a r + lamOf q ρ₁ ≤ T4a r + T4hi r := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h1.le) hepos.le
  linarith [hineq, hmono0, hmono1, heval, hterm, hp83]

/-! ## The real second zero and the repeated zero: HB Lemma 8.2 -/

/-- The real case of a certificate row, from HB Lemma 8.2. -/
theorem lam0_row_real_of_hb82 (h82 : HBLemma8_2) (r : T4Row) (hv : T4v r ≤ 2293/1000) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im = 0 →
      (∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q ρ) → T4v r ≤ lamOf q ρ₀ := by
  obtain ⟨q₀, hq₀⟩ := h82
  exact ⟨q₀, fun q hq _ χ₁ ρ₁ ρ₀ hw hsq hne him hZ₁ hZ₀ hne0 him0 hmax =>
    le_trans hv ((hq₀ q hq χ₁ ρ₁ hw hsq hne him hZ₁).2 ρ₀ hZ₀ hne0 him0 hmax)⟩

/-- The repeated-zero case (`2 ≤ zeroMult χ₁ ρ₁`) of HB 6, from HB Lemma 8.2. -/
theorem lam1_mult_of_hb82 (h82 : HBLemma8_2) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ →
      2 ≤ zeroMult χ₁ ρ₁ → 2293/1000 ≤ lamOf q ρ₁ := by
  obtain ⟨q₀, hq₀⟩ := h82
  exact ⟨q₀, fun q hq _ χ₁ ρ₁ hw hsq hne him hZ₁ hm =>
    (hq₀ q hq χ₁ ρ₁ hw hsq hne him hZ₁).1 hm⟩

/-! ## The certificate rows as explicit members -/

/-- Row 1 of the certificate list. -/
theorem memT4_1 : (⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 2 of the certificate list. -/
theorem memT4_2 : (⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 3 of the certificate list. -/
theorem memT4_3 : (⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 4 of the certificate list. -/
theorem memT4_4 : (⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 5 of the certificate list. -/
theorem memT4_5 : (⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 6 of the certificate list. -/
theorem memT4_6 : (⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 7 of the certificate list. -/
theorem memT4_7 : (⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 8 of the certificate list. -/
theorem memT4_8 : (⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 9 of the certificate list. -/
theorem memT4_9 : (⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 10 of the certificate list. -/
theorem memT4_10 : (⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 11 of the certificate list. -/
theorem memT4_11 : (⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 12 of the certificate list. -/
theorem memT4_12 : (⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 13 of the certificate list. -/
theorem memT4_13 : (⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 14 of the certificate list. -/
theorem memT4_14 : (⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 15 of the certificate list. -/
theorem memT4_15 : (⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 16 of the certificate list. -/
theorem memT4_16 : (⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 17 of the certificate list. -/
theorem memT4_17 : (⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 18 of the certificate list. -/
theorem memT4_18 : (⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 19 of the certificate list. -/
theorem memT4_19 : (⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 20 of the certificate list. -/
theorem memT4_20 : (⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 21 of the certificate list. -/
theorem memT4_21 : (⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 22 of the certificate list. -/
theorem memT4_22 : (⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 23 of the certificate list. -/
theorem memT4_23 : (⟨(1225/1000 : ℝ), (125/100 : ℝ), (1318/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 24 of the certificate list. -/
theorem memT4_24 : (⟨(125/100 : ℝ), (1275/1000 : ℝ), (1304/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-- Row 25 of the certificate list. -/
theorem memT4_25 : (⟨(1275/1000 : ℝ), (1294/1000 : ℝ), (1294/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ : T4Row) ∈ t4certRows := by
  simp only [t4certRows, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

/-! ## The cover of `[0, 1.294]` and the table's λ₀-bound -/

/-- Every row of `tableR hbTable4` has its second component at most `2293/1000`. -/
theorem t4_mem_le_max (p : ℝ × ℝ) (hp : p ∈ tableR hbTable4) : p.2 ≤ 2293/1000 := by
  simp only [tableR, hbTable4, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    | h | h | h | h <;>
    · rw [h]; norm_num

/-- **The λ₀-bound of HB Table 4**, above one threshold: every entry `p` of Table 4
gives `p.2 ≤ λ(ρ)` for every zero `ρ` of the working region (other than `ρ₁` and its
conjugate), and the repeated-zero bound `λ₁ ≥ 2.293`. -/
theorem t4_cover (h83 : HBLemma8_3) (h82 : HBLemma8_2) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ →
      (2 ≤ zeroMult χ₁ ρ₁ → 2293/1000 ≤ lamOf q ρ₁) ∧
      ∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → (χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) →
        ∀ p : ℝ × ℝ, p ∈ tableR hbTable4 → lamOf q ρ₁ ≤ p.1 → p.2 ≤ lamOf q ρ := by
  obtain ⟨Nc, hNc⟩ := exists_threshold_of_forall_mem t4certRows
    (fun r N => ∀ (q : ℕ), N ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 → T4lo r ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ T4hi r → T4v r ≤ lamOf q ρ₀)
    (fun r hr => by
      obtain ⟨ha, hK, hK4, hlo0, hlohi, hv, hhiv, hc88, hc86, hp83⟩ := t4certRows_facts r hr
      exact lam0_row_of_hb83 h83 r ha hK hK4 hlo0 hlohi hhiv hc88 hc86 hp83)
    (fun r hr n n' hn hpn q hq => hpn q (le_trans hn hq))
  obtain ⟨Nr, hNr⟩ := exists_threshold_of_forall_mem t4certRows
    (fun r N => ∀ (q : ℕ), N ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im = 0 → (∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q ρ) →
      T4v r ≤ lamOf q ρ₀)
    (fun r hr => by
      obtain ⟨ha, hK, hK4, hlo0, hlohi, hv, hhiv, hc88, hc86, hp83⟩ := t4certRows_facts r hr
      exact lam0_row_real_of_hb82 h82 r hv)
    (fun r hr n n' hn hpn q hq => hpn q (le_trans hn hq))
  obtain ⟨Nm, hNm⟩ := lam1_mult_of_hb82 h82
  refine ⟨max (max Nc Nr) Nm, ?_⟩
  intro q hq _ χ₁ ρ₁ hw hsq hne him hZ₁
  have hNcq : Nc ≤ q := by omega
  have hNrq : Nr ≤ q := by omega
  have hNmq : Nm ≤ q := by omega
  constructor
  · intro hm
    exact hNm q hNmq χ₁ ρ₁ hw hsq hne him hZ₁ hm
  · intro ρ hZρ hneρ hconj p hp hL
    have hpmax : p.2 ≤ 2293/1000 := t4_mem_le_max p hp
    obtain ⟨u, huz, hue, huim, hule, hmin⟩ :=
      Work.LinnikAreas.exists_minLam_zero χ₁ hne ρ₁ ρ 1 hZρ.2.1 hZρ.2.2 hneρ
    have hZu : IsZ χ₁ u := ⟨hne, huz, huim⟩
    have hmaxu : ∀ z : ℂ, IsZ χ₁ z → z ≠ ρ₁ → lamOf q u ≤ lamOf q z := by
      intro z hZz hz
      by_cases hzle : lamOf q z ≤ lamOf q ρ
      · exact hmin z hZz.2.1 hz hZz.2.2 hzle
      · push_neg at hzle
        linarith
    have hq2 : 2 ≤ q := two_le_modulus_of_char_ne_one (isZ_ne_one hZ₁)
    have hL0 : 0 ≤ lamOf q ρ₁ := Work.LinnikContract.API.isZ_lambda_nonneg hq2 hZ₁
    by_cases hu0 : u.im = 0
    · have h82u : 2293/1000 ≤ lamOf q u :=
        (hNr ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩
          memT4_1 q hNrq χ₁ ρ₁ u hw hsq hne him hZ₁ hZu hue hu0 hmaxu)
      linarith
    · have step : ∀ (r : T4Row) (hr : r ∈ t4certRows), T4lo r ≤ lamOf q ρ₁ →
          lamOf q ρ₁ ≤ T4hi r → T4v r ≤ lamOf q u :=
        fun r hr h1 h2 => hNc r hr q hNcq χ₁ ρ₁ u hw hsq hne him hZ₁ hZu hue hu0 h1 h2
      simp only [tableR, hbTable4, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        | h | h | h | h
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        · linarith [h2, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        · linarith [h3, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        · linarith [h4, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        · linarith [h5, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        · linarith [h6, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        · linarith [h7, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        · linarith [h8, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        · linarith [h9, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        · linarith [h10, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        · linarith [h11, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        · linarith [h12, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        · linarith [h13, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        · linarith [h14, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        · linarith [h15, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        · linarith [h16, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        · linarith [h17, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        by_cases h18 : lamOf q ρ₁ ≤ (11/10 : ℝ)
        · have hstep : T4v ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_18 (by linarith [h17]) h18
          linarith [hstep, hule]
        · linarith [h18, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        by_cases h18 : lamOf q ρ₁ ≤ (11/10 : ℝ)
        · have hstep : T4v ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_18 (by linarith [h17]) h18
          linarith [hstep, hule]
        by_cases h19 : lamOf q ρ₁ ≤ (115/100 : ℝ)
        · have hstep : T4v ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_19 (by linarith [h18]) h19
          linarith [hstep, hule]
        · linarith [h19, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        by_cases h18 : lamOf q ρ₁ ≤ (11/10 : ℝ)
        · have hstep : T4v ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_18 (by linarith [h17]) h18
          linarith [hstep, hule]
        by_cases h19 : lamOf q ρ₁ ≤ (115/100 : ℝ)
        · have hstep : T4v ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_19 (by linarith [h18]) h19
          linarith [hstep, hule]
        by_cases h20 : lamOf q ρ₁ ≤ (1175/1000 : ℝ)
        · have hstep : T4v ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_20 (by linarith [h19]) h20
          linarith [hstep, hule]
        · linarith [h20, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        by_cases h18 : lamOf q ρ₁ ≤ (11/10 : ℝ)
        · have hstep : T4v ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_18 (by linarith [h17]) h18
          linarith [hstep, hule]
        by_cases h19 : lamOf q ρ₁ ≤ (115/100 : ℝ)
        · have hstep : T4v ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_19 (by linarith [h18]) h19
          linarith [hstep, hule]
        by_cases h20 : lamOf q ρ₁ ≤ (1175/1000 : ℝ)
        · have hstep : T4v ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_20 (by linarith [h19]) h20
          linarith [hstep, hule]
        by_cases h21 : lamOf q ρ₁ ≤ (12/10 : ℝ)
        · have hstep : T4v ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ memT4_21 (by linarith [h20]) h21
          linarith [hstep, hule]
        · linarith [h21, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        by_cases h18 : lamOf q ρ₁ ≤ (11/10 : ℝ)
        · have hstep : T4v ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_18 (by linarith [h17]) h18
          linarith [hstep, hule]
        by_cases h19 : lamOf q ρ₁ ≤ (115/100 : ℝ)
        · have hstep : T4v ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_19 (by linarith [h18]) h19
          linarith [hstep, hule]
        by_cases h20 : lamOf q ρ₁ ≤ (1175/1000 : ℝ)
        · have hstep : T4v ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_20 (by linarith [h19]) h20
          linarith [hstep, hule]
        by_cases h21 : lamOf q ρ₁ ≤ (12/10 : ℝ)
        · have hstep : T4v ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ memT4_21 (by linarith [h20]) h21
          linarith [hstep, hule]
        by_cases h22 : lamOf q ρ₁ ≤ (1225/1000 : ℝ)
        · have hstep : T4v ⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_22 (by linarith [h21]) h22
          linarith [hstep, hule]
        · linarith [h22, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        by_cases h18 : lamOf q ρ₁ ≤ (11/10 : ℝ)
        · have hstep : T4v ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_18 (by linarith [h17]) h18
          linarith [hstep, hule]
        by_cases h19 : lamOf q ρ₁ ≤ (115/100 : ℝ)
        · have hstep : T4v ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_19 (by linarith [h18]) h19
          linarith [hstep, hule]
        by_cases h20 : lamOf q ρ₁ ≤ (1175/1000 : ℝ)
        · have hstep : T4v ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_20 (by linarith [h19]) h20
          linarith [hstep, hule]
        by_cases h21 : lamOf q ρ₁ ≤ (12/10 : ℝ)
        · have hstep : T4v ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ memT4_21 (by linarith [h20]) h21
          linarith [hstep, hule]
        by_cases h22 : lamOf q ρ₁ ≤ (1225/1000 : ℝ)
        · have hstep : T4v ⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_22 (by linarith [h21]) h22
          linarith [hstep, hule]
        by_cases h23 : lamOf q ρ₁ ≤ (125/100 : ℝ)
        · have hstep : T4v ⟨(1225/1000 : ℝ), (125/100 : ℝ), (1318/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1225/1000 : ℝ), (125/100 : ℝ), (1318/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_23 (by linarith [h22]) h23
          linarith [hstep, hule]
        · linarith [h23, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        by_cases h18 : lamOf q ρ₁ ≤ (11/10 : ℝ)
        · have hstep : T4v ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_18 (by linarith [h17]) h18
          linarith [hstep, hule]
        by_cases h19 : lamOf q ρ₁ ≤ (115/100 : ℝ)
        · have hstep : T4v ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_19 (by linarith [h18]) h19
          linarith [hstep, hule]
        by_cases h20 : lamOf q ρ₁ ≤ (1175/1000 : ℝ)
        · have hstep : T4v ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_20 (by linarith [h19]) h20
          linarith [hstep, hule]
        by_cases h21 : lamOf q ρ₁ ≤ (12/10 : ℝ)
        · have hstep : T4v ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ memT4_21 (by linarith [h20]) h21
          linarith [hstep, hule]
        by_cases h22 : lamOf q ρ₁ ≤ (1225/1000 : ℝ)
        · have hstep : T4v ⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_22 (by linarith [h21]) h22
          linarith [hstep, hule]
        by_cases h23 : lamOf q ρ₁ ≤ (125/100 : ℝ)
        · have hstep : T4v ⟨(1225/1000 : ℝ), (125/100 : ℝ), (1318/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1225/1000 : ℝ), (125/100 : ℝ), (1318/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_23 (by linarith [h22]) h23
          linarith [hstep, hule]
        by_cases h24 : lamOf q ρ₁ ≤ (1275/1000 : ℝ)
        · have hstep : T4v ⟨(125/100 : ℝ), (1275/1000 : ℝ), (1304/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(125/100 : ℝ), (1275/1000 : ℝ), (1304/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_24 (by linarith [h23]) h24
          linarith [hstep, hule]
        · linarith [h24, hL]
      · rw [h] at hL ⊢
        by_cases h1 : lamOf q ρ₁ ≤ (26/100 : ℝ)
        · have hstep : T4v ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(0 : ℝ), (26/100 : ℝ), (2293/1000 : ℝ), (41/10 : ℝ), (116/100 : ℝ)⟩ memT4_1 (by linarith [hL0]) h1
          linarith [hstep, hule]
        by_cases h2 : lamOf q ρ₁ ≤ (3/10 : ℝ)
        · have hstep : T4v ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(26/100 : ℝ), (3/10 : ℝ), (2293/1000 : ℝ), (19/5 : ℝ), (22/25 : ℝ)⟩ memT4_2 (by linarith [h1]) h2
          linarith [hstep, hule]
        by_cases h3 : lamOf q ρ₁ ≤ (35/100 : ℝ)
        · have hstep : T4v ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(3/10 : ℝ), (35/100 : ℝ), (2195/1000 : ℝ), (4 : ℝ), (88/100 : ℝ)⟩ memT4_3 (by linarith [h2]) h3
          linarith [hstep, hule]
        by_cases h4 : lamOf q ρ₁ ≤ (4/10 : ℝ)
        · have hstep : T4v ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(35/100 : ℝ), (4/10 : ℝ), (2108/1000 : ℝ), (41/10 : ℝ), (88/100 : ℝ)⟩ memT4_4 (by linarith [h3]) h4
          linarith [hstep, hule]
        by_cases h5 : lamOf q ρ₁ ≤ (45/100 : ℝ)
        · have hstep : T4v ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(4/10 : ℝ), (45/100 : ℝ), (2030/1000 : ℝ), (42/10 : ℝ), (87/100 : ℝ)⟩ memT4_5 (by linarith [h4]) h5
          linarith [hstep, hule]
        by_cases h6 : lamOf q ρ₁ ≤ (5/10 : ℝ)
        · have hstep : T4v ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(45/100 : ℝ), (5/10 : ℝ), (1958/1000 : ℝ), (43/10 : ℝ), (87/100 : ℝ)⟩ memT4_6 (by linarith [h5]) h6
          linarith [hstep, hule]
        by_cases h7 : lamOf q ρ₁ ≤ (55/100 : ℝ)
        · have hstep : T4v ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(5/10 : ℝ), (55/100 : ℝ), (1893/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_7 (by linarith [h6]) h7
          linarith [hstep, hule]
        by_cases h8 : lamOf q ρ₁ ≤ (6/10 : ℝ)
        · have hstep : T4v ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(55/100 : ℝ), (6/10 : ℝ), (1832/1000 : ℝ), (44/10 : ℝ), (86/100 : ℝ)⟩ memT4_8 (by linarith [h7]) h8
          linarith [hstep, hule]
        by_cases h9 : lamOf q ρ₁ ≤ (65/100 : ℝ)
        · have hstep : T4v ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(6/10 : ℝ), (65/100 : ℝ), (1776/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_9 (by linarith [h8]) h9
          linarith [hstep, hule]
        by_cases h10 : lamOf q ρ₁ ≤ (7/10 : ℝ)
        · have hstep : T4v ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(65/100 : ℝ), (7/10 : ℝ), (1724/1000 : ℝ), (45/10 : ℝ), (85/100 : ℝ)⟩ memT4_10 (by linarith [h9]) h10
          linarith [hstep, hule]
        by_cases h11 : lamOf q ρ₁ ≤ (75/100 : ℝ)
        · have hstep : T4v ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(7/10 : ℝ), (75/100 : ℝ), (1676/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_11 (by linarith [h10]) h11
          linarith [hstep, hule]
        by_cases h12 : lamOf q ρ₁ ≤ (8/10 : ℝ)
        · have hstep : T4v ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(75/100 : ℝ), (8/10 : ℝ), (1630/1000 : ℝ), (46/10 : ℝ), (84/100 : ℝ)⟩ memT4_12 (by linarith [h11]) h12
          linarith [hstep, hule]
        by_cases h13 : lamOf q ρ₁ ≤ (85/100 : ℝ)
        · have hstep : T4v ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(8/10 : ℝ), (85/100 : ℝ), (1587/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_13 (by linarith [h12]) h13
          linarith [hstep, hule]
        by_cases h14 : lamOf q ρ₁ ≤ (9/10 : ℝ)
        · have hstep : T4v ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(85/100 : ℝ), (9/10 : ℝ), (1547/1000 : ℝ), (47/10 : ℝ), (84/100 : ℝ)⟩ memT4_14 (by linarith [h13]) h14
          linarith [hstep, hule]
        by_cases h15 : lamOf q ρ₁ ≤ (95/100 : ℝ)
        · have hstep : T4v ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(9/10 : ℝ), (95/100 : ℝ), (1509/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_15 (by linarith [h14]) h15
          linarith [hstep, hule]
        by_cases h16 : lamOf q ρ₁ ≤ (1 : ℝ)
        · have hstep : T4v ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(95/100 : ℝ), (1 : ℝ), (1473/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_16 (by linarith [h15]) h16
          linarith [hstep, hule]
        by_cases h17 : lamOf q ρ₁ ≤ (105/100 : ℝ)
        · have hstep : T4v ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1 : ℝ), (105/100 : ℝ), (1439/1000 : ℝ), (48/10 : ℝ), (83/100 : ℝ)⟩ memT4_17 (by linarith [h16]) h17
          linarith [hstep, hule]
        by_cases h18 : lamOf q ρ₁ ≤ (11/10 : ℝ)
        · have hstep : T4v ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(105/100 : ℝ), (11/10 : ℝ), (1406/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_18 (by linarith [h17]) h18
          linarith [hstep, hule]
        by_cases h19 : lamOf q ρ₁ ≤ (115/100 : ℝ)
        · have hstep : T4v ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(11/10 : ℝ), (115/100 : ℝ), (1375/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_19 (by linarith [h18]) h19
          linarith [hstep, hule]
        by_cases h20 : lamOf q ρ₁ ≤ (1175/1000 : ℝ)
        · have hstep : T4v ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(115/100 : ℝ), (1175/1000 : ℝ), (1360/1000 : ℝ), (49/10 : ℝ), (83/100 : ℝ)⟩ memT4_20 (by linarith [h19]) h20
          linarith [hstep, hule]
        by_cases h21 : lamOf q ρ₁ ≤ (12/10 : ℝ)
        · have hstep : T4v ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1175/1000 : ℝ), (12/10 : ℝ), (1346/1000 : ℝ), (495/100 : ℝ), (83/100 : ℝ)⟩ memT4_21 (by linarith [h20]) h21
          linarith [hstep, hule]
        by_cases h22 : lamOf q ρ₁ ≤ (1225/1000 : ℝ)
        · have hstep : T4v ⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(12/10 : ℝ), (1225/1000 : ℝ), (1331/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_22 (by linarith [h21]) h22
          linarith [hstep, hule]
        by_cases h23 : lamOf q ρ₁ ≤ (125/100 : ℝ)
        · have hstep : T4v ⟨(1225/1000 : ℝ), (125/100 : ℝ), (1318/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1225/1000 : ℝ), (125/100 : ℝ), (1318/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_23 (by linarith [h22]) h23
          linarith [hstep, hule]
        by_cases h24 : lamOf q ρ₁ ≤ (1275/1000 : ℝ)
        · have hstep : T4v ⟨(125/100 : ℝ), (1275/1000 : ℝ), (1304/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(125/100 : ℝ), (1275/1000 : ℝ), (1304/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_24 (by linarith [h23]) h24
          linarith [hstep, hule]
        by_cases h25 : lamOf q ρ₁ ≤ (1294/1000 : ℝ)
        · have hstep : T4v ⟨(1275/1000 : ℝ), (1294/1000 : ℝ), (1294/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ ≤ lamOf q u :=
            step ⟨(1275/1000 : ℝ), (1294/1000 : ℝ), (1294/1000 : ℝ), (5 : ℝ), (83/100 : ℝ)⟩ memT4_25 (by linarith [h24]) h25
          linarith [hstep, hule]
        · linarith [h25, hL]
/-! ## HB Table 4 -/

/-- **HB Table 4** from the two engine inequalities. -/
theorem hbTable4_of_engines (h83 : HBLemma8_3) (h82 : HBLemma8_2) : HBTable4 := by
  obtain ⟨q₀, hq₀⟩ := t4_cover h83 h82
  refine ⟨max q₀ 2, ?_⟩
  intro q hq _ χ₁ ρ₁ hw hsq him p hp hL
  have hq₀' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hZ₁ : IsZ χ₁ ρ₁ := isMin1_isZ hw.1
  obtain ⟨hmult, hbound⟩ := hq₀ q hq₀' χ₁ ρ₁ hw hsq hZ₁.1 him hZ₁
  constructor
  · intro hm
    exact le_trans (t4_mem_le_max p hp) (hmult hm)
  · intro ρ hZρ hneρ hconj
    exact hbound ρ hZρ hneρ hconj p hp hL

end Work.ZeroFreeTables
