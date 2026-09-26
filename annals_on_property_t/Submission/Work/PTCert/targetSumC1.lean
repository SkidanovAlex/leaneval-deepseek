import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.letterAction

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects and the semantic Props of the data) and
`Glue3.lean` (math steps), `KernelShared.lean`/`KernelCert.lean` (the Bool check functions), the data
modules `Data/*.lean` (namespace `Submission.PTCert.D`) and the kernel theorems `Checks/*.lean`
(namespace `Submission.PTCert.C`, each `theorem xxx : <check> = true := by decide +kernel`, ALREADY BUILT).
Design notes: `NOTES_LEAD_glue.md` at the workspace root.
HARD RULES: never `decide`/`native_decide`/`simp`/`rfl` over the big data definitions (eAll, eM, the trees,
the class lists …) — they are thousands of entries; all data facts come from the Checks theorems. The only
kernel evaluation you may add is `decide +kernel` on genuinely small facts (≤ a few hundred table lookups,
e.g. `ngL.getD 0 0 = 18`, 18 row codes, `eAll = eC0 ++ … ++ eC7` IS allowed as `by decide +kernel` only
if it runs in < 60 s — otherwise prove it by `rfl`/unfolding at the list level). Never edit Checks/, Data/,
Kernel*.lean, Glue*.lean. The soundness proofs are "unfold the Bool function, turn `&&`/`allL`/`allR`/
`Nat.beq`/`bif` into ∀/∧/=/if (lemmas: Bool.and_eq_true, Nat.beq_eq, List.all_eq_true-style lemmas you prove
for allL/allR/allIdx by induction), then instantiate". Write small reusable lemmas (e.g. `allL_iff`, `allR_iff`,
`allIdx_iff`, `eqL_iff`, `strictInc → Nodup/Sorted`) in your own helper file first.
targetSum q Dq = Σ_{p < 6561} (q p / Dq) • of (lprod 5 [invL (p/81), p % 81, 0, 0]) (Glue3.lean);
gramL 5 Q = Σ_{a < 81} Σ_{b < 81} (Q a b : ℝ) • of ((b1 5 a)⁻¹ * b1 5 b) (Interfaces.lean; NB1 5 = 81).
(1) Reindex p ↔ (a, b) = (p / 81, p % 81) (Finset.range 6561 ≃ range 81 × range 81; e.g. Finset.sum_product +
    Nat.div_add_mod, or `Finset.range_eq … ` with `Finset.sum_nbij`).
(2) lprod 5 [invL a, b, 0, 0] = b1 5 (invL a) * b1 5 b * b1 5 0 * b1 5 0 * 1 = (b1 5 a)⁻¹ * b1 5 b
    (b1 r 0 = 1 by definition; (letterAction 5).1 a ha : (b1 5 a)⁻¹ = b1 5 (invL a)).
(3) Coefficients: (q (81a+b) : ℝ) / Dq = ((Q a b : ℚ) : ℝ): pointwise for a, b < 81.
    C1: qC1 p = 20 * cDZ a * cDZ b - 13 * (…) (KernelCert.lean; cDZ a = if a = 0 then 80 else -1 via `bif Nat.beq`);
        QDelta 5 λ a b = cDelta 5 a * cDelta 5 b - λ * (…)/2 with cDelta 5 a = if a = 0 then NB1 5 - 1 = 80 else -1.
        Case split a = 0 / b = 0; push_cast; norm_num.
    C2: qC2 p = 200 * adjOpZ 2 a b - 28 * (…); adjOpZ mirrors QAdjOp's list expression over ℤ (same edges list,
        same `if` structure with `bif`/`==` instead of `if`/`=`; cEdgeZ ↔ cEdge 5); prove
        ((adjOpZ kop a b : ℤ) : ℚ) = the ℚ list expression by pushing Int.cast through List.sum/List.map
        (List.sum_map / Int.cast_list_sum-style lemmas and `congr`), then the μ-part: 200 * (7/25)/2 = 28.
        QAdjOpDefs.lean / QAdjOpSplit.lean contain useful rewrites of QAdjOp.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G
open scoped BigOperators

/-- The number of letters of `SAut(F_5)`: `NB1 5 = 81`. -/
lemma tsC1_NB1 : Submission.PTCert.NB1 5 = 81 := by norm_num [Submission.PTCert.NB1]

/-- Reindexing a sum over `range (n * m)` as a double sum over `range n × range m`. -/
lemma tsC1_sum_range_mul {M : Type*} [AddCommMonoid M] (n m : ℕ) (f : ℕ → M) :
    ∑ p ∈ Finset.range (n * m), f p =
      ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, f (m * a + b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    simp only [Nat.mul_comm n m]

/-- The `C1` coefficient identity: the integer coefficients `qC1` of the certificate agree with
`20·QDelta 5 (13/10)` on the letter pairs `< 81`. -/
lemma tsC1_coef (a b : ℕ) (ha : a < 81) (hb : b < 81) :
    ((Submission.PTCert.qC1 (81 * a + b) : ℤ) : ℝ) / ((20 : ℤ) : ℝ)
      = ((Submission.PTCert.QDelta 5 (13 / 10) a b : ℚ) : ℝ) := by
  have hdiv : (81 * a + b) / 81 = a := by
    rw [Nat.mul_add_div (by norm_num : 0 < 81), Nat.div_eq_of_lt hb, Nat.add_zero]
  have hmod : (81 * a + b) % 81 = b := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  simp only [Submission.PTCert.qC1, Submission.PTCert.cDZ, hdiv, hmod]
  cases a <;> cases b <;>
    simp only [Nat.beq, Submission.PTCert.QDelta, Submission.PTCert.cDelta, Submission.PTCert.NB1,
      cond] <;>
    norm_num

/-- The `C1` monomial identity: the word `[a⁻¹, b, 0, 0]` of the certificate is the letter pair
`(a, b)` of `gramL`. -/
lemma tsC1_mon (a b : ℕ) (ha : a < 81) (_hb : b < 81) :
    Submission.PTCert.lprod 5 [Submission.PTCert.invL a, b, 0, 0]
      = (Submission.PTCert.b1 5 a)⁻¹ * Submission.PTCert.b1 5 b := by
  have ha' : a < Submission.PTCert.NB1 5 := by rw [tsC1_NB1]; exact ha
  have h := (letterAction 5).1 a ha'
  simp only [Submission.PTCert.lprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [show Submission.PTCert.b1 5 0 = 1 from by simp [Submission.PTCert.b1]]
  rw [← h]
  simp only [mul_one]

/-- Termwise identity of the two descriptions of the `C1` target. -/
lemma tsC1_term (a b : ℕ) (ha : a < 81) (hb : b < 81) :
    (((Submission.PTCert.qC1 (81 * a + b) : ℤ) : ℝ) / ((20 : ℤ) : ℝ)) •
        MonoidAlgebra.of ℝ G5
          (Submission.PTCert.lprod 5 [Submission.PTCert.invL ((81 * a + b) / 81), (81 * a + b) % 81, 0, 0])
      = ((Submission.PTCert.QDelta 5 (13 / 10) a b : ℚ) : ℝ) •
        MonoidAlgebra.of ℝ G5 ((Submission.PTCert.b1 5 a)⁻¹ * Submission.PTCert.b1 5 b) := by
  have hdiv : (81 * a + b) / 81 = a := by
    rw [Nat.mul_add_div (by norm_num : 0 < 81), Nat.div_eq_of_lt hb, Nat.add_zero]
  have hmod : (81 * a + b) % 81 = b := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [hdiv, hmod, tsC1_coef a b ha hb, tsC1_mon a b ha hb]

theorem targetSumC1 : targetSum qC1 20 = gramL 5 (QDelta 5 (13 / 10)) := by
  unfold targetSum gramL
  rw [tsC1_NB1]
  rw [show (6561 : ℕ) = 81 * 81 from by norm_num]
  rw [tsC1_sum_range_mul]
  exact Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb =>
    tsC1_term a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)))

end Work.PTCert
