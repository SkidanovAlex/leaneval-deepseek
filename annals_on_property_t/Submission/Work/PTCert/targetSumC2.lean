import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.QAdjOpDefs
import Submission.Work.PTCert.QAdjOpSplit
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

/-! ## The integer and rational weights of a pair of edges

`adjOpZ` (`KernelCert.lean`) and `QAdjOp` (`Interfaces.lean`) are both double sums over the list
`QEdges 5` of edges of the 5-simplex, with weight `0` on the diagonal, `1` on adjacent pairs and
`kop` on opposite pairs, times the two edge coefficients; `adjOpZ` works with `cEdgeZ : ℤ` and
Boolean tests (`bif`, `==`), `QAdjOp` with `cEdge 5 : ℚ` and equalities. The two weight functions
below make both pictures readable. -/

/-- The integer weight of a pair of edges `(e,f)` in `adjOpZ`. -/
def WZ (kop : ℤ) (a b : ℕ) (e f : ℕ × ℕ) : ℤ :=
  bif (e == f) then (0 : ℤ) else
    (bif (e.1 == f.1 || e.1 == f.2 || e.2 == f.1 || e.2 == f.2) then (1 : ℤ) else kop) *
      cEdgeZ e a * cEdgeZ f b

/-- The rational weight of a pair of edges `(e,f)` in `QAdjOp` (for `r = 5`). -/
def WQ (kop : ℚ) (a b : ℕ) (e f : ℕ × ℕ) : ℚ :=
  if e = f then (0 : ℚ) else
    (if (e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2) then (1 : ℚ) else kop) *
      cEdge 5 e a * cEdge 5 f b

/-! ## Casting `adjOpZ` to `ℚ` -/

/-- Boolean equality on `ℕ × ℕ` is decidable equality. -/
lemma beq_prod_eq (e f : ℕ × ℕ) : ((e == f) : Bool) = decide (e = f) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq]

/-- The Boolean "shares a vertex" test is the corresponding disjunction. -/
lemma or_beq_eq (e f : ℕ × ℕ) :
    ((e.1 == f.1 || e.1 == f.2 || e.2 == f.1 || e.2 == f.2) : Bool)
      = decide (e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, or_assoc]

/-- `cEdgeZ` is the integer version of `cEdge 5`. -/
lemma cEdgeZ_cast (e : ℕ × ℕ) (a : ℕ) : ((cEdgeZ e a : ℤ) : ℚ) = cEdge 5 e a := by
  unfold cEdgeZ cEdge
  by_cases ha : a = 0
  · simp [Bool.cond_eq_ite, ha]
  · by_cases hE : edgeL 5 a = e
    · simp [Bool.cond_eq_ite, Nat.beq_eq, ha, hE]
    · simp [Bool.cond_eq_ite, Nat.beq_eq, ha, hE]

/-- The two weight functions agree after casting `ℤ → ℚ`. -/
lemma WZ_cast (kop : ℤ) (a b : ℕ) (e f : ℕ × ℕ) :
    ((WZ kop a b e f : ℤ) : ℚ) = WQ kop a b e f := by
  unfold WZ WQ
  rw [beq_prod_eq, or_beq_eq]
  simp only [Bool.cond_eq_ite, decide_eq_true_eq]
  by_cases h1 : e = f
  · simp only [if_pos h1]
    norm_num
  · simp only [if_neg h1]
    by_cases h2 : e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2
    · simp only [if_pos h2]
      push_cast [cEdgeZ_cast]
      ring_nf
    · simp only [if_neg h2]
      push_cast [cEdgeZ_cast]
      ring_nf

/-- Casting a nested `List.sum` termwise. -/
lemma intCast_nested_sum (l : List (ℕ × ℕ)) (G : ℕ × ℕ → ℕ × ℕ → ℤ)
    (H : ℕ × ℕ → ℕ × ℕ → ℚ) (h : ∀ e f, ((G e f : ℤ) : ℚ) = H e f) :
    (((l.map (fun e => (l.map (fun f => G e f)).sum)).sum : ℤ) : ℚ)
      = (l.map (fun e => (l.map (fun f => H e f)).sum)).sum := by
  rw [Int.cast_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]
  rw [Int.cast_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro f _
  simpa using h e f

/-- `adjOpZ` is the `ℚ`-valued double sum over the edges of the simplex. -/
lemma adjOpZ_cast_edges (kop : ℤ) (a b : ℕ) :
    ((adjOpZ kop a b : ℤ) : ℚ) =
      ((QEdges 5).map (fun e => ((QEdges 5).map (fun f => WQ kop a b e f)).sum)).sum := by
  unfold adjOpZ
  exact intCast_nested_sum (QEdges 5) _ _ (fun e f => WZ_cast kop a b e f)

/-- **The `Adj + k·Op` form over `ℤ` is the `ℚ`-valued form `QAdjOp`.** -/
theorem tsC2_adjOpZ_cast (kop : ℤ) (mu : ℚ) (a b : ℕ) :
    ((adjOpZ kop a b : ℤ) : ℚ) =
      (QAdjOp 5 (kop : ℚ) mu a b) +
        mu * ((if a = 0 then cDelta 5 b else 0) + (if b = 0 then cDelta 5 a else 0)) / 2 := by
  rw [adjOpZ_cast_edges kop a b, QAdjOp_eq_QEdges]
  simp only [WQ]
  ring

/-! ## The reindexing of `targetSum` and the monomials -/

/-- The number of letters of `SAut(F_5)`: `NB1 5 = 81`. -/
lemma tsC2_NB1 : NB1 5 = 81 := by norm_num [NB1]

/-- Reindexing a sum over `range (n * m)` as a double sum over `range n × range m`. -/
lemma tsC2_sum_range_mul {M : Type*} [AddCommMonoid M] (n m : ℕ) (f : ℕ → M) :
    ∑ p ∈ Finset.range (n * m), f p =
      ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, f (m * a + b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    simp only [Nat.mul_comm n m]

/-- The `C2` monomial identity: the word `[a⁻¹, b, 0, 0]` of the certificate is the letter pair
`(a, b)` of `gramL`. -/
lemma tsC2_mon (a b : ℕ) (ha : a < 81) :
    lprod 5 [invL a, b, 0, 0] = (b1 5 a)⁻¹ * b1 5 b := by
  have ha' : a < NB1 5 := by rw [tsC2_NB1]; exact ha
  have h := (letterAction 5).1 a ha'
  simp only [lprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [show b1 5 0 = 1 from by simp [b1]]
  rw [← h]
  simp only [mul_one]

/-! ## The coefficient identity -/

/-- Cast of one Laplacian contribution: `cDZ` is the integer version of `cDelta 5`. -/
lemma tsC2_cast_cond (a b : ℕ) :
    ((bif Nat.beq a 0 then cDZ b else 0 : ℤ) : ℚ)
      = (if a = 0 then cDelta 5 b else 0) := by
  by_cases ha : a = 0 <;>
    simp [Bool.cond_eq_ite, Nat.beq_eq, ha, cDZ, cDelta, NB1] <;>
    norm_num

/-- **The `C2` coefficient identity** (in `ℚ`): `qC2 (81 a + b) = 200 · QAdjOp 5 2 (7/25) a b`. -/
lemma tsC2_coefQ (a b : ℕ) (_ha : a < 81) (hb : b < 81) :
    ((qC2 (81 * a + b) : ℤ) : ℚ) / ((200 : ℤ) : ℚ) = QAdjOp 5 2 (7 / 25) a b := by
  have hdiv : (81 * a + b) / 81 = a := by
    rw [Nat.mul_add_div (by norm_num : 0 < 81), Nat.div_eq_of_lt hb, Nat.add_zero]
  have hmod : (81 * a + b) % 81 = b := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  simp only [qC2, hdiv, hmod]
  push_cast
  rw [tsC2_adjOpZ_cast 2 (7 / 25) a b, tsC2_cast_cond a b, tsC2_cast_cond b a]
  ring_nf

/-- The `C2` coefficient identity over `ℝ`. -/
lemma tsC2_coef (a b : ℕ) (_ha : a < 81) (hb : b < 81) :
    ((qC2 (81 * a + b) : ℤ) : ℝ) / ((200 : ℤ) : ℝ)
      = ((QAdjOp 5 2 (7 / 25) a b : ℚ) : ℝ) := by
  have h := tsC2_coefQ a b _ha hb
  have h' : ((((qC2 (81 * a + b) : ℤ) : ℚ) / ((200 : ℤ) : ℚ) : ℚ) : ℝ)
      = ((QAdjOp 5 2 (7 / 25) a b : ℚ) : ℝ) := by rw [h]
  push_cast at h'
  simpa using h'

/-- Termwise identity of the two descriptions of the `C2` target. -/
lemma tsC2_term (a b : ℕ) (ha : a < 81) (hb : b < 81) :
    (((qC2 (81 * a + b) : ℤ) : ℝ) / ((200 : ℤ) : ℝ)) •
        MonoidAlgebra.of ℝ G5 (lprod 5 [invL ((81 * a + b) / 81), (81 * a + b) % 81, 0, 0])
      = ((QAdjOp 5 2 (7 / 25) a b : ℚ) : ℝ) •
        MonoidAlgebra.of ℝ G5 ((b1 5 a)⁻¹ * b1 5 b) := by
  have hdiv : (81 * a + b) / 81 = a := by
    rw [Nat.mul_add_div (by norm_num : 0 < 81), Nat.div_eq_of_lt hb, Nat.add_zero]
  have hmod : (81 * a + b) % 81 = b := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [hdiv, hmod, tsC2_coef a b ha hb, tsC2_mon a b ha]

/-! ## The target identity -/

theorem targetSumC2 : targetSum qC2 200 = gramL 5 (QAdjOp 5 2 (7 / 25)) := by
  unfold targetSum gramL
  rw [tsC2_NB1]
  rw [show (6561 : ℕ) = 81 * 81 from by norm_num]
  rw [tsC2_sum_range_mul]
  exact Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb =>
    tsC2_term a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)))

end Work.PTCert
