import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.ldlScaledPrinciple
import Submission.Work.PTCert.ldlChainSound.dotZ_eq_sum_range
import Submission.Work.PTCert.ldlChainSound.dotZ_comm
import Submission.Work.PTCert.ldlChainSound.sum_univ_erase_eq
import Submission.Work.PTCert.ldlChainSound.ldlRowStep_spec

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/GlueDefs.lean` (definitions + Props; read it first) glues the
kernel-checked certificate data to the proved generic chain (`Chain.lean`, `Math.lean`,
`Interfaces.lean`; all their Props are already PROVED: avgPrinciple, labelPrinciple, gramSOS,
avgGram, avgMatInvariant, rowFormula, psdOfBlock, psdSignedPerm, ldlScaledPrinciple,
twistedFourierCriterion, residualAbsorption, letterAction, signCodes8, sigmaGroupFacts, modelSound,
permCheckKSound, ...). The design note is `NOTES_LEAD_glue.md` at the workspace root.
Do NOT change GlueDefs.lean. If the statement is false, `declare_false` with a concrete counterexample.
Put helper lemmas in your own file or under `Submission/Work/PTCert/<yourLemma>/`.
Goal: PSD of the real matrix B from the kernel row steps. Use `ldlScaledPrinciple` (Chain.lean
Prop `LdlScaledPrinciple`, PROVED in ldlScaledPrinciple.lean): with w_i > 0,
diag(w) M diag(w) = L Lᵀ + R, R symmetric, diagonally dominant with R_ii ≥ Σ_{j≠i} |R_ij| ⇒ M PSD.
Define L i t := ((C i).getD t 0 : ℝ) (zero for t > i since length ≤ i+1), and
R i j := w i * w j * B i j - Σ_t L i t * L j t (symmetric since B symmetric).
Unfold `ldlRowStep` (KernelCert.lean): for row i, rs[d] = w i * w (i+d) * B i (i+d) - dotZ (C i) (C (i+d))
and dotZ (C i) (C j) = Σ_{t ≤ i} (C i)[t] (C j)[t] (zipWith truncates at length(C i) ≤ i+1 ≤ length? —
careful: zipWith truncates at the SHORTER list; for j ≥ i, missing entries are zeros of L, so dotZ = Σ_t L i t * L j t
as long as you treat getD beyond length as 0). So rs[d] = R i (i+d) (as integers).
Invariant (induction on i): acc i has length n - i and acc i [c] = Σ_{j < i} |R j (i + c)|.
Row i check: acc i [0] + Σ_{d ≥ 1} |R i (i+d)| ≤ R i i, i.e. Σ_{j<i} |R j i| + Σ_{j>i} |R i j| ≤ R i i, which is
diagonal dominance by symmetry of R. Work over ℤ first, then cast to ℝ (Int.cast_sum, Int.cast_abs).

## Solution

Everything is assembled here from four helper lemmas (one module each under
`Submission/Work/PTCert/ldlChainSound/`):

* `dotZ_eq_sum_range` : the integer dot product of two lists is the `range n` sum of the products of
  the entries read with `getD` (zero padding);
* `dotZ_comm` : `dotZ` is symmetric;
* `sum_univ_erase_eq` : splitting a sum over `Fin n \ {i}` into `j < i` and `j = i + 1 + d`;
* `ldlRowStep_spec` : the exact meaning of the successful `ldlRowStep` check of one row.

The proof defines `RZ i j = w i * w j * B i j - dotZ (C i) (C j)` (the entry `R i j` of the remainder,
over `ℤ`), proves the accumulator invariant `acc i [c] = Σ_{j < i} |RZ j (i + c)|` by induction (each step is
`ldlRowStep_spec`), turns it into diagonal dominance of `RZ` at every row (`sum_univ_erase_eq` plus
symmetry), and feeds the resulting `L`, `R` into the proved `LdlScaledPrinciple`. -/

namespace Work.PTCert

open Submission.PTCert
open scoped BigOperators

/-- `headD` is `getD 0` (both return the default on the empty list). -/
private lemma headD_eq_getD_zero_aux {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l with
  | nil => rfl
  | cons x xs => rfl

theorem ldlChainSound : LdlChainSound := by
  intro n B w C acc hsym hwpos hlenC hacc0 hstep
  classical
  set RZ : ℕ → ℕ → ℤ := fun i j => w i * w j * B i j - dotZ (C i) (C j) with hRZ
  -- `R` is symmetric
  have hRZsym : ∀ i j, RZ i j = RZ j i := by
    intro i j
    simp only [hRZ]
    rw [hsym j i, Work.PTCert.ldlChainSound.dotZ_comm]
    ring
  -- the accumulator invariant: `acc k [c] = Σ_{j < k} |R j (k + c)|`
  have hinv : ∀ k ≤ n, (acc k).length = n - k ∧
      (∀ c < n - k, (acc k).getD c 0 = ∑ j ∈ Finset.range k, |RZ j (k + c)|) := by
    intro k
    induction k with
    | zero =>
      intro _
      constructor
      · rw [hacc0, List.length_replicate, Nat.sub_zero]
      · intro c hc
        have hc' : c < n := by omega
        rw [hacc0, List.getD_replicate 0 hc']
        simp
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      obtain ⟨hlenk, hvalk⟩ := ih (by omega)
      have hm : 1 ≤ n - k := by omega
      -- the check of row `k`
      obtain ⟨hs1, hs2, hs3⟩ :=
        Work.PTCert.ldlChainSound.ldlRowStep_spec (m := n - k) hm (f := fun d => B k (k + d)) (g := fun d => w (k + d))
          (h := fun d => C (k + d)) (wi := w k) (ci := C k) (acc := acc k) (acc' := acc (k + 1))
          (by omega) (hstep k hkn)
      constructor
      · rw [hs1]; omega
      · intro c hc
        rw [hs2 c (by omega), hvalk (c + 1) (by omega)]
        have hidx : (k + 1) + c = k + (c + 1) := by omega
        rw [hidx, Finset.sum_range_succ]
  have hlenC' : ∀ i : Fin n, (C i.val).length ≤ n := fun i => by have := hlenC i.val i.isLt; omega
  -- `Σ_t L i t * L j t = dotZ (C i) (C j)` (as reals)
  have hdot : ∀ i j : Fin n,
      (∑ t : Fin n, (((C i.val).getD t.val 0 : ℤ) : ℝ) * (((C j.val).getD t.val 0 : ℤ) : ℝ))
        = ((dotZ (C i.val) (C j.val) : ℤ) : ℝ) := by
    intro i j
    rw [Work.PTCert.ldlChainSound.dotZ_eq_sum_range (ha := hlenC' i) (hb := hlenC' j)]
    rw [Int.cast_sum]
    rw [Fin.sum_univ_eq_sum_range
      (fun t => (((C i.val).getD t 0 : ℤ) : ℝ) * (((C j.val).getD t 0 : ℤ) : ℝ)) n]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Int.cast_mul]
  -- diagonal dominance of `RZ` (over `ℤ`)
  have hdomZ : ∀ i : Fin n, (∑ j ∈ Finset.univ.erase i, |RZ i.val j.val|) ≤ RZ i.val i.val := by
    intro i
    have hni : i.val < n := i.isLt
    obtain ⟨hleni, hvali⟩ := hinv i.val (le_of_lt hni)
    have hm : 1 ≤ n - i.val := by omega
    -- the check of row `i`: `acc i [0] + Σ_{d} |R i (i+1+d)| ≤ R i i`
    obtain ⟨-, -, hrow⟩ :=
      Work.PTCert.ldlChainSound.ldlRowStep_spec (m := n - i.val) hm (f := fun d => B i.val (i.val + d))
        (g := fun d => w (i.val + d)) (h := fun d => C (i.val + d)) (wi := w i.val) (ci := C i.val)
        (acc := acc i.val) (acc' := acc (i.val + 1)) (by omega) (hstep i.val hni)
    have hrow' : (acc i.val).headD 0 + (∑ d ∈ Finset.range (n - i.val - 1),
        |RZ i.val (i.val + (d + 1))|) ≤ RZ i.val i.val := by
      simpa only [hRZ, Nat.add_zero] using hrow
    -- split the sum over `j ≠ i` at `i`
    rw [Work.PTCert.ldlChainSound.sum_univ_erase_eq i (fun j => |RZ i.val j|)]
    have hfirst : (∑ j ∈ Finset.range i.val, |RZ i.val j|) = (acc i.val).headD 0 := by
      rw [show (acc i.val).headD 0 = (acc i.val).getD 0 0 from headD_eq_getD_zero_aux _ _]
      rw [hvali 0 (by omega)]
      apply Finset.sum_congr rfl
      intro j _
      rw [hRZsym i.val j]
      simp
    rw [hfirst]
    exact hrow'
  refine ldlScaledPrinciple (M := Matrix.of fun i j : Fin n => (B i.val j.val : ℝ))
    (L := Matrix.of fun i t : Fin n => (((C i.val).getD t.val 0 : ℤ) : ℝ))
    (R := Matrix.of fun i j : Fin n => ((RZ i.val j.val : ℤ) : ℝ))
    (w := fun i : Fin n => ((w i.val : ℤ) : ℝ)) ?_ ?_ ?_ ?_
  · intro i
    exact_mod_cast hwpos i.val i.isLt
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact_mod_cast hRZsym j.val i.val
  · intro i
    simp only [Matrix.of_apply]
    have hcast : (∑ j ∈ Finset.univ.erase i, |((RZ i.val j.val : ℤ) : ℝ)|)
        = (((∑ j ∈ Finset.univ.erase i, |RZ i.val j.val|) : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl (fun j _ => (Int.cast_abs).symm)
    rw [hcast]
    exact_mod_cast hdomZ i
  · ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.add_apply]
    rw [hdot i j]
    simp only [hRZ]
    push_cast
    ring

end Work.PTCert
