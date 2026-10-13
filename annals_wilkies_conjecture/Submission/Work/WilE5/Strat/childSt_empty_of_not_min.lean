/-
  A child of a state is *empty* at every test that is not "minimal", where minimal means:
  the test is valid and its peeled direction `t.l` is the smallest direction carrying a nonzero
  exponent (i.e. no `l' < t.l` has `t.m l' ≠ 0`).

  There are exactly two reasons for emptiness, matching the two disjuncts of the hypothesis:

  * `¬ valid σ t`: then `opVal X.c σ t = 0` (`opVal_eq_zero_of_not_valid`), while the child's
    conditions contain the strict sign condition `0 < opVal` (or `opVal < 0`) — contradiction.

  * some `l' < t.l` carries a nonzero exponent: `opVal` does *not* depend on the peeled
    direction `l`, so the test `t' := (t.i, t.m, l')` has the same `opVal`; it is `testLt`-below
    `t` (all the earlier keys of the order coincide) and still belongs to `testL` (its peeled
    exponent `t.m l'` is nonzero) and is valid whenever `t` is (validity only involves `i` and
    `m`).  Hence `opVal X.c σ t'` is one of the child's `Ξ`-conditions
    (through `prec M NΦ σ t`), giving `opVal = 0`, against the strict sign condition on the
    very same polynomial.
-/
import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children
import Submission.Work.WilE5.Strat.opVal_eq_zero_of_not_valid

set_option autoImplicit false

namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-! ## §1. Two order bookkeeping lemmas -/

/-- The lexicographic comparison of a list with itself is `false`. -/
theorem mlexLtAux_self (xs : List ℕ) : mlexLtAux xs xs = false := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [mlexLtAux]
    rw [if_neg (lt_irrefl a), if_neg (lt_irrefl a), ih]

/-- Two tests with the same source index and the same multi-index are ordered by their peeled
direction: the test with the smaller direction comes first. -/
theorem testLt_same_dir_lt {q : ℕ} (t : Work.WilE5.Test q) (l' : Fin q) (h : l' < t.l) :
    testLt (⟨t.i, t.m, l'⟩ : Work.WilE5.Test q) t = true := by
  unfold testLt
  rw [if_neg (lt_irrefl t.i), if_neg (lt_irrefl t.i),
    if_neg (lt_irrefl (mSum t.m)), if_neg (lt_irrefl (mSum t.m))]
  simp [mlexLtAux_self, h]

/-- `opVal` does not depend on the peeled direction of the test. -/
theorem opVal_mk_eq {p q r : ℕ} (c : EAChain (p + q) r) (σ : St p q r)
    (t : Work.WilE5.Test q) (l' : Fin q) :
    opVal c σ (⟨t.i, t.m, l'⟩ : Work.WilE5.Test q) = opVal c σ t := rfl

/-! ## §2. Emptiness of the child at a non-minimal test -/

theorem childSt_empty_of_not_min {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (M NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r) (t : Work.WilE5.Test q) (s : Bool)
    (ht : t ∈ Work.WilE5.testL q M NΦ)
    (hnot : ¬ Work.WilE5.valid σ t ∨ ∃ l' : Fin q, l' < t.l ∧ t.m l' ≠ 0) :
    ∀ z : Fin (p + q) → ℝ,
      z ∉ (Work.WilE5.stSemiPf X (Work.WilE5.childSt X.c M NΦ σ t s)).set := by
  intro z hz
  rw [stSemiPf_child_set_eq] at hz
  obtain ⟨_, _, hprec, _, hsign⟩ := hz
  -- the operator value of the (possibly non-minimal) test vanishes at `z`
  have key : eaEval X.c (opVal X.c σ t) z = 0 := by
    by_cases hv : valid σ t
    · rcases hnot with h | ⟨l', hl't, hml'⟩
      · exact absurd hv h
      · -- the test with the smaller peeled direction is an earlier valid test
        have htL := (mem_testL_iff t).mp ht
        have ht' : (⟨t.i, t.m, l'⟩ : Work.WilE5.Test q) ∈ testL q M NΦ :=
          (mem_testL_iff _).mpr ⟨htL.1, htL.2.1, hml'⟩
        have hv' : valid σ (⟨t.i, t.m, l'⟩ : Work.WilE5.Test q) := hv
        have hlt : testLt (⟨t.i, t.m, l'⟩ : Work.WilE5.Test q) t = true :=
          testLt_same_dir_lt t l' hl't
        have hh := hprec _ ((mem_prec_iff σ t _).mpr ⟨ht', hv', hlt⟩)
        rwa [opVal_mk_eq X.c σ t l'] at hh
    · -- an invalid test has vanishing operator value
      have hopv0 : opVal X.c σ t = 0 := opVal_eq_zero_of_not_valid X.c σ t hv
      rw [hopv0]
      simp [eaEval]
  -- the strict sign condition of the child contradicts vanishing
  rw [key] at hsign
  simp at hsign

end Work.WilE5.Strat
