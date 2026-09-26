import Mathlib
import Submission.Work.PTCert.Glue3

/-!
# PTCert — auxiliary definitions and lemmas for the `LdlFacts` glue lemma

`ldlSeg` (KernelCert.lean) is a structural recursion over the list `is` of rows of one segment: it
performs the four `ψ`-steps (`ldlRowStep`) of row `i` and recurses on `is`.  To unroll the chain of
segments into a chain of *rows* we introduce

* `foldStep` — the generic fold of a `ℕ`-indexed step function over a list of rows;
* `ldlStep` — the single `ψ`-step of `ldlSeg` at row `i`;
* `ldlStepAll` — the four `ψ`-steps at row `i`, packaged as one step of `foldStep`.

The lemmas below show that `ldlSeg` *is* `foldStep (ldlStepAll …)` and give the componentwise
meaning of a successful `ldlStepAll` step.
-/

open OnPropertyT Submission.FreeGroupAut Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace Submission.PTCert

/-! ## The generic fold -/

/-- Fold a step function `g` over a list of rows, threading the accumulator state. -/
def foldStep (g : ℕ → List (List ℤ) → Option (List (List ℤ))) :
    List ℕ → List (List ℤ) → Option (List (List ℤ))
  | [], accs => some accs
  | i :: is, accs => (g i accs).bind (foldStep g is)

lemma foldStep_nil (g : ℕ → List (List ℤ) → Option (List (List ℤ))) :
    foldStep g [] = fun accs => some accs := by funext a; rfl

lemma foldStep_cons (g : ℕ → List (List ℤ) → Option (List (List ℤ))) (i : ℕ) (is : List ℕ) :
    foldStep g (i :: is) = fun accs => (g i accs).bind (foldStep g is) := by funext a; rfl

@[simp] lemma foldStep_nil_apply (g : ℕ → List (List ℤ) → Option (List (List ℤ)))
    (accs : List (List ℤ)) : foldStep g [] accs = some accs := rfl

@[simp] lemma foldStep_cons_apply (g : ℕ → List (List ℤ) → Option (List (List ℤ)))
    (i : ℕ) (is : List ℕ) (accs : List (List ℤ)) :
    foldStep g (i :: is) accs = (g i accs).bind (foldStep g is) := rfl

lemma foldStep_singleton (g : ℕ → List (List ℤ) → Option (List (List ℤ))) (i : ℕ) :
    foldStep g [i] = g i := by
  funext accs
  rw [foldStep_cons]
  simp [foldStep_nil]

lemma foldStep_append (g : ℕ → List (List ℤ) → Option (List (List ℤ)))
    (is is' : List ℕ) (accs : List (List ℤ)) :
    foldStep g (is ++ is') accs = (foldStep g is accs).bind (foldStep g is') := by
  induction is generalizing accs with
  | nil => simp [foldStep_nil, Option.bind_some]
  | cons i is ih =>
    have hf : foldStep g (is ++ is') = fun a => (foldStep g is a).bind (foldStep g is') :=
      funext fun a => ih a
    rw [List.cons_append, foldStep_cons, foldStep_cons]
    simp only []
    rw [hf, Option.bind_assoc]

lemma foldStep_range_succ (g : ℕ → List (List ℤ) → Option (List (List ℤ))) (i : ℕ)
    (accs : List (List ℤ)) :
    foldStep g (List.range (i + 1)) accs = (foldStep g (List.range i) accs).bind (g i) := by
  have h : foldStep g [i] = g i := foldStep_singleton g i
  rw [List.range_succ, foldStep_append, h]

/-- A successful `bind` always has a successful left factor. -/
lemma exists_of_bind_eq_some {γ δ : Type} {a : Option γ} {f : γ → Option δ} {z : δ}
    (h : a.bind f = some z) : ∃ y, a = some y := by
  rw [Option.bind_eq_some_iff] at h
  exact ⟨h.choose, h.choose_spec.1⟩

/-- `List.range n` splits at `i` into the first `i` rows and the remaining ones. -/
lemma range_take_append (n i : ℕ) (hi : i ≤ n) :
    List.range n = List.range i ++ (List.range n).drop i := by
  conv_lhs => rw [← List.take_append_drop i (List.range n)]
  rw [List.take_range, min_eq_left hi]

/-- The composite `match` of the four `ψ`-steps is the `bind` of the "all four" match. -/
lemma match_bind_some {f0 f1 f2 f3 : Option (List ℤ)} {γ : Type} {k : List (List ℤ) → Option γ} :
    (match f0, f1, f2, f3 with
      | some a0, some a1, some a2, some a3 => k [a0, a1, a2, a3]
      | _, _, _, _ => none)
    = (match f0, f1, f2, f3 with
        | some a0, some a1, some a2, some a3 => some [a0, a1, a2, a3]
        | _, _, _, _ => none).bind k := by
  rcases f0 with _ | a0 <;> rcases f1 with _ | a1 <;> rcases f2 with _ | a2 <;>
    rcases f3 with _ | a3 <;> rfl

/-- The four `ψ`-steps of a successful `ψ`-block step are all successful, with the expected values. -/
lemma match4_spec {f0 f1 f2 f3 : Option (List ℤ)} {r : List (List ℤ)}
    (h : (match f0, f1, f2, f3 with
        | some a0, some a1, some a2, some a3 => some [a0, a1, a2, a3]
        | _, _, _, _ => none) = some r) :
    ∃ a0 a1 a2 a3 : List ℤ, f0 = some a0 ∧ f1 = some a1 ∧ f2 = some a2 ∧ f3 = some a3 ∧
      r = [a0, a1, a2, a3] := by
  rcases f0 with _ | a0 <;> rcases f1 with _ | a1 <;> rcases f2 with _ | a2 <;>
    rcases f3 with _ | a3 <;> simp_all

/-! ## `ldlSeg` as a `foldStep` -/

section LdlStep

variable (cm eM repT repInfoT piIT : NT) (piCodes : List ℕ) (rowTs : List NT) (S : ℕ)
  (ks ys : List ℕ) (Cs : List (List (List ℤ))) (Ws : List (List ℤ))

/-- The single `ψ`-step of `ldlSeg` at row `i`. -/
abbrev ldlStep (i : ℕ) (accs : List (List ℤ)) (ψ : ℕ) : Option (List ℤ) :=
  ldlRowStep ((blockRows4 cm eM repT repInfoT piIT piCodes rowTs S ks ys i).getD ψ [])
    ((Ws.getD ψ []).getD i 1) ((Ws.getD ψ []).drop i) ((Cs.getD ψ []).getD i [])
    ((Cs.getD ψ []).drop i) (accs.getD ψ [])

/-- The four `ψ`-steps of `ldlSeg` at row `i`, packaged as one step. -/
abbrev ldlStepAll (i : ℕ) (accs : List (List ℤ)) : Option (List (List ℤ)) :=
  match ldlStep cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws i accs 0,
        ldlStep cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws i accs 1,
        ldlStep cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws i accs 2,
        ldlStep cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws i accs 3 with
  | some a0, some a1, some a2, some a3 => some [a0, a1, a2, a3]
  | _, _, _, _ => none

theorem ldlSeg_nil (accs : List (List ℤ)) :
    ldlSeg cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws [] accs = some accs :=
  Submission.PTCert.ldlSeg.eq_1 cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws accs

theorem ldlSeg_cons (i : ℕ) (is : List ℕ) (accs : List (List ℤ)) :
    ldlSeg cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws (i :: is) accs =
      (ldlStepAll cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws i accs).bind
        (ldlSeg cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws is) := by
  rw [Submission.PTCert.ldlSeg.eq_2]
  exact match_bind_some

/-- **`ldlSeg` is the fold of the row-wise `ψ`-block steps.** -/
theorem ldlSeg_eq_foldStep (is : List ℕ) (accs : List (List ℤ)) :
    ldlSeg cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws is accs =
      foldStep (ldlStepAll cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws) is accs := by
  induction is generalizing accs with
  | nil => rw [ldlSeg_nil]; rfl
  | cons i is ih =>
    rw [ldlSeg_cons, foldStep_cons]
    rw [show ldlSeg cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws is
        = foldStep (ldlStepAll cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws) is from
      funext fun a => ih a]

/-- The componentwise meaning of a successful `ldlStepAll` step. -/
theorem ldlStepAll_spec (i : ℕ) (accs : List (List ℤ)) {r : List (List ℤ)}
    (h : ldlStepAll cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws i accs = some r)
    {ψ : ℕ} (hψ : ψ < 4) :
    ∃ a : List ℤ, ldlStep cm eM repT repInfoT piIT piCodes rowTs S ks ys Cs Ws i accs ψ = some a ∧
      r.getD ψ [] = a := by
  obtain ⟨a0, a1, a2, a3, h0, h1, h2, h3, hr⟩ := match4_spec h
  subst hr
  interval_cases ψ <;> simp_all

end LdlStep

end Submission.PTCert

end
