import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.MainP.crtDefs
import Submission.Work.MainP.crtMath

/-!
# `crtLabWord`: shared definitions (mathematical and runtime)

`Work.MainP.crtLabWord` asks for a StackLang word turning `int S :: intList ss` into
`intList (sigmaList ss)` (where `S = ss.prod`) at cost `K * (S * (vsz ss + 1) * (S.size + 1) + 1)`.

## The algorithm formalised here

The labels `crtIdx ss m = Σ_j (m % s_j) · P_j` (with `(s_j, P_j) = [crtTab ss]_j`) are produced by an
*incremental odometer*: each modulus carries a state triple `(c, P, Q) = (r·P, P, s·P)` where
`r = m % s`; increasing `m` by one replaces `c` by `c + P`, except that `c + P = Q` wraps to `0`.
Summing the `c` over the triples gives the current label.

The output is accumulated in a single *nested value*

`acc i = cons (prp v_{i-1} (Est i)) (ofList (Xh i))`,

i.e. a pair `(previous label, current state)` consed onto the list of all earlier pairs.  Only the
*head* of this value is touched at each step (`unconsV`/`consV`), so the running cost per step is
`O(d · size S)` and never sees the accumulated history.  At the very end the labels are read off the
history and reversed (the last entry being a dummy).

## Contents

* `triple`, `entryC`, `entryUpd`: the runtime representation of a state entry and its update.
* `canon ss i`: the *canonical* state at time `i` (all entries on which `c = (i % s)·P`).
* `Est ss i = canon i` if `i` is even and `(canon i).reverse` otherwise: the runtime state, because
  the update pass of the word rebuilds the entry list by *prepending* (so it reverses it each time).
* `prp`, `vlab`, `Xh`, `acc`, `drv`: the runtime accumulator, the history, and the driver list.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

theorem crtTab_length (ss : List ℕ) : (crtTab ss).length = ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [crtTab, ih]

/-! ## Entries -/

/-- A state entry: the triple `(c, P, Q)` held as a nested `cons` value. -/
def triple (c P Q : ℤ) : Val := .cons (.int c) (.cons (.int P) (.int Q))

@[simp] theorem triple_inj {c P Q c' P' Q' : ℤ} (h : triple c P Q = triple c' P' Q') :
    c = c' ∧ P = P' ∧ Q = Q' := by
  simp only [triple, Val.cons.injEq, Val.int.injEq] at h
  exact h

/-- The current contribution `c` of an entry (`0` for a non-entry). -/
def entryC : Val → ℤ
  | .cons (.int c) _ => c
  | _ => 0

/-- The update of an entry `(c, P, Q)`: `c ↦ c + P`, except that `c + P = Q` wraps to `0`. -/
def entryUpd : Val → Val
  | .cons (.int c) (.cons (.int P) (.int Q)) =>
      .cons (.int (if c + P = Q then 0 else c + P)) (.cons (.int P) (.int Q))
  | e => e

@[simp] theorem entryC_triple (c P Q : ℤ) : entryC (triple c P Q) = c := rfl

@[simp] theorem entryUpd_triple (c P Q : ℤ) :
    entryUpd (triple c P Q) = triple (if c + P = Q then 0 else c + P) P Q := rfl

/-- `triple` never produces `nil`. -/
theorem triple_ne_nil (c P Q : ℤ) : triple c P Q ≠ .nil := by simp [triple]

/-- `triple` always produces a `cons`. -/
theorem exists_triple_of_eq_triple {e : Val} {c P Q : ℤ} (h : e = triple c P Q) :
    ∃ a b, e = .cons a b := ⟨_, _, by rw [h]; rfl⟩

/-! ## The canonical states and the runtime states -/

/-- The canonical state at time `i`: entry `j` is `((i % s_j)·P_j, P_j, s_j·P_j)`. -/
def canon (ss : List ℕ) (i : ℕ) : List Val :=
  (crtTab ss).map fun sp => triple (((i % sp.1) * sp.2 : ℕ) : ℤ) (sp.2 : ℤ) ((sp.1 * sp.2 : ℕ) : ℤ)

@[simp] theorem canon_length (ss : List ℕ) (i : ℕ) : (canon ss i).length = ss.length := by
  simp [canon, crtTab_length]

/-- The runtime state at time `i` (the update pass reverses the entry list). -/
def Est (ss : List ℕ) (i : ℕ) : List Val :=
  if Even i then canon ss i else (canon ss i).reverse

theorem Est_length (ss : List ℕ) (i : ℕ) : (Est ss i).length = ss.length := by
  unfold Est
  split <;> simp [List.length_reverse, canon_length]

/-! ## The runtime accumulator -/

/-- A pair `(label, state)` as a `cons` value. -/
def prp (v : ℤ) (E : List Val) : Val := .cons (.int v) (ofList E)

/-- The label `crtIdx ss j` as an integer. -/
def vlab (ss : List ℕ) (j : ℕ) : ℤ := ((crtIdx ss j : ℕ) : ℤ)

/-- The history of the accumulator after `i` steps: the pairs of all previous steps, most recent
first.  Its `j`-th entry is `(v_{j-1}, Est ss j)`. -/
def Xh (ss : List ℕ) : ℕ → List Val
  | 0 => []
  | (i + 1) => prp (vlab ss (i - 1)) (Est ss i) :: Xh ss i

/-- The accumulator before step `i`: `(last label, current state) :: history`. -/
def acc (ss : List ℕ) (i : ℕ) : Val :=
  .cons (prp (vlab ss (i - 1)) (Est ss i)) (ofList (Xh ss i))

/-- The driver list of the main loop: `S` copies of `nil` (only its length matters). -/
def drv (S : ℕ) : List Val := List.replicate S .nil

@[simp] theorem drv_length (S : ℕ) : (drv S).length = S := by simp [drv]

theorem drv_vsz (S : ℕ) : ∀ x ∈ drv S, vsz x ≤ 1 := by
  intro x hx
  simp only [drv, List.mem_replicate] at hx
  rw [hx.2]
  simp [vsz, Val.enc]

/-! ## Elementary list facts -/

@[simp] theorem Xh_zero (ss : List ℕ) : Xh ss 0 = [] := by simp [Xh]

@[simp] theorem Xh_succ (ss : List ℕ) (i : ℕ) :
    Xh ss (i + 1) = prp (vlab ss (i - 1)) (Est ss i) :: Xh ss i := rfl

theorem ofList_Xh_succ (ss : List ℕ) (i : ℕ) :
    ofList (Xh ss (i + 1)) = .cons (prp (vlab ss (i - 1)) (Est ss i)) (ofList (Xh ss i)) := by
  rw [Xh_succ]
  rfl

theorem acc_succ (ss : List ℕ) (i : ℕ) :
    acc ss (i + 1) = .cons (prp (vlab ss i) (Est ss (i + 1)))
      (.cons (prp (vlab ss (i - 1)) (Est ss i)) (ofList (Xh ss i))) := by
  rw [acc, ofList_Xh_succ]
  rfl

theorem acc_zero (ss : List ℕ) : acc ss 0 = .cons (prp (vlab ss 0) (Est ss 0)) .nil := by
  simp [acc, Xh, ofList]

theorem acc_cons (ss : List ℕ) (i : ℕ) :
    acc ss i = .cons (prp (vlab ss (i - 1)) (Est ss i)) (ofList (Xh ss i)) := rfl

/-! ## Bridge lemmas (used by the assembly) -/

private theorem ofList_cons (p : Val) (X : List Val) : ofList (p :: X) = .cons p (ofList X) := rfl

@[simp] theorem pairKey_prp (v : ℤ) (E : List Val) : HvdH.pairKey (prp v E) = v := rfl

theorem crtIdx_zero (ss : List ℕ) : crtIdx ss 0 = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [crtIdx_cons, ih]

theorem vlab_zero (ss : List ℕ) : vlab ss 0 = 0 := by simp [vlab, crtIdx_zero]

theorem Est_zero (ss : List ℕ) : Est ss 0 = canon ss 0 := by simp [Est]

/-- Every element of the driver list is `nil`. -/
theorem drv_getD : ∀ (S i : ℕ), (drv S).getD i .nil = (HvdH.Val.nil : Val)
  | _, 0 => by simp [drv]
  | 0, _ + 1 => rfl
  | S + 1, i + 1 => by
      rw [show drv (S + 1) = (HvdH.Val.nil : Val) :: drv S from by
        simp [drv, List.replicate_succ]]
      simpa using drv_getD S i

/-- `intList (sigmaList ss)` is the list of the values `vlab ss j` for `j < ss.prod`. -/
theorem intList_sigmaList (ss : List ℕ) :
    intList (sigmaList ss) = ofList ((sigmaList ss).map (fun n => Val.int n)) := rfl

theorem range_succ_reverse_map (i : ℕ) (g : ℕ → Val) :
    ((List.range (i + 1)).reverse).map g = g i :: ((List.range i).reverse).map g := by
  simp only [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.map_cons, List.map_append, List.map_nil]

/-- The labels of the history after `i` steps, most recent first. -/
theorem Xh_labels (ss : List ℕ) (i : ℕ) :
    (Xh ss i).map (fun p => Val.int (HvdH.pairKey p))
      = ((List.range i).reverse).map (fun j => Val.int (vlab ss (j - 1))) := by
  induction i with
  | zero => simp [Xh]
  | succ i ih =>
      rw [Xh_succ, List.map_cons, ih, range_succ_reverse_map, pairKey_prp]

end Work.MainP
