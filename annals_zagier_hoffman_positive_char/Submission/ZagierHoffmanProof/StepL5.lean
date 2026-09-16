import Submission.ZagierHoffmanProof.StepL4

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L5: §2.3 — binary-relation data and the (2.10) lift

`BinaryRel` packages the paper's binary relation `R` (Def 2.3): an `a`-family of
level-`e` tuples with `RatFunc F` coefficients, a `b`-family of level-`(e+1)` tuples
(all of depth ≥ 2 — the `hB2` hypothesis every §2.3 relation satisfies), and a validity
`Σ_i a_i S_e(s_i) + Σ_j b_j S_{e+1}(t_j) = 0` for every level `e`.  The operator lemmas
`bstar`, `CW`, `BC_q`/`BC_q_pure` of StepL4 are stated directly on such families.

`lemma_2_9_rel` packages paper (2.10) (our `lemma_2_9`) as a `BinaryRel`: its `a`-side is
the distinguished leading output `(q+w1) :: B` (coefficient `1`, depth `k+1`) together
with the `a`-outputs of Lemma 2.9 (bounded by `(q)+W`, first entry `< q+w1`), and its
`b`-side is the `(1 :: t_j)`-family (`t_j ≤ (q−1)+W`).  This is the data shape
Prop 2.12's `BC_q`-iteration consumes.
-/

namespace ZagierHoffmanPositiveChar

/-- A binary relation over levels `e : ℕ` (paper Def 2.3, ℕ-version). -/
structure BinaryRel (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] where
  ιA : Type
  finA : Fintype ιA
  depA : ιA → ℕ
  hdepA : ∀ i, 0 < depA i
  cA : ∀ i, Fin (depA i) → ℕ+
  aA : ιA → RatFunc F
  ιB : Type
  finB : Fintype ιB
  depB : ιB → ℕ
  hdepB : ∀ j, 0 < depB j
  hB2 : ∀ j, 1 < depB j
  cB : ∀ j, Fin (depB j) → ℕ+
  aB : ιB → RatFunc F
  valid : ∀ e : ℕ,
    (∑ i : ιA, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (depA i) (hdepA i) (cA i) e)) +
    (∑ j : ιB, (((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (depB j) (hdepB j) (cB j) (e + 1))) = 0

attribute [instance] BinaryRel.finA
attribute [instance] BinaryRel.finB

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The level-`e` value of a binary relation (the `R(e)` of the paper). -/
noncomputable def BinaryRel.level (R : BinaryRel F) (e : ℕ) : RatFunc.CompletionAtInfty F :=
  (∑ i : R.ιA, (((R.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (R.depA i) (R.hdepA i) (R.cA i) e)) +
  (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (R.depB j) (R.hdepB j) (R.cB j) (e + 1)))

/-- Every level value of a valid relation is zero. -/
lemma BinaryRel.level_zero (R : BinaryRel F) (e : ℕ) : BinaryRel.level F R e = 0 := R.valid e

/-- The ℤ coefficients of Lemma 2.9's `a`-outputs, as `RatFunc F` coefficients. -/
noncomputable def zCoeffRat (n : ℤ) : RatFunc F := (n : RatFunc F)

/-- ★ Lift of paper (2.10): the Lemma-2.9 output is a binary relation whose `a`-side has a
coefficient-`1` output `u` of depth `k+1` (the merged head `(q+w1) :: B`), whose other
`a`-outputs are bounded by `(q)+W` with first entry `< q+w1`, and whose `b`-side is the
`(1 :: t_j)`-family with tails `t_j ≤ (q−1)+W`. -/
theorem lemma_2_9_rel (k : ℕ) (w1 : ℕ+) (B : Fin k → ℕ+) :
    ∃ (R : BinaryRel F) (u : R.ιA),
      R.depA u = k + 1 ∧ R.aA u = 1 ∧
      (∀ hd : R.depA u = k + 1,
          (fun x : Fin (k + 1) => R.cA u (Fin.cast hd.symm x)) =
            consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B) ∧
      (∀ i : R.ιA, i ≠ u → LePad (R.cA i) (single (qExp F)) (consVec w1 B) ∧
          ((R.cA i) ⟨0, R.hdepA i⟩ : ℕ) < (qExp F : ℕ) + (w1 : ℕ)) ∧
      (∀ j : R.ιB, ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) ∧
      (∀ j : R.ιB, LePad (expTail (R.cB j)) (single (qMinusExp F)) (consVec w1 B)) ∧
      (∀ e : ℕ,
        (∑ i : R.ιA, (((R.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
            S F (R.depA i) (R.hdepA i) (R.cA i) e)) +
        (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
            S F (R.depB j) (R.hdepB j) (R.cB j) (e + 1))) = 0) := by
  classical
  rcases lemma_2_9 F k w1 B with ⟨ιa, fina, depa, hdepa, ca, aa, ιb, finb, depb, hdepb, cb, bb, hleA, hleB, hid⟩
  let ιA' : Type := PUnit.{1} ⊕ ιa
  letI : Fintype ιA' := by dsimp [ιA']; infer_instance
  let depA' : ιA' → ℕ := fun i => match i with
    | Sum.inl _ => k + 1
    | Sum.inr x => depa x
  have hdepA' : ∀ i, 0 < depA' i := by
    intro i
    cases i with
    | inl u => dsimp [depA']; omega
    | inr x => dsimp [depA']; exact hdepa x
  let cA' : ∀ i, Fin (depA' i) → ℕ+ := fun i => match i with
    | Sum.inl _ => consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B
    | Sum.inr x => ca x
  let aA' : ιA' → RatFunc F := fun i => match i with
    | Sum.inl _ => 1
    | Sum.inr x => ((aa x : ℤ) : RatFunc F)
  let depB' : ιb → ℕ := fun j => depb j + 1
  have hdepB' : ∀ j, 0 < depB' j := by intro j; dsimp [depB']; omega
  have hB2' : ∀ j, 1 < depB' j := by
    intro j
    dsimp [depB']
    have hd : 0 < depb j := hdepb j
    omega
  let cB' : ∀ j, Fin (depB' j) → ℕ+ := fun j => consVec oneExp (cb j)
  let aB' : ιb → RatFunc F := bb
  have hvalid : ∀ e : ℕ,
      (∑ i : ιA', (((aA' i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA' i) (hdepA' i) (cA' i) e)) +
      (∑ j : ιb, (((aB' j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB' j) (hdepB' j) (cB' j) (e + 1))) = 0 := by
    intro e
    have hh := hid e
    rw [Fintype.sum_sum_type]
    simp [depA', cA', aA', depB', cB', aB', intCast_ratFunc_completion F,
      completion_coe_one, one_mul] at hh ⊢
    simpa [add_assoc] using hh
  let R : BinaryRel F := {
    ιA := ιA'
    finA := inferInstance
    depA := depA'
    hdepA := hdepA'
    cA := cA'
    aA := aA'
    ιB := ιb
    finB := inferInstance
    depB := depB'
    hdepB := hdepB'
    hB2 := hB2'
    cB := cB'
    aB := aB'
    valid := hvalid }
  refine ⟨R, Sum.inl PUnit.unit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro hd
    apply _root_.funext
    intro x
    dsimp [R]
  · intro i hi
    cases i with
    | inl u =>
        exfalso
        apply hi
        rfl
    | inr x => exact hleA x
  · intro p
    dsimp [R, cB']
    have hh := consVec_zero oneExp (cb p)
    have hv1 : (oneExp : ℕ) = 1 := by simp [oneExp]
    have hh3 : consVec oneExp (cb p) ⟨0, hdepB' p⟩ = oneExp := by
      simpa using hh
    simpa [oneExp] using congrArg (fun t : ℕ+ => (t : ℕ)) hh3
  · intro j
    dsimp [R, cB']
    rw [expTail_consVec]
    exact hleB j
  · intro e
    dsimp [R]
    exact hvalid e


end ZagierHoffmanPositiveChar
