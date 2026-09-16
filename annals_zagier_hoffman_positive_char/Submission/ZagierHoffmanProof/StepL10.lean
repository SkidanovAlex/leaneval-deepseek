import Submission.ZagierHoffmanProof.StepL6
import Submission.ZagierHoffmanProof.StepL9

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L10: the S-level spine of Prop 2.12's (2.11) → (2.14) chain

`bstarBinary` is the S-level B*_v step on a binary relation (plug of `bstar_pure`,
paper (2.13) first line): the fixed level-`d` relation with the `a`-tuples `v`-prepended
and the `b`-terms split into the fixed `(v :: t)` and merged `(v + (t)₁, t⁻)` terms.
`iterated_leading_member` tracks the distinguished `a`-output through the `BC_q`-
iteration: its coefficient is preserved and its (transported) tuple is the `n`-`q`-
prepend of the original — the leading-term identification used by Prop 2.12's (2.11)
(instantiate at `lemma_2_9_rel`'s `u` and combine with its tuple conjunct).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ B*_v on a mixed binary relation, S-level (per level d): prepending `v` to every
`a`-tuple and splitting each `b`-term into the fixed level-`d` terms gives a FIXED
relation (the paper's (2.13) first line).  Plug of `bstar_pure`. -/
theorem bstarBinary (R : BinaryRel F) (v : ℕ+)
    (hv : ∀ j : R.ιB, (v : ℕ) + ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) ≤ Nat.card F) :
    ∀ d : ℕ,
      (∑ i : R.ιA, (((R.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (R.depA i + 1) (by omega : 0 < R.depA i + 1) (consVec v (R.cA i)) d)) +
      (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (R.depB j + 1) (by omega : 0 < R.depB j + 1) (consVec v (R.cB j)) d)) +
      (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (R.depB j) (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j)) d)) = 0 := by
  intro d
  exact bstar_pure F (depA := R.depA) (hdepA := R.hdepA) (cA := R.cA) (aA := R.aA)
    (depB := R.depB) (hdepB := R.hdepB) (hB2 := R.hB2) (cB := R.cB) (aB := R.aB)
    v R.valid hv d

/-- The distinguished `a`-output of the `n`-fold `BC_q`-iterate: coefficient preserved,
and (transported) tuple value = the `n`-`q`-prepend of the original.  This is the
leading-term tracking used by Prop 2.12's (2.11): instantiate at the `u` of
`lemma_2_9_rel` and combine with its tuple conjunct. -/
lemma iterated_leading_member (n : ℕ) (R : BinaryRel F) (u : R.ιA) :
    let D := toData F R
    (RelData.BCqIter F n D).aA (RelData.iterIdx F n D u) = R.aA u ∧
    (∀ x : Fin (R.depA u + n),
        (RelData.BCqIter F n D).cA (RelData.iterIdx F n D u)
          (Fin.cast (RelData.BCqIter_depA_at F n D u).symm x) =
          qsTuple F n (R.depA u) (R.cA u) x) := by
  classical
  intro D
  constructor
  · -- coefficient preserved
    have h := RelData.BCqIter_aA_at F n D u
    simpa [D, toData] using h
  · intro x
    have h := RelData.BCqIter_cA_value F n D u x
    rw [h]
    rw [value_qsTuple F n (R.depA u) (R.cA u) x]
    by_cases hx : (x : ℕ) < n
    · simp [hx]
    · simp [hx, D, toData]


/-- ★ Prepending a further fixed entry `x` to all three families of the `B*_v`-output
keeps the fixed relation valid at every level (plug of `StepL1.fixed_rel_prepend`;
Prop 2.12's prefix step). -/
theorem bstarPrepend (R : BinaryRel F) (v x : ℕ+)
    (hv : ∀ j : R.ιB, (v : ℕ) + ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) ≤ Nat.card F) :
    ∀ d : ℕ,
      (∑ i : R.ιA, (((R.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (R.depA i + 2) (by omega : 0 < R.depA i + 2)
            (consVec x (consVec v (R.cA i))) d)) +
      (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (R.depB j + 2) (by omega : 0 < R.depB j + 2)
            (consVec x (consVec v (R.cB j))) d)) +
      (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (R.depB j + 1) (by omega : 0 < R.depB j + 1)
            (consVec x (headAdd v (R.hdepB j) (R.cB j))) d)) = 0 := by
  classical
  intro d
  -- combined family ι := R.ιA ⊕ R.ιB ⊕ R.ιB
  let ι : Type := R.ιA ⊕ (R.ιB ⊕ R.ιB)
  letI : Fintype ι := by dsimp [ι]; infer_instance
  let dep : ι → ℕ := fun p => match p with
    | Sum.inl i => R.depA i + 1
    | Sum.inr (Sum.inl j) => R.depB j + 1
    | Sum.inr (Sum.inr j) => R.depB j
  have hdep : ∀ p : ι, 0 < dep p := by
    intro p
    cases p with
    | inl i => dsimp [dep]; omega
    | inr q => cases q with
      | inl j => dsimp [dep]; omega
      | inr j => dsimp [dep]; exact R.hdepB j
  let c : ∀ p, Fin (dep p) → ℕ+ := fun p => match p with
    | Sum.inl i => consVec v (R.cA i)
    | Sum.inr (Sum.inl j) => consVec v (R.cB j)
    | Sum.inr (Sum.inr j) => headAdd v (R.hdepB j) (R.cB j)
  let a : ι → RatFunc F := fun p => match p with
    | Sum.inl i => R.aA i
    | Sum.inr (Sum.inl j) => R.aB j
    | Sum.inr (Sum.inr j) => R.aB j
  -- combined sum at every level is zero (from bstarBinary)
  have hB : ∀ e : ℕ, (∑ p : ι, (((a p : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (dep p) (hdep p) (c p) e)) = 0 := by
    intro e
    have hb := bstarBinary F R v hv e
    -- expand the combined sum into the three families and match hb
    change (∑ p : R.ιA ⊕ (R.ιB ⊕ R.ιB),
        ((a p : RatFunc F) : RatFunc.CompletionAtInfty F) * S F (dep p) (hdep p) (c p) e) = 0
    dsimp [ι, dep, c, a]
    rw [Fintype.sum_sum_type]
    rw [Fintype.sum_sum_type]
    simpa [add_assoc] using hb
  -- fixed_rel_prepend at x on the combined family
  have hpre := fixed_rel_prepend F dep hdep c a x hB d
  -- hpre : (∑ p, (a p : K) * S F (dep p + 1) … (consVec x (c p)) d) = 0
  change (∑ p : R.ιA ⊕ (R.ιB ⊕ R.ιB),
      ((a p : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (dep p + 1) (by omega : 0 < dep p + 1) (consVec x (c p)) d) = 0 at hpre
  dsimp [ι, dep, c, a] at hpre
  rw [Fintype.sum_sum_type] at hpre
  rw [Fintype.sum_sum_type] at hpre
  simpa [add_assoc] using hpre



/-- Every `b`-tuple produced by one `BC_q` step has head `1`. -/
lemma RelData.BCq_cB_head (D : RelData F) (p : (RelData.BCq F D).ιB) :
    ((RelData.BCq F D).cB p) ⟨0, (RelData.BCq F D).hdepB p⟩ = oneExp := by
  dsimp [RelData.BCq]
  exact consVec_zero oneExp ((p2WpT F (qMinusExp F) (D.hdepB p.1) (D.cB p.1)).c p.2)

/-- After at least one `BC_q` step (and hence after any number of further iterations)
every `b`-tuple of the iterate has head `1`. -/
lemma RelData.BCqIter_cB_head (n : ℕ) (D : RelData F) :
    ∀ p : (RelData.BCqIter F (n + 1) D).ιB,
      ((RelData.BCqIter F (n + 1) D).cB p) ⟨0, (RelData.BCqIter F (n + 1) D).hdepB p⟩ = oneExp := by
  revert D
  induction n with
  | zero =>
      intro D p
      -- BCqIter 1 D = BCq D
      have h := RelData.BCq_cB_head F D p
      simpa [RelData.BCqIter] using h
  | succ n ih =>
      intro D p
      -- BCqIter ((n+1)+1) D = BCqIter (n+1) (BCq D) (rfl); heads via the IH at (BCq D)
      change ((RelData.BCqIter F (n + 1) (RelData.BCq F D)).cB p)
        ⟨0, (RelData.BCqIter F (n + 1) (RelData.BCq F D)).hdepB p⟩ = oneExp
      exact ih (RelData.BCq F D) p



/-- ★ The leading tuple after `n` `BC_q`-steps, on the iterate's own index type:
its entries are the corresponding entries of the `n`-`q`-prepend of the original
tuple (cast along the depth equality).  Type-correct form of `BCqIter_cA_at` for use
inside `ζ_A`-terms. -/
lemma iter_leading_tuple (n : ℕ) (R : BinaryRel F) (u : R.ιA) :
    (RelData.BCqIter F n (toData F R)).cA (RelData.iterIdx F n (toData F R) u) =
      fun y : Fin ((RelData.BCqIter F n (toData F R)).depA (RelData.iterIdx F n (toData F R) u)) =>
        qsTuple F n (R.depA u) (R.cA u)
          (Fin.cast (RelData.BCqIter_depA_at F n (toData F R) u) y) := by
  classical
  apply _root_.funext
  intro y
  let x : Fin (R.depA u + n) := Fin.cast (RelData.BCqIter_depA_at F n (toData F R) u) y
  have hyx : y = Fin.cast (RelData.BCqIter_depA_at F n (toData F R) u).symm x := by
    apply Fin.ext
    rfl
  have h2 := congrFun (RelData.BCqIter_cA_at F n (toData F R) u) x
  rw [hyx]
  rw [h2]
  dsimp [x]
  apply congrArg (fun z : Fin (R.depA u + n) => qsTuple F n (R.depA u) (R.cA u) z)
  apply Fin.ext
  rfl


end ZagierHoffmanPositiveChar
