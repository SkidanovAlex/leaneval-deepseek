import Submission.ZagierHoffmanProof.StepL5

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L6: §2.3 step (b) — the BC_q iteration skeleton (Prop 2.12's prefix lowering)

`BCqData` is the pure data transform performed by one application of `BC_q` (Prop 2.10)
to the relation of (2.10): every `a`-tuple gains a leading `q`, and each `b`-tuple
`t_j = (1 :: cb_j)` (stored as `cB j`) is replaced by the family of its
`BC_q`-outputs `(1 :: c_e)` over the Σ-type index `j : ιB, e : D_j.ι`, where
`D_j := p2WpT (q−1) (cB j)` expands `S_<d+1(q−1)·S_<d+1(cB_j)` (the (2.6) step) and the
new coefficient is `−a_j·D1·(f_e : ℤ)` (the paper's (2.12) recurrence).  `BCqIter` is the
`Nat.iterate` recursion of `BCqData` (the `k−j−1` applications).  Validity preservation
(`R.valid ⇒ (BCqIter n (data R)).valid`) is a separate theorem to be proved from
`BC_q_pure` by induction over `n` — this module only fixes the types.
-/

namespace ZagierHoffmanPositiveChar

attribute [instance] P2Data.fin

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The data of a binary relation (validity discarded) — the carrier the `BC_q`
iteration runs on. -/
structure RelData (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] where
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

attribute [instance] RelData.finA
attribute [instance] RelData.finB

/-- Forget the validity of a binary relation. -/
noncomputable def toData (R : BinaryRel F) : RelData F :=
  { ιA := R.ιA
    finA := R.finA
    depA := R.depA
    hdepA := R.hdepA
    cA := R.cA
    aA := R.aA
    ιB := R.ιB
    finB := R.finB
    depB := R.depB
    hdepB := R.hdepB
    hB2 := R.hB2
    cB := R.cB
    aB := R.aB }

/-- The `p2WpT` witness expanding `S_<d+1(q−1)·S_<d+1(cB_j)` for a data relation. -/
noncomputable def RelData.D (R : RelData F) (j : R.ιB) :
    P2Data F 1 (R.depB j) (by omega : 0 < 1) (R.hdepB j) (single (qMinusExp F)) (R.cB j) :=
  p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)

/-- Σ-type index of the new b-family: pairs `(j, e)` over the `p2WpT`-fibers. -/
noncomputable abbrev RelData.BCqIdx (R : RelData F) : Type :=
  Σ j : R.ιB, (p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).ι

/-- One `BC_q` data transform: prepend `q` to the a-tuples and reindex the b-family. -/
noncomputable def RelData.BCq (R : RelData F) : RelData F :=
  { ιA := R.ιA
    finA := R.finA
    depA := fun i => R.depA i + 1
    hdepA := fun i => by
      have hd : 0 < R.depA i := R.hdepA i
      omega
    cA := fun i => consVec (qExp F) (R.cA i)
    aA := R.aA
    ιB := R.BCqIdx
    finB := by
      dsimp [RelData.BCqIdx]
      infer_instance
    depB := fun p => (p2WpT F (qMinusExp F) (R.hdepB p.1) (R.cB p.1)).dep p.2 + 1
    hdepB := fun p => by
      have hd : 0 < (p2WpT F (qMinusExp F) (R.hdepB p.1) (R.cB p.1)).dep p.2 :=
        (p2WpT F (qMinusExp F) (R.hdepB p.1) (R.cB p.1)).hdep p.2
      omega
    hB2 := fun p => by
      have hd : 0 < (p2WpT F (qMinusExp F) (R.hdepB p.1) (R.cB p.1)).dep p.2 :=
        (p2WpT F (qMinusExp F) (R.hdepB p.1) (R.cB p.1)).hdep p.2
      exact Nat.succ_lt_succ hd
    cB := fun p => consVec oneExp ((p2WpT F (qMinusExp F) (R.hdepB p.1) (R.cB p.1)).c p.2)
    aB := fun p => -(R.aB p.1 * D1rat F * (((p2WpT F (qMinusExp F) (R.hdepB p.1) (R.cB p.1)).f p.2 : ℤ) : RatFunc F)) }

/-- ★ The `BC_q`-iteration recursion (Prop 2.12's `k−j−1` applications). -/
noncomputable def RelData.BCqIter (n : ℕ) (R : RelData F) : RelData F :=
  Nat.iterate (RelData.BCq F) n R

/-- Iterating once prepends one more `q` to every a-tuple. -/
lemma RelData.BCqIter_succ (n : ℕ) (R : RelData F) :
    RelData.BCqIter F (n + 1) R = RelData.BCqIter F n (RelData.BCq F R) := by
  rfl

/-- The a-tuples of the `n`-fold iterate are `n` copies of `q` prepended to the originals:
`depA (BCqIter n R) i = depA R i + n` and `cA (…) i = (q{n}) :: cA R i`; proved at n = 0, 1
(the general case is a short induction, left for the validity step). -/
lemma RelData.BCqIter_one (R : RelData F) : RelData.BCqIter F 1 R = RelData.BCq F R := by
  rfl

/-- The Coe from `RatFunc F` to its completion is a ring homomorphism on negation
(the Coe is NOT defeq to `algebraMap`, so this needs `change` + `map_neg`). -/
lemma ratFunc_coe_neg (x : RatFunc F) :
    (((-x : RatFunc F)) : RatFunc.CompletionAtInfty F) =
      -((x : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-x)) =
    -((algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) x)
  exact map_neg (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) x

/-- The level-`e` value of a data relation: the `R(e)` of the paper for `RelData`. -/
noncomputable def RelData.level (R : RelData F) (e : ℕ) : RatFunc.CompletionAtInfty F :=
  (∑ i : R.ιA, (((R.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (R.depA i) (R.hdepA i) (R.cA i) e)) +
  (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (R.depB j) (R.hdepB j) (R.cB j) (e + 1)))

/-- Level value agrees with `BinaryRel.level` after forgetting validity. -/
lemma RelData.level_toData (R : BinaryRel F) (e : ℕ) :
    RelData.level F (toData F R) e = BinaryRel.level F R e := by
  dsimp [RelData.level, BinaryRel.level, toData]

/-- The image of a data relation's `b`-coefficient under the `BC_q` transform,
as an element of the completion (the paper's (2.12) coefficient): the whole cast of
the negated `RatFunc` product equals the separated ring-hom form. -/
lemma bcoeff_image (a : RatFunc F) (n : ℤ) :
    ((-(a * D1rat F * ((n : ℤ) : RatFunc F))) : RatFunc.CompletionAtInfty F) =
      -(((a : RatFunc F) : RatFunc.CompletionAtInfty F) * D1c F * ((n : ℤ) : RatFunc.CompletionAtInfty F)) := by
  classical
  simp [D1c_eq_D1rat, ratFunc_coe_mul, intCast_ratFunc_completion F]

/-- Negated coefficients pull out of a finite sum. -/
lemma sum_neg_mul {κ : Type} [Fintype κ] (c : κ → RatFunc.CompletionAtInfty F)
    (S : κ → RatFunc.CompletionAtInfty F) :
    (∑ j : κ, (-(c j)) * S j) = - (∑ j : κ, c j * S j) := by
  classical
  calc
    (∑ j : κ, (-(c j)) * S j) = ∑ j : κ, -((c j) * S j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = - (∑ j : κ, c j * S j) := by rw [Finset.sum_neg_distrib]

/-- ★ One `BC_q` step preserves validity: `BC_q(data R)` (as a data relation) is valid
at every level, from `BC_q_pure` (Prop 2.10) applied to the relation `R`.  This is the
paper's (2.12) recurrence: the new `b`-family reindexed over the `p2WpT`-fibers with
coefficients `−a_j·D1·f_e` sums to the same value as the original `b`-sum. -/
theorem BCq_step_valid (R : BinaryRel F) :
    ∀ e : ℕ, RelData.level F (RelData.BCq F (toData F R)) e = 0 := by
  classical
  intro e
  let K := RatFunc.CompletionAtInfty F
  let D := toData F R
  let BD := RelData.BCq F D
  let WP := fun j : R.ιB => p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)
  have hpq := BC_q_pure F (depA := R.depA) (hdepA := R.hdepA) (cA := R.cA) (aA := R.aA)
      (depB := R.depB) (hdepB := R.hdepB) (hB2 := R.hB2) (cB := R.cB) (aB := R.aB)
      R.valid e
  let A := ∑ i : R.ιA, ((R.aA i : RatFunc F) : K) * S F (R.depA i + 1)
      (by omega : 0 < R.depA i + 1) (consVec (qExp F) (R.cA i)) e
  let T := ∑ j : R.ιB, ∑ e' : (WP j).ι,
      ((R.aB j : RatFunc F) : K) * (D1c F * (((WP j).f e' : ℤ) : K)) *
      S F ((WP j).dep e' + 1) (by omega : 0 < (WP j).dep e' + 1)
        (consVec oneExp ((WP j).c e')) (e + 1)
  have hT : A - T = 0 := by
    simpa [A, T, WP, D] using hpq
  have hB : (∑ p : (Σ j : R.ιB, (WP j).ι),
        ((BD.aB p : RatFunc F) : K) *
        S F ((WP p.1).dep p.2 + 1) (by omega : 0 < (WP p.1).dep p.2 + 1)
          (consVec oneExp ((WP p.1).c p.2)) (e + 1)) = -T := by
    calc
      (∑ p : (Σ j : R.ιB, (WP j).ι),
          ((BD.aB p : RatFunc F) : K) *
          S F ((WP p.1).dep p.2 + 1) (by omega : 0 < (WP p.1).dep p.2 + 1)
            (consVec oneExp ((WP p.1).c p.2)) (e + 1))
          = (∑ p : (Σ j : R.ιB, (WP j).ι),
              (-(((R.aB p.1 : RatFunc F) : K) * (D1c F * (((WP p.1).f p.2 : ℤ) : K)))) *
              S F ((WP p.1).dep p.2 + 1) (by omega : 0 < (WP p.1).dep p.2 + 1)
                (consVec oneExp ((WP p.1).c p.2)) (e + 1)) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hd : BD.aB p = -(R.aB p.1 * D1rat F * (((WP p.1).f p.2 : ℤ) : RatFunc F)) := by
              dsimp [BD, D, toData, RelData.BCq, WP]
            have hcoef : ((BD.aB p : RatFunc F) : K) =
                -(((R.aB p.1 : RatFunc F) : K) * (D1c F * (((WP p.1).f p.2 : ℤ) : K))) := by
              rw [hd]
              rw [ratFunc_coe_neg F (R.aB p.1 * D1rat F * (((WP p.1).f p.2 : ℤ) : RatFunc F))]
              rw [ratFunc_coe_mul F (R.aB p.1 * D1rat F) (((WP p.1).f p.2 : ℤ) : RatFunc F)]
              rw [ratFunc_coe_mul F (R.aB p.1) (D1rat F)]
              rw [← D1c_eq_D1rat F]
              rw [intCast_ratFunc_completion F ((WP p.1).f p.2)]
              ring
            rw [hcoef]
      _ = - (∑ p : (Σ j : R.ιB, (WP j).ι),
              (((R.aB p.1 : RatFunc F) : K) * (D1c F * (((WP p.1).f p.2 : ℤ) : K))) *
              S F ((WP p.1).dep p.2 + 1) (by omega : 0 < (WP p.1).dep p.2 + 1)
                (consVec oneExp ((WP p.1).c p.2)) (e + 1)) := by
            rw [sum_neg_mul]
      _ = -T := by
            dsimp [T]
            apply congrArg (fun t : K => -t)
            rw [Fintype.sum_sigma]
  calc
    RelData.level F BD e = A + (∑ p : (Σ j : R.ιB, (WP j).ι),
          ((BD.aB p : RatFunc F) : K) *
          S F ((WP p.1).dep p.2 + 1) (by omega : 0 < (WP p.1).dep p.2 + 1)
            (consVec oneExp ((WP p.1).c p.2)) (e + 1)) := by
          dsimp [RelData.level, BD, D, A, WP, toData, RelData.BCq]
    _ = A + -T := by rw [hB]
    _ = A - T := by rw [sub_eq_add_neg]
    _ = 0 := hT

/-- Rebuild a `BinaryRel` from data plus a level-validity proof. -/
noncomputable def RelData.toBinaryRel (R : RelData F)
    (hv : ∀ e : ℕ, RelData.level F R e = 0) : BinaryRel F :=
  { ιA := R.ιA
    finA := R.finA
    depA := R.depA
    hdepA := R.hdepA
    cA := R.cA
    aA := R.aA
    ιB := R.ιB
    finB := R.finB
    depB := R.depB
    hdepB := R.hdepB
    hB2 := R.hB2
    cB := R.cB
    aB := R.aB
    valid := fun e => by
      simpa [RelData.level] using hv e }

/-- `toData` inverts `toBinaryRel`. -/
lemma RelData.toData_toBinaryRel (R : RelData F) (hv : ∀ e, RelData.level F R e = 0) :
    toData F (RelData.toBinaryRel F R hv) = R := by
  dsimp [toData, RelData.toBinaryRel]

/-- ★ The `BC_q`-iteration preserves validity: every one of the `k−j−1` applications
of Prop 2.10 to the relation of (2.10) yields a valid relation.  Induction over `n`
using `BCq_step_valid` at each step (Prop 2.12's recursion). -/
theorem BCqIter_valid (n : ℕ) (R : BinaryRel F) :
    ∀ e : ℕ, RelData.level F (RelData.BCqIter F n (toData F R)) e = 0 := by
  revert R
  induction n with
  | zero =>
      intro R e
      calc
        RelData.level F (RelData.BCqIter F 0 (toData F R)) e
            = RelData.level F (toData F R) e := by rfl
        _ = BinaryRel.level F R e := by
            dsimp [RelData.level, BinaryRel.level, toData]
        _ = 0 := R.valid e
  | succ n ih =>
      intro R e
      let R1 : BinaryRel F := RelData.toBinaryRel F (RelData.BCq F (toData F R)) (BCq_step_valid F R)
      have hdR1 : toData F R1 = RelData.BCq F (toData F R) := by
        dsimp [R1]
        rw [RelData.toData_toBinaryRel]
      calc
        RelData.level F (RelData.BCqIter F (n + 1) (toData F R)) e
            = RelData.level F (RelData.BCqIter F n (RelData.BCq F (toData F R))) e := by
              rw [RelData.BCqIter_succ]
        _ = RelData.level F (RelData.BCqIter F n (toData F R1)) e := by
              rw [← hdR1]
        _ = 0 := ih R1 e



/-- One BC_q step keeps the a-index type. -/
lemma RelData.BCq_ιA (D : RelData F) : (RelData.BCq F D).ιA = D.ιA := by
  rfl

/-- One BC_q step keeps the a-coefficients. -/
lemma RelData.BCq_aA (D : RelData F) : (RelData.BCq F D).aA = D.aA := by
  dsimp [RelData.BCq]

/-- One BC_q step increases every a-depth by one. -/
lemma RelData.BCq_depA (D : RelData F) (i : D.ιA) :
    (RelData.BCq F D).depA i = D.depA i + 1 := by
  dsimp [RelData.BCq]

/-- One BC_q step prepends q to every a-tuple. -/
lemma RelData.BCq_cA (D : RelData F) (i : D.ιA) :
    (RelData.BCq F D).cA i = consVec (qExp F) (D.cA i) := by
  dsimp [RelData.BCq]

/-- The index type of the `n`-fold iterate is the original `a`-index type. -/
lemma RelData.BCqIter_ιA (n : ℕ) (D : RelData F) :
    (RelData.BCqIter F n D).ιA = D.ιA := by
  revert D
  induction n with
  | zero => intro D; rfl
  | succ n ih =>
      intro D
      calc
        (RelData.BCqIter F (n + 1) D).ιA = (RelData.BCqIter F n (RelData.BCq F D)).ιA := by rfl
        _ = (RelData.BCq F D).ιA := ih (RelData.BCq F D)
        _ = D.ιA := by rfl



noncomputable def RelData.iterIdx (n : ℕ) (D : RelData F) : D.ιA → (RelData.BCqIter F n D).ιA :=
  Eq.mpr (RelData.BCqIter_ιA F n D)

lemma RelData.iterIdx_zero (D : RelData F) (i : D.ιA) :
    RelData.iterIdx F 0 D i = i := by
  rfl

lemma RelData.BCqIter_aA_at (n : ℕ) (D : RelData F) (i : D.ιA) :
    (RelData.BCqIter F n D).aA (RelData.iterIdx F n D i) = D.aA i := by
  revert D i
  induction n with
  | zero => intro D i; rfl
  | succ n ih =>
      intro D i
      have hrec : RelData.BCqIter F (n + 1) D = RelData.BCqIter F n (RelData.BCq F D) := by rfl
      change (RelData.BCq F (RelData.BCqIter F n (RelData.BCq F D))).aA
        (RelData.iterIdx F n (RelData.BCq F D) i) = D.aA i
      · rw [RelData.BCq_aA]
        exact ih (RelData.BCq F D) i

-- a-depths after n iterations = original + n (index transported)
lemma RelData.BCqIter_depA_at (n : ℕ) (D : RelData F) (i : D.ιA) :
    (RelData.BCqIter F n D).depA (RelData.iterIdx F n D i) = D.depA i + n := by
  revert D i
  induction n with
  | zero => intro D i; rfl
  | succ n ih =>
      intro D i
      have hrec : RelData.BCqIter F (n + 1) D = RelData.BCqIter F n (RelData.BCq F D) := by rfl
      change (RelData.BCqIter F n (RelData.BCq F D)).depA
        (RelData.iterIdx F n (RelData.BCq F D) i) = D.depA i + (n + 1)
      · have hih := ih (RelData.BCq F D) i
        -- hih : (BCqIter n (BCq D)).depA (iterIdx n (BCq D) i) = (BCq D).depA i + n
        have hstep : (RelData.BCq F D).depA i = D.depA i + 1 := RelData.BCq_depA F D i
        rw [hih]
        rw [hstep]
        omega



/-- `n` copies of `qExp F` prepended to `c : Fin r → ℕ+` (resulting length `r + n`).
One step adds a `q` at the front. -/
noncomputable def qsTuple (n r : ℕ) (c : Fin r → ℕ+) : Fin (r + n) → ℕ+ :=
  match n with
  | 0 => fun i => c ⟨(i : ℕ), by simpa using i.isLt⟩
  | m + 1 =>
      fun i => (consVec (qExp F) (qsTuple m r c)) ⟨(i : ℕ), i.isLt⟩

/-- qsTuple at `n = 0` is the identity. -/
lemma qsTuple_zero (r : ℕ) (c : Fin r → ℕ+) (i : Fin (r + 0)) :
    qsTuple F 0 r c i = c ⟨(i : ℕ), by simpa using i.isLt⟩ := by
  rfl

/-- The first entry of a nonempty qsTuple is `q`. -/
lemma qsTuple_head (r : ℕ) (c : Fin r → ℕ+) (n : ℕ) :
    (qsTuple F (n + 1) r c) ⟨0, (by omega : 0 < r + (n + 1))⟩ = qExp F := by
  change (consVec (qExp F) (qsTuple F n r c)) ⟨0, (by omega : 0 < (r + n) + 1)⟩ = qExp F
  exact consVec_zero (qExp F) (qsTuple F n r c)

/-- The tail of a nonempty qsTuple is the shorter one. -/
lemma qsTuple_tail (r : ℕ) (c : Fin r → ℕ+) (n : ℕ) (j : Fin (r + n)) :
    (qsTuple F (n + 1) r c) ⟨(j : ℕ) + 1, by omega⟩ = qsTuple F n r c j := by
  change (consVec (qExp F) (qsTuple F n r c)) ⟨(j : ℕ) + 1, (by omega : (j : ℕ) + 1 < (r + n) + 1)⟩ =
    qsTuple F n r c j
  simpa using (consVec_succ (qExp F) (qsTuple F n r c) j)



/-- Value of qsTuple: the first `n` entries are `q`, afterwards it is `c` shifted by `n`. -/
lemma value_qsTuple (n r : ℕ) (c : Fin r → ℕ+) :
    ∀ i : Fin (r + n),
      (qsTuple F n r c i : ℕ+) = if hi : (i : ℕ) < n then qExp F else
        c ⟨(i : ℕ) - n, by
          have hn : n ≤ (i : ℕ) := le_of_not_gt hi
          omega⟩ := by
  classical
  induction n with
  | zero =>
      intro i
      simp [qsTuple]
  | succ n ih =>
      intro i
      by_cases hz : (i : ℕ) = 0
      · have hhead : qsTuple F (n + 1) r c ⟨0, (by omega : 0 < r + (n + 1))⟩ = qExp F :=
          qsTuple_head F r c n
        have hi0 : i = ⟨0, (by omega : 0 < r + (n + 1))⟩ := Fin.ext (by simpa using hz)
        rw [hi0]
        rw [hhead]
        simp
      · have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hz
        let j : Fin (r + n) := ⟨(i : ℕ) - 1, by
          have hlt : (i : ℕ) < r + (n + 1) := i.isLt
          omega⟩
        have hij : i = ⟨(j : ℕ) + 1, by omega⟩ := by
          apply Fin.ext
          simp [j]
          omega
        rw [hij]
        rw [qsTuple_tail F r c n j]
        rw [ih j]
        by_cases hjn : (j : ℕ) < n
        · have h1 : (j : ℕ) + 1 < n + 1 := by omega
          simp [hjn, h1]
        · have h1 : ¬ (j : ℕ) + 1 < n + 1 := by omega
          simp [hjn, h1]

/-- Value of a consVec: `q` at the head, `c` after. -/
lemma value_consVec {m : ℕ} (c : Fin m → ℕ+) (i : Fin (m + 1)) :
    (consVec (qExp F) c i : ℕ+) =
      (if hz : (i : ℕ) = 0 then qExp F else
        c ⟨(i : ℕ) - 1, by omega⟩) := by
  by_cases hz : (i : ℕ) = 0
  · have hi0 : i = ⟨0, (by omega : 0 < m + 1)⟩ := Fin.ext (by simpa using hz)
    rw [hi0]
    rw [consVec_zero]
    simp
  · have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hz
    let j : Fin m := ⟨(i : ℕ) - 1, by
      have hlt : (i : ℕ) < m + 1 := i.isLt
      omega⟩
    have hij : i = ⟨(j : ℕ) + 1, by omega⟩ := by
      apply Fin.ext
      simp [j]
      omega
    rw [hij]
    rw [consVec_succ]
    simp

/-- `n` q's in front of `(q :: c)` is the same tuple as `n+1` q's in front of `c`,
viewed at the matching depths. -/
lemma qsTuple_shift (n r : ℕ) (c : Fin r → ℕ+) :
    (fun x : Fin (r + (n + 1)) =>
      qsTuple F n (r + 1) (consVec (qExp F) c)
        (Fin.cast (by omega : r + (n + 1) = (r + 1) + n) x))
    = qsTuple F (n + 1) r c := by
  funext x
  -- value of the LHS at x:
  have hv1 := value_qsTuple F n (r + 1) (consVec (qExp F) c) (Fin.cast (by omega : r + (n + 1) = (r + 1) + n) x)
  have hv2 := value_qsTuple F (n + 1) r c x
  rw [hv1, hv2]
  -- indices: (Fin.cast … x).val = x.val
  simp only [Fin.cast]
  -- three cases on x.val vs n
  by_cases hlt : (x : ℕ) < n
  · have hlt2 : (x : ℕ) < n + 1 := by omega
    simp [hlt, hlt2]
  · by_cases heq : (x : ℕ) = n
    · have hlt2 : (x : ℕ) < n + 1 := by omega
      have hge : ¬ (x : ℕ) < n := hlt
      -- LHS: else-branch value at index (x − n) = 0 → head q
      have hz : (x : ℕ) - n = 0 := by omega
      simp [hlt, hlt2, heq, hz]
      simpa using (consVec_zero (qExp F) c)
    · -- n < x.val
      have hgt : n < (x : ℕ) := Nat.lt_of_le_of_ne (le_of_not_gt hlt) (by intro hh; exact heq hh.symm)
      have hge2 : ¬ (x : ℕ) < n + 1 := by omega
      have hnz : (x : ℕ) - n ≠ 0 := by omega
      have hidx : (x : ℕ) - n - 1 = (x : ℕ) - (n + 1) := by omega
      simp [hlt, hge2]
      have hv := value_consVec F c ⟨(x : ℕ) - n, by
        have hlt' : (x : ℕ) < r + (n + 1) := x.isLt
        omega⟩
      rw [hv]
      simp [hnz, hidx]



/-- Value of the iterated `a`-tuple (transported index): the first `n` entries are
`q`, then the original tuple shifted by `n`. -/
lemma RelData.BCqIter_cA_value (n : ℕ) (D : RelData F) (i : D.ιA) :
    ∀ x : Fin (D.depA i + n),
      (RelData.BCqIter F n D).cA (RelData.iterIdx F n D i)
        (Fin.cast (RelData.BCqIter_depA_at F n D i).symm x) =
        (if hx : (x : ℕ) < n then qExp F else
          (D.cA i) ⟨(x : ℕ) - n, by
            have hn : n ≤ (x : ℕ) := le_of_not_gt hx
            omega⟩) := by
  classical
  revert D i
  induction n with
  | zero =>
      intro D i x
      change (D.cA i) (Fin.cast (RelData.BCqIter_depA_at F 0 D i).symm x) =
        (if hx : (x : ℕ) < 0 then qExp F else (D.cA i) ⟨(x : ℕ) - 0, by omega⟩)
      have hx0 : ¬ (x : ℕ) < 0 := by omega
      simp [hx0]
  | succ n ih =>
      intro D i x
      let r : ℕ := D.depA i
      let y : Fin ((r + 1) + n) := Fin.cast (by omega : r + (n + 1) = (r + 1) + n) x
      change (RelData.BCqIter F n (RelData.BCq F D)).cA
          (RelData.iterIdx F n (RelData.BCq F D) i)
          (Fin.cast (RelData.BCqIter_depA_at F n (RelData.BCq F D) i).symm y) =
          (if hx : (x : ℕ) < n + 1 then qExp F else
            (D.cA i) ⟨(x : ℕ) - (n + 1), by omega⟩)
      have hih := ih (RelData.BCq F D) i y
      rw [hih]
      change (if h1 : (y : ℕ) < n then qExp F else
            (consVec (qExp F) (D.cA i)) ⟨(y : ℕ) - n, by omega⟩) =
          (if hx : (x : ℕ) < n + 1 then qExp F else
            (D.cA i) ⟨(x : ℕ) - (n + 1), by omega⟩)
      have hyv : (y : ℕ) = (x : ℕ) := by simp [y]
      by_cases hlt : (x : ℕ) < n
      · have h1 : (y : ℕ) < n := by omega
        have h2 : (x : ℕ) < n + 1 := by omega
        simp [hlt, h1, h2]
      · by_cases heq : (x : ℕ) = n
        · have h1 : ¬ (y : ℕ) < n := by omega
          have h2 : (x : ℕ) < n + 1 := by omega
          have hz : (y : ℕ) - n = 0 := by omega
          simp [h1, h2, hz]
          simpa using (consVec_zero (qExp F) (D.cA i))
        · have h1 : ¬ (y : ℕ) < n := by omega
          have h2 : ¬ (x : ℕ) < n + 1 := by omega
          have hnz : (y : ℕ) - n ≠ 0 := by omega
          have hidx2 : (y : ℕ) - n - 1 = (x : ℕ) - (n + 1) := by omega
          simp [h1, h2]
          have hv := value_consVec F (D.cA i) ⟨(y : ℕ) - n, by
            have hlt' : (y : ℕ) < (r + 1) + n := y.isLt
            omega⟩
          rw [hv]
          have hxnz : (x : ℕ) - n ≠ 0 := by omega
          have hidx3 : (x : ℕ) - n - 1 = (x : ℕ) - (n + 1) := by omega
          simp [hnz, hidx2, hxnz, hidx3, hyv]



/-- The `a`-tuple after `n` `BC_q`-iterations (at the transported index) is the tuple
with `n` leading `q`'s in front of the original one. -/
lemma RelData.BCqIter_cA_at (n : ℕ) (D : RelData F) (i : D.ιA) :
    (fun x : Fin (D.depA i + n) =>
      (RelData.BCqIter F n D).cA (RelData.iterIdx F n D i)
        (Fin.cast (RelData.BCqIter_depA_at F n D i).symm x))
    = qsTuple F n (D.depA i) (D.cA i) := by
  funext x
  rw [RelData.BCqIter_cA_value F n D i x]
  rw [value_qsTuple F n (D.depA i) (D.cA i) x]


end ZagierHoffmanPositiveChar
