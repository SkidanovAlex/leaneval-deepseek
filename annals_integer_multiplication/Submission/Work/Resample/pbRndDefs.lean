import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.pbRoundDefs
import Submission.Work.Resample.pbIterGoDefs
import Submission.Work.Resample.axisDefs

/-!
# `Work.Resample.pbIterGoRound`: the round block of `progTensorB`

This module fixes the *interface* of the round block of `progTensorB` (the per-axis step of the
`B̃` half of paper Theorem 4.1), as it is used in `Submission/Work/Resample/pbIterGoRound.lean`:

* `PBL1 … PBL7` — the seven cost atoms of the per-round budget `Work.Resample.PBBracket`
  (`PBBracket = PBL1 + … + PBL7`, `PBBracket_eq_atoms`), so that the three phases of the round can
  state their cost as a constant times a *sum of atoms*;
* `PBS1`, `PBS2` — the intermediate state invariants of the round: `PBS1` is the state after the
  preamble (the table `Pj` has been built by `prep`, the array is back on top of stack 0 with the
  four `LayoutLib.applyAlong` parameters pushed above it), `PBS2` is the state after the slice word
  has been applied to every slice (the new array is on top of the table, the auxiliary stacks are
  those of `PBInv` at round `j+1`).

The round is the composition of three programs

  `round = pbRndStage ; pbRndApply ; pbRndFinish`

proved in `pbRndStage.lean`, `pbRndApply.lean`, `pbRndFinish.lean`, with the invariants
`PBInv j --stage--> PBS1 --apply--> PBS2 --finish--> PBInv (j+1)`.  The assembly (and the
`Kb = 0` degenerate case) is in `Submission/Work/Resample/pbIterGoRound.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-- `HvdH.D` is positive. -/
theorem pbRndD_pos : 0 < D := by decide

/-! ## The cost atoms of `PBBracket` -/

/-- The cost of the `prep` call of one round: `Kb*(t+1)*(p+1)^Kb`. -/
def PBL1 (Kb p t : ℕ) : ℕ := Kb * (t + 1) * (p + 1) ^ Kb

/-- The `A*B*c` part of the `applyAlong` cost of one round (`c` = the slice word's cost). -/
def PBL2 (Kb : ℕ) (Cm : ℕ → ℕ) (p α t s A B : ℕ) : ℕ :=
  A * B *
    (Kb * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) +
      Kb * (t + 1) * (p + 1) ^ 2)

/-- The polynomial overhead of the `applyAlong` call of one round. -/
def PBL3 (p t s A B : ℕ) : ℕ :=
  (A * B * (t + s + 1) + 1) * ((2 * p + 8) + (A * B * (t + s + 1)).size + 1) *
    ((A * B * (t + s + 1)).size + 1)

/-- The cost of parking and unparking the array. -/
def PBL4 (p : ℕ) (ts : List ℕ) : ℕ := 32 * (ts.prod * (2 * p + 8) + 2)

/-- The bookkeeping budget of one round. -/
def PBL5 (D p : ℕ) : ℕ := 800 * (D * (p + 1))

/-- The quadratic cleanup budget of one round. -/
def PBL6 (Kb p : ℕ) (ts : List ℕ) : ℕ := (2 * PBTab Kb p ts + 5) * (2 * PBTab Kb p ts + 5)

/-- The constant overhead of one round. -/
def PBL7 : ℕ := 100

/-- `PBBracket` is the sum of its seven atoms. -/
theorem PBBracket_eq_atoms (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) :
    PBBracket Kb Cm p α ss ts j =
      PBL1 Kb p (ts.getD j 0) + PBL2 Kb Cm p α (ts.getD j 0) (ss.getD j 0)
        (ss.take j).prod (ts.drop (j + 1)).prod +
      PBL3 p (ts.getD j 0) (ss.getD j 0) (ss.take j).prod (ts.drop (j + 1)).prod +
      PBL4 p ts + PBL5 HvdH.D p + PBL6 Kb p ts + PBL7 := rfl

/-! ## The intermediate invariants -/

/-- The state after the preamble of the round: the value stack holds the four `applyAlong`
parameters and the array (which is still the `j`-fold axis application), the table `Pj` sits below
the array and above the marker, the auxiliary stacks are those of `PBInv` at round `j+1` (the
consumed parameters have been peeled off), and the table is shorter than `PBTab`. -/
def PBS1 (p α : ℕ) (ss ts : List ℕ) (Kb : ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (M : Val) (rest : List Val) (j : ℕ) (Pj : List Val) :
    List Val → (Stk → List Val) → Prop :=
  fun vs a =>
    RInv
      ([.int ((ss.take (j + 1)).prod), .int (ts.getD j 0), .int (ss.getD j 0),
          .int ((ts.drop (j + 1)).prod)] ++
        cvecVal (progAxis ss ts Φ j zs0) :: Pj ++ M :: rest)
      [intList (ts.drop (j + 1))] [intList (ss.drop (j + 1))] [.int α] [.int p]
      [.int ((ss.take (j + 1)).prod)] [.int ((ts.drop (j + 1)).prod)] [] [] [] [] [M] [] vs a ∧
    (Pj.map vsz).sum ≤ PBTab Kb p ts

/-- The state after the slice word of the round: the value stack holds the new array (the
`(j+1)`-fold axis application) above the table and the marker, the auxiliary stacks are those of
`PBInv` at round `j+1`, and the table is still shorter than `PBTab`; moreover the new array has the
right length and lies in the disc. -/
def PBS2 (p α : ℕ) (ss ts : List ℕ) (Kb : ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (M : Val) (rest : List Val) (j : ℕ) (Pj : List Val) :
    List Val → (Stk → List Val) → Prop :=
  fun vs a =>
    RInv
      (cvecVal (progAxis ss ts Φ (j + 1) zs0) :: Pj ++ M :: rest)
      [intList (ts.drop (j + 1))] [intList (ss.drop (j + 1))] [.int α] [.int p]
      [.int ((ss.take (j + 1)).prod)] [.int ((ts.drop (j + 1)).prod)] [] [] [] [] [M] [] vs a ∧
    (Pj.map vsz).sum ≤ PBTab Kb p ts ∧
    (progAxis ss ts Φ (j + 1) zs0).length =
      (ss.take (j + 1)).prod * (ts.drop (j + 1)).prod ∧
    (∀ z ∈ progAxis ss ts Φ (j + 1) zs0, inDisc p z)

/-- `PBInv` at round `j` is (up to the order of the conjuncts) the semantic part together with
`RInv`; stated in this form it is the bridge between the phase invariants and `PBInv`. -/
theorem PBInv_bridge (p α : ℕ) (ss ts : List ℕ) (Kb : ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (M : Val) (rest : List Val) (j : ℕ)
    (vs : List Val) (a : Stk → List Val) :
    PBInv p α ss ts Kb Φ zs0 M rest j vs a ↔
      ((progAxis ss ts Φ j zs0).length = (ss.take j).prod * (ts.drop j).prod ∧
        (∀ z ∈ progAxis ss ts Φ j zs0, inDisc p z) ∧
        PBTab Kb p ts < vsz M ∧ vsz M ≤ PBTab Kb p ts + 3) ∧
      RInv (cvecVal (progAxis ss ts Φ j zs0) :: M :: rest)
        [intList (ts.drop j)] [intList (ss.drop j)] [.int α] [.int p]
        [.int ((ss.take j).prod)] [.int ((ts.drop j).prod)] [] [] [] [] [M] [] vs a :=
  PBInv_split p α ss ts Kb Φ zs0 M rest j vs a

/-! ## Toolkit: `Eval` costs and stack growth -/

/-- Every `Eval` has cost at least `1`.  (Used to refute the degenerate case `Kb = 0`, where the
hypothesis `SliceSpecAt` would give `prep` a run of cost `≤ 0`.) -/
theorem pbRnd_one_le_eval {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main c s s' n) : 1 ≤ n := by
  induction h with
  | skip s => simp
  | pop k r s => simp
  | peek k r s => simp
  | push k r s => simp
  | set r c s => simp
  | mov dst src s => simp
  | seq _ _ _ _ => omega
  | iteT _ _ _ => omega
  | iteF _ _ _ => omega
  | loopF _ => simp
  | loopT _ _ _ _ _ => omega
  | self _ _ => omega

/-- An `Eval` of cost `n` grows the raw length of any stack by at most `n`. -/
theorem pbRnd_stkLen_le_cost {main p : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main p s s' n) (k : Stk) : (s'.stk k).length ≤ (s.stk k).length + n := by
  induction h with
  | skip s => simp
  | pop j r s =>
    by_cases hkj : k = j
    · subst hkj
      simp only [Function.update_self, List.length_tail]
      omega
    · simp only [Function.update_apply, ite_eq_right hkj]
      omega
  | peek j r s => simp
  | push j r s =>
    by_cases hkj : k = j
    · subst hkj
      simp only [Function.update_self, List.length_cons]
      omega
    · simp only [Function.update_apply, ite_eq_right hkj]
      omega
  | set r c s => simp
  | mov dst src s => simp
  | seq h1 h2 ih1 ih2 => have := ih1; have := ih2; omega
  | iteT h1 h2 ih => have := ih; omega
  | iteF h1 h2 ih => have := ih; omega
  | loopF h1 => simp
  | loopT h1 h2 h3 ih1 ih2 => have := ih1; have := ih2; omega
  | self h1 ih => have := ih; omega

/-! ## Toolkit: the encoding length of a value list -/

/-- The raw length of `encs vs` is the sum of the sizes of its values. -/
theorem pbRnd_encs_length (vs : List Val) : (encs vs).length = (vs.map vsz).sum := by
  rw [encs, List.length_flatten, List.map_map]
  congr 1

/-! ## Toolkit: list products -/


/-- `(l.take j).prod * (l.drop j).prod = l.prod`. -/
theorem pbRnd_prod_take_mul_drop (l : List ℕ) (j : ℕ) : (l.take j).prod * (l.drop j).prod = l.prod := by
  conv_rhs => rw [← List.take_append_drop j l]
  rw [List.prod_append]

/-- `(l.take (j+1)).prod = (l.take j).prod * l.getD j 0` for `j < l.length`. -/
theorem pbRnd_prod_take_succ (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    (l.take (j + 1)).prod = (l.take j).prod * l.getD j 0 := by
  rw [← List.take_concat_get' l j hj, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    List.getD_eq_getElem l 0 hj]

/-- `(l.drop j).prod = l.getD j 0 * (l.drop (j + 1)).prod` for `j < l.length`. -/
theorem pbRnd_prod_drop_eq_prod (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    (l.drop j).prod = l.getD j 0 * (l.drop (j + 1)).prod := by
  rw [List.drop_eq_getElem_cons hj, List.prod_cons, List.getD_eq_getElem l 0 hj]

/-- The product of a list of naturals `≥ 1` is `≥ 1`. -/
theorem pbRnd_one_le_prod {l : List ℕ} (h : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    calc 1 = 1 * 1 := (mul_one 1).symm
      _ ≤ a * t.prod := Nat.mul_le_mul (h a (List.mem_cons_self ..))
          (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- The product of a list of naturals `≤ b` is `≤ b ^ length`. -/
theorem pbRnd_prod_le_pow (b : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ b) → l.prod ≤ b ^ l.length
  | [], _ => by simp
  | a :: t, h => by
    rw [List.prod_cons, List.length_cons]
    calc a * t.prod ≤ b * b ^ t.length :=
          Nat.mul_le_mul (h a (List.mem_cons_self ..))
            (pbRnd_prod_le_pow b t (fun x hx => h x (List.mem_cons_of_mem a hx)))
      _ = b ^ (t.length + 1) := by ring

/-- The product of a non-empty list of naturals `< b` (`b ≥ 1`) is `< b ^ length`. -/
theorem pbRnd_prod_lt_pow (b : ℕ) (hb : 1 ≤ b) : ∀ l : List ℕ, l ≠ [] → (∀ x ∈ l, x < b) →
    l.prod < b ^ l.length
  | [], h, _ => absurd rfl h
  | a :: t, _, h => by
    have ha : a < b := h a (List.mem_cons_self ..)
    have ht : t.prod ≤ b ^ t.length := pbRnd_prod_le_pow b t (fun x hx => le_of_lt (h x (List.mem_cons_of_mem a hx)))
    rw [List.prod_cons, List.length_cons]
    calc a * t.prod ≤ a * b ^ t.length := Nat.mul_le_mul_left a ht
      _ < b * b ^ t.length := Nat.mul_lt_mul_of_pos_right ha (pow_pos (by omega) t.length)
      _ = b ^ (t.length + 1) := by ring

/-- `(l.take j).prod ≤ l.prod` when every entry is `≥ 1`. -/
theorem pbRnd_prod_take_le (l : List ℕ) {j : ℕ} (h : ∀ x ∈ l, 1 ≤ x) : (l.take j).prod ≤ l.prod := by
  have h1 : 1 ≤ (l.drop j).prod :=
    pbRnd_one_le_prod (fun x hx => h x ((List.drop_sublist j l).subset hx))
  calc (l.take j).prod = (l.take j).prod * 1 := (mul_one _).symm
    _ ≤ (l.take j).prod * (l.drop j).prod := Nat.mul_le_mul_left _ h1
    _ = l.prod := pbRnd_prod_take_mul_drop l j

/-- `(l.drop j).prod ≤ l.prod` when every entry is `≥ 1`. -/
theorem pbRnd_prod_drop_le (l : List ℕ) {j : ℕ} (h : ∀ x ∈ l, 1 ≤ x) : (l.drop j).prod ≤ l.prod := by
  have h1 : 1 ≤ (l.take j).prod :=
    pbRnd_one_le_prod (fun x hx => h x ((List.take_sublist j l).subset hx))
  calc (l.drop j).prod = 1 * (l.drop j).prod := (one_mul _).symm
    _ ≤ (l.take j).prod * (l.drop j).prod := Nat.mul_le_mul_right _ h1
    _ = l.prod := pbRnd_prod_take_mul_drop l j

/-- `(l.take i).prod = ((List.range i).map (fun k => l.getD k 0)).prod` (local copy of
`Work.Resample.prod_take_range_getD`). -/
theorem pbRnd_prod_take_range (l : List ℕ) {i : ℕ} (hi : i ≤ l.length) :
    (l.take i).prod = ((List.range i).map (fun k => l.getD k 0)).prod :=
  prod_take_range_getD l hi

/-- `(Finset.range n).sum (fun j => l.getD j 0) = l.sum` when `l.length = n`. -/
theorem pbRnd_sum_range_getD : ∀ (l : List ℕ) (n : ℕ), l.length = n →
    (Finset.range n).sum (fun j => l.getD j 0) = l.sum := by
  intro l
  induction l with
  | nil =>
    intro n h
    rw [List.length_nil] at h
    rw [← h]
    simp
  | cons a l ih =>
    intro n h
    rcases n with _ | n'
    · simp only [List.length_cons] at h
      exact absurd h (by omega)
    · rw [Finset.sum_range_succ', List.sum_cons, List.getD_cons_zero,
        ← ih n' (by simpa using h)]
      have hcong : (Finset.range n').sum (fun i => (a :: l).getD (i + 1) 0)
          = (Finset.range n').sum (fun i => l.getD i 0) :=
        Finset.sum_congr rfl (fun i _ => by rw [List.getD_cons_succ])
      rw [hcong]
      exact Nat.add_comm _ _

/-! ## Toolkit: arithmetic of `ResParams` -/

/-- `t < 2^p` for every axis of a `ResParams` setting. -/
theorem pbRnd_getD_ts_lt (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts)
    {i : ℕ} (hi : i < D) : ts.getD i 0 < 2 ^ p := by
  obtain ⟨-, -, -, -, -, hdim⟩ := h
  exact (hdim i hi).2.2.1

/-- `2 ≤ s < t` for every axis of a `ResParams` setting. -/
theorem pbRnd_getD_ss (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts)
    {i : ℕ} (hi : i < D) : 2 ≤ ss.getD i 0 ∧ ss.getD i 0 < ts.getD i 0 := by
  obtain ⟨-, -, -, -, -, hdim⟩ := h
  exact ⟨(hdim i hi).1, (hdim i hi).2.1⟩

/-- `ts.length = D = ss.length` in a `ResParams` setting. -/
theorem pbRnd_lengths (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) :
    ss.length = D ∧ ts.length = D := by
  obtain ⟨h1, h2, -⟩ := h
  exact ⟨h1, h2⟩

/-- `3 * D ≤ ts.sum`: every axis has `t i ≥ 3`. -/
theorem pbRnd_sum3D (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) :
    3 * D ≤ ts.sum := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := h
  have h1 : (Finset.range D).sum (fun _ => 3) ≤ (Finset.range D).sum (fun j => ts.getD j 0) :=
    Finset.sum_le_sum (fun j hj => by
      have hjD : j < D := Finset.mem_range.mp hj
      have hh := hdim j hjD
      omega)
  rw [pbRnd_sum_range_getD ts D htslen] at h1
  simpa [Finset.sum_const, smul_eq_mul, mul_comm] using h1

/-- Every entry of `ts` is `≥ 1` in a `ResParams` setting. -/
theorem pbRnd_one_le_ts (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) :
    ∀ x ∈ ts, 1 ≤ x := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  rw [← hix, ← List.getD_eq_getElem ts 0 hi]
  have hD : i < D := by rw [← (pbRnd_lengths p α ss ts h).2]; exact hi
  have hh := (pbRnd_getD_ss p α ss ts h hD).2
  omega

/-- `(ss.take j).prod ≤ (ts.take j).prod` for `j ≤ D`. -/
theorem pbRnd_take_prod_le (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) {j : ℕ} (hj : j ≤ D) :
    (ss.take j).prod ≤ (ts.take j).prod := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := h
  rw [pbRnd_prod_take_range ss (by rw [hsslen]; exact hj), pbRnd_prod_take_range ts (by rw [htslen]; exact hj)]
  refine List.prod_le_prod (fun i hi => ?_)
  simp only [List.mem_range] at hi
  exact le_of_lt (hdim i (by omega)).2.1

/-- `ts.prod` has at most `D * p` bits. -/
theorem pbRnd_size_ts_prod_le (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) :
    ts.prod.size ≤ D * p := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := h
  have hmem : ∀ x ∈ ts, x < 2 ^ p := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    rw [← hix, ← List.getD_eq_getElem ts 0 hi]
    exact pbRnd_getD_ts_lt p α ss ts ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩
      (by rw [← htslen]; exact hi)
  have hne : ts ≠ [] := by
    intro hnil
    rw [hnil] at htslen
    simp only [List.length_nil] at htslen
    have hD := pbRndD_pos
    omega
  have hlt : ts.prod < 2 ^ (D * p) := by
    have h1 : ts.prod < (2 ^ p) ^ ts.length :=
      pbRnd_prod_lt_pow (2 ^ p) Nat.one_le_two_pow ts hne hmem
    rw [← pow_mul, htslen, Nat.mul_comm] at h1
    exact h1
  exact Nat.size_le.mpr hlt

/-- `(ts.drop j).prod` has at most `D * p` bits. -/
theorem pbRnd_size_drop_prod_le (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) (j : ℕ) :
    ((ts.drop j).prod).size ≤ D * p :=
  le_trans (Nat.size_le_size (pbRnd_prod_drop_le ts (pbRnd_one_le_ts p α ss ts h)))
    (pbRnd_size_ts_prod_le p α ss ts h)

/-- `(ss.take j).prod` has at most `D * p` bits (for `j ≤ D`). -/
theorem pbRnd_size_take_prod_le (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) {j : ℕ} (hj : j ≤ D) :
    ((ss.take j).prod).size ≤ D * p := by
  refine le_trans (Nat.size_le_size ?_) (pbRnd_size_ts_prod_le p α ss ts h)
  calc (ss.take j).prod ≤ (ts.take j).prod := pbRnd_take_prod_le p α ss ts h hj
    _ ≤ ts.prod := pbRnd_prod_take_le ts (pbRnd_one_le_ts p α ss ts h)

/-- `PBTab ≥ 3*D*(p+1)` as soon as `Kb ≥ 1`. -/
theorem pbRnd_PBTab_ge (Kb : ℕ) (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) (hKb : 1 ≤ Kb) :
    3 * D * (p + 1) ≤ PBTab Kb p ts := by
  have hsum := pbRnd_sum3D p α ss ts h
  have hpow : p + 1 ≤ (p + 1) ^ Kb := by
    calc p + 1 = (p + 1) ^ 1 := (pow_one _).symm
      _ ≤ (p + 1) ^ Kb := Nat.pow_le_pow_right (by omega) hKb
  have h1 : 3 * D * (p + 1) ≤ (ts.sum + 1) * (p + 1) := by
    have : 3 * D ≤ ts.sum + 1 := by omega
    exact Nat.mul_le_mul_right _ this
  have h2 : 3 * D * (p + 1) ≤ 1 * (ts.sum + 1) * (p + 1) ^ Kb := by
    calc 3 * D * (p + 1) ≤ (ts.sum + 1) * (p + 1) := h1
      _ = 1 * (ts.sum + 1) * (p + 1) := by ring
      _ ≤ 1 * (ts.sum + 1) * (p + 1) ^ Kb := Nat.mul_le_mul_left _ hpow
  have h3 : 1 * (ts.sum + 1) * (p + 1) ^ Kb ≤ Kb * (ts.sum + 1) * (p + 1) ^ Kb :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hKb)
  unfold PBTab
  exact le_trans h2 (le_trans h3 (Nat.le_add_right _ _))

/-- `PBL6 ≥ 36*D*D*(p+1)*(p+1)` in a `ResParams` setting with `Kb ≥ 1`. -/
theorem pbRnd_PBL6_ge (Kb : ℕ) (p α : ℕ) (ss ts : List ℕ) (h : ResParams p α ss ts) (hKb : 1 ≤ Kb) :
    36 * D * D * (p + 1) * (p + 1) ≤ PBL6 Kb p ts := by
  have h1 := pbRnd_PBTab_ge Kb p α ss ts h hKb
  have h2 : 6 * D * (p + 1) ≤ 2 * PBTab Kb p ts := by
    have h3 : 2 * (3 * D * (p + 1)) ≤ 2 * PBTab Kb p ts := Nat.mul_le_mul_left 2 h1
    calc 6 * D * (p + 1) = 2 * (3 * D * (p + 1)) := by ring
      _ ≤ 2 * PBTab Kb p ts := h3
  have h4 : 6 * D * (p + 1) + 5 ≤ 2 * PBTab Kb p ts + 5 := Nat.add_le_add_right h2 5
  have h5 : (6 * D * (p + 1) + 5) * (6 * D * (p + 1) + 5) ≤
      (2 * PBTab Kb p ts + 5) * (2 * PBTab Kb p ts + 5) := Nat.mul_le_mul h4 h4
  have h6 : 36 * D * D * (p + 1) * (p + 1) ≤ (6 * D * (p + 1)) * (6 * D * (p + 1)) := by
    have h7 : 36 * D * D * (p + 1) * (p + 1) = (6 * D * (p + 1)) * (6 * D * (p + 1)) := by ring
    rw [h7]
  have h8 : (6 * D * (p + 1)) * (6 * D * (p + 1)) ≤ (6 * D * (p + 1) + 5) * (6 * D * (p + 1) + 5) :=
    Nat.mul_le_mul (Nat.le_add_right _ 5) (Nat.le_add_right _ 5)
  unfold PBL6
  exact le_trans h6 (le_trans h8 h5)

end Work.Resample
