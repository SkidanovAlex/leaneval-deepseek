import Submission.ZagierHoffmanProof.StepH

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step I: data-carrying witnesses (structures) for Prop 2.1

`P1W`/`P2W` are ∃-Propositions — fine for statements, painful for inductive use (a
witness for each Δ-index must be re-extracted per index).  Here we add the equivalent
*structures* `P1Data`/`P2Data` carrying the same data as plain fields, the forgetful
maps into the ∃-forms, the `Nonempty`-family statements `P1oneD`/`P2oneD` (whose
witnesses are extracted by one `Classical.choice`), and the data bases at depths (1,1)
and (1,2) built from the concrete witness definitions already in StepD/StepE/StepF.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Data witness for Part 1 (paper (2.5)). -/
structure P1Data (r k : ℕ) (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+) where
  ι : Type
  fin : Fintype ι
  dep : ι → ℕ
  hdep : ∀ i, 0 < dep i
  f : ι → ℤ
  c : ∀ i, Fin (dep i) → ℕ+
  hid : ∀ d : ℕ,
    S F r hr a d * S F k hk b d =
      ∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep i) (hdep i) (c i) d
  hle : ∀ i, LePad (c i) a b
  hbd : ∀ i, dep i ≤ r + k

/-- Data witness for Part 2 (paper (2.6)). -/
structure P2Data (r k : ℕ) (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+) where
  ι : Type
  fin : Fintype ι
  dep : ι → ℕ
  hdep : ∀ i, 0 < dep i
  f : ι → ℤ
  c : ∀ i, Fin (dep i) → ℕ+
  hid : ∀ d : ℕ,
    S_lt F r hr a d * S_lt F k hk b d =
      ∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (dep i) (hdep i) (c i) d
  hle : ∀ i, LePad (c i) a b
  hbd : ∀ i, dep i ≤ r + k

/-- Forget the data: a data witness gives the existential statement. -/
theorem p1w_of_data {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+)
    (D : P1Data F r k hr hk a b) : P1W F r k hr hk a b := by
  refine ⟨D.ι, D.fin, D.dep, D.hdep, D.f, D.c, D.hid, D.hle, D.hbd⟩

theorem p2w_of_data {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+)
    (D : P2Data F r k hr hk a b) : P2W F r k hr hk a b := by
  refine ⟨D.ι, D.fin, D.dep, D.hdep, D.f, D.c, D.hid, D.hle, D.hbd⟩

/-- Family statements with extractable witnesses. -/
def P1oneD (k : ℕ) (hk : 0 < k) : Prop :=
  ∀ (v : ℕ+) (W : Fin k → ℕ+), Nonempty (P1Data F 1 k (by omega : 0 < 1) hk (single v) W)

def P2oneD (k : ℕ) (hk : 0 < k) : Prop :=
  ∀ (v : ℕ+) (W : Fin k → ℕ+), Nonempty (P2Data F 1 k (by omega : 0 < 1) hk (single v) W)

/-- Index type of the depth-(1,1) Part-1 data. -/
abbrev p11Idx (x y : ℕ+) := PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1)

noncomputable def p11Dep (x y : ℕ+) : p11Idx x y → ℕ := fun a => match a with
  | Sum.inl _ => 1
  | Sum.inr _ => 2

lemma p11Dep_pos (x y : ℕ+) (a : p11Idx x y) : 0 < p11Dep x y a := by
  cases a with
  | inl u => simp [p11Dep]
  | inr j => simp [p11Dep]

lemma p11Dep_le (x y : ℕ+) (a : p11Idx x y) : p11Dep x y a ≤ 2 := by
  cases a with
  | inl u => simp [p11Dep]
  | inr j => simp [p11Dep]

noncomputable def p11F (x y : ℕ+) : p11Idx x y → ℤ := fun a => match a with
  | Sum.inl _ => (1 : ℤ)
  | Sum.inr j => ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1)

noncomputable def p11C (x y : ℕ+) : ∀ a : p11Idx x y, Fin (p11Dep x y a) → ℕ+ := fun a => match a with
  | Sum.inl _ => single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩
  | Sum.inr j => thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
      have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
      simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩

/-- The depth-(1,1) Part-1 carrier sum equals the product, at every level. -/
lemma p1one_carrier_id (x y : ℕ+) (d : ℕ) :
    (∑ a : p11Idx x y,
      ((p11F F x y a : ℤ) : RatFunc.CompletionAtInfty F) *
      S F (p11Dep x y a) (p11Dep_pos x y a) (p11C x y a) d) =
    S F 1 (by omega : 0 < 1) (single x) d * S F 1 (by omega : 0 < 1) (single y) d := by
  classical
  let T : p11Idx x y → RatFunc.CompletionAtInfty F := fun a =>
    ((p11F F x y a : ℤ) : RatFunc.CompletionAtInfty F) *
    S F (p11Dep x y a) (p11Dep_pos x y a) (p11C x y a) d
  have hsplit : (∑ a : p11Idx x y, T a) =
      T (Sum.inl PUnit.unit) + ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1), T (Sum.inr j) := by
    have hsum := Fintype.sum_sum_type (f := T)
    rw [hsum]
    simp
  calc
    (∑ a : p11Idx x y, T a)
        = S F 1 (by omega : 0 < 1)
            (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
          ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
            ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
            S F 2 (by omega : 0 < 2) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
              have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
              simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d := by
          rw [hsplit]
          simp [T, p11F, p11Dep, p11C]
    _ = S F 1 (by omega : 0 < 1) (single x) d * S F 1 (by omega : 0 < 1) (single y) d := by
          exact (S_one_mul_eq_fin F x y d).symm

/-- Depth-(1,1) Part-1 data witness. -/
noncomputable def p1Data11 (x y : ℕ+) :
    P1Data F 1 1 (by omega : 0 < 1) (by omega : 0 < 1) (single x) (single y) where
  ι := p11Idx x y
  fin := inferInstance
  dep := p11Dep x y
  hdep := p11Dep_pos x y
  f := p11F F x y
  c := p11C x y
  hid := by
    intro d
    exact (p1one_carrier_id F x y d).symm
  hle := by
    intro a
    cases a with
    | inl u => simpa [p11Dep, p11C] using LePad_single_of_sum x y
    | inr j => simpa [p11Dep, p11C] using LePad_thakurExp_of_sum x y ⟨j.1 + 1, by
        have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
        simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩
  hbd := by
    intro a
    exact p11Dep_le x y a

/-- Part-1 data family base at depth 1. -/
theorem p1oneD_one : P1oneD F 1 (by omega : 0 < 1) := by
  intro v W
  rw [fin1_eq_single W]
  exact ⟨p1Data11 F v (W ⟨0, by omega⟩)⟩

/-- Depth-(1,1) Part-2 data witness. -/
noncomputable def p2Data11 (x y : ℕ+) :
    P2Data F 1 1 (by omega : 0 < 1) (by omega : 0 < 1) (single x) (single y) where
  ι := P2Idx x y
  fin := inferInstance
  dep := p2Dep x y
  hdep := p2Dep_pos x y
  f := p2F F x y
  c := p2C x y
  hid := by
    intro d
    exact (p2stuffle_eq F x y d).symm
  hle := by
    intro t
    exact p2C_LePad x y t
  hbd := by
    intro t
    exact p2Dep_le_two x y t

/-- Part-2 data family base at depth 1. -/
theorem p2oneD_one : P2oneD F 1 (by omega : 0 < 1) := by
  intro v W
  rw [fin1_eq_single W]
  exact ⟨p2Data11 F v (W ⟨0, by omega⟩)⟩

/-- Depth-(1,2) Part-1 data witness. -/
noncomputable def p1Data12 (v w1 w2 : ℕ+) :
    P1Data F 1 2 (by omega : 0 < 1) (by omega : 0 < 2) (single v) (pair w1 w2) where
  ι := p1twoIdx v w1 w2
  fin := inferInstance
  dep := p1twoDep v w1 w2
  hdep := p1twoDep_pos v w1 w2
  f := p1twoF F v w1 w2
  c := p1twoC v w1 w2
  hid := by
    intro d
    exact (p1two_carrier_id F v w1 w2 d).symm
  hle := by
    intro a
    cases a with
    | inl u => exact p1two_lePad_pure v w1 w2
    | inr p => exact p1two_lePad_delta v w1 w2 p.1 p.2
  hbd := by
    intro a
    exact p1twoDep_le v w1 w2 a

/-- Part-1 data family base at depth 2. -/
theorem p1oneD_two : P1oneD F 2 (by omega : 0 < 2) := by
  intro v W
  rw [fin2_eq_pair W]
  exact ⟨p1Data12 F v (W ⟨0, by omega⟩) (W ⟨1, by omega⟩)⟩

/-- Depth-(1,2) Part-2 data witness. -/
noncomputable def p2Data12 (v w1 w2 : ℕ+) :
    P2Data F 1 2 (by omega : 0 < 1) (by omega : 0 < 2) (single v) (pair w1 w2) where
  ι := p2twoIdx v w1 w2
  fin := inferInstance
  dep := p2twoDep v w1 w2
  hdep := p2twoDep_pos v w1 w2
  f := p2twoF F v w1 w2
  c := p2twoC v w1 w2
  hid := by
    intro d
    exact (p2two_level F v w1 w2 d).trans (p2two_rhs_eq F v w1 w2 d).symm
  hle := by
    intro a
    cases a with
    | inl u => exact p2two_lePad_pure v w1 w2
    | inr p => cases p with
      | inl t => exact p2two_lePad_stuffle v w1 w2 t
      | inr x => exact p2two_lePad_p1 v w1 w2 x
  hbd := by
    intro a
    exact p2twoDep_le v w1 w2 a

/-- Part-2 data family base at depth 2. -/
theorem p2oneD_two : P2oneD F 2 (by omega : 0 < 2) := by
  intro v W
  rw [fin2_eq_pair W]
  exact ⟨p2Data12 F v (W ⟨0, by omega⟩) (W ⟨1, by omega⟩)⟩
/-- `pad0` of a prepended tuple at index 0 is the head. -/
lemma pad0_cons_zero {m : ℕ} (x : ℕ+) (𝔱 : Fin m → ℕ+) : pad0 (consVec x 𝔱) 0 = (x : ℕ) := by
  change (if h : 0 < m + 1 then ((consVec x 𝔱) ⟨0, h⟩ : ℕ) else 0) = (x : ℕ)
  rw [dif_pos (by omega : 0 < m + 1)]
  exact congrArg (fun q : ℕ+ => (q : ℕ)) (consVec_zero x 𝔱)

/-- Zero-padded sum of `(v) + (w1::W)`. -/
lemma tupPadSum_single_cons {k : ℕ} (v w1 : ℕ+) (W : Fin k → ℕ+) (j : ℕ) :
    tupPadSum (single v) (consVec w1 W) j =
      if j = 0 then (v : ℕ) + (w1 : ℕ) else pad0 W (j - 1) := by
  classical
  by_cases hj : j = 0
  · subst j
    simp [tupPadSum, pad0_single_zero, pad0_cons_zero]
  · have h1 : pad0 (single v) j = 0 := by
      rw [show j = (j - 1) + 1 by omega, pad0_single_succ]
    have h2 : pad0 (consVec w1 W) j = pad0 W (j - 1) := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega]
      exact pad0_consVec w1 W (j - 1)
    calc
      tupPadSum (single v) (consVec w1 W) j
          = pad0 (single v) j + pad0 (consVec w1 W) j := rfl
      _ = pad0 W (j - 1) := by
            rw [h1, h2]
            simp
      _ = if j = 0 then (v : ℕ) + (w1 : ℕ) else pad0 W (j - 1) := by rw [if_neg hj]

/-- Prefix sums of `(v) + (w1::W)`. -/
lemma psumSeq_single_cons {k : ℕ} (v w1 : ℕ+) (W : Fin k → ℕ+) (m : ℕ) :
    psumSeq (tupPadSum (single v) (consVec w1 W)) m =
      (if 0 < m then (v : ℕ) + (w1 : ℕ) else 0) + psumSeq (pad0 W) (m - 1) := by
  classical
  induction m with
  | zero =>
    simp [psumSeq]
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      rw [psumSeq_range_succ]
      have hu : tupPadSum (single v) (consVec w1 W) 0 = (v : ℕ) + (w1 : ℕ) := by
        rw [tupPadSum_single_cons]
        simp
      rw [hu]
      simp [psumSeq]
    · have hm' : 0 < m := Nat.pos_of_ne_zero hm
      rw [psumSeq_range_succ]
      rw [ih]
      have hu : tupPadSum (single v) (consVec w1 W) m = pad0 W (m - 1) := by
        rw [tupPadSum_single_cons]
        have hne : m ≠ 0 := by omega
        simp [hne]
      rw [hu]
      have hmminus : (m + 1) - 1 = m := by omega
      rw [hmminus]
      have hrhs : psumSeq (pad0 W) m = psumSeq (pad0 W) (m - 1) + pad0 W (m - 1) := by
        rw [show m = (m - 1) + 1 by omega]
        exact psumSeq_range_succ (pad0 W) (m - 1)
      rw [hrhs]
      rw [if_pos hm', if_pos (by omega : 0 < m + 1)]
      omega

/-- Values of `(i) + W` at 0 and successors. -/
lemma tupPadSum_single_tail_zero {k : ℕ} (i : ℕ+) (W : Fin k → ℕ+) :
    tupPadSum (single i) W 0 = (i : ℕ) + pad0 W 0 := by
  simp [tupPadSum, pad0_single_zero]

lemma tupPadSum_single_tail_succ {k : ℕ} (i : ℕ+) (W : Fin k → ℕ+) (m : ℕ) :
    tupPadSum (single i) W (m + 1) = pad0 W (m + 1) := by
  simp [tupPadSum, pad0_single_succ]

/-- Prefix sums of `(i) + W` (one step). -/
lemma psumSeq_single_tail {k : ℕ} (i : ℕ+) (W : Fin k → ℕ+) (n : ℕ) :
    psumSeq (tupPadSum (single i) W) (n + 1) = (i : ℕ) + psumSeq (pad0 W) (n + 1) := by
  classical
  induction n with
  | zero =>
    rw [psumSeq_range_succ]
    rw [tupPadSum_single_tail_zero]
    simp [psumSeq]
  | succ n ih =>
    rw [psumSeq_range_succ]
    rw [ih]
    rw [tupPadSum_single_tail_succ]
    rw [psumSeq_range_succ (pad0 W) (n + 1)]
    omega

/-- The cons bound for depth-(k+1) targets: if the tail `c2` is ≤ `(i) + W` in weight and
prefixes, then `a :: c2 ≤ (v) + (w1 :: W)` when `a+i = v+w1` and `a ≤ v+w1`. -/
lemma LePad_cons_k {k L : ℕ} (v w1 a i : ℕ+) (W : Fin k → ℕ+) (c2 : Fin L → ℕ+)
    (hwt2 : weight L c2 = (i : ℕ) + weight k W)
    (hpre2 : ∀ m, psum c2 m ≤ psumSeq (tupPadSum (single i) W) m)
    (ha : (a : ℕ) ≤ (v : ℕ) + (w1 : ℕ))
    (haSum : (a : ℕ) + (i : ℕ) = (v : ℕ) + (w1 : ℕ)) :
    LePad (consVec a c2) (single v) (consVec w1 W) := by
  classical
  constructor
  · rw [weight_consVec, hwt2, weight_single]
    rw [weight_consVec]
    omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single v) (consVec w1 W)) 0
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        by_cases hn : n = 0
        · subst n
          have ht : psumSeq (tupPadSum (single v) (consVec w1 W)) 1 = (v : ℕ) + (w1 : ℕ) := by
            rw [psumSeq_single_cons]
            simp [psumSeq]
          rw [ht]
          have hc : psum c2 0 = 0 := by rw [psum_zero]
          rw [hc]
          exact ha
        · have hn' : 0 < n := Nat.pos_of_ne_zero hn
          have ht : psumSeq (tupPadSum (single v) (consVec w1 W)) (n + 1) =
              (v : ℕ) + (w1 : ℕ) + psumSeq (pad0 W) n := by
            rw [psumSeq_single_cons]
            simp
          rw [ht]
          have hpre := hpre2 n
          have htn : psumSeq (tupPadSum (single i) W) n = (i : ℕ) + psumSeq (pad0 W) n := by
            rw [show n = (n - 1) + 1 by omega]
            exact psumSeq_single_tail i W (n - 1)
          rw [htn] at hpre
          omega

/-- The pure merged term `(⟨v+w1⟩ :: W) ≤ (v) + (w1 :: W)`. -/
lemma LePad_cons_pure_k {k : ℕ} (v w1 : ℕ+) (W : Fin k → ℕ+) :
    LePad (consVec ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩ W)
      (single v) (consVec w1 W) := by
  classical
  let m : ℕ+ := ⟨(v : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos v) (w1 : ℕ)⟩
  change LePad (consVec m W) (single v) (consVec w1 W)
  constructor
  · rw [weight_consVec, weight_single, weight_consVec]
    dsimp [m]
    omega
  · intro n0
    by_cases hm0 : n0 = 0
    · subst n0
      rw [psum_zero]
      simp [psumSeq]
    · rcases n0 with _ | n
      · omega
      · rw [psum_consVec]
        have ht : psumSeq (tupPadSum (single v) (consVec w1 W)) (n + 1) =
            (v : ℕ) + (w1 : ℕ) + psumSeq (pad0 W) n := by
          rw [psumSeq_single_cons]
          simp
        rw [ht]
        dsimp [m]
        change (v : ℕ) + (w1 : ℕ) + psum W n ≤
          (v : ℕ) + (w1 : ℕ) + psumSeq (pad0 W) n
        have hc : psum W n = psumSeq (pad0 W) n := rfl
        omega

end ZagierHoffmanPositiveChar
