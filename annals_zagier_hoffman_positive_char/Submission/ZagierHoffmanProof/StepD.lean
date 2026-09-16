import Submission.ZagierHoffmanProof.StepC

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step D: Prop 2.1 (Thakur shuffle for power sums of arbitrary depth) — scaffolding

The goal (paper Prop 2.1, nd21 §2.1): for exponent tuples `a : Fin r → ℕ+`, `b : Fin k → ℕ+`
(r,k ≥ 1) there are ℤ-coefficient families and tuples `c_i` with
  (Part 1) `S_d(a)·S_d(b) = Σ_i f_i·S_d(c_i)`   for all levels d,
  (Part 2) `S_<d(a)·S_<d(b) = Σ_i f_i·S_<d(c_i)` for all levels d,
where each `c_i` is ≤ `a + b` in the paper's prefix-sum order (zero padding) and has depth
≤ r+k. This file builds the statement scaffolding, the tuple-order toolkit, and proves the
depth-(1,1) base cases in that form.  Coefficients are ℤ (they are Chen's Δ's and 1; they
act on K∞ through the canonical cast).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Singleton exponent tuple of depth 1. -/
noncomputable def single (x : ℕ+) : Fin 1 → ℕ+ := fun _ => x

/-- Head entry (index 0). -/
noncomputable def expHead {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) : ℕ+ := 𝔰 ⟨0, hr⟩

/-- Tail entries (indices 1,…,r-1); the target depth is `r - 1`. -/
noncomputable def expTail {r : ℕ} (𝔰 : Fin r → ℕ+) : Fin (r - 1) → ℕ+ :=
  fun j => 𝔰 ⟨j.1 + 1, by omega⟩

/-- `psumSeq u m = Σ_{j<m} u j` for a (zero-padded) ℕ-valued exponent sequence. -/
noncomputable def psumSeq (u : ℕ → ℕ) (m : ℕ) : ℕ := ∑ j ∈ Finset.range m, u j

/-- The pointwise (zero-padded) sum of two exponent tuples, as a ℕ-sequence. -/
noncomputable def tupPadSum {r k : ℕ} (a : Fin r → ℕ+) (b : Fin k → ℕ+) : ℕ → ℕ :=
  fun j => pad0 a j + pad0 b j

/-- Paper's order `c ≤ a + b` (zero padding): equal total weight and all prefix sums ≤.
The target is the ℕ-sequence `pad0 a + pad0 b`. -/
def LePad {L : ℕ} (c : Fin L → ℕ+) {r k : ℕ} (a : Fin r → ℕ+) (b : Fin k → ℕ+) : Prop :=
  weight L c = weight r a + weight k b ∧
    ∀ m : ℕ, psum c m ≤ psumSeq (tupPadSum a b) m

/-- singleton tuple: entries -/
lemma pad0_single_zero (x : ℕ+) : pad0 (single x) 0 = (x : ℕ) := by
  change (if h : 0 < 1 then ((single x) ⟨0, h⟩ : ℕ) else 0) = (x : ℕ)
  simp [single]

lemma pad0_single_succ (x : ℕ+) (j : ℕ) : pad0 (single x) (j + 1) = 0 := by
  change (if h : j + 1 < 1 then ((single x) ⟨j + 1, h⟩ : ℕ) else 0) = 0
  simp

/-- prefix sum of a singleton tuple is x once m ≥ 1 -/
lemma psum_single_of_pos (x : ℕ+) {m : ℕ} (hm : 0 < m) : psum (single x) m = (x : ℕ) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [psum_succ]
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero, pad0_single_zero]
      simp
    · have hmp : 0 < m := Nat.pos_of_ne_zero hm0
      rw [ih hmp]
      have hmm : m = (m - 1) + 1 := by omega
      rw [hmm, pad0_single_succ]
      simp

/-- weight of a singleton -/
lemma weight_single (x : ℕ+) : weight 1 (single x) = (x : ℕ) := by
  change (∑ i : Fin 1, ((single x i : ℕ))) = (x : ℕ)
  simp [single]

/-- `tupPadSum` of two singletons: `x+y` at index 0, then zeros. -/
lemma tupPadSum_single_single (x y : ℕ+) :
    tupPadSum (single x) (single y) = fun j => if j = 0 then (x : ℕ) + (y : ℕ) else 0 := by
  funext j
  by_cases hj : j = 0
  · subst j
    simp [tupPadSum, pad0_single_zero]
  · have hpos : 0 < j := Nat.pos_of_ne_zero hj
    rw [show j = (j - 1) + 1 by omega]
    change pad0 (single x) ((j - 1) + 1) + pad0 (single y) ((j - 1) + 1) = 0
    rw [pad0_single_succ, pad0_single_succ]

/-- prefix sums of the `(x+y, 0, …)` sequence -/
lemma psumSeq_single_single (x y : ℕ+) (m : ℕ) :
    psumSeq (tupPadSum (single x) (single y)) m = if 0 < m then (x : ℕ) + (y : ℕ) else 0 := by
  classical
  by_cases hm : 0 < m
  · have hf : (Finset.range m).filter (fun j : ℕ => j = 0) = {0} := by
      ext j
      constructor
      · intro hj
        rw [Finset.mem_filter] at hj
        rcases hj with ⟨_, hz⟩
        subst j
        simp
      · intro hj
        rw [Finset.mem_filter]
        simp at hj
        subst j
        constructor <;> simp [hm]
    have hs : (∑ j ∈ Finset.range m, if j = 0 then (x : ℕ) + (y : ℕ) else 0) =
        (x : ℕ) + (y : ℕ) := by
      rw [← Finset.sum_filter (s := Finset.range m) (p := fun j : ℕ => j = 0)
        (f := fun _ : ℕ => (x : ℕ) + (y : ℕ))]
      rw [hf]
      simp
    calc
      psumSeq (tupPadSum (single x) (single y)) m
          = (∑ j ∈ Finset.range m, tupPadSum (single x) (single y) j) := by rfl
      _ = (∑ j ∈ Finset.range m, if j = 0 then (x : ℕ) + (y : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [tupPadSum_single_single]
      _ = (x : ℕ) + (y : ℕ) := hs
      _ = if 0 < m then (x : ℕ) + (y : ℕ) else 0 := by rw [if_pos hm]
  · have hm0 : m = 0 := by omega
    subst m
    simp [psumSeq]

/-- If `w = x + y` then `LePad (single ⟨x+y,…⟩) (single x) (single y)`. -/
lemma LePad_single_of_sum (x y : ℕ+) :
    LePad (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) (single x) (single y) := by
  constructor
  · simp [weight, single]
  · intro m
    by_cases hm : 0 < m
    · have hp : psum (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) m =
            (x : ℕ) + (y : ℕ) := by
            exact psum_single_of_pos ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩ hm
      rw [hp]
      rw [psumSeq_single_single]
      simp [hm]
    · have hm0 : m = 0 := by omega
      subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single x) (single y)) 0
      simp [psumSeq]

/-- A prefix sum never exceeds the total weight. -/
lemma psum_le_weight {r : ℕ} (𝔰 : Fin r → ℕ+) (m : ℕ) : psum 𝔰 m ≤ weight r 𝔰 := by
  classical
  by_cases hm : m ≤ r
  · have hsub : (Finset.range m : Finset ℕ) ⊆ Finset.range r := by
      intro x hx
      have hxm : x < m := Finset.mem_range.mp hx
      exact Finset.mem_range.mpr (by omega)
    calc
      psum 𝔰 m = (∑ j ∈ Finset.range m, pad0 𝔰 j) := by rfl
      _ ≤ (∑ j ∈ Finset.range r, pad0 𝔰 j) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro x hx hxr
            exact Nat.zero_le _
      _ = psum 𝔰 r := by rfl
      _ = weight r 𝔰 := by
            exact psum_ge_depth 𝔰 (le_refl r)
  · have hr : r ≤ m := by omega
    rw [psum_ge_depth 𝔰 hr]

/-- Weight of a depth-two tuple splits as the sum of its two entries. -/
lemma weight_two (𝔱 : Fin 2 → ℕ+) : weight 2 𝔱 = (𝔱 ⟨0, by omega⟩ : ℕ) + (𝔱 ⟨1, by omega⟩ : ℕ) := by
  change (∑ i : Fin 2, (𝔱 i : ℕ)) = (𝔱 ⟨0, by omega⟩ : ℕ) + (𝔱 ⟨1, by omega⟩ : ℕ)
  rw [Fin.sum_univ_two]
  simp

/-- The depth-two tuple `(x,y)`. -/
noncomputable def pair (u v : ℕ+) : Fin 2 → ℕ+ := fun j => if (j : ℕ) = 0 then u else v

lemma pair_zero (u v : ℕ+) : pair u v ⟨0, by omega⟩ = u := by
  change (if (⟨0, by omega⟩ : Fin 2) = 0 then u else v) = u
  simp
lemma pair_one (u v : ℕ+) : pair u v ⟨1, by omega⟩ = v := by
  change (if (⟨1, by omega⟩ : Fin 2) = 0 then u else v) = v
  simp

lemma weight_pair (u v : ℕ+) : weight 2 (pair u v) = (u : ℕ) + (v : ℕ) := by
  rw [weight_two]
  rw [pair_zero, pair_one]

/-- `pad0` of a depth-two tuple at index 0 and 1 -/
lemma pad0_pair_zero (u v : ℕ+) : pad0 (pair u v) 0 = (u : ℕ) := by
  change (if h : 0 < 2 then ((pair u v) ⟨0, h⟩ : ℕ) else 0) = (u : ℕ)
  simp [pad0, pair]

lemma pad0_pair_one (u v : ℕ+) : pad0 (pair u v) 1 = (v : ℕ) := by
  change (if h : 1 < 2 then ((pair u v) ⟨1, h⟩ : ℕ) else 0) = (v : ℕ)
  simp [pad0, pair]

/-- For positive `m`, the prefix sum of the depth-two tuple `(x,y)` is at most `x+y`. -/
lemma psum_pair_le (u v : ℕ+) {m : ℕ} (hm : 0 < m) :
    psum (pair u v) m ≤ (u : ℕ) + (v : ℕ) := by
  have h1 := psum_le_weight (pair u v) m
  rwa [weight_pair] at h1

/-- `LePad (x,y) ≤ (x)+(y)`. -/
lemma LePad_pair_of_sum (x y : ℕ+) : LePad (pair x y) (single x) (single y) := by
  constructor
  · rw [weight_pair]
    simp [weight, single]
  · intro m
    by_cases hm : 0 < m
    · calc
        psum (pair x y) m ≤ (x : ℕ) + (y : ℕ) := psum_pair_le x y hm
        _ = psumSeq (tupPadSum (single x) (single y)) m := by
              rw [psumSeq_single_single]
              simp [hm]
    · have hm0 : m = 0 := by omega
      subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single x) (single y)) 0
      simp [psumSeq]

/-- Weight of `thakurExp A B i` is `A + B`. -/
lemma weight_thakurExp (A B : ℕ) (i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)}) :
    weight 2 (thakurExp A B i) = A + B := by
  rw [weight_two]
  change ((thakurExp A B i) ⟨0, by omega⟩ : ℕ) + ((thakurExp A B i) ⟨1, by omega⟩ : ℕ) = A + B
  have hi : i.1 ≤ A + B - 1 := (Finset.mem_Icc.mp i.2).2
  have hiA : i.1 ≤ A + B := by omega
  simp [thakurExp, hi, hiA]

/-- `LePad (thakurExp (x) (y) i) ≤ (x)+(y)` for every `i ∈ Icc 1 (x+y-1)`. -/
lemma LePad_thakurExp_of_sum (x y : ℕ+) (i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)}) :
    LePad (thakurExp (x : ℕ) (y : ℕ) i) (single x) (single y) := by
  constructor
  · rw [weight_thakurExp]
    simp [weight, single]
  · intro m
    by_cases hm : 0 < m
    · calc
        psum (thakurExp (x : ℕ) (y : ℕ) i) m ≤ weight 2 (thakurExp (x : ℕ) (y : ℕ) i) :=
              psum_le_weight _ _
        _ = (x : ℕ) + (y : ℕ) := by
              rw [weight_thakurExp]
        _ = psumSeq (tupPadSum (single x) (single y)) m := by
              rw [psumSeq_single_single]
              simp [hm]
    · have hm0 : m = 0 := by omega
      subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single x) (single y)) 0
      simp [psumSeq]
/-- Part 1 (paper (2.5)) for the pair of tuples `a,b`: `S_d(a)·S_d(b)` is, for every level
`d`, a ℤ-combination of `S_d(c_i)` where each `c_i ≤ a + b` and has depth ≤ r+k. -/
def P1W (r k : ℕ) (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (dep : ι → ℕ) (hdep : ∀ i, 0 < dep i) (f : ι → ℤ)
      (c : ∀ i, Fin (dep i) → ℕ+),
    (∀ d : ℕ,
      S F r hr a d * S F k hk b d =
        ∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep i) (hdep i) (c i) d) ∧
    (∀ i, LePad (c i) a b) ∧ (∀ i, dep i ≤ r + k)

/-- Part 2 (paper (2.6)): the same statement for the `S_<d` power sums. -/
def P2W (r k : ℕ) (hr : 0 < r) (hk : 0 < k) (a : Fin r → ℕ+) (b : Fin k → ℕ+) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (dep : ι → ℕ) (hdep : ∀ i, 0 < dep i) (f : ι → ℤ)
      (c : ∀ i, Fin (dep i) → ℕ+),
    (∀ d : ℕ,
      S_lt F r hr a d * S_lt F k hk b d =
        ∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (dep i) (hdep i) (c i) d) ∧
    (∀ i, LePad (c i) a b) ∧ (∀ i, dep i ≤ r + k)

/-- The depth-(1,1) product identity at one level `d` (base of Part 1). -/
lemma S_one_mul_eq (x y : ℕ+) (d : ℕ) :
    S F 1 (by omega) (single x) d * S F 1 (by omega) (single y) d =
      S F 1 (by omega)
        (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
        ((ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : ℤ) : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d := by
  calc
    S F 1 (by omega) (single x) d * S F 1 (by omega) (single y) d
        = P F d x * P F d y := by
          rw [S_one_eq_P F d (by omega) (single x)]
          rw [S_one_eq_P F d (by omega) (single y)]
          simp [single]
    _ = P F d ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩ +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
            ((ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : ℤ) : RatFunc.CompletionAtInfty F) *
            S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d := by
          exact diag_level F d x y
    _ = S F 1 (by omega)
          (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
            ((ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : ℤ) : RatFunc.CompletionAtInfty F) *
            S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d := by
          have hp : P F d ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩ =
              S F 1 (by omega)
                (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d := by
            simpa [single] using (S_one_eq_P F d (by omega)
              (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩)).symm
          rw [hp]

/-- The depth-(1,1) `S_<d` stuffle identity at one level `d` (base of Part 2). -/
lemma S_lt_one_mul_eq (x y : ℕ+) (d : ℕ) :
    S_lt F 1 (by omega) (single x) d * S_lt F 1 (by omega) (single y) d =
      S_lt F 2 (by omega) (pair x y) d +
      S_lt F 2 (by omega) (pair y x) d +
      S_lt F 1 (by omega)
        (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
        ((ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d := by
  have hx : single x = (fun _ : Fin 1 => x) := rfl
  have hy : single y = (fun _ : Fin 1 => y) := rfl
  have hxy : single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩ =
      (fun _ : Fin 1 => ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) := rfl
  have hp1 : pair x y = (fun j : Fin 2 => if (j : ℕ) = 0 then x else y) := rfl
  have hp2 : pair y x = (fun j : Fin 2 => if (j : ℕ) = 0 then y else x) := rfl
  rw [hx, hy, hxy, hp1, hp2]
  exact S_lt_one_stuffle F d x y
/-- Reindex: a sum over `{i ∈ Icc 1 N}` equals the same sum indexed by `Fin N` via
`j ↦ j+1` (N ≥ 1). -/
lemma sum_fin_succ_eq_Icc (N : ℕ) (hN : 1 ≤ N) {M : Type*} [AddCommMonoid M]
    (g : {i : ℕ // i ∈ Finset.Icc 1 N} → M) :
    (∑ j : Fin N, g ⟨j.1 + 1, by
      have hj : j.1 < N := j.2
      simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ N)⟩) =
    ∑ i : {i : ℕ // i ∈ Finset.Icc 1 N}, g i := by
  classical
  let e : Fin N ≃ {i : ℕ // i ∈ Finset.Icc 1 N} := {
    toFun := fun j => ⟨j.1 + 1, by
      have hj : j.1 < N := j.2
      simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ N)⟩
    invFun := fun i => ⟨i.1 - 1, by
      have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
      have hin : i.1 ≤ N := (Finset.mem_Icc.mp i.2).2
      omega⟩
    left_inv := by
      intro j
      apply Fin.ext
      dsimp
    right_inv := by
      intro i
      apply Subtype.ext
      dsimp
      have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
      omega }
  simpa [e] using (Equiv.sum_comp (e := e) (g := fun i : {i : ℕ // i ∈ Finset.Icc 1 N} => g i))

/-- The depth-(1,1) product identity, Δ-terms indexed by `Fin (x+y-1)`. -/
lemma S_one_mul_eq_fin (x y : ℕ+) (d : ℕ) :
    S F 1 (by omega) (single x) d * S F 1 (by omega) (single y) d =
      S F 1 (by omega)
        (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
      ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
        ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
          have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
          simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d := by
  classical
  have hN : 1 ≤ (x : ℕ) + (y : ℕ) - 1 := by
    have hx1 : 1 ≤ (x : ℕ) := PNat.pos x
    have hy1 : 1 ≤ (y : ℕ) := PNat.pos y
    omega
  rw [S_one_mul_eq F x y d]
  congr 1
  symm
  exact sum_fin_succ_eq_Icc ((x : ℕ) + (y : ℕ) - 1) hN
    (fun i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)} =>
      ((ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : ℤ) : RatFunc.CompletionAtInfty F) *
      S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d)

/-- The depth-(1,1) `S_<d` stuffle, Δ-terms indexed by `Fin (x+y-1)`. -/
lemma S_lt_one_mul_eq_fin (x y : ℕ+) (d : ℕ) :
    S_lt F 1 (by omega) (single x) d * S_lt F 1 (by omega) (single y) d =
      S_lt F 2 (by omega) (pair x y) d +
      S_lt F 2 (by omega) (pair y x) d +
      S_lt F 1 (by omega)
        (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
      ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
        ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
          have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
          simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d := by
  classical
  have hN : 1 ≤ (x : ℕ) + (y : ℕ) - 1 := by
    have hx1 : 1 ≤ (x : ℕ) := PNat.pos x
    have hy1 : 1 ≤ (y : ℕ) := PNat.pos y
    omega
  rw [S_lt_one_mul_eq F x y d]
  congr 1
  symm
  exact sum_fin_succ_eq_Icc ((x : ℕ) + (y : ℕ) - 1) hN
    (fun i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)} =>
      ((ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d)

/-- `LePad (y,x) ≤ (x)+(y)`: the symmetric pair is also ≤ the same target. -/
lemma LePad_pair_swap_of_sum (x y : ℕ+) : LePad (pair y x) (single x) (single y) := by
  constructor
  · rw [weight_pair]
    simp [weight, single]
    omega
  · intro m
    by_cases hm : 0 < m
    · calc
        psum (pair y x) m ≤ (y : ℕ) + (x : ℕ) := psum_pair_le y x hm
        _ = (x : ℕ) + (y : ℕ) := by omega
        _ = psumSeq (tupPadSum (single x) (single y)) m := by
              rw [psumSeq_single_single]
              simp [hm]
    · have hm0 : m = 0 := by omega
      subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single x) (single y)) 0
      simp [psumSeq]

end ZagierHoffmanPositiveChar
