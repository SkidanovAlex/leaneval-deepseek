import Submission.ZagierHoffmanProof.StepD2

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step E: Prop 2.1 — depth-1 × arbitrary-depth family and the first cons step `p1two`

EVERYTHING in §2.2–3 multiplies power sums with one factor of depth 1, so the engine is
the two families
  P1one k : ∀ v W (W of depth k), P1W F 1 k (single v) W     (2.5)
  P2one k : ∀ v W, P2W F 1 k (single v) W                   (2.6)
mutually inducted over k.  This file:
  • P1one/P2one, base-family conversions (p1one_one/p2one_one);
  • combo_prepend (P_d(x)·(Σ f·S_<d) = Σ f·S_d(x::…));
  • p1two_level — the depth (1,2) level identity (P-factored, ∀ d);
  • concrete witness data for the depth-(1,1) S_<d stuffle: p2Dep/p2HDp/p2F/p2C over the
    index type P2Idx x y, with p2stuffle_eq (the combo equals the depth-1 product);
  • prefix/order tools for cons steps (pad0_consVec, psum_consVec, psumSeq_single_pair,
    LePad_prepend_cons, LePad_merge_pair);
  • ★ p1two : P1W F 1 2 (single v) (pair t1 t2) — the first inductive cons step.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Part 1 of Prop 2.1 with the first factor of depth 1, second factor of depth `k`. -/
def P1one (k : ℕ) (hk : 0 < k) : Prop :=
  ∀ (v : ℕ+) (W : Fin k → ℕ+), P1W F 1 k (by omega : 0 < 1) hk (single v) W

/-- Part 2 of Prop 2.1 with the first factor of depth 1, second factor of depth `k`. -/
def P2one (k : ℕ) (hk : 0 < k) : Prop :=
  ∀ (v : ℕ+) (W : Fin k → ℕ+), P2W F 1 k (by omega : 0 < 1) hk (single v) W

/-- Any depth-one tuple is the singleton of its value. -/
lemma fin1_eq_single (W : Fin 1 → ℕ+) : W = single (W ⟨0, by omega⟩) := by
  funext j
  fin_cases j
  simp [single]

/-- Any depth-two tuple is the pair of its entries. -/
lemma fin2_eq_pair (W : Fin 2 → ℕ+) : W = pair (W ⟨0, by omega⟩) (W ⟨1, by omega⟩) := by
  funext j
  fin_cases j <;> simp [pair]

/-- P1one 1 = the depth-(1,1) base. -/
theorem p1one_one : P1one F 1 (by omega : 0 < 1) := by
  intro v W
  rw [fin1_eq_single W]
  exact part1_base F v (W ⟨0, by omega⟩)

/-- P2one 1 = the depth-(1,1) stuffle base. -/
theorem p2one_one : P2one F 1 (by omega : 0 < 1) := by
  intro v W
  rw [fin1_eq_single W]
  exact part2_base F v (W ⟨0, by omega⟩)

/-- `P_d(x) · (Σ f_i·S_<d(c_i)) = Σ f_i·S_d(x :: c_i)`. -/
lemma combo_prepend (d : ℕ) (x : ℕ+) {ι : Type} [Fintype ι]
    (dep : ι → ℕ) (hdep : ∀ i, 0 < dep i) (f : ι → ℤ) (c : ∀ i, Fin (dep i) → ℕ+) :
    (P F d x) * (∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F (dep i) (hdep i) (c i) d) =
    ∑ i, ((f i : ℤ) : RatFunc.CompletionAtInfty F) *
      S F (dep i + 1) (by omega) (consVec x (c i)) d := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (P F d x) * (((f i : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F (dep i) (hdep i) (c i) d)
        = ((f i : ℤ) : RatFunc.CompletionAtInfty F) *
          (P F d x * S_lt F (dep i) (hdep i) (c i) d) := by ring
    _ = ((f i : ℤ) : RatFunc.CompletionAtInfty F) *
        S F (dep i + 1) (by omega) (consVec x (c i)) d := by
          rw [S_prepend F d x (hdep i) (c i)]

/-- The depth-(1,2) product identity at a single level `d` (cons case k=1), P-factored.
Valid ∀ d. -/
lemma p1two_level (v t1 t2 : ℕ+) (d : ℕ) :
    S F 1 (by omega : 0 < 1) (single v) d *
        S F 2 (by omega : 0 < 2) (pair t1 t2) d =
      S F 2 (by omega : 0 < 2) (pair
        ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (t1 : ℕ) - 1)},
        (ChenDeltaZ F (v : ℕ) (t1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        P F d ⟨(v : ℕ) + (t1 : ℕ) - i.1, by
            have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
            have hin : i.1 ≤ (v : ℕ) + (t1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
            omega⟩ *
        (S_lt F 2 (by omega : 0 < 2) (pair
            ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩ t2) d +
         S_lt F 2 (by omega : 0 < 2) (pair
            t2 ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d +
         S_lt F 1 (by omega : 0 < 1) (single
            ⟨i.1 + (t2 : ℕ), Nat.add_pos_left (Finset.mem_Icc.mp i.2).1 (t2 : ℕ)⟩) d +
         ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (i.1 + (t2 : ℕ) - 1)},
           (ChenDeltaZ F i.1 (t2 : ℕ) j.1 : RatFunc.CompletionAtInfty F) *
           S_lt F 2 (by omega : 0 < 2) (thakurExp i.1 (t2 : ℕ) j) d) := by
  classical
  by_cases hd : d = 0
  · subst d
    have hS0 : S F 1 (by omega : 0 < 1) (single v) 0 = P F 0 v := by
      simpa [single] using S_one_eq_P F 0 (by omega) (single v)
    have hlt (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) : S_lt F r hr 𝔰 0 = 0 := by
      rw [S_lt_eq_sum_levels F r hr 𝔰 0]
      simp
    rw [hS0]
    rw [P_zero_eq_one F v]
    rw [S_two_zero F (pair t1 t2)]
    rw [S_two_zero F (pair
      ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2)]
    simp [hlt]
  · have hd1 : 1 ≤ d := by omega
    have hS : S F 1 (by omega : 0 < 1) (single v) d = P F d v :=
      S_one_eq_P F d (by omega) (single v)
    rw [hS]
    exact S_two_mul_P_stuffle F d hd1 v t1 t2

/-- `pad0` of a prepended tuple: entries beyond the head are the tail's pad. -/
lemma pad0_consVec {m : ℕ} (x : ℕ+) (𝔱 : Fin m → ℕ+) (j : ℕ) :
    pad0 (consVec x 𝔱) (j + 1) = pad0 𝔱 j := by
  classical
  by_cases hj : j < m
  · have hmem : j + 1 < m + 1 := by omega
    rw [show pad0 (consVec x 𝔱) (j + 1) =
        ((consVec x 𝔱) ⟨j + 1, hmem⟩ : ℕ) by simp [pad0, hmem]]
    have hc : (consVec x 𝔱) ⟨j + 1, hmem⟩ = 𝔱 ⟨j, hj⟩ := by
      simpa using consVec_succ x 𝔱 ⟨j, hj⟩
    rw [hc]
    change (𝔱 ⟨j, hj⟩ : ℕ) = pad0 𝔱 j
    simp [pad0, hj]
  · have hge : m ≤ j := by omega
    have hmem : ¬ j + 1 < m + 1 := by omega
    rw [show pad0 (consVec x 𝔱) (j + 1) = 0 by simp [pad0, hmem]]
    exact (pad0_of_ge 𝔱 hge).symm

/-- Prefix sums of a prepended tuple. -/
lemma psum_consVec {m : ℕ} (x : ℕ+) (𝔱 : Fin m → ℕ+) (n : ℕ) :
    psum (consVec x 𝔱) (n + 1) = (x : ℕ) + psum 𝔱 n := by
  induction n with
  | zero =>
    have h0 : pad0 (consVec x 𝔱) 0 = (x : ℕ) := by
      change (if h : 0 < m + 1 then ((consVec x 𝔱) ⟨0, h⟩ : ℕ) else 0) = (x : ℕ)
      rw [dif_pos (by omega : 0 < m + 1)]
      exact congrArg (fun q : ℕ+ => (q : ℕ)) (consVec_zero x 𝔱)
    rw [psum_succ, psum_zero, h0]
    simp [psum_zero]
  | succ n ih =>
    rw [psum_succ]
    rw [ih]
    rw [psum_succ]
    rw [pad0_consVec]
    omega
/-- `pad0` of a two-tuple beyond depth 2 is zero. -/
lemma pad0_pair_of_ge (u v : ℕ+) {j : ℕ} (h : 2 ≤ j) : pad0 (pair u v) j = 0 := by
  change (if hj : j < 2 then ((pair u v) ⟨j, hj⟩ : ℕ) else 0) = 0
  have hnot : ¬ j < 2 := by omega
  simp [hnot]

/-- The zero-padded sum target `(v) + (t1,t2)`: `v+t1` at 0, `t2` at 1, then 0. -/
lemma tupPadSum_single_pair (v t1 t2 : ℕ+) :
    tupPadSum (single v) (pair t1 t2) = fun j =>
      if j = 0 then (v : ℕ) + (t1 : ℕ) else if j = 1 then (t2 : ℕ) else 0 := by
  funext j
  by_cases hj0 : j = 0
  · subst j
    simp [tupPadSum, pad0_single_zero, pad0_pair_zero]
  · have hj0' : 0 < j := Nat.pos_of_ne_zero hj0
    by_cases hj1 : j = 1
    · subst j
      simp [tupPadSum, pad0_single_succ, pad0_pair_one]
    · have hj2 : 2 ≤ j := by omega
      have h1v : pad0 (single v) j = 0 := by
        rw [show j = (j - 1) + 1 by omega, pad0_single_succ]
      have h1p : pad0 (pair t1 t2) j = 0 := pad0_pair_of_ge t1 t2 hj2
      change pad0 (single v) j + pad0 (pair t1 t2) j =
        (if j = 0 then (v : ℕ) + (t1 : ℕ) else if j = 1 then (t2 : ℕ) else 0)
      rw [h1v, h1p, if_neg hj0, if_neg hj1]

/-- `psumSeq` successor step (local). -/
lemma psumSeq_range_succ (u : ℕ → ℕ) (m : ℕ) : psumSeq u (m + 1) = psumSeq u m + u m := by
  change (∑ j ∈ Finset.range (m + 1), u j) = (∑ j ∈ Finset.range m, u j) + u m
  rw [Finset.sum_range_succ]

/-- First prefix of `(v) + (t1,t2)` is `v + t1`. -/
lemma psumSeq_single_pair_one (v t1 t2 : ℕ+) :
    psumSeq (tupPadSum (single v) (pair t1 t2)) 1 = (v : ℕ) + (t1 : ℕ) := by
  rw [psumSeq_range_succ]
  simp [psumSeq, tupPadSum_single_pair]

/-- Long prefixes of `(v) + (t1,t2)` (length ≥ 2) are the full weight. -/
lemma psumSeq_single_pair_ge (v t1 t2 : ℕ+) {m : ℕ} (hm : 2 ≤ m) :
    psumSeq (tupPadSum (single v) (pair t1 t2)) m = (v : ℕ) + (t1 : ℕ) + (t2 : ℕ) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm2 : 2 ≤ m
    · calc
        psumSeq (tupPadSum (single v) (pair t1 t2)) (m + 1)
            = psumSeq (tupPadSum (single v) (pair t1 t2)) m +
              tupPadSum (single v) (pair t1 t2) m := psumSeq_range_succ _ _
        _ = (v : ℕ) + (t1 : ℕ) + (t2 : ℕ) := by
              rw [ih hm2]
              rw [tupPadSum_single_pair]
              have hm0 : m ≠ 0 := by omega
              have hm1 : m ≠ 1 := by omega
              simp [hm0, hm1]
    · have hmeq : m = 1 := by omega
      subst m
      calc
        psumSeq (tupPadSum (single v) (pair t1 t2)) (1 + 1)
            = psumSeq (tupPadSum (single v) (pair t1 t2)) 1 +
              tupPadSum (single v) (pair t1 t2) 1 := psumSeq_range_succ _ _
        _ = (v : ℕ) + (t1 : ℕ) + (t2 : ℕ) := by
              rw [psumSeq_single_pair_one]
              rw [tupPadSum_single_pair]
              simp

/-- The generic "prepend" bound used by cons steps. -/
lemma LePad_prepend_cons (v t1 t2 a i : ℕ+) (ha : (a : ℕ) ≤ (v : ℕ) + (t1 : ℕ))
    (haSum : (a : ℕ) + (i : ℕ) = (v : ℕ) + (t1 : ℕ)) {L : ℕ} (c : Fin L → ℕ+)
    (hwt : weight L c = (i : ℕ) + (t2 : ℕ))
    (hpre : ∀ m : ℕ, psum c m ≤ (i : ℕ) + (t2 : ℕ)) :
    LePad (consVec a c) (single v) (pair t1 t2) := by
  constructor
  · rw [weight_consVec]
    rw [hwt]
    rw [weight_single, weight_pair]
    omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single v) (pair t1 t2)) 0
      simp [psumSeq]
    · rcases m with _ | n
      · omega
      · rw [psum_consVec]
        by_cases hn : n = 0
        · subst n
          have ht : psumSeq (tupPadSum (single v) (pair t1 t2)) 1 = (v : ℕ) + (t1 : ℕ) :=
            psumSeq_single_pair_one v t1 t2
          rw [ht]
          have hc0 : psum c 0 = 0 := by
            rw [psum_zero]
          rw [hc0]
          exact ha
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          have hge2 : 2 ≤ n + 1 := by omega
          have ht : psumSeq (tupPadSum (single v) (pair t1 t2)) (n + 1) =
              (v : ℕ) + (t1 : ℕ) + (t2 : ℕ) := psumSeq_single_pair_ge v t1 t2 hge2
          rw [ht]
          have hb : psum c n ≤ (i : ℕ) + (t2 : ℕ) := hpre n
          omega

/-- The pure merged term of the (1,2) product is ≤ `(v) + (t1,t2)`. -/
lemma LePad_merge_pair (v t1 t2 : ℕ+) :
    LePad (pair ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2)
      (single v) (pair t1 t2) := by
  let m1 : ℕ+ := ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩
  have hcoe : (m1 : ℕ) = (v : ℕ) + (t1 : ℕ) := by
    dsimp [m1]
  change LePad (pair m1 t2) (single v) (pair t1 t2)
  constructor
  · rw [weight_two, pair_zero, pair_one, weight_single, weight_pair]
    rw [hcoe]
    omega
  · intro m
    by_cases hm0 : m = 0
    · subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single v) (pair t1 t2)) 0
      simp [psumSeq]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hp : psum (pair m1 t2) m ≤ (m1 : ℕ) + (t2 : ℕ) := psum_pair_le m1 t2 hmpos
      have hcoe : (m1 : ℕ) = (v : ℕ) + (t1 : ℕ) := by
        dsimp [m1]
      by_cases hm1 : 1 < m
      · have hge2 : 2 ≤ m := by omega
        have ht : psumSeq (tupPadSum (single v) (pair t1 t2)) m =
            (v : ℕ) + (t1 : ℕ) + (t2 : ℕ) := psumSeq_single_pair_ge v t1 t2 hge2
        rw [ht]
        rwa [hcoe] at hp
      · have hm1eq : m = 1 := by omega
        subst m
        rw [psum_succ, psum_zero]
        have h0 : pad0 (pair m1 t2) 0 = (m1 : ℕ) := by
          change (if h : 0 < 2 then ((pair m1 t2) ⟨0, h⟩ : ℕ) else 0) = (m1 : ℕ)
          rw [dif_pos (by omega : 0 < 2)]
          exact congrArg (fun q : ℕ+ => (q : ℕ)) (pair_zero m1 t2)
        rw [h0, psumSeq_single_pair_one, hcoe]
        simp

/-- Concrete witness data for the depth-(1,1) `S_<d` stuffle over `P2Idx x y`. -/
noncomputable def p2Dep (x y : ℕ+) : P2Idx x y → ℕ := fun t => match t with
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => 2

lemma p2Dep_pos (x y : ℕ+) (t : P2Idx x y) : 0 < p2Dep x y t := by
  cases t with
  | inl u => simp [p2Dep]
  | inr t2 => cases t2 with
    | inl u => simp [p2Dep]
    | inr t3 => cases t3 with
      | inl u => simp [p2Dep]
      | inr j => simp [p2Dep]

lemma p2Dep_le_two (x y : ℕ+) (t : P2Idx x y) : p2Dep x y t ≤ 2 := by
  cases t with
  | inl u => simp [p2Dep]
  | inr t2 => cases t2 with
    | inl u => simp [p2Dep]
    | inr t3 => cases t3 with
      | inl u => simp [p2Dep]
      | inr j => simp [p2Dep]

noncomputable def p2F (x y : ℕ+) : P2Idx x y → ℤ := fun t => match t with
  | Sum.inl _ => (1 : ℤ)
  | Sum.inr (Sum.inl _) => (1 : ℤ)
  | Sum.inr (Sum.inr (Sum.inl _)) => (1 : ℤ)
  | Sum.inr (Sum.inr (Sum.inr j)) => ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1)

noncomputable def p2C (x y : ℕ+) : ∀ t : P2Idx x y, Fin (p2Dep x y t) → ℕ+ := fun t => match t with
  | Sum.inl _ => pair x y
  | Sum.inr (Sum.inl _) => pair y x
  | Sum.inr (Sum.inr (Sum.inl _)) => single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩
  | Sum.inr (Sum.inr (Sum.inr j)) => thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
      have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
      simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩

/-- Weight of every stuffle output is `x + y`; prefix sums are bounded by it. -/
lemma p2C_weight (x y : ℕ+) (t : P2Idx x y) : weight (p2Dep x y t) (p2C x y t) = (x : ℕ) + (y : ℕ) := by
  cases t with
  | inl u =>
    change weight 2 (pair x y) = (x : ℕ) + (y : ℕ)
    exact weight_pair x y
  | inr t2 => cases t2 with
    | inl u =>
      change weight 2 (pair y x) = (x : ℕ) + (y : ℕ)
      rw [weight_pair]
      omega
    | inr t3 => cases t3 with
      | inl u =>
        change weight 1 (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) =
          (x : ℕ) + (y : ℕ)
        exact weight_single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩
      | inr j =>
        change weight 2 (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
          have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
          simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) =
          (x : ℕ) + (y : ℕ)
        exact weight_thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
          have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
          simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩

lemma p2C_prefix_le (x y : ℕ+) (t : P2Idx x y) (m : ℕ) :
    psum (p2C x y t) m ≤ (x : ℕ) + (y : ℕ) := by
  have h1 := psum_le_weight (p2C x y t) m
  rwa [p2C_weight] at h1

/-- `LePad` for every stuffle output: `p2C x y t ≤ (x) + (y)`. -/
lemma p2C_LePad (x y : ℕ+) (t : P2Idx x y) : LePad (p2C x y t) (single x) (single y) := by
  constructor
  · rw [p2C_weight]
    simp [weight, single]
  · intro m
    by_cases hm : 0 < m
    · calc
        psum (p2C x y t) m ≤ (x : ℕ) + (y : ℕ) := p2C_prefix_le x y t m
        _ = psumSeq (tupPadSum (single x) (single y)) m := by
              rw [psumSeq_single_single]
              simp [hm]
    · have hm0 : m = 0 := by omega
      subst m
      rw [psum_zero]
      change (0 : ℕ) ≤ psumSeq (tupPadSum (single x) (single y)) 0
      simp [psumSeq]

/-- The stuffle combo of depth-1 tuples equals their `S_<d` product, at every level. -/
lemma p2stuffle_eq (x y : ℕ+) (d : ℕ) :
    (∑ t : P2Idx x y, ((p2F F x y t : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F (p2Dep x y t) (p2Dep_pos x y t) (p2C x y t) d) =
    S_lt F 1 (by omega : 0 < 1) (single x) d *
      S_lt F 1 (by omega : 0 < 1) (single y) d := by
  classical
  let G : P2Idx x y → RatFunc.CompletionAtInfty F := fun t =>
    ((p2F F x y t : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F (p2Dep x y t) (p2Dep_pos x y t) (p2C x y t) d
  have h1 : (∑ t : P2Idx x y, G t) =
      G (Sum.inl PUnit.unit) +
        ∑ b : PUnit ⊕ PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr b) := by
    have hsum := Fintype.sum_sum_type (f := G)
    rw [hsum]
    simp
  have h2 : (∑ b : PUnit ⊕ PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr b)) =
      G (Sum.inr (Sum.inl PUnit.unit)) +
        ∑ w : PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr (Sum.inr w)) := by
    have hsum := Fintype.sum_sum_type
      (f := fun b : PUnit ⊕ (PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1)) => G (Sum.inr b))
    rw [hsum]
    simp
  have h3 : (∑ w : PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr (Sum.inr w))) =
      G (Sum.inr (Sum.inr (Sum.inl PUnit.unit))) +
        ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr (Sum.inr (Sum.inr j))) := by
    have hsum := Fintype.sum_sum_type
      (f := fun w : PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1) => G (Sum.inr (Sum.inr w)))
    rw [hsum]
    simp
  calc
    (∑ t : P2Idx x y, G t)
        = S_lt F 2 (by omega : 0 < 2) (pair x y) d +
            S_lt F 2 (by omega : 0 < 2) (pair y x) d +
            S_lt F 1 (by omega : 0 < 1)
              (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
            ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
              ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F 2 (by omega : 0 < 2) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
                have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
                simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d := by
          rw [h1, h2, h3]
          simp [G, p2F, p2Dep, p2C]
          ac_rfl
    _ = S_lt F 1 (by omega : 0 < 1) (single x) d * S_lt F 1 (by omega : 0 < 1) (single y) d := by
          exact (S_lt_one_mul_eq_fin F x y d).symm

/-- The depth-(1,2) product identity, Δ-terms indexed by `Fin N`, N = v+t1-1. -/
lemma p1two_level_fin (v t1 t2 : ℕ+) (d : ℕ) :
    S F 1 (by omega : 0 < 1) (single v) d *
        S F 2 (by omega : 0 < 2) (pair t1 t2) d =
      S F 2 (by omega : 0 < 2) (pair
        ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2) d +
      ∑ j : Fin ((v : ℕ) + (t1 : ℕ) - 1),
        (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
        P F d ⟨(v : ℕ) + (t1 : ℕ) - (j.1 + 1), by
            have hj : j.1 < (v : ℕ) + (t1 : ℕ) - 1 := j.2
            omega⟩ *
        (S_lt F 2 (by omega : 0 < 2) (pair
            ⟨j.1 + 1, by
              have hj : j.1 < (v : ℕ) + (t1 : ℕ) - 1 := j.2
              simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (v : ℕ) + (t1 : ℕ) - 1)⟩ t2) d +
         S_lt F 2 (by omega : 0 < 2) (pair
            t2 ⟨j.1 + 1, by
              have hj : j.1 < (v : ℕ) + (t1 : ℕ) - 1 := j.2
              simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (v : ℕ) + (t1 : ℕ) - 1)⟩) d +
         S_lt F 1 (by omega : 0 < 1) (single
            ⟨j.1 + 1 + (t2 : ℕ), by omega⟩) d +
         ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (j.1 + 1 + (t2 : ℕ) - 1)},
           (ChenDeltaZ F (j.1 + 1) (t2 : ℕ) k.1 : RatFunc.CompletionAtInfty F) *
           S_lt F 2 (by omega : 0 < 2) (thakurExp (j.1 + 1) (t2 : ℕ) k) d) := by
  classical
  rw [p1two_level F v t1 t2 d]
  congr 1
  symm
  exact sum_fin_succ_eq_Icc ((v : ℕ) + (t1 : ℕ) - 1)
    (by have hx : 1 ≤ (v : ℕ) := PNat.pos v; have hy : 1 ≤ (t1 : ℕ) := PNat.pos t1; omega)
    (fun i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (t1 : ℕ) - 1)} =>
      (ChenDeltaZ F (v : ℕ) (t1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
      P F d ⟨(v : ℕ) + (t1 : ℕ) - i.1, by
            have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
            have hin : i.1 ≤ (v : ℕ) + (t1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
            omega⟩ *
      (S_lt F 2 (by omega : 0 < 2) (pair
            ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩ t2) d +
       S_lt F 2 (by omega : 0 < 2) (pair
            t2 ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d +
       S_lt F 1 (by omega : 0 < 1) (single
            ⟨i.1 + (t2 : ℕ), Nat.add_pos_left (Finset.mem_Icc.mp i.2).1 (t2 : ℕ)⟩) d +
       ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (i.1 + (t2 : ℕ) - 1)},
         (ChenDeltaZ F i.1 (t2 : ℕ) k.1 : RatFunc.CompletionAtInfty F) *
         S_lt F 2 (by omega : 0 < 2) (thakurExp i.1 (t2 : ℕ) k) d))

/-- The finite index type of the depth-(1,2) expansion: the pure term ⊕ a Δ-index and
the stuffle witness for each `⟨j+1⟩` against `t2`. -/
abbrev p1twoIdx (v t1 t2 : ℕ+) :=
  PUnit.{1} ⊕ (Σ j : Fin ((v : ℕ) + (t1 : ℕ) - 1), P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2)

/-- The value `v+t1-(j+1)` appearing as the head of each Δ-output tuple. -/
noncomputable def p1twoHead (v t1 : ℕ+) (j : Fin ((v : ℕ) + (t1 : ℕ) - 1)) : ℕ+ :=
  ⟨(v : ℕ) + (t1 : ℕ) - (j.1 + 1), by
    have hj : j.1 + 1 ≤ (v : ℕ) + (t1 : ℕ) - 1 := by omega
    omega⟩

/-- Depths of the (1,2) expansion outputs. -/
noncomputable def p1twoDep (v t1 t2 : ℕ+) : p1twoIdx v t1 t2 → ℕ := fun a => match a with
  | Sum.inl _ => 2
  | Sum.inr p => p2Dep (⟨p.1.1 + 1, by omega⟩ : ℕ+) t2 p.2 + 1

lemma p1twoDep_pos (v t1 t2 : ℕ+) (a : p1twoIdx v t1 t2) : 0 < p1twoDep v t1 t2 a := by
  cases a with
  | inl u => simp [p1twoDep]
  | inr p =>
    change 0 < p2Dep (⟨p.1.1 + 1, by omega⟩ : ℕ+) t2 p.2 + 1
    omega

/-- Coefficients of the (1,2) expansion. -/
noncomputable def p1twoF (v t1 t2 : ℕ+) : p1twoIdx v t1 t2 → ℤ := fun a => match a with
  | Sum.inl _ => (1 : ℤ)
  | Sum.inr p => ChenDeltaZ F (v : ℕ) (t1 : ℕ) (p.1.1 + 1) * p2F F (⟨p.1.1 + 1, by omega⟩ : ℕ+) t2 p.2

/-- Exponent tuples of the (1,2) expansion. -/
noncomputable def p1twoC (v t1 t2 : ℕ+) :
    ∀ a : p1twoIdx v t1 t2, Fin (p1twoDep v t1 t2 a) → ℕ+ := fun a => match a with
  | Sum.inl _ =>
      pair ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2
  | Sum.inr p =>
      consVec (p1twoHead v t1 p.1) (p2C (⟨p.1.1 + 1, by omega⟩ : ℕ+) t2 p.2)

/-- Depth bound of the (1,2) outputs: ≤ 1 + 2. -/
lemma p1twoDep_le (v t1 t2 : ℕ+) (a : p1twoIdx v t1 t2) : p1twoDep v t1 t2 a ≤ 3 := by
  cases a with
  | inl u => simp [p1twoDep]
  | inr p =>
    change p2Dep (⟨p.1.1 + 1, by omega⟩ : ℕ+) t2 p.2 + 1 ≤ 3
    have hlt := p2Dep_le_two (⟨p.1.1 + 1, by omega⟩ : ℕ+) t2 p.2
    omega

/-- `LePad` for the pure term of the (1,2) product. -/
lemma p1two_lePad_pure (v t1 t2 : ℕ+) :
    LePad (p1twoC v t1 t2 (Sum.inl PUnit.unit)) (single v) (pair t1 t2) := by
  simpa [p1twoC, p1twoDep] using LePad_merge_pair v t1 t2

/-- `LePad` for the Δ-terms of the (1,2) product. -/
lemma p1two_lePad_delta (v t1 t2 : ℕ+) (j : Fin ((v : ℕ) + (t1 : ℕ) - 1))
    (t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2) :
    LePad (p1twoC v t1 t2 (Sum.inr ⟨j, t⟩)) (single v) (pair t1 t2) := by
  let x : ℕ+ := ⟨j.1 + 1, by omega⟩
  change LePad (consVec (p1twoHead v t1 j) (p2C x t2 t)) (single v) (pair t1 t2)
  apply LePad_prepend_cons v t1 t2 (p1twoHead v t1 j) x
  · dsimp [p1twoHead]
    omega
  · dsimp [x, p1twoHead]
    have hv : 1 ≤ (v : ℕ) := PNat.pos v
    have ht1 : 1 ≤ (t1 : ℕ) := PNat.pos t1
    have hjp : j.1 < (v : ℕ) + (t1 : ℕ) - 1 := j.2
    omega
  · exact p2C_weight x t2 t
  · intro m
    exact p2C_prefix_le x t2 t m

/-- `P F d a · (stuffsum x t2)` equals the prepended S-block combo (helper, universe-safely
stated). -/
lemma p2prepend_stuffle (x a t2 : ℕ+) (d : ℕ) :
    (∑ t : P2Idx x t2, ((p2F F x t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
        S F (p2Dep x t2 t + 1) (by omega) (consVec a (p2C x t2 t)) d) =
    P F d a * (∑ t : P2Idx x t2, ((p2F F x t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F (p2Dep x t2 t) (p2Dep_pos x t2 t) (p2C x t2 t) d) := by
  exact (combo_prepend F d a (p2Dep x t2) (p2Dep_pos x t2) (p2F F x t2) (p2C x t2)).symm

lemma p1two_delta_sum (v t1 t2 : ℕ+) (d : ℕ)
    (j : Fin ((v : ℕ) + (t1 : ℕ) - 1)) :
    (∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2,
      ((p1twoF F v t1 t2 (Sum.inr ⟨j, t⟩) : ℤ) : RatFunc.CompletionAtInfty F) *
      S F (p1twoDep v t1 t2 (Sum.inr ⟨j, t⟩)) (p1twoDep_pos v t1 t2 (Sum.inr ⟨j, t⟩))
        (p1twoC v t1 t2 (Sum.inr ⟨j, t⟩)) d) =
    (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
    (P F d (p1twoHead v t1 j) *
      (∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2,
        ((p2F F (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
        S_lt F (p2Dep (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
          (p2Dep_pos (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t) (p2C (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t) d)) := by
  classical
  let x : ℕ+ := ⟨j.1 + 1, by omega⟩
  let a : ℕ+ := p1twoHead v t1 j
  change (∑ t : P2Idx x t2,
      (((ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) * p2F F x t2 t) : ℤ) : RatFunc.CompletionAtInfty F) *
      S F (p2Dep x t2 t + 1) (by omega) (consVec a (p2C x t2 t)) d) =
    (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
    (P F d a * (∑ t : P2Idx x t2,
      ((p2F F x t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F (p2Dep x t2 t) (p2Dep_pos x t2 t) (p2C x t2 t) d))
  calc
    (∑ t : P2Idx x t2,
        (((ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) * p2F F x t2 t) : ℤ) : RatFunc.CompletionAtInfty F) *
        S F (p2Dep x t2 t + 1) (by omega) (consVec a (p2C x t2 t)) d)
        = (∑ t : P2Idx x t2,
            (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
            (((p2F F x t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
              S F (p2Dep x t2 t + 1) (by omega) (consVec a (p2C x t2 t)) d)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Int.cast_mul]
          rw [mul_assoc]
    _ = (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
          (∑ t : P2Idx x t2,
            ((p2F F x t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
            S F (p2Dep x t2 t + 1) (by omega) (consVec a (p2C x t2 t)) d) := by
          have hm := Finset.mul_sum (s := (Finset.univ : Finset (P2Idx x t2)))
            (a := (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F))
            (f := fun t : P2Idx x t2 =>
              ((p2F F x t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
              S F (p2Dep x t2 t + 1) (by omega) (consVec a (p2C x t2 t)) d)
          simpa using hm.symm
    _ = (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
          (P F d a * (∑ t : P2Idx x t2,
            ((p2F F x t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (p2Dep x t2 t) (p2Dep_pos x t2 t) (p2C x t2 t) d)) := by
          exact congrArg (fun q : RatFunc.CompletionAtInfty F =>
            (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) * q)
            (p2prepend_stuffle F x a t2 d)
/-- The depth-(1,2) product identity, Δ-terms in stuffle-sum form (assemble of `p1two`). -/
lemma p1two_level_wit (v t1 t2 : ℕ+) (d : ℕ) :
    S F 1 (by omega : 0 < 1) (single v) d *
        S F 2 (by omega : 0 < 2) (pair t1 t2) d =
      S F 2 (by omega : 0 < 2) (pair
        ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2) d +
      ∑ j : Fin ((v : ℕ) + (t1 : ℕ) - 1),
        (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
        (P F d (p1twoHead v t1 j) *
          (∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2,
            ((p2F F (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (p2Dep (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
              (p2Dep_pos (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
              (p2C (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t) d)) := by
  classical
  rw [p1two_level_fin F v t1 t2 d]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  let x : ℕ+ := ⟨j.1 + 1, by omega⟩
  let fp : RatFunc.CompletionAtInfty F :=
    S_lt F 2 (by omega : 0 < 2) (pair x t2) d +
    S_lt F 2 (by omega : 0 < 2) (pair t2 x) d +
    S_lt F 1 (by omega : 0 < 1)
      (single ⟨(x : ℕ) + (t2 : ℕ), Nat.add_pos_left (PNat.pos x) (t2 : ℕ)⟩) d +
    ∑ k : {k : ℕ // k ∈ Finset.Icc 1 ((x : ℕ) + (t2 : ℕ) - 1)},
      (ChenDeltaZ F (x : ℕ) (t2 : ℕ) k.1 : RatFunc.CompletionAtInfty F) *
      S_lt F 2 (by omega : 0 < 2) (thakurExp (x : ℕ) (t2 : ℕ) k) d
  let ss : RatFunc.CompletionAtInfty F :=
    ∑ t : P2Idx x t2,
      ((p2F F x t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
      S_lt F (p2Dep x t2 t) (p2Dep_pos x t2 t) (p2C x t2 t) d
  have h4s : fp = ss := by
    dsimp [fp, ss]
    exact ((S_lt_one_mul_eq F x t2 d).symm).trans (p2stuffle_eq F x t2 d).symm
  have hP : P F d ⟨(v : ℕ) + (t1 : ℕ) - (j.1 + 1), by
        have hjp : j.1 < (v : ℕ) + (t1 : ℕ) - 1 := j.2
        omega⟩ = P F d (p1twoHead v t1 j) := by
    rfl
  have hin : P F d ⟨(v : ℕ) + (t1 : ℕ) - (j.1 + 1), by
        have hjp : j.1 < (v : ℕ) + (t1 : ℕ) - 1 := j.2
        omega⟩ * fp = P F d (p1twoHead v t1 j) * ss := by
    calc
      P F d ⟨(v : ℕ) + (t1 : ℕ) - (j.1 + 1), by
          have hjp : j.1 < (v : ℕ) + (t1 : ℕ) - 1 := j.2
          omega⟩ * fp = P F d (p1twoHead v t1 j) * fp := by
        exact congrArg (fun r : RatFunc.CompletionAtInfty F => r * fp) hP
      _ = P F d (p1twoHead v t1 j) * ss := by
        exact congrArg (fun r : RatFunc.CompletionAtInfty F => P F d (p1twoHead v t1 j) * r) h4s
  rw [mul_assoc]
  exact congrArg (fun q : RatFunc.CompletionAtInfty F =>
    (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) * q) hin

/-- The carrier sum of the depth-(1,2) product equals the level-(1,2) RHS (stuffle form). -/
lemma p1two_rhs_eq (v t1 t2 : ℕ+) (d : ℕ) :
    (∑ a : p1twoIdx v t1 t2,
      ((p1twoF F v t1 t2 a : ℤ) : RatFunc.CompletionAtInfty F) *
      S F (p1twoDep v t1 t2 a) (p1twoDep_pos v t1 t2 a) (p1twoC v t1 t2 a) d) =
    S F 2 (by omega : 0 < 2) (pair
        ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2) d +
      ∑ j : Fin ((v : ℕ) + (t1 : ℕ) - 1),
        (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
        (P F d (p1twoHead v t1 j) *
          (∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2,
            ((p2F F (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F (p2Dep (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
              (p2Dep_pos (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
              (p2C (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t) d)) := by
  classical
  let T : p1twoIdx v t1 t2 → RatFunc.CompletionAtInfty F := fun a =>
    ((p1twoF F v t1 t2 a : ℤ) : RatFunc.CompletionAtInfty F) *
    S F (p1twoDep v t1 t2 a) (p1twoDep_pos v t1 t2 a) (p1twoC v t1 t2 a) d
  have hsplit : (∑ a : p1twoIdx v t1 t2, T a) =
      T (Sum.inl PUnit.unit) +
        ∑ p : (j : Fin ((v : ℕ) + (t1 : ℕ) - 1)) ×
          P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2, T (Sum.inr p) := by
    have hsum := Fintype.sum_sum_type (f := T)
    rw [hsum]
    simp
  have hsigma : (∑ p : (j : Fin ((v : ℕ) + (t1 : ℕ) - 1)) ×
        P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2, T (Sum.inr p)) =
      ∑ j : Fin ((v : ℕ) + (t1 : ℕ) - 1),
        ∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2, T (Sum.inr ⟨j, t⟩) := by
    exact Fintype.sum_sigma (f := fun p : (j : Fin ((v : ℕ) + (t1 : ℕ) - 1)) ×
      P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2 => T (Sum.inr p))
  calc
    (∑ a : p1twoIdx v t1 t2, T a)
        = T (Sum.inl PUnit.unit) +
            ∑ j : Fin ((v : ℕ) + (t1 : ℕ) - 1),
              ∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2, T (Sum.inr ⟨j, t⟩) := by
          rw [hsplit, hsigma]
    _ = S F 2 (by omega : 0 < 2) (pair
          ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2) d +
        ∑ j : Fin ((v : ℕ) + (t1 : ℕ) - 1),
          ∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2, T (Sum.inr ⟨j, t⟩) := by
        have hpure : T (Sum.inl PUnit.unit) =
            S F 2 (by omega : 0 < 2) (pair
              ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2) d := by
          simp [T, p1twoF, p1twoDep, p1twoC]
        rw [hpure]
    _ = S F 2 (by omega : 0 < 2) (pair
          ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2) d +
        ∑ j : Fin ((v : ℕ) + (t1 : ℕ) - 1),
          (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
          (P F d (p1twoHead v t1 j) *
            (∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2,
              ((p2F F (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (p2Dep (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
                (p2Dep_pos (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
                (p2C (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t) d)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [p1two_delta_sum]

/-- ★ The first inductive cons step: depth (1,2), Part 1. -/
theorem p1two (v t1 t2 : ℕ+) :
    P1W F 1 2 (by omega : 0 < 1) (by omega : 0 < 2) (single v) (pair t1 t2) := by
  refine ⟨p1twoIdx v t1 t2, ?_, p1twoDep v t1 t2, p1twoDep_pos v t1 t2, p1twoF F v t1 t2,
    p1twoC v t1 t2, ?hid, ?hle, ?hbd⟩
  · infer_instance
  · intro d
    calc
      S F 1 (by omega : 0 < 1) (single v) d * S F 2 (by omega : 0 < 2) (pair t1 t2) d
          = S F 2 (by omega : 0 < 2) (pair
              ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ t2) d +
            ∑ j : Fin ((v : ℕ) + (t1 : ℕ) - 1),
              (ChenDeltaZ F (v : ℕ) (t1 : ℕ) (j.1 + 1) : RatFunc.CompletionAtInfty F) *
              (P F d (p1twoHead v t1 j) *
                (∑ t : P2Idx (⟨j.1 + 1, by omega⟩ : ℕ+) t2,
                  ((p2F F (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t : ℤ) : RatFunc.CompletionAtInfty F) *
                  S_lt F (p2Dep (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
                    (p2Dep_pos (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t)
                    (p2C (⟨j.1 + 1, by omega⟩ : ℕ+) t2 t) d)) :=
            p1two_level_wit F v t1 t2 d
      _ = (∑ a : p1twoIdx v t1 t2, ((p1twoF F v t1 t2 a : ℤ) : RatFunc.CompletionAtInfty F) *
            S F (p1twoDep v t1 t2 a) (p1twoDep_pos v t1 t2 a) (p1twoC v t1 t2 a) d) := by
            exact (p1two_rhs_eq F v t1 t2 d).symm
  · intro a
    cases a with
    | inl u => exact p1two_lePad_pure v t1 t2
    | inr p =>
      exact p1two_lePad_delta v t1 t2 p.1 p.2
  · intro a
    exact p1twoDep_le v t1 t2 a

/-- Part 1 at depth (1,2) for an arbitrary depth-two tuple. -/
theorem p1one_two : P1one F 2 (by omega : 0 < 2) := by
  intro v W
  rw [fin2_eq_pair W]
  exact p1two F v (W ⟨0, by omega⟩) (W ⟨1, by omega⟩)

end ZagierHoffmanPositiveChar
