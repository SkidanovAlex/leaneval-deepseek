import Submission.ZagierHoffmanProof.StepB8

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step C: tuple order library for Prop 2.1 / §2.2–2.3 (paper §2.1 "s ≤ t")

Exponent tuples are `Fin r → ℕ+` (as everywhere: `𝔰 : Fin r → ℕ+`).  The paper orders
tuples of *possibly different* depths by padding with 0 beyond the depth and comparing
prefix sums of equal total weight.  Here we record the concrete arithmetic core:
`pad0`, `psum` (prefix sums into ℕ), `weight`, and the prefix/weight order `TupleLe`.
-/

namespace ZagierHoffmanPositiveChar
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A tuple (length-`r` positive exponent vector) padded with zeros to all of ℕ. -/
noncomputable def pad0 {r : ℕ} (𝔰 : Fin r → ℕ+) (j : ℕ) : ℕ :=
  if h : j < r then (𝔰 ⟨j, h⟩ : ℕ) else 0

/-- The `m`-th prefix sum of a tuple (entries beyond the depth contribute 0). -/
noncomputable def psum {r : ℕ} (𝔰 : Fin r → ℕ+) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, pad0 𝔰 j

/-- The weight of a tuple (sum of its positive entries). -/
noncomputable def weight (r : ℕ) (𝔰 : Fin r → ℕ+) : ℕ :=
  ∑ j : Fin r, (𝔰 j : ℕ)

lemma pad0_of_lt {r : ℕ} (𝔰 : Fin r → ℕ+) {j : ℕ} (h : j < r) :
    pad0 𝔰 j = (𝔰 ⟨j, h⟩ : ℕ) := by
  simp [pad0, h]

lemma pad0_of_ge {r : ℕ} (𝔰 : Fin r → ℕ+) {j : ℕ} (h : r ≤ j) :
    pad0 𝔰 j = 0 := by
  simp [pad0, h]

lemma psum_succ {r : ℕ} (𝔰 : Fin r → ℕ+) (m : ℕ) :
    psum 𝔰 (m + 1) = psum 𝔰 m + pad0 𝔰 m := by
  change (∑ j ∈ Finset.range (m + 1), pad0 𝔰 j) = (∑ j ∈ Finset.range m, pad0 𝔰 j) + pad0 𝔰 m
  rw [Finset.sum_range_succ]

lemma psum_zero {r : ℕ} (𝔰 : Fin r → ℕ+) : psum 𝔰 0 = 0 := by
  change (∑ j ∈ Finset.range 0, pad0 𝔰 j) = 0
  simp

lemma psum_mono {r : ℕ} (𝔰 : Fin r → ℕ+) {m n : ℕ} (h : m ≤ n) :
    psum 𝔰 m ≤ psum 𝔰 n := by
  change (∑ j ∈ Finset.range m, pad0 𝔰 j) ≤ (∑ j ∈ Finset.range n, pad0 𝔰 j)
  have hn : n = m + (n - m) := (Nat.add_sub_of_le h).symm
  rw [hn, Finset.sum_range_add]
  exact Nat.le_add_right _ _

/-- Prefix sums at or beyond the depth equal the weight. -/
lemma psum_ge_depth {r : ℕ} (𝔰 : Fin r → ℕ+) {m : ℕ} (h : r ≤ m) :
    psum 𝔰 m = weight r 𝔰 := by
  classical
  change (∑ j ∈ Finset.range m, pad0 𝔰 j) = weight r 𝔰
  have hm : m = r + (m - r) := (Nat.add_sub_of_le h).symm
  rw [hm, Finset.sum_range_add]
  have hrest : (∑ x ∈ Finset.range (m - r), pad0 𝔰 (r + x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact pad0_of_ge 𝔰 (by omega)
  rw [hrest, add_zero]
  rw [weight, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x hx
  have hxr : x < r := Finset.mem_range.mp hx
  rw [pad0, dif_pos hxr]

/-- Prefix sums at the depth equal the weight. -/
lemma psum_self {r : ℕ} (𝔰 : Fin r → ℕ+) : psum 𝔰 r = weight r 𝔰 := by
  exact psum_ge_depth 𝔰 (le_rfl)

/-- The weight of a tuple extended (by an arbitrary value) is the old weight plus the
extension value; here specialised to `consVec`. -/
lemma weight_consVec (x : ℕ+) {m : ℕ} (𝔰 : Fin m → ℕ+) :
    weight (m + 1) (consVec x 𝔰) = (x : ℕ) + weight m 𝔰 := by
  classical
  calc
    weight (m + 1) (consVec x 𝔰)
        = ((consVec x 𝔰) ⟨0, (by omega : 0 < m + 1)⟩ : ℕ) +
            (∑ i : Fin m, ((consVec x 𝔰) i.succ : ℕ)) := by
          rw [weight, Fin.sum_univ_succ]
          rfl
    _ = (x : ℕ) + (∑ i : Fin m, (𝔰 i : ℕ)) := by
          have h0 : ((consVec x 𝔰) ⟨0, (by omega : 0 < m + 1)⟩ : ℕ) = (x : ℕ) :=
            congrArg (fun v : ℕ+ => (v : ℕ)) (consVec_zero x 𝔰)
          rw [h0]
          apply congrArg (fun t : ℕ => (x : ℕ) + t)
          apply Finset.sum_congr rfl
          intro i hi
          exact congrArg (fun v : ℕ+ => (v : ℕ)) (consVec_succ x 𝔰 i)
    _ = (x : ℕ) + weight m 𝔰 := by
          rw [weight]

/-- The paper's order on tuples of (possibly different) depths: equal weight and all
prefix sums ≤. -/
def TupleLe {r k : ℕ} (a : Fin r → ℕ+) (b : Fin k → ℕ+) : Prop :=
  weight r a = weight k b ∧ ∀ m : ℕ, psum a m ≤ psum b m

lemma TupleLe.refl (r : ℕ) (a : Fin r → ℕ+) : TupleLe a a := by
  constructor
  · rfl
  · intro m
    exact le_rfl

lemma TupleLe.trans {r k l : ℕ} (a : Fin r → ℕ+) (b : Fin k → ℕ+) (c : Fin l → ℕ+)
    (hab : TupleLe a b) (hbc : TupleLe b c) : TupleLe a c := by
  constructor
  · exact Eq.trans hab.1 hbc.1
  · intro m
    exact le_trans (hab.2 m) (hbc.2 m)

end ZagierHoffmanPositiveChar
