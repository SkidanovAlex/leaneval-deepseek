import Mathlib
import Submission.Commons.Data.Nat.interval_partition
import Submission.Commons.Data.Nat.card_pi_Ico_fin
import Submission.Commons.NumberTheory.Sieve.LambdaR_prime

/-!
# The box decomposition of `(ZMod p)^t` (Green–Tao Proposition 9.8, localisation step)

Green–Tao's proof that the Goldston–Yıldırım majorant `ν` obeys the linear forms condition
proceeds by chopping `Z_N^t` into `Q^t` almost-equal boxes `B_u` (`Q` growing slowly with `N`),
applying the box-average asymptotic (their Proposition 9.5) on each box, and estimating the
number of *non-nice* boxes.

This file formalises the (purely combinatorial) box decomposition.  Working with the
representatives `val : ZMod p → Fin p`, the boxes are products of integer intervals
`[u_j * p / Q, (u_j + 1) * p / Q)`, i.e. the fibres of the explicit map
`v ↦ (fun j => boxIdx (v j))`.
-/

open Finset
open scoped BigOperators

namespace GYMaj

section Boxes

variable {p Q : ℕ}

/-- The index of the box containing a representative `v : Fin p`: the unique `u < Q` with
`u * p / Q ≤ v.val < (u + 1) * p / Q`. -/
noncomputable def boxIdx (hQ : 0 < Q) (hQp : Q ≤ p) (v : Fin p) : Fin Q :=
  ⟨Classical.choose (Commons.Data.Nat.interval_partition hQ hQp v.isLt),
    ((Classical.choose_spec (Commons.Data.Nat.interval_partition hQ hQp v.isLt)).1).1⟩

lemma boxIdx_le (hQ : 0 < Q) (hQp : Q ≤ p) (v : Fin p) :
    (boxIdx hQ hQp v).val * p / Q ≤ v.val :=
  ((Classical.choose_spec (Commons.Data.Nat.interval_partition hQ hQp v.isLt)).1).2.1

lemma boxIdx_lt' (hQ : 0 < Q) (hQp : Q ≤ p) (v : Fin p) :
    v.val < ((boxIdx hQ hQp v).val + 1) * p / Q :=
  ((Classical.choose_spec (Commons.Data.Nat.interval_partition hQ hQp v.isLt)).1).2.2

/-- Uniqueness form: any `u < Q` whose interval contains `v` is `boxIdx v`. -/
lemma boxIdx_eq_of_mem (hQ : 0 < Q) (hQp : Q ≤ p) {v : Fin p} {u : ℕ} (hu : u < Q)
    (h1 : u * p / Q ≤ v.val) (h2 : v.val < (u + 1) * p / Q) :
    u = (boxIdx hQ hQp v).val :=
  (Classical.choose_spec (Commons.Data.Nat.interval_partition hQ hQp v.isLt)).2 u ⟨hu, h1, h2⟩

/-- The box with index `u`. -/
noncomputable def boxOf (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ} (u : Fin t → Fin Q) :
    Finset (Fin t → Fin p) :=
  Finset.univ.filter (fun v => (fun j => boxIdx hQ hQp (v j)) = u)

lemma mem_boxOf (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ} {u : Fin t → Fin Q} {v : Fin t → Fin p} :
    v ∈ boxOf hQ hQp u ↔ (fun j => boxIdx hQ hQp (v j)) = u := by
  simp [boxOf]

/-- The defining property of `boxOf`. -/
lemma mem_boxOf_iff (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ} {u : Fin t → Fin Q} {v : Fin t → Fin p} :
    v ∈ boxOf hQ hQp u ↔ ∀ j, (u j).val * p / Q ≤ (v j).val ∧ (v j).val < ((u j).val + 1) * p / Q := by
  rw [mem_boxOf]
  constructor
  · intro h j
    have hb : boxIdx hQ hQp (v j) = u j := congrFun h j
    rw [← hb]
    exact ⟨boxIdx_le hQ hQp (v j), boxIdx_lt' hQ hQp (v j)⟩
  · intro h
    funext j
    have hj := h j
    exact Fin.ext (boxIdx_eq_of_mem hQ hQp (u j).isLt hj.1 hj.2).symm

lemma boxOf_disjoint (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ} {u u' : Fin t → Fin Q} (h : u ≠ u') :
    Disjoint (boxOf hQ hQp u) (boxOf hQ hQp u') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact h ((mem_boxOf hQ hQp).1 hv ▸ (mem_boxOf hQ hQp).1 hv')

lemma biUnion_boxOf (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ} :
    (Finset.univ : Finset (Fin t → Fin Q)).biUnion (boxOf hQ hQp) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  exact Finset.mem_biUnion.2 ⟨fun j => boxIdx hQ hQp (v j), Finset.mem_univ _,
    (mem_boxOf hQ hQp).2 rfl⟩

/-- **The box decomposition.** -/
theorem sum_boxOf (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ} (g : (Fin t → Fin p) → ℂ) :
    ∑ v : Fin t → Fin p, g v = ∑ u : Fin t → Fin Q, ∑ v ∈ boxOf hQ hQp u, g v := by
  have hd := Finset.sum_biUnion (s := (Finset.univ : Finset (Fin t → Fin Q)))
    (t := boxOf hQ hQp) (f := g)
    (fun u _ u' _ h => boxOf_disjoint hQ hQp h)
  rw [biUnion_boxOf hQ hQp] at hd
  simpa using hd

/-- Indicator form: `∑_u ∑_v [boxIdx v = u] g v = ∑_v g v`. -/
theorem sum_boxOf_filter (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ} (g : (Fin t → Fin p) → ℂ) :
    ∑ u : Fin t → Fin Q, ∑ v : Fin t → Fin p,
        (if (fun j => boxIdx hQ hQp (v j)) = u then g v else 0)
      = ∑ v : Fin t → Fin p, g v := by
  rw [sum_boxOf hQ hQp g]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [boxOf, Finset.sum_filter]

/-- **The cardinality of a box** is the product of its side lengths (Green–Tao's boxes have
side `\u2248 p/Q`). -/
lemma card_boxOf (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ} (u : Fin t → Fin Q) :
    (boxOf hQ hQp u).card
      = ∏ j, (((u j).val + 1) * p / Q - (u j).val * p / Q) := by
  have hset : boxOf hQ hQp u = Finset.univ.filter (fun v : Fin t → Fin p =>
      ∀ j, (u j).val * p / Q ≤ (v j).val ∧ (v j).val < ((u j).val + 1) * p / Q) := by
    ext v
    rw [mem_boxOf_iff hQ hQp]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset]
  exact Commons.Data.Nat.card_pi_Ico_fin hQp u


end Boxes

section ZModBoxes

variable {p Q : ℕ} [NeZero p]

/-- The reindexing `(Fin t → Fin p) ≃ (Fin t → ZMod p)` given by the representatives. -/
noncomputable def finFunEquiv (p : ℕ) [NeZero p] (t : ℕ) : (Fin t → Fin p) ≃ (Fin t → ZMod p) where
  toFun v j := (v j : ZMod p)
  invFun x j := ⟨(x j).val, ZMod.val_lt (x j)⟩
  left_inv v := by funext j; exact Fin.ext (ZMod.val_cast_of_lt (v j).isLt)
  right_inv x := by funext j; exact ZMod.natCast_zmod_val (x j)

/-- Sums over `(Fin t → Fin p)` are sums over `(ZMod p)^t`. -/
theorem sum_fin_eq_sum_zmod {t : ℕ} (F : (Fin t → Fin p) → ℂ) :
    ∑ v : Fin t → Fin p, F v
      = ∑ x : Fin t → ZMod p, F ((finFunEquiv p t).symm x) :=
  (Fintype.sum_equiv (finFunEquiv p t).symm (fun x => F ((finFunEquiv p t).symm x)) F
    (fun _ => rfl)).symm

/-- **The box decomposition on `(ZMod p)^t`.** -/
theorem sum_zmod_boxOf (hQ : 0 < Q) (hQp : Q ≤ p) {t : ℕ}
    (F : (Fin t → ZMod p) → ℂ) :
    ∑ x : Fin t → ZMod p, F x
      = ∑ u : Fin t → Fin Q, ∑ v ∈ boxOf hQ hQp u, F (fun j => (v j : ZMod p)) := by
  have hcomp : ∑ v : Fin t → Fin p, F (finFunEquiv p t v)
      = ∑ x : Fin t → ZMod p, F x :=
    Fintype.sum_equiv (finFunEquiv p t) (fun v => F (finFunEquiv p t v)) F (fun _ => rfl)
  rw [← hcomp]
  exact sum_boxOf hQ hQp (fun v : Fin t → Fin p => F (finFunEquiv p t v))

end ZModBoxes

end GYMaj

namespace GYMaj

section BoxAvg

/-- **Green–Tao Proposition 9.5, box form** (the analytic input of the localisation).

For every system of `m` integer linear forms in `t` variables with non-zero, pairwise
non-proportional linear parts, every integer shifts `b`, and every box `∏ [l_j, r_j)` with
`r_j - l_j ≥ R ^ (10*m)` and `m ≤ k·2^{k-1}`, `t ≤ 3k-4`, the box average of
`∏_i Λ_R(W·ψ_i(x) + 1)²` is `(1 ± ε)·(W log R / φ(W))^m`. -/
def BoxAvgGood (k R W : ℕ) (ε : ℝ) : Prop :=
  ∀ (m t : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ),
    1 ≤ m → m ≤ k * 2 ^ (k - 1) → 0 < t → t ≤ 3 * k - 4 →
    (∀ i, ∃ j, A i j ≠ 0) →
    (∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ)) →
    (∀ i j, (A i j).natAbs ≤ k.factorial * k) →
    (∀ j, (R : ℤ) ^ (10 * m) ≤ r j - l j) →
    (∀ x ∈ Fintype.piFinset (fun j => Finset.Icc (l j) (r j - 1)), ∀ i,
      0 < W * ((∑ j, A i j * x j) + b i) + 1) →
    abs (((∏ j, ((r j - l j : ℤ) : ℝ))⁻¹ *
        ∑ x ∈ Fintype.piFinset (fun j => Finset.Icc (l j) (r j - 1)),
          ∏ i, ((Commons.NumberTheory.Sieve.LambdaR R (Int.toNat (W * ((∑ j, A i j * x j) + b i) + 1)) : ℝ)) ^ 2)
      - ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m)
      ≤ ε * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m

end BoxAvg

end GYMaj
