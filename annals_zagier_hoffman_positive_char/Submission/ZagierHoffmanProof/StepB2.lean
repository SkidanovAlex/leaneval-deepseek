import Submission.ZagierHoffmanProof.StepB

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step B3 assembly (`thakur_prod_one` for all `d`)

`StepB.lean` established, over `RatFunc F`, the per-`m` shuffle `E_m_rat` and its
sum over `m` (`E_m_sum`).  This module assembles those into the paper's (2.1):

* the level-`d` diagonal/off-diagonal split of the product `(Σ_p p^{-a})(Σ_p p^{-b})`,
* the off-diagonal ↔ shift reindexing (`headShiftEquiv`, B1),
* then embedding into the completion and matching the `P`/`S` sums via
  `S_d_recursion`, yielding `thakur_prod_one` at every level `d ≥ 1`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- In `RatFunc F`, inverse powers add: `X^{-k}·X^{-l} = X^{-(k+l)}`. -/
lemma rat_inv_pow_add (X : RatFunc F) (k l : ℕ) :
    (X ^ k)⁻¹ * (X ^ l)⁻¹ = (X ^ (k + l))⁻¹ := by
  calc
    (X ^ k)⁻¹ * (X ^ l)⁻¹ = (X ^ k * X ^ l)⁻¹ := by
          rw [mul_comm (X ^ k)⁻¹ (X ^ l)⁻¹]
          exact (mul_inv_rev (X ^ k) (X ^ l)).symm
    _ = (X ^ (k + l))⁻¹ := by rw [pow_add]

/-- The level-`d` diagonal split: the product of the two power sums splits into the
diagonal `Σ_p p^{-(a+b)}` plus the off-diagonal double sum `Σ_p Σ_{q≠p}`. -/
lemma headDiag_split (d : ℕ) (a b : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ a)⁻¹)) *
        (∑ q : HeadD F d, (((q.1 : RatFunc F) ^ b)⁻¹)) =
      (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p,
        (((p.1 : RatFunc F) ^ a)⁻¹) * (((q.1 : RatFunc F) ^ b)⁻¹)) +
      (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b))⁻¹)) := by
  classical
  let f : HeadD F d → RatFunc F := fun p => (((p.1 : RatFunc F) ^ a)⁻¹)
  let g : HeadD F d → RatFunc F := fun q => (((q.1 : RatFunc F) ^ b)⁻¹)
  let S : RatFunc F := ∑ q : HeadD F d, g q
  have hfg : ∀ p : HeadD F d, f p * g p = (((p.1 : RatFunc F) ^ (a + b))⁻¹) := by
    intro p
    dsimp [f, g]
    exact rat_inv_pow_add F (p.1 : RatFunc F) a b
  have hstep1 : (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p, f p * g q) =
      ∑ p : HeadD F d, (f p * S - f p * g p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have h := Finset.sum_erase_add (Finset.univ : Finset (HeadD F d))
      (fun q : HeadD F d => f p * g q) (Finset.mem_univ p)
    have hmain : (∑ q : HeadD F d, f p * g q) = f p * S := by
      dsimp [S]
      rw [Finset.mul_sum]
    calc
      (∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p, f p * g q)
          = (∑ q : HeadD F d, f p * g q) - f p * g p := by
            exact eq_sub_of_add_eq h
      _ = f p * S - f p * g p := by rw [hmain]
  have hprod : (∑ p : HeadD F d, f p) * (∑ q : HeadD F d, g q) =
      ∑ p : HeadD F d, ∑ q : HeadD F d, f p * g q := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
  calc
    (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ a)⁻¹)) * (∑ q : HeadD F d, (((q.1 : RatFunc F) ^ b)⁻¹))
        = (∑ p : HeadD F d, f p) * (∑ q : HeadD F d, g q) := by rfl
    _ = ∑ p : HeadD F d, ∑ q : HeadD F d, f p * g q := hprod
    _ = ∑ p : HeadD F d, (f p * S) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hmain : (∑ q : HeadD F d, f p * g q) = f p * S := by
            dsimp [S]
            rw [Finset.mul_sum]
          exact hmain
    _ = ∑ p : HeadD F d, (f p * S - f p * g p + f p * g p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = (∑ p : HeadD F d, (f p * S - f p * g p)) + ∑ p : HeadD F d, (f p * g p) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p, f p * g q) +
          ∑ p : HeadD F d, (f p * g p) := by
          rw [← hstep1]
    _ = (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p,
            (((p.1 : RatFunc F) ^ a)⁻¹) * (((q.1 : RatFunc F) ^ b)⁻¹)) +
          ∑ p : HeadD F d, (f p * g p) := by rfl
    _ = (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p,
            (((p.1 : RatFunc F) ^ a)⁻¹) * (((q.1 : RatFunc F) ^ b)⁻¹)) +
          (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b))⁻¹)) := by
          apply congrArg (fun t : RatFunc F =>
            (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p,
              (((p.1 : RatFunc F) ^ a)⁻¹) * (((q.1 : RatFunc F) ^ b)⁻¹)) + t)
          apply Finset.sum_congr rfl
          intro p hp
          exact hfg p

/-- The `y`-summand of the shifted sums (`q = p + δ·m`, `y = (m, δ)`). -/
noncomputable def shiftSummand (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (k : ℕ)
    (y : {z : MonicLt F d × F // z.2 ≠ 0}) : RatFunc F :=
  ((((p.1 + Polynomial.C y.1.2 * y.1.1.1 : F[X]) : RatFunc F) ^ k)⁻¹)

/-- The `q`-summand over off-diagonal heads. -/
noncomputable def headSummand (d : ℕ) (p : HeadD F d) (k : ℕ)
    (q : {q : HeadD F d // q ≠ p}) : RatFunc F :=
  (((q.1.1 : RatFunc F) ^ k)⁻¹)

/-- The paired `(m, δ)` summand. -/
noncomputable def pairSummand (d : ℕ) (p : HeadD F d) (k : ℕ)
    (r : MonicLt F d × {δ : F // δ ≠ 0}) : RatFunc F :=
  ((((p.1 + Polynomial.C r.2.1 * r.1.1 : F[X]) : RatFunc F) ^ k)⁻¹)

lemma shiftInverse_poly (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d)
    (y : {z : MonicLt F d × F // z.2 ≠ 0}) :
    ((shiftInverse F d hd p y).1).1 = p.1 + Polynomial.C y.1.2 * y.1.1.1 := by
  dsimp [shiftInverse]

lemma prodShiftSum_eq (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (k : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ r : MonicLt F d × {δ : F // δ ≠ 0}, pairSummand F d p k r) =
      ∑ y : {y : MonicLt F d × F // y.2 ≠ 0}, shiftSummand F d hd p k y := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let e2 : MonicLt F d × {δ : F // δ ≠ 0} ≃ {y : MonicLt F d × F // y.2 ≠ 0} :=
    { toFun := fun r => ⟨(r.1, r.2.1), r.2.2⟩,
      invFun := fun y => (y.1.1, ⟨y.1.2, y.2⟩),
      left_inv := by intro r; rfl,
      right_inv := by intro y; rfl }
  have hc2 := Equiv.sum_comp (e := e2.symm) (g := pairSummand F d p k)
  calc
    (∑ r : MonicLt F d × {δ : F // δ ≠ 0}, pairSummand F d p k r)
        = ∑ y : {y : MonicLt F d × F // y.2 ≠ 0}, pairSummand F d p k (e2.symm y) := by
          exact hc2.symm
    _ = ∑ y : {y : MonicLt F d × F // y.2 ≠ 0}, shiftSummand F d hd p k y := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [pairSummand, shiftSummand, e2]

lemma qShiftSum_eq (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (k : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ q : {q : HeadD F d // q ≠ p}, headSummand F d p k q) =
      ∑ y : {y : MonicLt F d × F // y.2 ≠ 0}, shiftSummand F d hd p k y := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hc2 := Equiv.sum_comp (e := (headShiftEquiv F d hd p).symm) (g := headSummand F d p k)
  calc
    (∑ q : {q : HeadD F d // q ≠ p}, headSummand F d p k q)
        = ∑ y : {y : MonicLt F d × F // y.2 ≠ 0}, headSummand F d p k ((headShiftEquiv F d hd p).symm y) := by
          exact hc2.symm
    _ = ∑ y : {y : MonicLt F d × F // y.2 ≠ 0}, shiftSummand F d hd p k y := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [headSummand, shiftSummand]
          apply congrArg (fun w : RatFunc F => (w ^ k)⁻¹)
          apply congrArg (fun w : F[X] => (w : RatFunc F))
          dsimp [headShiftEquiv]
          exact shiftInverse_poly F d hd p y


/-- Per-`p` off-diagonal reindexing: `Σ_{q≠p} q^{-k} = Σ_m Σ_{δ≠0} (p + δ·m)^{-k}`. -/
lemma headOffShiftSum (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (k : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ m : MonicLt F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ k)⁻¹)) =
      ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p, (((q.1 : RatFunc F) ^ k)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    (∑ m : MonicLt F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ k)⁻¹))
        = ∑ m : MonicLt F d, ∑ δ₀ : {δ : F // δ ≠ 0},
            ((((p.1 + Polynomial.C δ₀.1 * m.1 : F[X]) : RatFunc F) ^ k)⁻¹) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact Finset.sum_subtype (s := (Finset.univ : Finset F).erase 0)
            (h := fun δ : F => by simp) (f := fun δ : F =>
              ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ k)⁻¹))
    _ = ∑ r : MonicLt F d × {δ : F // δ ≠ 0}, pairSummand F d p k r := by
          exact (Fintype.sum_prod_type (fun r : MonicLt F d × {δ : F // δ ≠ 0} =>
            pairSummand F d p k r)).symm
    _ = ∑ y : {y : MonicLt F d × F // y.2 ≠ 0}, shiftSummand F d hd p k y := by
          exact prodShiftSum_eq F d hd p k
    _ = ∑ q : {q : HeadD F d // q ≠ p}, headSummand F d p k q := by
          exact (qShiftSum_eq F d hd p k).symm
    _ = ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p, (((q.1 : RatFunc F) ^ k)⁻¹) := by
          exact (Finset.sum_subtype (s := (Finset.univ : Finset (HeadD F d)).erase p)
            (h := fun q : HeadD F d => by simp)
            (f := fun q : HeadD F d => (((q.1 : RatFunc F) ^ k)⁻¹))).symm

/-- The level-`d` off-diagonal double sum reindexed as shifts (B1): for every ordered
pair `(p, q)` with `q ≠ p`, `q = p + δ·m` for a unique monic `m` of degree `< d` and
`δ ≠ 0`. -/
lemma headOffdiag_eq_shift (d : ℕ) (hd : 1 ≤ d) (a b : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p,
        (((p.1 : RatFunc F) ^ a)⁻¹) * (((q.1 : RatFunc F) ^ b)⁻¹)) =
      (∑ m : MonicLt F d, ∑ p : HeadD F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
        (((p.1 : RatFunc F) ^ a)⁻¹) *
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p,
        (((p.1 : RatFunc F) ^ a)⁻¹) * (((q.1 : RatFunc F) ^ b)⁻¹))
        = ∑ p : HeadD F d, (((p.1 : RatFunc F) ^ a)⁻¹) *
            (∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p, (((q.1 : RatFunc F) ^ b)⁻¹)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mul_sum (s := (Finset.univ : Finset (HeadD F d)).erase p)
            (a := (((p.1 : RatFunc F) ^ a)⁻¹)) (f := fun q : HeadD F d => (((q.1 : RatFunc F) ^ b)⁻¹))).symm
    _ = ∑ p : HeadD F d, (((p.1 : RatFunc F) ^ a)⁻¹) *
          (∑ m : MonicLt F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
            ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [headOffShiftSum F d hd p b]
    _ = ∑ p : HeadD F d, ∑ m : MonicLt F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
          (((p.1 : RatFunc F) ^ a)⁻¹) *
          ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          exact Finset.mul_sum (s := (Finset.univ : Finset F).erase 0)
            (f := fun δ : F => ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹))
            (a := (((p.1 : RatFunc F) ^ a)⁻¹))
    _ = ∑ m : MonicLt F d, ∑ p : HeadD F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
          (((p.1 : RatFunc F) ^ a)⁻¹) *
          ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹) := by
          rw [Finset.sum_comm (s := (Finset.univ : Finset (HeadD F d))) (t := (Finset.univ : Finset (MonicLt F d)))]

/-- The full level-`d` shuffle in `RatFunc F` (B3): the product of the two power sums
equals the diagonal plus Chen's `Δ`-combination. -/
lemma headProdSum (d : ℕ) (hd : 1 ≤ d) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ a)⁻¹)) *
        (∑ q : HeadD F d, (((q.1 : RatFunc F) ^ b)⁻¹)) =
      (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b))⁻¹)) +
      ∑ i ∈ Finset.Icc 1 (a + b - 1),
        RatFunc.C (ChenDeltaZ F a b i : F) * (∑ m : MonicLt F d, (((m.1 : RatFunc F) ^ i)⁻¹)) *
          (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ a)⁻¹)) * (∑ q : HeadD F d, (((q.1 : RatFunc F) ^ b)⁻¹))
        = (∑ p : HeadD F d, ∑ q ∈ (Finset.univ : Finset (HeadD F d)).erase p,
            (((p.1 : RatFunc F) ^ a)⁻¹) * (((q.1 : RatFunc F) ^ b)⁻¹)) +
          (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b))⁻¹)) := by
          exact headDiag_split F d a b
    _ = (∑ m : MonicLt F d, ∑ p : HeadD F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
            (((p.1 : RatFunc F) ^ a)⁻¹) *
            ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)) +
          (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b))⁻¹)) := by
          rw [headOffdiag_eq_shift F d hd a b]
    _ = (∑ i ∈ Finset.Icc 1 (a + b - 1),
            RatFunc.C (ChenDeltaZ F a b i : F) * (∑ m : MonicLt F d, (((m.1 : RatFunc F) ^ i)⁻¹)) *
              (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹))) +
          (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b))⁻¹)) := by
          rw [E_m_sum F d hd a b ha hb]
    _ = (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b))⁻¹)) +
          ∑ i ∈ Finset.Icc 1 (a + b - 1),
            RatFunc.C (ChenDeltaZ F a b i : F) * (∑ m : MonicLt F d, (((m.1 : RatFunc F) ^ i)⁻¹)) *
              (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
          ring

end ZagierHoffmanPositiveChar
