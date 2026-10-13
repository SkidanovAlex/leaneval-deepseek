import Mathlib
import Submission.Work.WilkiesH.Interp.JetSetup

set_option autoImplicit false
noncomputable section

open Classical
open Finset

namespace Work.WilkiesH.Interp

open Work.WilkiesH

/-- The fiber of `multVecE hn` over `α` is described by the plain multiplicity
vector: `multVecE hn g = α` iff `multFun g` agrees with `α.toFun` on every
coordinate.  (The map `multVecE hn` into `ExpVec μ b` is injective, so equality
in `ExpVec` is equality of the underlying functions.) -/
private lemma multVecE_eq_iff {μ n b : ℕ} (hn : n ≤ b) (g : Fin n → Fin μ) (α : ExpVec μ b) :
    multVecE hn g = α ↔ ∀ i, multFun g i = α.toFun i := by
  constructor
  · intro h i
    rw [← multVecE_toFun hn g i, h]
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact h i

/-- The number of tuples `g : Fin n → Fin μ` whose multiplicity vector is `α`
is exactly `jetFiberCard μ n α.toFun`. -/
lemma fiberCard_multVecE {μ n b : ℕ} (hn : n ≤ b) (α : ExpVec μ b) :
    Fintype.card {g : Fin n → Fin μ // multVecE hn g = α} = jetFiberCard μ n α.toFun := by
  rw [jetFiberCard]
  apply Fintype.card_congr
  refine Equiv.subtypeEquivRight (fun g => ?_)
  rw [multVecE_eq_iff]
  constructor
  · intro h i; rw [← multFun_eq_card g i]; exact h i
  · intro h i; rw [multFun_eq_card g i]; exact h i

/-- Grouping a product over a tuple by the multiplicities of its values:
`∏ l, w (p l) = ∏ i, w i ^ multFun p i`. -/
lemma prod_eq_prod_pow_multFun {μ n : ℕ} (w : Fin μ → ℝ) (p : Fin n → Fin μ) :
    ∏ l : Fin n, w (p l) = ∏ i : Fin μ, w i ^ multFun p i := by
  rw [← Fintype.prod_fiberwise p (fun l => w (p l))]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : (∏ i : {i // p i = j}, w (p i.val)) = ∏ _i : {i // p i = j}, w j :=
    Finset.prod_congr rfl (fun i _ => by rw [i.2])
  rw [h1, Finset.prod_const, Finset.card_univ, ← multFun_eq_card p j]

theorem sum_fiberCard_weight {μ b n : ℕ} (hn : n ≤ b) (w : Fin μ → ℝ) :
    ∑ α : ExpVec μ b, (∏ i, w i ^ α.toFun i) * ((jetFiberCard μ n α.toFun : ℕ) : ℝ)
      = (∑ i, w i) ^ n := by
  have hinner : ∀ α : ExpVec μ b,
      (∑ p : {p : Fin n → Fin μ // multVecE hn p = α}, ∏ i : Fin μ, w i ^ multFun p.1 i)
        = (jetFiberCard μ n α.toFun : ℝ) * (∏ i : Fin μ, w i ^ α.toFun i) := by
    intro α
    have hconst : ∀ p : {p : Fin n → Fin μ // multVecE hn p = α},
        (∏ i : Fin μ, w i ^ multFun p.1 i) = (∏ i : Fin μ, w i ^ α.toFun i) := by
      intro p
      refine Finset.prod_congr rfl fun i _ => ?_
      have : multFun p.1 i = α.toFun i := by rw [← multVecE_toFun hn p.1 i, p.2]
      rw [this]
    rw [Finset.sum_congr rfl (fun p _ => hconst p), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, fiberCard_multVecE hn α]
  calc
    ∑ α : ExpVec μ b, (∏ i, w i ^ α.toFun i) * ((jetFiberCard μ n α.toFun : ℕ) : ℝ)
        = ∑ α : ExpVec μ b, (jetFiberCard μ n α.toFun : ℝ) * (∏ i, w i ^ α.toFun i) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [mul_comm]
      _ = ∑ α : ExpVec μ b, ∑ p : {p : Fin n → Fin μ // multVecE hn p = α},
              (∏ i : Fin μ, w i ^ multFun p.1 i) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hinner α]
      _ = ∑ p : Fin n → Fin μ, (∏ i : Fin μ, w i ^ multFun p i) :=
          Fintype.sum_fiberwise (multVecE hn)
            (fun p : Fin n → Fin μ => ∏ i : Fin μ, w i ^ multFun p i)
      _ = ∑ p : Fin n → Fin μ, (∏ l : Fin n, w (p l)) := by
          refine Finset.sum_congr rfl fun p _ => (prod_eq_prod_pow_multFun w p).symm
      _ = (∑ i : Fin μ, w i) ^ n := (Fintype.sum_pow w n).symm

end Work.WilkiesH.Interp
