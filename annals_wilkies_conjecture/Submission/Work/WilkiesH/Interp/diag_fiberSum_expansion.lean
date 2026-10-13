import Mathlib
import Submission.Work.WilkiesH.Interp.JetSetup

open Classical Finset

namespace Work.WilkiesH.Interp

open Work.WilkiesH

/-- Every vector of `Fin μ → ℝ` is the sum of its coordinates times the coordinate
vectors `Pi.single j 1` of the standard basis. -/
lemma sum_smul_single {μ : ℕ} (v : Fin μ → ℝ) :
    (∑ j : Fin μ, v j • (Pi.single j (1 : ℝ) : Fin μ → ℝ)) = v := by
  ext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- Expansion of a continuous `n`-multilinear map of `Fin μ → ℝ` on the diagonal in
the coordinate basis `e j = Pi.single j 1`: expanding each of the `n` arguments with
`v = ∑ j, v j • e j` and using multilinearity, one gets the sum over all tuples
`r : Fin n → Fin μ` of `(∏ k, v (r k)) • f (e_{r 1}, …, e_{r n})`. -/
lemma diag_expansion {μ n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => (Fin μ → ℝ)) ℝ) (v : Fin μ → ℝ) :
    f (fun _ => v) = ∑ r : Fin n → Fin μ, (∏ k, v (r k)) * f (fun k => Pi.single (r k) 1) := by
  have hG : (fun _ : Fin n => v)
      = (fun i : Fin n => ∑ j : Fin μ, v j • (Pi.single j (1 : ℝ) : Fin μ → ℝ)) := by
    funext i; exact (sum_smul_single v).symm
  calc f (fun _ => v)
      = f (fun i : Fin n => ∑ j : Fin μ, v j • (Pi.single j (1 : ℝ) : Fin μ → ℝ)) := by
          rw [hG]
    _ = f.toMultilinearMap
          (fun i : Fin n => ∑ j : Fin μ, v j • (Pi.single j (1 : ℝ) : Fin μ → ℝ)) := rfl
    _ = ∑ r : Fin n → Fin μ, f.toMultilinearMap
          (fun i : Fin n => v (r i) • (Pi.single (r i) (1 : ℝ) : Fin μ → ℝ)) :=
          MultilinearMap.map_sum _ _
    _ = ∑ r : Fin n → Fin μ, (∏ k : Fin n, v (r k)) * f (fun k => Pi.single (r k) 1) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [MultilinearMap.map_smul_univ, smul_eq_mul]
          rfl

/-- Grouping a product over a tuple by the multiplicities of its values:
`∏ l, w (p l) = ∏ i, w i ^ multFun p i`. -/
lemma prod_eq_prod_pow_multFun' {μ n : ℕ} (w : Fin μ → ℝ) (p : Fin n → Fin μ) :
    ∏ l : Fin n, w (p l) = ∏ i : Fin μ, w i ^ multFun p i := by
  rw [← Fintype.prod_fiberwise p (fun l => w (p l))]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : (∏ i : {i // p i = j}, w (p i.val)) = ∏ _i : {i // p i = j}, w j :=
    Finset.prod_congr rfl (fun i _ => by rw [i.2])
  rw [h1, Finset.prod_const, Finset.card_univ, ← multFun_eq_card p j]

/-- The fiber of `multVecE hn` over `α` is described by the plain multiplicity vector:
`multVecE hn g = α` iff `multFun g` agrees with `α.toFun` on every coordinate. -/
lemma multVecE_eq_iff' {μ n b : ℕ} (hn : n ≤ b) (g : Fin n → Fin μ) (α : ExpVec μ b) :
    multVecE hn g = α ↔ ∀ i, multFun g i = α.toFun i := by
  constructor
  · intro h i
    rw [← multVecE_toFun hn g i, h]
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (multVecE hn g).toFun i = α.toFun i
    rw [multVecE_toFun hn g i, h i]

/-- The sum of the `n`-jet of `F` at `t₀`, evaluated on the tuples of coordinate basis
vectors belonging to the fiber of the multiplicity vector `α`, is the fiber sum
`jetFiberSum n α.toFun F t₀`. -/
lemma fiberSum_eq_jetFiberSum {μ b n : ℕ} (hn : n ≤ b) (α : ExpVec μ b)
    (F : (Fin μ → ℝ) → ℝ) (t₀ : Fin μ → ℝ) :
    (∑ r : {r : Fin n → Fin μ // multVecE hn r = α},
        (iteratedFDeriv ℝ n F t₀) (fun k => Pi.single (r.1 k) 1))
      = jetFiberSum n α.toFun F t₀ := by
  rw [jetFiberSum]
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight ?_) _ _ (fun x => rfl)
  intro g
  rw [multVecE_eq_iff']
  constructor
  · intro h i; rw [← multFun_eq_card g i]; exact h i
  · intro h i; rw [multFun_eq_card g i]; exact h i

/-- **Diagonal expansion of an iterated derivative over multiplicity fibers.**
The `n`-th derivative of `F` at `t₀`, evaluated on the diagonal `(v, …, v)`, is the sum over
exponent vectors `α` of total degree `≤ b` of `(∏ i, v i ^ α i)` times the sum of
`(D^n F t₀)(e_{g 1}, …, e_{g n})` over the tuples `g` with multiplicity vector `α`
(`= jetFiberSum n α.toFun F t₀`; that sum is `0` when `∑ i, α i ≠ n`).
The proof needs no smoothness of `F`: `iteratedFDeriv n F t₀` is an `n`-multilinear map, so each
of its `n` arguments can be expanded in the basis `e i = Pi.single i 1` of `Fin μ → ℝ`. -/
theorem diag_fiberSum_expansion {μ b n : ℕ} (hn : n ≤ b) (F : (Fin μ → ℝ) → ℝ)
    (t₀ v : Fin μ → ℝ) :
    (iteratedFDeriv ℝ n F t₀) (fun _ => v) =
      ∑ α : Work.WilkiesH.ExpVec μ b,
        (∏ i, v i ^ (Work.WilkiesH.ExpVec.toFun α) i) *
          Work.WilkiesH.Interp.jetFiberSum n (Work.WilkiesH.ExpVec.toFun α) F t₀ := by
  rw [diag_expansion]
  rw [← Fintype.sum_fiberwise (multVecE hn)
        (fun r : Fin n → Fin μ =>
          (∏ k, v (r k)) * (iteratedFDeriv ℝ n F t₀) (fun k => Pi.single (r k) 1))]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hconst : ∀ r : {r : Fin n → Fin μ // multVecE hn r = α},
      (∏ k : Fin n, v (r.1 k)) = ∏ i : Fin μ, v i ^ α.toFun i := by
    intro r
    rw [prod_eq_prod_pow_multFun']
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← multVecE_toFun hn r.1 i, r.2]
  rw [Finset.sum_congr rfl (fun r _ => by rw [hconst r]), ← Finset.mul_sum,
    fiberSum_eq_jetFiberSum hn α F t₀]

end Work.WilkiesH.Interp
