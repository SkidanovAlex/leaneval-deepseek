import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Order
import Submission.Work.BoseDictC.modeProd_eq_zero_of_sum_ne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDictC.modeProd_cons_expand`

The pointwise expansion of the symmetric mode product `M_α := modeProd e · α` in its first
coordinate.  Writing `e_k := Work.BoseB4.e m k = Finsupp.single k 1`, the statement is

`M_α(z, y) = Σ_k e_k(z) · M_{α - e_k}(y)`  (`y ∈ Xn d`, `z ∈ Sp`, `deg α = d + 1`),

the box-side shadow of the model row `ann_l (x^α) = α_l x^{α - e_l}` (read here as the
first-coordinate expansion of a symmetric mode product).

## Proof

`modeProd e (d+1) α (Fin.cons z y)` is the sum over the labellings `σ : Fin (d+1) → Fin m`
with `modeMult σ = α` of `∏_i e_{σ i}((z,y)_i)`.  Reindexing a labelling by its first
coordinate, `σ = Fin.cons k τ` with `k = σ 0` and `τ = Fin.tail σ` (`consEquiv`), the two
ingredients are

* `modeMult_cons : modeMult (Fin.cons k τ) = modeMult τ + e_k`, so that the occupation
  indicator `[modeMult τ + e_k = α]` can be rewritten as `[modeMult τ = α - e_k]`
  (`sum_add_single_eq_sum_sub_single`; the two conditions differ only in the degenerate case
  `α k = 0`, where both are false because `modeMult τ` has degree `d ≠ d + 1 = deg α`), and
* `prod_cons_cons : ∏_i e_{σ i}((z,y)_i) = e_k(z) · ∏_i e_{τ i}(y_i)`.

The result follows by exchanging the sum over pairs `(k, τ)` for the iterated sum
(`Fintype.sum_prod_type`) and pulling `e_k(z)` out of the inner sum (`Finset.mul_sum`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseDictC

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The occupation multi-index of a labelling -/

/-- The occupation multi-index of a labelling is the sum of the mode indices `e_{σ i}`. -/
lemma modeMult_eq_sum_single {m n : ℕ} (σ : Fin n → Fin m) :
    Work.BoseDict.modeMult σ = ∑ i : Fin n, Finsupp.single (σ i) 1 := by
  classical
  ext k
  rw [Work.BoseDict.modeMult, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The component at `k` of the occupation multi-index of `σ` is the number of particles
carrying the label `k`. -/
lemma modeMult_apply {m n : ℕ} (σ : Fin n → Fin m) (k : Fin m) :
    Work.BoseDict.modeMult σ k = (Finset.univ.filter fun i => σ i = k).card := by
  classical
  rw [Work.BoseDict.modeMult, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Splitting a labelling as `Fin.cons k τ` in its first coordinate adds the mode `e_k` to the
occupation multi-index. -/
lemma modeMult_cons {m d : ℕ} (k : Fin m) (τ : Fin d → Fin m) :
    Work.BoseDict.modeMult (Fin.cons k τ) = Work.BoseDict.modeMult τ + Finsupp.single k 1 := by
  classical
  rw [modeMult_eq_sum_single (Fin.cons k τ), modeMult_eq_sum_single τ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact add_comm _ _

/-- The product of the modes along the labelling `Fin.cons k τ` at the configuration
`Fin.cons z y` splits into the first factor and the product along `τ`. -/
lemma prod_cons_cons {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (k : Fin m)
    (τ : Fin d → Fin m) {y : Fin d → Work.BoseDict.Sp} {z : Work.BoseDict.Sp} :
    (∏ i : Fin (d + 1), e ((Fin.cons k τ : Fin (d + 1) → Fin m) i)
        ((Fin.cons z y : Fin (d + 1) → Work.BoseDict.Sp) i))
      = e k z * ∏ i : Fin d, e (τ i) (y i) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The occupation condition `β + e_k = α` is the condition `β = α - e_k`, for a multi-index
`β` of degree `d` and a multi-index `α` of degree `d + 1`.

The forward direction is `β = (β + e_k) - e_k`.  For the converse, if `α k = 0` then
`α - e_k = α` has degree `d + 1 ≠ d`, so `β = α - e_k` is impossible; otherwise `e_k ≤ α`,
whence `(α - e_k) + e_k = α`. -/
lemma sum_add_single_eq_sum_sub_single {m d : ℕ} {α : Fin m →₀ ℕ}
    (hα : α.sum (fun _ k => k) = d + 1) {β : Fin m →₀ ℕ} (hβ : β.sum (fun _ k => k) = d)
    (k : Fin m) :
    (if β + Finsupp.single k 1 = α then (1 : ℂ) else 0)
      = (if β = α - Finsupp.single k 1 then (1 : ℂ) else 0) := by
  classical
  have hiff : (β + Finsupp.single k 1 = α) ↔ (β = α - Finsupp.single k 1) := by
    constructor
    · intro h
      rw [← h]
      ext j
      rw [Finsupp.tsub_apply, Finsupp.add_apply, Nat.add_sub_cancel]
    · intro h
      have hk : α k ≠ 0 := by
        intro hk0
        have hsub : α - Finsupp.single k 1 = α := by
          ext j
          rw [Finsupp.tsub_apply]
          by_cases hj : j = k
          · subst hj; rw [hk0]; simp
          · rw [Finsupp.single_eq_of_ne hj]; simp
        have hd := hβ
        rw [h, hsub, hα] at hd
        omega
      have hk1 : 1 ≤ α k := Nat.pos_of_ne_zero hk
      rw [h]
      ext j
      rw [Finsupp.add_apply, Finsupp.tsub_apply]
      by_cases hj : j = k
      · subst hj
        rw [Finsupp.single_eq_same, Nat.sub_add_cancel hk1]
      · rw [Finsupp.single_eq_of_ne hj]
        simp
  by_cases h : β + Finsupp.single k 1 = α
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]

/-- Reindexing the labellings of `Fin (d+1)` particles by the label of the first particle:
`σ ↦ (σ 0, Fin.tail σ)`, inverse to `(k, τ) ↦ Fin.cons k τ`. -/
private def consEquiv (m d : ℕ) : (Fin m × (Fin d → Fin m)) ≃ (Fin (d + 1) → Fin m) where
  toFun p := Fin.cons p.1 p.2
  invFun σ := (σ 0, Fin.tail σ)
  left_inv p := by obtain ⟨a, b⟩ := p; simp [Fin.cons_zero, Fin.tail_cons]
  right_inv σ := by simp [Fin.cons_self_tail]

/-- **The first-coordinate expansion of the symmetric mode product.**  For a multi-index `α` of
total degree `d + 1`, a `d`-particle configuration `y` and a one-particle point `z`,

`modeProd e (d+1) α (z, y) = Σ_k e k z · modeProd e d (α - e_k) y`. -/
theorem modeProd_cons_expand {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} {α : Fin m →₀ ℕ}
    (hα : α.sum (fun _ k => k) = d + 1) (y : Work.BoseDict.Xn d) (z : Work.BoseDict.Sp) :
    Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y)
      = ∑ k : Fin m, e k z * Work.BoseDict.modeProd e d (α - Work.BoseB4.e m k) y := by
  classical
  have step1 : Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y)
      = ∑ p : Fin m × (Fin d → Fin m),
          (if Work.BoseDict.modeMult (Fin.cons p.1 p.2) = α then (1 : ℂ) else 0)
            * ∏ i : Fin (d + 1), e ((Fin.cons p.1 p.2 : Fin (d + 1) → Fin m) i)
                ((Fin.cons z y : Fin (d + 1) → Work.BoseDict.Sp) i) := by
    rw [Work.BoseDict.modeProd]
    exact (Equiv.sum_comp (consEquiv m d) (fun σ : Fin (d + 1) → Fin m =>
      (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
        * ∏ i : Fin (d + 1), e (σ i)
            ((Fin.cons z y : Fin (d + 1) → Work.BoseDict.Sp) i))).symm
  have step2 : (∑ p : Fin m × (Fin d → Fin m),
          (if Work.BoseDict.modeMult (Fin.cons p.1 p.2) = α then (1 : ℂ) else 0)
            * ∏ i : Fin (d + 1), e ((Fin.cons p.1 p.2 : Fin (d + 1) → Fin m) i)
                ((Fin.cons z y : Fin (d + 1) → Work.BoseDict.Sp) i))
      = ∑ p : Fin m × (Fin d → Fin m),
          e p.1 z * ((if Work.BoseDict.modeMult p.2 = α - Finsupp.single p.1 1
              then (1 : ℂ) else 0)
            * ∏ i : Fin d, e (p.2 i) (y i)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [modeMult_cons, prod_cons_cons]
    rw [sum_add_single_eq_sum_sub_single hα (modeMult_sum p.2) p.1]
    ring
  have step3 : (∑ p : Fin m × (Fin d → Fin m),
          e p.1 z * ((if Work.BoseDict.modeMult p.2 = α - Finsupp.single p.1 1
              then (1 : ℂ) else 0)
            * ∏ i : Fin d, e (p.2 i) (y i)))
      = ∑ k : Fin m, ∑ τ : Fin d → Fin m,
          e k z * ((if Work.BoseDict.modeMult τ = α - Finsupp.single k 1
              then (1 : ℂ) else 0)
            * ∏ i : Fin d, e (τ i) (y i)) :=
    Fintype.sum_prod_type _
  have step4 : (∑ k : Fin m, ∑ τ : Fin d → Fin m,
          e k z * ((if Work.BoseDict.modeMult τ = α - Finsupp.single k 1
              then (1 : ℂ) else 0)
            * ∏ i : Fin d, e (τ i) (y i)))
      = ∑ k : Fin m, e k z * ∑ τ : Fin d → Fin m,
          ((if Work.BoseDict.modeMult τ = α - Finsupp.single k 1 then (1 : ℂ) else 0)
            * ∏ i : Fin d, e (τ i) (y i)) :=
    Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  have step5 : (∑ k : Fin m, e k z * ∑ τ : Fin d → Fin m,
          ((if Work.BoseDict.modeMult τ = α - Finsupp.single k 1 then (1 : ℂ) else 0)
            * ∏ i : Fin d, e (τ i) (y i)))
      = ∑ k : Fin m, e k z * Work.BoseDict.modeProd e d (α - Work.BoseB4.e m k) y := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rfl
  rw [step1, step2, step3, step4, step5]

end Work.BoseDictC
