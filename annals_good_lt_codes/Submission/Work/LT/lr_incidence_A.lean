import Mathlib
import Submission.Work.LT.lr_local_defs

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

/-- The canonical bijection between `Vtx G × Fin Δ` (a vertex and a direction) and
`EIdx G Δ × Fin 2` (an A-edge and a layer), sending `(v,i)` to the A-edge through `v` in
direction `i` together with the layer `v.1` of `v`. Its inverse sends `(p,α)` to the endpoint
`aEnd A p α` of `p` in layer `α` (with the direction `p.2.2` of `p`). -/
noncomputable def aEquiv {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G) :
    Vtx G × Fin Δ ≃ EIdx G Δ × Fin 2 where
  toFun x := (aIdx A x.1 x.2, x.1.1)
  invFun q := (aEnd A q.1 q.2, q.1.2.2)
  left_inv x := by
    obtain ⟨⟨a, b, g⟩, i⟩ := x
    fin_cases a <;> simp [aIdx, aEnd]
  right_inv q := by
    obtain ⟨⟨b, g, i⟩, α⟩ := q
    fin_cases α <;> simp [aIdx, aEnd, inv_mul_cancel_left]

lemma aEquiv_apply {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G) (x : Vtx G × Fin Δ) :
    aEquiv A x = (aIdx A x.1 x.2, x.1.1) := rfl

/-- The summand of the incidence identity, transported across `aEquiv`: the canonical index of
the A-edge through `v` in direction `i` carries the same dispute condition as `(v,i)`, and the
endpoint `aEnd A (aIdx A v i) v.1` is `v` again. -/
lemma aEquiv_step {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (F : Vtx G → ℝ)
    (x : Vtx G × Fin Δ) :
    (if disputeA A W (aEquiv A x).1.1 (aEquiv A x).1.2.1 (aEquiv A x).1.2.2
      then F (aEnd A (aEquiv A x).1 (aEquiv A x).2) else 0)
      = (if dispAE A W x.1 x.2 then F x.1 else 0) := by
  obtain ⟨⟨a, b, g⟩, i⟩ := x
  rw [aEquiv_apply]
  fin_cases a
  · have hiff : disputeA A W b g i ↔ dispAE A W ((0 : Fin 2), b, g) i := by
      simp [disputeA, dispAE, pdispA, view, nA]
    simp [aIdx, aEnd]
    exact if_congr hiff rfl rfl
  · have hiff : disputeA A W b ((A i)⁻¹ * g) i ↔ dispAE A W ((1 : Fin 2), b, g) i := by
      simp [disputeA, dispAE, pdispA, view, nA, ne_comm]
    simp [aIdx, aEnd]
    exact if_congr hiff rfl rfl

/-- **Incidence identity for A-edges.** Summing a vertex function `F` over the two endpoints
`(0,β,g)` and `(1,β,A i * g)` of the A-edge `(β,g,i)`, restricted to disputed A-edges, equals the
sum of `rA` (the number of disputed A-edges through a vertex) against `F`. Equivalently: the map
`(v,i) ↦ (aIdx A v i, v.1)` is a bijection `Vtx G × Fin Δ ≃ EIdx G Δ × Fin 2` (with inverse
`(p,α) ↦ (aEnd A p α, p.2.2)`), `dispAE A W v i ↔ disputeA A W (aIdx A v i)`
(`disputeA_aIdx`), `aEnd A (aIdx A v i) v.1 = v` (`aEnd_aIdx`), and `rA A W v` is the cardinality
of `{i : dispAE A W v i}`. Purely combinatorial; needs `open Classical` for the `if`. -/
theorem lr_incidence_A {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (F : Vtx G → ℝ) :
    (∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2
        then F (0, p.1, p.2.1) + F (1, p.1, A p.2.2 * p.2.1) else 0)
      = ∑ v : Vtx G, (rA A W v : ℝ) * F v := by
  -- Replace the two endpoints of `p` by the two values `aEnd A p α`, `α : Fin 2`.
  have h1 : ∀ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2
        then F (0, p.1, p.2.1) + F (1, p.1, A p.2.2 * p.2.1) else 0)
      = ∑ α : Fin 2, (if disputeA A W p.1 p.2.1 p.2.2 then F (aEnd A p α) else 0) := by
    intro p
    rw [Fin.sum_univ_two]
    by_cases h : disputeA A W p.1 p.2.1 p.2.2 <;> simp [h, aEnd]
  simp_rw [h1]
  -- Reindex `EIdx G Δ × Fin 2` as `Vtx G × Fin Δ` along the canonical bijection.
  have hprod : (∑ p : EIdx G Δ, ∑ α : Fin 2,
        (if disputeA A W p.1 p.2.1 p.2.2 then F (aEnd A p α) else 0))
      = ∑ x : Vtx G × Fin Δ, (if dispAE A W x.1 x.2 then F x.1 else 0) := by
    rw [← Fintype.sum_prod_type (f := fun q : EIdx G Δ × Fin 2 =>
      (if disputeA A W q.1.1 q.1.2.1 q.1.2.2 then F (aEnd A q.1 q.2) else 0))]
    rw [← Equiv.sum_comp (aEquiv A) (fun q : EIdx G Δ × Fin 2 =>
      (if disputeA A W q.1.1 q.1.2.1 q.1.2.2 then F (aEnd A q.1 q.2) else 0))]
    exact Finset.sum_congr rfl (fun x _ => aEquiv_step A W F x)
  rw [hprod]
  -- Each vertex contributes `(number of disputed A-edges through it) * F v`.
  rw [Fintype.sum_prod_type (f := fun q : Vtx G × Fin Δ =>
      (if dispAE A W q.1 q.2 then F q.1 else 0))]
  have hstep : ∀ v : Vtx G,
      (∑ y : Fin Δ, (if dispAE A W (v, y).1 (v, y).2 then F (v, y).1 else 0))
        = (rA A W v : ℝ) * F v := by
    intro v
    have hmid : (∑ y : Fin Δ,
          (if dispAE A W (v, y).1 (v, y).2 then F (v, y).1 else 0))
        = ∑ y : Fin Δ, (if dispAE A W v y then F v else 0) :=
      Finset.sum_congr rfl (fun y _ => by simp)
    refine hmid.trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  exact Finset.sum_congr rfl (fun v _ => hstep v)

end Work.LT
