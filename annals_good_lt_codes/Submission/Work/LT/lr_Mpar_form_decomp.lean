import Mathlib
import Submission.Work.LT.lr_Mpar_defs

/-! The parallel-move quadratic form decomposes over the `2Δ` label classes.

`MparForm = ⟨1_R, M‖ 1_R⟩` is, by definition, the sum over the A-edges and the B-edges of the
contribution `[edge disputed] · (#parallel disputed edges across a random square)/Δ`.  For a fixed
A-label `i` the A-edge `(β,g,i)` carries the label-class indicator `sA A W i (β,g)`, and the
"parallel A-edge across a random square" probability is exactly the walk `classOpB B` applied to
that indicator (`classOpB_sA_eq_parA`); symmetrically for the B-labels with `classOpA`
(`classOpA_sB_eq_parB`).  Reindexing the edge sum by label (`sum_EIdx_reindex`) therefore turns the
A-part into `∑ i, QA i` and the B-part into `∑ j, QB j`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] {Δ : ℕ}

/-- `EIdx G Δ = Fin 2 × (G × Fin Δ)` reindexed by the last coordinate: a sum over edges is a sum
over labels of a sum over `Fin 2 × G`. -/
lemma sum_EIdx_reindex (f : EIdx G Δ → ℝ) :
    (∑ p : EIdx G Δ, f p) = ∑ i : Fin Δ, ∑ q : Fin 2 × G, f (q.1, (q.2, i)) := by
  let e : EIdx G Δ ≃ Fin Δ × (Fin 2 × G) :=
    { toFun := fun p => (p.2.2, (p.1, p.2.1))
      invFun := fun x => (x.2.1, (x.2.2, x.1))
      left_inv := by rintro ⟨β, g, i⟩; rfl
      right_inv := by rintro ⟨i, β, g⟩; rfl }
  rw [← Equiv.sum_comp e.symm f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun q _ => ?_))
  rfl

/-- The walk `classOpB B` on the label-`i` indicator `sA A W i` computes exactly the fraction
`parA A B W (β,g,i)` of squares through the A-edge `(β,g,i)` whose parallel A-edge is disputed.

The class of A-edges with label `i` is indexed by `(β,g) ↦ (β,g,i)`, and the walk `classOpB B`
sends `(0,g) ↦ (1, g * B j)`, `(1,g) ↦ (0, g * (B j)⁻¹)`; these are precisely the A-edges of label
`i` through the parallel vertices `nB B (0,β,g) j`, so `disputeA_aIdx` identifies the two
dispute conditions and the `0/1` sum over `j` is the cardinality of the disputed set. -/
lemma classOpB_sA_eq_parA (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (i : Fin Δ) (q : Fin 2 × G) :
    classOpB B (sA A W i) q = parA A B W (q.1, q.2, i) := by
  obtain ⟨β, g⟩ := q
  fin_cases β <;>
    simp only [classOpB, sA, parA, nB, Fin.isValue, Fin.zero_eta, ite_true, ite_false,
      Fin.mk_one, Fin.reduceEq]
  · -- `β = 0`: the walk goes to `(1, g * B j)`
    have hiff : ∀ j : Fin Δ, disputeA A W 1 (g * B j) i ↔ dispAE A W (0, 1, g * B j) i := by
      intro j
      have h := disputeA_aIdx A W ((0 : Fin 2), (1 : Fin 2), g * B j) i
      simpa [aIdx] using h
    have hsum : (∑ j : Fin Δ, (if disputeA A W 1 (g * B j) i then (1 : ℝ) else 0))
        = ((Finset.univ.filter (fun x => dispAE A W (0, 1, g * B x) i)).card : ℝ) := by
      rw [show (∑ j : Fin Δ, (if disputeA A W 1 (g * B j) i then (1 : ℝ) else 0))
          = ∑ j : Fin Δ, (if dispAE A W (0, 1, g * B j) i then (1 : ℝ) else 0) from
          Finset.sum_congr rfl (fun j _ => by rw [hiff j])]
      rw [Finset.card_filter]
      push_cast
      exact Finset.sum_congr rfl (fun x _ => rfl)
    rw [hsum]
  · -- `β = 1`: the walk goes to `(0, g * (B j)⁻¹)`
    have hiff : ∀ j : Fin Δ,
        disputeA A W 0 (g * (B j)⁻¹) i ↔ dispAE A W (0, 0, g * (B j)⁻¹) i := by
      intro j
      have h := disputeA_aIdx A W ((0 : Fin 2), (0 : Fin 2), g * (B j)⁻¹) i
      simpa [aIdx] using h
    have hsum : (∑ j : Fin Δ, (if disputeA A W 0 (g * (B j)⁻¹) i then (1 : ℝ) else 0))
        = ((Finset.univ.filter (fun x => dispAE A W (0, 0, g * (B x)⁻¹) i)).card : ℝ) := by
      rw [show (∑ j : Fin Δ, (if disputeA A W 0 (g * (B j)⁻¹) i then (1 : ℝ) else 0))
          = ∑ j : Fin Δ, (if dispAE A W (0, 0, g * (B j)⁻¹) i then (1 : ℝ) else 0) from
          Finset.sum_congr rfl (fun j _ => by rw [hiff j])]
      rw [Finset.card_filter]
      push_cast
      exact Finset.sum_congr rfl (fun x _ => rfl)
    rw [hsum]

/-- The walk `classOpA A` on the label-`j` indicator `sB B W j` computes exactly the fraction
`parB A B W (α,g,j)` of squares through the B-edge `(α,g,j)` whose parallel B-edge is disputed.
Transposed form of `classOpB_sA_eq_parA`, using `disputeB_bIdx` and the walk
`(0,g) ↦ (1, A i * g)`, `(1,g) ↦ (0, (A i)⁻¹ * g)` of `classOpA A`. -/
lemma classOpA_sB_eq_parB (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (j : Fin Δ) (q : Fin 2 × G) :
    classOpA A (sB B W j) q = parB A B W (q.1, q.2, j) := by
  obtain ⟨α, g⟩ := q
  fin_cases α <;>
    simp only [classOpA, sB, parB, nA, Fin.isValue, Fin.zero_eta, ite_true, ite_false,
      Fin.mk_one, Fin.reduceEq]
  · -- `α = 0`: the walk goes to `(1, A i * g)`
    have hiff : ∀ i : Fin Δ, disputeB B W 1 (A i * g) j ↔ dispBE B W (1, 0, A i * g) j := by
      intro i
      have h := disputeB_bIdx B W ((1 : Fin 2), (0 : Fin 2), A i * g) j
      simpa [bIdx] using h
    have hsum : (∑ i : Fin Δ, (if disputeB B W 1 (A i * g) j then (1 : ℝ) else 0))
        = ((Finset.univ.filter (fun x => dispBE B W (1, 0, A x * g) j)).card : ℝ) := by
      rw [show (∑ i : Fin Δ, (if disputeB B W 1 (A i * g) j then (1 : ℝ) else 0))
          = ∑ i : Fin Δ, (if dispBE B W (1, 0, A i * g) j then (1 : ℝ) else 0) from
          Finset.sum_congr rfl (fun i _ => by rw [hiff i])]
      rw [Finset.card_filter]
      push_cast
      exact Finset.sum_congr rfl (fun x _ => rfl)
    rw [hsum]
  · -- `α = 1`: the walk goes to `(0, (A i)⁻¹ * g)`
    have hiff : ∀ i : Fin Δ,
        disputeB B W 0 ((A i)⁻¹ * g) j ↔ dispBE B W (0, 0, (A i)⁻¹ * g) j := by
      intro i
      have h := disputeB_bIdx B W ((0 : Fin 2), (0 : Fin 2), (A i)⁻¹ * g) j
      simpa [bIdx] using h
    have hsum : (∑ i : Fin Δ, (if disputeB B W 0 ((A i)⁻¹ * g) j then (1 : ℝ) else 0))
        = ((Finset.univ.filter (fun x => dispBE B W (0, 0, (A x)⁻¹ * g) j)).card : ℝ) := by
      rw [show (∑ i : Fin Δ, (if disputeB B W 0 ((A i)⁻¹ * g) j then (1 : ℝ) else 0))
          = ∑ i : Fin Δ, (if dispBE B W (0, 0, (A i)⁻¹ * g) j then (1 : ℝ) else 0) from
          Finset.sum_congr rfl (fun i _ => by rw [hiff i])]
      rw [Finset.card_filter]
      push_cast
      exact Finset.sum_congr rfl (fun x _ => rfl)
    rw [hsum]

theorem lr_Mpar_form_decomp {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    MparForm A B W = (∑ i : Fin Δ, QA A B W i) + (∑ j : Fin Δ, QB A B W j) := by
  have hA : (∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2 then parA A B W p else 0)
      = ∑ i : Fin Δ, QA A B W i := by
    rw [sum_EIdx_reindex]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [QA]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [classOpB_sA_eq_parA]
    by_cases h : disputeA A W q.1 q.2 i <;> simp [sA, h]
  have hB : (∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2 then parB A B W p else 0)
      = ∑ j : Fin Δ, QB A B W j := by
    rw [sum_EIdx_reindex]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [QB]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [classOpA_sB_eq_parB]
    by_cases h : disputeB B W q.1 q.2 j <;> simp [sB, h]
  rw [MparForm, hA, hB]

end Work.LT
