import Mathlib
import Submission.Work.LT.lr_local_defs

namespace Work.LT

open Classical

/-- A B-edge is determined by the vertex `v` at which it is seen together with the layer `v.2.1`
of that vertex: `(v, j) ↦ (bIdx B v j, v.2.1)` is a bijection `Vtx G × Fin Δ ≃ EIdx G Δ × Fin 2`
(inverse `(p, β) ↦ (bEnd B p β, p.2.2)`).  Consequently the multiset of pairs "B-edge, one of its
two endpoints" is the multiset of pairs "vertex, incident B-edge direction". -/
def bIdxEquiv {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) :
    Vtx G × Fin Δ ≃ EIdx G Δ × Fin 2 where
  toFun x := (bIdx B x.1 x.2, x.1.2.1)
  invFun y := (bEnd B y.1 y.2, y.1.2.2)
  left_inv x := by
    obtain ⟨⟨a, b, g⟩, j⟩ := x
    refine Prod.ext ?_ ?_
    · exact bEnd_bIdx B (a, b, g) j
    · by_cases h : b = 0 <;> simp [bIdx, h]
  right_inv y := by
    obtain ⟨p, β⟩ := y
    refine Prod.ext ?_ ?_
    · exact bIdx_bEnd B p β
    · rfl

lemma bIdxEquiv_apply {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (v : Vtx G) (j : Fin Δ) : bIdxEquiv B (v, j) = (bIdx B v j, v.2.1) := rfl

/-- **Incidence identity for B-edges** (the transposed form of `lr_incidence_A`): summing a vertex
function `F` over the two endpoints `(α,0,g)` and `(α,1,g * B j)` of the B-edge `(α,g,j)`,
restricted to disputed B-edges, equals the sum of `rB` against `F`. -/
theorem lr_incidence_B {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (F : Vtx G → ℝ) :
    (∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2
        then F (p.1, 0, p.2.1) + F (p.1, 1, p.2.1 * B p.2.2) else 0)
      = ∑ v : Vtx G, (rB B W v : ℝ) * F v := by
  classical
  -- Replace the sum over the two endpoints of `p` by a sum over the layer `β : Fin 2`, and turn
  -- the double sum over `(p, β)` into a sum over the product type.
  have hstep1 : (∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2
        then F (p.1, 0, p.2.1) + F (p.1, 1, p.2.1 * B p.2.2) else 0)
      = ∑ p : EIdx G Δ, ∑ β : Fin 2,
          (if disputeB B W p.1 p.2.1 p.2.2 then F (bEnd B p β) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro p _
    by_cases h : disputeB B W p.1 p.2.1 p.2.2
    · simp [h, bEnd]
    · simp [h]
  have hstep2 : (∑ p : EIdx G Δ, ∑ β : Fin 2,
          (if disputeB B W p.1 p.2.1 p.2.2 then F (bEnd B p β) else 0))
      = ∑ y : EIdx G Δ × Fin 2,
          (if disputeB B W y.1.1 y.1.2.1 y.1.2.2 then F (bEnd B y.1 y.2) else 0) :=
    (Fintype.sum_prod_type (fun y : EIdx G Δ × Fin 2 =>
      (if disputeB B W y.1.1 y.1.2.1 y.1.2.2 then F (bEnd B y.1 y.2) else 0))).symm
  -- Reindex along the bijection `(v, j) ↦ (bIdx B v j, v.2.1)`: the incidence structure becomes
  -- the "vertex, incident direction" picture.
  have hstep3 : (∑ y : EIdx G Δ × Fin 2,
          (if disputeB B W y.1.1 y.1.2.1 y.1.2.2 then F (bEnd B y.1 y.2) else 0))
      = ∑ x : Vtx G × Fin Δ, (if dispBE B W x.1 x.2 then F x.1 else 0) := by
    rw [← Equiv.sum_comp (bIdxEquiv B) (fun y : EIdx G Δ × Fin 2 =>
      (if disputeB B W y.1.1 y.1.2.1 y.1.2.2 then F (bEnd B y.1 y.2) else 0))]
    refine Finset.sum_congr rfl ?_
    rintro ⟨v, j⟩ _
    simp only [bIdxEquiv_apply, disputeB_bIdx B W v j, bEnd_bIdx B v j]
  have hstep4 : (∑ x : Vtx G × Fin Δ, (if dispBE B W x.1 x.2 then F x.1 else 0))
      = ∑ v : Vtx G, ∑ j : Fin Δ, (if dispBE B W v j then F v else 0) :=
    Fintype.sum_prod_type _
  -- At a fixed vertex, the sum over the incident directions counts `rB` copies of `F v`.
  have hstep5 : ∀ v : Vtx G, (∑ j : Fin Δ, (if dispBE B W v j then F v else 0))
      = (rB B W v : ℝ) * F v := by
    intro v
    calc ∑ j : Fin Δ, (if dispBE B W v j then F v else 0)
        = ∑ j : Fin Δ, (if dispBE B W v j then (1 : ℝ) else 0) * F v := by
          refine Finset.sum_congr rfl ?_
          intro j _
          by_cases h : dispBE B W v j <;> simp [h]
      _ = (∑ j : Fin Δ, (if dispBE B W v j then (1 : ℝ) else 0)) * F v :=
          (Finset.sum_mul Finset.univ
            (fun j : Fin Δ => (if dispBE B W v j then (1 : ℝ) else 0)) (F v)).symm
      _ = (rB B W v : ℝ) * F v := by
          congr 1
          rw [rB]
          exact Finset.sum_boole (fun j : Fin Δ => dispBE B W v j) Finset.univ
  rw [hstep1, hstep2, hstep3, hstep4]
  exact Finset.sum_congr rfl (fun v _ => hstep5 v)

end Work.LT
