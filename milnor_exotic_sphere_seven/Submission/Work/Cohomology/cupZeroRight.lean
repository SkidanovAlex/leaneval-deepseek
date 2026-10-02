import Mathlib
import Submission.Work.Cohomology.cup1defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cup product with a `0`-cocycle on the right

Let `γ` be a cochain of degree `k` and `β` a `0`-**cocycle** (`cochainDiff β = 0`) on the singular
cochains of a simplicial set `X`.  Then the Alexander–Whitney cup product becomes commutative:

`(Nat.add_comm k 0) ▸ (γ ⌣ β) = β ⌣ γ`

(the transport `Nat.add_comm k 0 : k + 0 = 0 + k` is only there because the two sides live in the
degrees `k + 0` and `0 + k`).

Mathematically this is the statement that a `0`-cocycle is constant on the vertices of a simplex:
evaluating at a `k`-simplex `σ` the two products give

* `(γ ⌣ β)(σ) = γ(σ) · β(σ_back)` where `σ_back` is the **last** vertex of `σ`,
* `(β ⌣ γ)(σ) = β(σ_front) · γ(σ)` where `σ_front` is the **first** vertex of `σ`,

and the `0`-cocycle condition, applied to the edge of `σ` joining its first and last vertex, says
exactly `β(σ_front) = β(σ_back)`; then `R` is commutative.

## Contents

* `cupZeroRight_edgeTo` — the edge `⦋1⦌ ⟶ ⦋n⦌` from vertex `0` to vertex `n`;
* `cupZeroRight_hom_fin1_ext` — two maps out of `⦋0⦌` agreeing on the unique point agree;
* `cupZeroRight_zero_cocycle_edge` — a `0`-cocycle takes the same value at the two ends of an edge;
* `cupZeroRight_eqToHom_add_comm` / `cupZeroRight_delta_one_comp` / `cupZeroRight_delta_zero_comp` —
  the identifications of the relevant face maps;
* `cupZeroRight` — the theorem.
-/

set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The edge `⦋1⦌ ⟶ ⦋n⦌` from the vertex `0` to the vertex `n`. -/
private def cupZeroRight_edgeTo (n : ℕ) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun j => if (j : ℕ) = 0 then ⟨0, by simp⟩ else ⟨n, by simp⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def, SimplexCategory.len_mk] at hij ⊢
        rcases (by omega : (i:ℕ) = 0 ∨ (i:ℕ) = 1) with hi|hi <;>
          rcases (by omega : (j:ℕ) = 0 ∨ (j:ℕ) = 1) with hj|hj <;> simp [hi, hj] <;> omega }

private lemma cupZeroRight_edgeTo_zero (n : ℕ) :
    (ConcreteCategory.hom (cupZeroRight_edgeTo n)) (0 : Fin 2) =
      ⟨0, Nat.zero_lt_succ n⟩ := by
  rw [show (ConcreteCategory.hom (cupZeroRight_edgeTo n)) (0:Fin 2) =
      (if ((0:Fin 2):ℕ) = 0 then ⟨0, Nat.zero_lt_succ n⟩ else ⟨n, Nat.lt_succ_self n⟩) from rfl]
  simp

private lemma cupZeroRight_edgeTo_one (n : ℕ) :
    (ConcreteCategory.hom (cupZeroRight_edgeTo n)) (1 : Fin 2) =
      ⟨n, Nat.lt_succ_self n⟩ := by
  rw [show (ConcreteCategory.hom (cupZeroRight_edgeTo n)) (1:Fin 2) =
      (if ((1:Fin 2):ℕ) = 0 then ⟨0, Nat.zero_lt_succ n⟩ else ⟨n, Nat.lt_succ_self n⟩) from rfl]
  simp

/-- Two morphisms `⦋0⦌ ⟶ ⦋n⦌` that agree on the unique point of `⦋0⦌` are equal. -/
private lemma cupZeroRight_hom_fin1_ext {n : ℕ} (f g : ⦋0⦌ ⟶ ⦋n⦌)
    (h : (ConcreteCategory.hom f) (0 : Fin 1) = (ConcreteCategory.hom g) (0 : Fin 1)) :
    f = g := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  rw [show i = (0:Fin 1) from Fin.eq_zero i]
  exact h

/-- The transport `⦋k + 0⦌ ⟶ ⦋0 + k⦌` along `k + 0 = 0 + k` is the inclusion of the last `k + 1`
vertices. -/
private lemma cupZeroRight_eqToHom_add_comm (k : ℕ) :
    eqToHom (congrArg SimplexCategory.mk (Nat.add_comm k 0)) = backIncl 0 k := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  change ((ConcreteCategory.hom
      (eqToHom (congrArg SimplexCategory.mk (Nat.add_comm k 0)))) i).val
    = ((ConcreteCategory.hom (backIncl 0 k)) i).val
  rw [coe_eqToHom_mk (Nat.add_comm k 0), hom_backIncl_val]
  omega

/-- The first face of the edge `⦋1⦌ ⟶ ⦋0 + k⦌` is the inclusion of the first vertex. -/
private lemma cupZeroRight_delta_one_comp (k : ℕ) (h : 0 ≤ 0 + k) :
    SimplexCategory.δ (1 : Fin 2) ≫ cupZeroRight_edgeTo (0 + k)
      = frontIncl 0 (0 + k) h := by
  apply cupZeroRight_hom_fin1_ext
  rw [CategoryTheory.comp_apply]
  rw [show (ConcreteCategory.hom (SimplexCategory.δ (1:Fin 2))) (0:Fin 1) = (0:Fin 2) from rfl]
  apply Fin.ext
  rw [cupZeroRight_edgeTo_zero, hom_frontIncl_val]
  rfl

/-- The zeroth face of the edge `⦋1⦌ ⟶ ⦋0 + k⦌` is the inclusion of the last vertex (composed with
the index identification `k + 0 = 0 + k`). -/
private lemma cupZeroRight_delta_zero_comp (k : ℕ) :
    SimplexCategory.δ (0 : Fin 2) ≫ cupZeroRight_edgeTo (0 + k)
      = backIncl k 0 ≫ eqToHom (congrArg SimplexCategory.mk (Nat.add_comm k 0)) := by
  apply cupZeroRight_hom_fin1_ext
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  rw [show (ConcreteCategory.hom (SimplexCategory.δ (0:Fin 2))) (0:Fin 1) = (1:Fin 2) from rfl]
  apply Fin.ext
  rw [cupZeroRight_edgeTo_one, coe_eqToHom_mk (Nat.add_comm k 0), hom_backIncl_val]
  simp only [Fin.val_zero]
  omega

/-- **A `0`-cocycle is constant on the two ends of an edge**: for an edge `e : ⦋1⦌ ⟶ ⦋n⦌` and a
simplex `σ : X _⦋n⦌`, the value of a `0`-cocycle `β` at `e`'s zeroth vertex equals its value at
`e`'s first vertex. -/
private lemma cupZeroRight_zero_cocycle_edge (R : Type) [CommRing R] (X : SSet) (n : ℕ)
    (β : Cochain R X 0) (hβ : cochainDiff R X β = 0)
    (e : ⦋1⦌ ⟶ ⦋n⦌) (σ : X _⦋n⦌) :
    genEval R X β (X.map (SimplexCategory.δ (0 : Fin 2) ≫ e).op σ) =
      genEval R X β (X.map (SimplexCategory.δ (1 : Fin 2) ≫ e).op σ) := by
  have h := genEval_cochainDiff (R := R) (X := X) (k := 0) β (X.map e.op σ)
  rw [hβ] at h
  simp only [genEval, LinearMap.zero_apply] at h
  rw [Fin.sum_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  have h' : genEval R X β (X.δ (0:Fin 2) (X.map e.op σ)) =
      genEval R X β (X.δ (1:Fin 2) (X.map e.op σ)) := by
    have h2 : genEval R X β (X.δ (0:Fin 2) (X.map e.op σ))
        - genEval R X β (X.δ (1:Fin 2) (X.map e.op σ)) = 0 := by
      simp only [genEval] at h ⊢
      rw [h]; ring
    exact sub_eq_zero.mp h2
  convert h' using 2
  · rw [SimplicialObject.δ_def, map_op_comp]
  · rw [SimplicialObject.δ_def, map_op_comp]

theorem cupZeroRight (R : Type) [CommRing R] (X : SSet) (k : ℕ)
    (γ : Cochain R X k) (β : Cochain R X 0) (hβ : cochainDiff R X β = 0) :
    (Nat.add_comm k 0) ▸ (cup R X γ β) = cup R X β γ := by
  apply genEval_ext
  intro σ
  show genEval R X ((Nat.add_comm k 0) ▸ (cup R X γ β)) σ =
    genEval R X (cup R X β γ) σ
  rw [genEval_cast']
  rw [cup_apply', cup_apply']
  -- `τ` is `σ` reindexed along `k + 0 = 0 + k`.
  have hA : genEval R X γ (frontFace X k (k + 0) (by omega)
      ((ConcreteCategory.hom
        (X.map (eqToHom (congrArg SimplexCategory.mk (Nat.add_comm k 0))).op)) σ))
      = genEval R X γ (backFace X 0 k σ) := by
    rw [frontFace_self, cupZeroRight_eqToHom_add_comm, backFace]
    rfl
  have hB : genEval R X β (backFace X k 0
      ((ConcreteCategory.hom
        (X.map (eqToHom (congrArg SimplexCategory.mk (Nat.add_comm k 0))).op)) σ))
      = genEval R X β (frontFace X 0 (0 + k) (by omega) σ) := by
    rw [backFace, frontFace]
    rw [map_op_comp]
    rw [← cupZeroRight_delta_zero_comp k]
    rw [cupZeroRight_zero_cocycle_edge R X (0 + k) β hβ (cupZeroRight_edgeTo (0 + k)) σ]
    rw [cupZeroRight_delta_one_comp k (by omega)]
  rw [hA, hB]
  exact mul_comm _ _

end

end Work.Cohomology
