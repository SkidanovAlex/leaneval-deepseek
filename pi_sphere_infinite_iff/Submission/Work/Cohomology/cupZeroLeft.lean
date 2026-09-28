import Mathlib
import Submission.Work.Cohomology.cup1defs

/-!
# The cup product with a `0`-cocycle

The Alexander–Whitney cup product `⌣` on the singular cochains of a simplicial set is
graded-commutative: `α ⌣ β = (-1)^{nm} β ⌣ α` modulo coboundaries.  In degree `n = 0` the sign is
`1` and, what is more, the identity already holds at the *cochain* level provided `α` is a
`0`-**cocycle**: this file proves

`α ⌣ β = β ⌣ α`  for `α : Cochain R X 0` with `cochainDiff α = 0` and `β : Cochain R X m`,

the two sides living in degrees `0 + m` and `m + 0` (compared through `Nat.add_comm 0 m`).

The mathematical content is that a `0`-cocycle is constant on the vertices of a connected
simplex: `α(σ)` is the same on the first and the last vertex of an `m`-simplex `σ`, since
`0 = (δα)(τ) = α(τ_1) - α(τ_0)` for the "spine" edge `τ` of `σ` (the edge from its first to its
last vertex).  The computation on generators of the Alexander–Whitney product is
`(α ⌣ β)(σ) = α(σ_front) β(σ_back)`: for `n = 0` the front face of a `(0+m)`-simplex is its first
vertex and the back face of an `m`-simplex is the whole simplex, so
`(α ⌣ β)(σ) = α(σ_0) β(σ)` and `(β ⌣ α)(σ) = β(σ) α(σ_m)`, which agree by the constancy above.

Remarks on grading.  The coproduct `cup R X α β` of a degree `0` and a degree `m` cochain lives in
degree `0 + m`; the identity is therefore naturally stated after transporting along
`Nat.zero_add m : 0 + m = m` (`cupZeroLeft_aux`), and the announced form along `Nat.add_comm 0 m`
is deduced from it by replacing the transport proof (proof irrelevance) and splitting the composite
transport (`trans_cast`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-! ## Elementary vertex computations

Throughout, `⦋0⦌` has a single vertex `0`, so a morphism `⦋0⦌ ⟶ ⦋n⦌` is determined by the value of
its underlying monotone map at `0`; this is the source of the following computations.
-/

/-- The unique element of `Fin (⦋0⦌.len + 1)` is `0`. -/
lemma val_zero_of_fin_one {i : Fin (⦋0⦌.len + 1)} : (i : ℕ) = 0 := by
  have h := i.isLt
  simp only [SimplexCategory.len_mk] at h
  omega

/-- Looking at the first vertex of a simplex and then identifying `⦋0+n⦌` with `⦋n⦌` is the same as
looking at the first vertex directly. -/
lemma frontIncl_zero_comp (n : ℕ) (h : 0 ≤ 0 + n) :
    frontIncl 0 (0 + n) h ≫ eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n))
      = frontIncl 0 n (Nat.zero_le n) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  rw [CategoryTheory.comp_apply, hom_frontIncl_val]
  have hval := coe_eqToHom_mk (Nat.zero_add n)
    ((ConcreteCategory.hom (frontIncl 0 (0 + n) h)) i)
  rw [hval, hom_frontIncl_val]

/-- The first vertex of a simplex which has been transported from degree `n` to degree `0+n` is the
first vertex of the original simplex. -/
lemma frontFace_zero_cast (n : ℕ) (σ : X _⦋n⦌) (h : 0 ≤ 0 + n) :
    frontFace X 0 (0 + n) h (X.map (eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n))).op σ)
      = frontFace X 0 n (Nat.zero_le n) σ := by
  simp only [frontFace]
  rw [map_op_comp, frontIncl_zero_comp]

/-! ## Morphism identities in `SimplexCategory` for the spine edge -/

/-- The first face of the spine edge is the inclusion of the last vertex. -/
lemma delta_zero_diag (n : ℕ) : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.diag n
    = backIncl n 0 := by
  apply ConcreteCategory.hom_ext
  intro i
  have h0 : (i : ℕ) = 0 := val_zero_of_fin_one
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ]
  rw [Fin.succAbove_zero_apply]
  rw [show i.succ = (1 : Fin 2) from by apply Fin.ext; simp]
  show n = n + ↑i
  rw [h0]
  omega

/-- The second face of the spine edge is the inclusion of the first vertex. -/
lemma delta_one_diag (n : ℕ) : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.diag n
    = frontIncl 0 n (Nat.zero_le n) := by
  apply ConcreteCategory.hom_ext
  intro i
  have h0 : (i : ℕ) = 0 := val_zero_of_fin_one
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, hom_frontIncl_val, SimplexCategory.coe_δ]
  rw [show Fin.succAbove (1 : Fin 2) i = (0 : Fin 2) from by
    rw [show i = (0 : Fin 1) from Fin.ext h0,
      show (1 : Fin 2) = (0 : Fin 1).succ from rfl, Fin.succAbove_succ_self]
    decide]
  rw [h0]
  rfl

/-! ## The spine edge of a simplex

The edge of `σ` joining its first vertex to its last vertex is the image of `σ` under the
"diagonal" morphism `SimplexCategory.diag n : ⦋1⦌ ⟶ ⦋n⦌`, whose faces are the two vertices. -/

/-- The spine edge of a simplex: the edge from its first to its last vertex. -/
def spineEdge (n : ℕ) (σ : X _⦋n⦌) : X _⦋1⦌ := X.map (SimplexCategory.diag n).op σ

/-- The first face of the spine edge is the last vertex of the simplex. -/
lemma delta_zero_spineEdge (n : ℕ) (σ : X _⦋n⦌) :
    X.δ (0 : Fin 2) (spineEdge X n σ) = backFace X n 0 σ := by
  have h : X.δ (0 : Fin 2) (spineEdge X n σ)
      = X.map (SimplexCategory.δ (0 : Fin 2)).op (X.map (SimplexCategory.diag n).op σ) := rfl
  rw [h, map_op_comp, delta_zero_diag]
  simp only [backFace]
  rfl

/-- The second face of the spine edge is the first vertex of the simplex. -/
lemma delta_one_spineEdge (n : ℕ) (σ : X _⦋n⦌) :
    X.δ (1 : Fin 2) (spineEdge X n σ) = frontFace X 0 n (Nat.zero_le n) σ := by
  have h : X.δ (1 : Fin 2) (spineEdge X n σ)
      = X.map (SimplexCategory.δ (1 : Fin 2)).op (X.map (SimplexCategory.diag n).op σ) := rfl
  rw [h, map_op_comp, delta_one_diag]
  simp only [frontFace]

/-! ## Constancy of a `0`-cocycle on the vertices of a simplex -/

/-- A `0`-cocycle takes the same value on the first and on the last vertex of every simplex: its
coboundary evaluated on the spine edge `τ` is `α(τ_1) - α(τ_0) = 0`. -/
lemma genEval_frontFace_eq_backFace (n : ℕ) (α : Cochain R X 0)
    (hα : cochainDiff R X α = 0) (σ : X _⦋n⦌) :
    genEval R X α (frontFace X 0 n (Nat.zero_le n) σ) = genEval R X α (backFace X n 0 σ) := by
  have hedge : genEval R X (cochainDiff R X α) (spineEdge X n σ) = 0 := by
    rw [hα]
    rfl
  rw [genEval_cochainDiff] at hedge
  rw [Fin.sum_univ_two] at hedge
  rw [delta_zero_spineEdge X n σ, delta_one_spineEdge X n σ] at hedge
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_mul] at hedge
  linear_combination -hedge

/-! ## The cochain-level statement, in degree `n` -/

/-- **The cup product with a `0`-cocycle is commutative**, stated after transporting the cup
product of a degree `0` and a degree `n` cochain from degree `0+n` to degree `n`. -/
theorem cupZeroLeft_aux (n : ℕ) (α : Cochain R X 0) (β : Cochain R X n)
    (hα : cochainDiff R X α = 0) :
    ((Nat.zero_add n) ▸ (cup R X α β) : Cochain R X n) = cup R X β α := by
  apply genEval_ext
  intro σ
  have hL : genEval R X ((Nat.zero_add n) ▸ cup R X α β) σ
      = genEval R X α (frontFace X 0 n (Nat.zero_le n) σ) * genEval R X β σ := by
    rw [genEval_cast' R X (Nat.zero_add n), cup_apply', frontFace_zero_cast, backFace_zero_cast]
  have hR : genEval R X (cup R X β α) σ
      = genEval R X β σ * genEval R X α (backFace X n 0 σ) := by
    rw [cup_apply', frontFace_self]
  rw [hL, hR, genEval_frontFace_eq_backFace R X n α hα σ, mul_comm]

/-- Transporting a cochain along a composite of degree equalities. -/
lemma trans_cast {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (x : Cochain R X a) :
    (h₁.trans h₂) ▸ x = h₂ ▸ (h₁ ▸ x) := by cases h₁; cases h₂; rfl

end

theorem cupZeroLeft (R : Type) [CommRing R] (X : SSet) (m : ℕ)
    (α : Cochain R X 0) (β : Cochain R X m) (hα : cochainDiff R X α = 0) :
    (Nat.add_comm 0 m) ▸ (cup R X α β) = cup R X β α := by
  have hproof : (Nat.add_comm 0 m) = (Nat.zero_add m).trans (Nat.add_zero m).symm :=
    Subsingleton.elim _ _
  calc (Nat.add_comm 0 m) ▸ (cup R X α β)
      = ((Nat.zero_add m).trans (Nat.add_zero m).symm) ▸ (cup R X α β) :=
        congrArg (fun pr => pr ▸ (cup R X α β)) hproof
    _ = (Nat.add_zero m).symm ▸ ((Nat.zero_add m) ▸ (cup R X α β)) :=
        trans_cast R X (Nat.zero_add m) ((Nat.add_zero m).symm) (cup R X α β)
    _ = cup R X β α := cupZeroLeft_aux R X m α β hα

end Work.Cohomology
