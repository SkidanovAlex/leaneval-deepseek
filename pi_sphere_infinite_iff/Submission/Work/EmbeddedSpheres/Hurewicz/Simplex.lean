import Submission.Work.EmbeddedSpheres.Basic
import Mathlib
import Submission.Work.Cohomology.SingBridge

/-!
# A clean model for singular simplices: concatenation and reversal

The singular simplices of a space `X` are the continuous maps `stdSimplex ℝ (Fin (n+1)) → X`
(`TopCat.toSSetObjEquivT`).  This file develops, in that model, the concatenation of two composable
1-simplices (`concat`), the reversal of a 1-simplex (`rev`), the two elementary 2-simplices
(`compSimplex`, `revSimplex`) witnessing the chain identities, and the basic chain-level API.
The actual face computations and the chain identities live in `Hurewicz/Face.lean`.
-/

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.EmbeddedSpheres.Hurewicz

open Classical

noncomputable section

/-! ## 1. The standard simplices -/

/-- The point of `Δ¹` with coordinates `(a,b)`. -/
def ss2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : stdSimplex ℝ (Fin 2) :=
  ⟨fun i => if i = 0 then a else b, by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h : i = 0 <;> simp [h, ha, hb]
    · rw [Fin.sum_univ_two]; simp [hab]⟩

@[simp] theorem ss2_zero {a b : ℝ} (ha hb hab) : (ss2 a b ha hb hab : Fin 2 → ℝ) 0 = a := by
  show (if (0 : Fin 2) = 0 then a else b) = a
  simp

@[simp] theorem ss2_one {a b : ℝ} (ha hb hab) : (ss2 a b ha hb hab : Fin 2 → ℝ) 1 = b := by
  show (if (1 : Fin 2) = 0 then a else b) = b
  simp

theorem ss2_congr {a b a' b' : ℝ} {ha : 0 ≤ a} {hb : 0 ≤ b} {hab : a + b = 1}
    {ha' : 0 ≤ a'} {hb' : 0 ≤ b'} {hab' : a' + b' = 1} (e : a = a') (e' : b = b') :
    ss2 a b ha hb hab = ss2 a' b' ha' hb' hab' := by subst e e'; rfl

theorem ss2_self (y : stdSimplex ℝ (Fin 2)) :
    ss2 ((y : Fin 2 → ℝ) 0) ((y : Fin 2 → ℝ) 1) (stdSimplex.zero_le y 0) (stdSimplex.zero_le y 1)
      (by rw [← Fin.sum_univ_two]; exact stdSimplex.sum_eq_one y) = y := by
  refine Subtype.ext ?_
  funext i
  fin_cases i <;> rfl

theorem ss2_vertex_one :
    ss2 0 1 (by norm_num) (by norm_num) (by norm_num) = stdSimplex.vertex (1 : Fin 2) := by
  refine Subtype.ext ?_
  funext i
  fin_cases i <;> simp [ss2, stdSimplex.vertex]

theorem ss2_vertex_zero :
    ss2 1 0 (by norm_num) (by norm_num) (by norm_num) = stdSimplex.vertex (0 : Fin 2) := by
  refine Subtype.ext ?_
  funext i
  fin_cases i <;> simp [ss2, stdSimplex.vertex]

theorem ss2_sum (y : stdSimplex ℝ (Fin 2)) :
    (y : Fin 2 → ℝ) 0 + (y : Fin 2 → ℝ) 1 = 1 := by
  rw [← Fin.sum_univ_two]; exact stdSimplex.sum_eq_one y

theorem continuous_ss2 {β : Type*} [TopologicalSpace β] (A B : β → ℝ) (hA : Continuous A)
    (hB : Continuous B) (hp : ∀ x, 0 ≤ A x) (hq : ∀ x, 0 ≤ B x) (hr : ∀ x, A x + B x = 1) :
    Continuous (fun x => ss2 (A x) (B x) (hp x) (hq x) (hr x)) := by
  have hf : Continuous (fun x : β => (fun i : Fin 2 => if i = 0 then A x else B x)) := by
    apply continuous_pi; intro i; by_cases h : i = 0
    · simp only [h, if_true]; exact hA
    · simp only [h, if_false]; exact hB
  exact Continuous.subtype_mk hf (fun x =>
    ⟨fun i => by by_cases h : i = 0 <;> simp [h, hp x, hq x],
      by rw [Fin.sum_univ_two]; simp [hr x]⟩)

/-! ## 2. The clean model of simplices, and faces -/

/-- Continuous maps from the standard `n`-simplex. -/
abbrev Simp (X : TopCat.{0}) (n : ℕ) : Type := C(stdSimplex ℝ (Fin (n+1)), X)

/-- The `i`-th face of an `(n+1)`-simplex. -/
def face {X : TopCat.{0}} {n : ℕ} (i : Fin (n+2)) (σ : Simp X (n+1)) : Simp X n :=
  σ.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩

@[simp] theorem face_apply {X : TopCat.{0}} {n : ℕ} (i : Fin (n+2)) (σ : Simp X (n+1))
    (y : stdSimplex ℝ (Fin (n+1))) :
    face i σ y = σ (stdSimplex.map i.succAbove y) := rfl

/-! ## 3. The 2-simplex for composition -/

/-- The reparametrisation used for the "then" branch of the composition 2-simplex. -/
def rhoA (x : stdSimplex ℝ (Fin 3)) : stdSimplex ℝ (Fin 2) :=
  ss2 (max 0 ((x : Fin 3 → ℝ) 0 - (x : Fin 3 → ℝ) 2))
      (1 - max 0 ((x : Fin 3 → ℝ) 0 - (x : Fin 3 → ℝ) 2))
      (le_max_left _ _)
      (by
        rw [sub_nonneg]
        apply max_le (by norm_num)
        have h1 : (x : Fin 3 → ℝ) 0 ≤ 1 := stdSimplex.le_one x 0
        have h2 : 0 ≤ (x : Fin 3 → ℝ) 2 := stdSimplex.zero_le x 2
        linarith)
      (by ring)

/-- The reparametrisation used for the "else" branch of the composition 2-simplex. -/
def rhoB (x : stdSimplex ℝ (Fin 3)) : stdSimplex ℝ (Fin 2) :=
  ss2 (1 - max 0 ((x : Fin 3 → ℝ) 2 - (x : Fin 3 → ℝ) 0))
      (max 0 ((x : Fin 3 → ℝ) 2 - (x : Fin 3 → ℝ) 0))
      (by
        rw [sub_nonneg]
        apply max_le (by norm_num)
        have h1 : (x : Fin 3 → ℝ) 2 ≤ 1 := stdSimplex.le_one x 2
        have h0 : 0 ≤ (x : Fin 3 → ℝ) 0 := stdSimplex.zero_le x 0
        linarith)
      (le_max_left _ _)
      (by ring)

theorem continuous_rhoA : Continuous rhoA :=
  continuous_ss2 (fun x : stdSimplex ℝ (Fin 3) => max 0 ((x : Fin 3 → ℝ) 0 - (x : Fin 3 → ℝ) 2))
    (fun x => 1 - max 0 ((x : Fin 3 → ℝ) 0 - (x : Fin 3 → ℝ) 2))
    (continuous_const.max
      (((continuous_apply 0).comp continuous_subtype_val).sub
        ((continuous_apply 2).comp continuous_subtype_val)))
    (continuous_const.sub (continuous_const.max
      (((continuous_apply 0).comp continuous_subtype_val).sub
        ((continuous_apply 2).comp continuous_subtype_val))))
    (fun x => le_max_left _ _)
    (fun x => by
      rw [sub_nonneg]
      apply max_le (by norm_num)
      have h1 : (x : Fin 3 → ℝ) 0 ≤ 1 := stdSimplex.le_one x 0
      have h2 : 0 ≤ (x : Fin 3 → ℝ) 2 := stdSimplex.zero_le x 2
      linarith)
    (fun x => by ring)

theorem continuous_rhoB : Continuous rhoB :=
  continuous_ss2 (fun x : stdSimplex ℝ (Fin 3) => 1 - max 0 ((x : Fin 3 → ℝ) 2 - (x : Fin 3 → ℝ) 0))
    (fun x => max 0 ((x : Fin 3 → ℝ) 2 - (x : Fin 3 → ℝ) 0))
    (continuous_const.sub (continuous_const.max
      (((continuous_apply 2).comp continuous_subtype_val).sub
        ((continuous_apply 0).comp continuous_subtype_val))))
    (continuous_const.max
      (((continuous_apply 2).comp continuous_subtype_val).sub
        ((continuous_apply 0).comp continuous_subtype_val)))
    (fun x => by
      rw [sub_nonneg]
      apply max_le (by norm_num)
      have h1 : (x : Fin 3 → ℝ) 2 ≤ 1 := stdSimplex.le_one x 2
      have h0 : 0 ≤ (x : Fin 3 → ℝ) 0 := stdSimplex.zero_le x 0
      linarith)
    (fun x => le_max_left _ _)
    (fun x => by ring)

theorem rhoA_eq_vertex_one (x : stdSimplex ℝ (Fin 3))
    (hx : (x : Fin 3 → ℝ) 2 = (x : Fin 3 → ℝ) 0) :
    rhoA x = stdSimplex.vertex (1 : Fin 2) := by
  rw [← ss2_vertex_one]
  dsimp only [rhoA]
  refine ss2_congr ?_ ?_
  · rw [hx, sub_self]; exact max_eq_left le_rfl
  · rw [hx, sub_self]; norm_num

theorem rhoB_eq_vertex_zero (x : stdSimplex ℝ (Fin 3))
    (hx : (x : Fin 3 → ℝ) 2 = (x : Fin 3 → ℝ) 0) :
    rhoB x = stdSimplex.vertex (0 : Fin 2) := by
  rw [← ss2_vertex_zero]
  dsimp only [rhoB]
  refine ss2_congr ?_ ?_
  · rw [hx, sub_self]; norm_num
  · rw [hx, sub_self]; exact max_eq_left le_rfl

/-- **The composition 2-simplex**: its faces are `q`, the concatenation of `p` and `q`, and `p`. -/
def compSimplex {X : TopCat.{0}} (p q : Simp X 1)
    (h : p (stdSimplex.vertex (1 : Fin 2)) = q (stdSimplex.vertex (0 : Fin 2))) : Simp X 2 :=
  ⟨fun x => if (x : Fin 3 → ℝ) 2 ≤ (x : Fin 3 → ℝ) 0 then p (rhoA x) else q (rhoB x), by
    refine Continuous.if_le (p.continuous.comp continuous_rhoA) (q.continuous.comp continuous_rhoB)
      ((continuous_apply 2).comp continuous_subtype_val)
      ((continuous_apply 0).comp continuous_subtype_val) ?_
    intro x hx
    rw [rhoA_eq_vertex_one x hx, rhoB_eq_vertex_zero x hx]
    exact h⟩

/-! ## 4. The concatenation of 1-simplices -/

/-- The reparametrisation for the "then" branch of the concatenation. -/
def rho1 (y : stdSimplex ℝ (Fin 2)) : stdSimplex ℝ (Fin 2) :=
  ss2 (1 - min 1 (2 * (y : Fin 2 → ℝ) 1)) (min 1 (2 * (y : Fin 2 → ℝ) 1))
      (by
        have h : (0:ℝ) ≤ 2 * (y : Fin 2 → ℝ) 1 := by
          have := stdSimplex.zero_le y 1; linarith
        nlinarith [min_le_left (1:ℝ) (2 * (y : Fin 2 → ℝ) 1)])
      (le_min (by norm_num) (by have := stdSimplex.zero_le y 1; linarith))
      (by ring)

/-- The reparametrisation for the "else" branch of the concatenation. -/
def rho2 (y : stdSimplex ℝ (Fin 2)) : stdSimplex ℝ (Fin 2) :=
  ss2 (min 1 (2 * (y : Fin 2 → ℝ) 0)) (1 - min 1 (2 * (y : Fin 2 → ℝ) 0))
      (le_min (by norm_num) (by have := stdSimplex.zero_le y 0; linarith))
      (by
        have h : (0:ℝ) ≤ 2 * (y : Fin 2 → ℝ) 0 := by
          have := stdSimplex.zero_le y 0; linarith
        nlinarith [min_le_left (1:ℝ) (2 * (y : Fin 2 → ℝ) 0)])
      (by ring)

theorem continuous_rho1 : Continuous rho1 :=
  continuous_ss2 (fun y : stdSimplex ℝ (Fin 2) => 1 - min 1 (2 * (y : Fin 2 → ℝ) 1))
    (fun y => min 1 (2 * (y : Fin 2 → ℝ) 1))
    (continuous_const.sub (continuous_const.min (continuous_const.mul
      ((continuous_apply 1).comp continuous_subtype_val))))
    (continuous_const.min (continuous_const.mul
      ((continuous_apply 1).comp continuous_subtype_val)))
    (fun y => by
      have h : (0:ℝ) ≤ 2 * (y : Fin 2 → ℝ) 1 := by
        have := stdSimplex.zero_le y 1; linarith
      linarith [min_le_left (1:ℝ) (2 * (y : Fin 2 → ℝ) 1)])
    (fun y => le_min (by norm_num) (by have := stdSimplex.zero_le y 1; linarith))
    (fun y => by ring)

theorem continuous_rho2 : Continuous rho2 :=
  continuous_ss2 (fun y : stdSimplex ℝ (Fin 2) => min 1 (2 * (y : Fin 2 → ℝ) 0))
    (fun y => 1 - min 1 (2 * (y : Fin 2 → ℝ) 0))
    (continuous_const.min (continuous_const.mul
      ((continuous_apply 0).comp continuous_subtype_val)))
    (continuous_const.sub (continuous_const.min (continuous_const.mul
      ((continuous_apply 0).comp continuous_subtype_val))))
    (fun y => le_min (by norm_num) (by have := stdSimplex.zero_le y 0; linarith))
    (fun y => by
      have h : (0:ℝ) ≤ 2 * (y : Fin 2 → ℝ) 0 := by
        have := stdSimplex.zero_le y 0; linarith
      linarith [min_le_left (1:ℝ) (2 * (y : Fin 2 → ℝ) 0)])
    (fun y => by ring)

/-- Under `y 1 ≤ y 0` the "then" reparametrisation has the expected coordinates. -/
theorem rho1_eq {y : stdSimplex ℝ (Fin 2)}
    (hy : (y : Fin 2 → ℝ) 1 ≤ (y : Fin 2 → ℝ) 0) :
    rho1 y = ss2 ((y : Fin 2 → ℝ) 0 - (y : Fin 2 → ℝ) 1) (2 * (y : Fin 2 → ℝ) 1)
      (by have := stdSimplex.zero_le y 0; have' := stdSimplex.zero_le y 1; linarith)
      (by have := stdSimplex.zero_le y 1; linarith)
      (by have := ss2_sum y; linarith) := by
  have H : min 1 (2 * (y : Fin 2 → ℝ) 1) = 2 * (y : Fin 2 → ℝ) 1 := by
    apply min_eq_right
    have hs := ss2_sum y
    linarith
  dsimp only [rho1]
  refine ss2_congr ?_ ?_
  · rw [H]; have hs := ss2_sum y; linarith
  · exact H

/-- Under `y 0 ≤ y 1` the "else" reparametrisation has the expected coordinates. -/
theorem rho2_eq {y : stdSimplex ℝ (Fin 2)}
    (hy : (y : Fin 2 → ℝ) 0 ≤ (y : Fin 2 → ℝ) 1) :
    rho2 y = ss2 (2 * (y : Fin 2 → ℝ) 0) ((y : Fin 2 → ℝ) 1 - (y : Fin 2 → ℝ) 0)
      (by have := stdSimplex.zero_le y 0; linarith)
      (by have := stdSimplex.zero_le y 1; linarith)
      (by have := ss2_sum y; linarith) := by
  have H : min 1 (2 * (y : Fin 2 → ℝ) 0) = 2 * (y : Fin 2 → ℝ) 0 := by
    apply min_eq_right
    have hs := ss2_sum y
    linarith
  dsimp only [rho2]
  refine ss2_congr ?_ ?_
  · exact H
  · rw [H]; have hs := ss2_sum y; linarith

theorem rho1_vertex_one {y : stdSimplex ℝ (Fin 2)}
    (hy : (y : Fin 2 → ℝ) 1 = (y : Fin 2 → ℝ) 0) :
    rho1 y = stdSimplex.vertex (1 : Fin 2) := by
  rw [← ss2_vertex_one]
  dsimp only [rho1]
  have H : min 1 (2 * (y : Fin 2 → ℝ) 1) = 1 := by
    apply min_eq_left
    have hs := ss2_sum y
    rw [hy] at hs
    linarith
  refine ss2_congr ?_ ?_
  · rw [H]; norm_num
  · exact H

theorem rho2_vertex_zero {y : stdSimplex ℝ (Fin 2)}
    (hy : (y : Fin 2 → ℝ) 1 = (y : Fin 2 → ℝ) 0) :
    rho2 y = stdSimplex.vertex (0 : Fin 2) := by
  rw [← ss2_vertex_zero]
  dsimp only [rho2]
  have H : min 1 (2 * (y : Fin 2 → ℝ) 0) = 1 := by
    apply min_eq_left
    have hs := ss2_sum y
    rw [← hy] at hs
    linarith
  refine ss2_congr ?_ ?_
  · exact H
  · rw [H]; norm_num

/-- **Concatenation of two composable 1-simplices.** -/
def concat {X : TopCat.{0}} (p q : Simp X 1)
    (h : p (stdSimplex.vertex (1 : Fin 2)) = q (stdSimplex.vertex (0 : Fin 2))) : Simp X 1 :=
  ⟨fun y => if (y : Fin 2 → ℝ) 1 ≤ (y : Fin 2 → ℝ) 0 then p (rho1 y) else q (rho2 y), by
    refine Continuous.if_le (p.continuous.comp continuous_rho1) (q.continuous.comp continuous_rho2)
      ((continuous_apply 1).comp continuous_subtype_val)
      ((continuous_apply 0).comp continuous_subtype_val) ?_
    intro y hy
    rw [rho1_vertex_one hy, rho2_vertex_zero hy]
    exact h⟩

/-! ## 5. Reversal of a 1-simplex -/

/-- The reversal of a 1-simplex. -/
def rev {X : TopCat.{0}} (p : Simp X 1) : Simp X 1 :=
  p.comp ⟨fun y => ss2 ((y : Fin 2 → ℝ) 1) ((y : Fin 2 → ℝ) 0)
      (stdSimplex.zero_le y 1) (stdSimplex.zero_le y 0)
      (by have := ss2_sum y; linarith), by
    exact continuous_ss2 (fun y : stdSimplex ℝ (Fin 2) => (y : Fin 2 → ℝ) 1)
      (fun y => (y : Fin 2 → ℝ) 0)
      ((continuous_apply 1).comp continuous_subtype_val)
      ((continuous_apply 0).comp continuous_subtype_val)
      (fun y => stdSimplex.zero_le y 1) (fun y => stdSimplex.zero_le y 0)
      (fun y => by have := ss2_sum y; linarith)⟩

/-- The reversal 2-simplex; its faces are `rev p`, the constant simplex at the start of `p`, and
`p`. -/
def revSimplex {X : TopCat.{0}} (p : Simp X 1) : Simp X 2 :=
  ⟨fun x => p (ss2 (1 - (x : Fin 3 → ℝ) 1) ((x : Fin 3 → ℝ) 1)
      (by have h1 := stdSimplex.le_one x 1; linarith)
      (stdSimplex.zero_le x 1)
      (by ring)), by
    exact p.continuous.comp (continuous_ss2 (fun x : stdSimplex ℝ (Fin 3) => 1 - (x : Fin 3 → ℝ) 1)
      (fun x => (x : Fin 3 → ℝ) 1)
      (continuous_const.sub ((continuous_apply 1).comp continuous_subtype_val))
      ((continuous_apply 1).comp continuous_subtype_val)
      (fun x => by have h1 := stdSimplex.le_one x 1; linarith)
      (fun x => stdSimplex.zero_le x 1)
      (fun x => by ring))⟩

/-- The constant 1-simplex at a point. -/
def const1 {X : TopCat.{0}} (x : X) : Simp X 1 := ⟨fun _ => x, continuous_const⟩

/-- The constant 2-simplex at a point. -/
def const2 {X : TopCat.{0}} (x : X) : Simp X 2 := ⟨fun _ => x, continuous_const⟩

@[simp] theorem compSimplex_apply {X : TopCat.{0}} (p q : Simp X 1)
    (h : p (stdSimplex.vertex (1 : Fin 2)) = q (stdSimplex.vertex (0 : Fin 2)))
    (x : stdSimplex ℝ (Fin 3)) :
    compSimplex p q h x = (if (x : Fin 3 → ℝ) 2 ≤ (x : Fin 3 → ℝ) 0
      then p (rhoA x) else q (rhoB x)) := rfl

@[simp] theorem concat_apply {X : TopCat.{0}} (p q : Simp X 1)
    (h : p (stdSimplex.vertex (1 : Fin 2)) = q (stdSimplex.vertex (0 : Fin 2)))
    (y : stdSimplex ℝ (Fin 2)) :
    concat p q h y = (if (y : Fin 2 → ℝ) 1 ≤ (y : Fin 2 → ℝ) 0
      then p (rho1 y) else q (rho2 y)) := rfl

@[simp] theorem rev_apply {X : TopCat.{0}} (p : Simp X 1) (y : stdSimplex ℝ (Fin 2)) :
    rev p y = p (ss2 ((y : Fin 2 → ℝ) 1) ((y : Fin 2 → ℝ) 0) (stdSimplex.zero_le y 1)
      (stdSimplex.zero_le y 0) (by have := ss2_sum y; linarith)) := rfl

@[simp] theorem revSimplex_apply {X : TopCat.{0}} (p : Simp X 1) (x : stdSimplex ℝ (Fin 3)) :
    revSimplex p x = p (ss2 (1 - (x : Fin 3 → ℝ) 1) ((x : Fin 3 → ℝ) 1)
      (by have h1 := stdSimplex.le_one x 1; linarith) (stdSimplex.zero_le x 1) (by ring)) := rfl

@[simp] theorem const1_apply {X : TopCat.{0}} (x : X) (y : stdSimplex ℝ (Fin 2)) :
    const1 x y = x := rfl

@[simp] theorem const2_apply {X : TopCat.{0}} (x : X) (z : stdSimplex ℝ (Fin 3)) :
    const2 x z = x := rfl

/-! ## 6. The chain complex and the chain carried by a simplex -/

/-- The `n`-chain carried by a single `n`-simplex. -/
def chainOf {X : TopCat.{0}} {n : ℕ} (σ : Simp X n) :
    (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).X n :=
  Work.Cohomology.genElt ℤ (TopCat.toSSet.obj X)
    ((TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk n))).symm σ)

end

end Work.EmbeddedSpheres.Hurewicz
