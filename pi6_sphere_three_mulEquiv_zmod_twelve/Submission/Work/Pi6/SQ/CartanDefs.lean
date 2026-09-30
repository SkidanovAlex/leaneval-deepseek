/-
# Interface definitions for the Cartan instance `δH(x) = (x∪x)∪₂(x∪x) + (x∪₁x)∪(x∪₁x)`

This file packages the *atoms* of the computation: for a fixed simplicial set `X`, a `2`-cochain
`x` and a `6`-simplex `τ` of `X`, the value `Fv X x τ a b c` of `x` on the `2`-face of `τ` spanned
by the vertices `a < b < c` (via the canonical inclusion `inc6`).  Everything about the Cartan
instance is a polynomial identity in the fifteen atoms `Fv X x τ 0 a b` (`1 ≤ a < b ≤ 6`), once
the twenty cocycle relations `Fv X x τ a b c = Fv X x τ 0 b c + Fv X x τ 0 a c + Fv X x τ 0 a b`
have been used.
-/
import Mathlib
import Submission.Work.Pi6.SQ.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cup cup1 cup_apply cup1 genEval_cup1 frontIncl backIncl
  Fface Gface shmap frontFace backFace Gfun)

/-! ## The canonical faces of a `6`-simplex -/

/-- The order embedding `⦋2⦌ ⟶ ⦋6⦌` onto the vertices `a < b < c`. -/
def inc6 (a b c : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c ≤ 6) : ⦋2⦌ ⟶ ⦋6⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨if i.val = 0 then a else if i.val = 1 then b else c, by
        simp only [SimplexCategory.len_mk]; split_ifs <;> omega⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def] at hij ⊢; split_ifs <;> omega }

/-- The order embedding `⦋3⦌ ⟶ ⦋6⦌` onto the vertices `a < b < c < d`. -/
def inc7 (a b c d : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d ≤ 6) : ⦋3⦌ ⟶ ⦋6⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c
        else d, by
        simp only [SimplexCategory.len_mk]; split_ifs <;> omega⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def] at hij ⊢; split_ifs <;> omega }

@[simp] lemma inc6_val (a b c : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c ≤ 6) (i : Fin 3) :
    ((ConcreteCategory.hom (inc6 a b c h1 h2 h3)) i).val =
      (if i.val = 0 then a else if i.val = 1 then b else c) := rfl

@[simp] lemma inc7_val (a b c d : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d ≤ 6)
    (i : Fin 4) :
    ((ConcreteCategory.hom (inc7 a b c d h1 h2 h3 h4)) i).val =
      (if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d) := rfl

/-! ## The atoms -/

variable (X : SSet)

/-- The value of the `2`-cochain `x` on the `2`-face of `τ` spanned by the vertices `a,b,c`
(and `0` on a non-increasing triple, which never occurs). -/
def Fv (x : Cochain F2 X 2) (τ : X _⦋6⦌) (a b c : ℕ) : ZMod 2 :=
  if h : a < b ∧ b < c ∧ c ≤ 6 then
    genEval F2 X x (X.map (inc6 a b c h.1 h.2.1 h.2.2).op τ) else 0

/-- The defining equation of `Fv` on a strictly increasing triple. -/
lemma Fv_eq (x : Cochain F2 X 2) (τ : X _⦋6⦌) (a b c : ℕ) (h1 : a < b) (h2 : b < c)
    (h3 : c ≤ 6) :
    genEval F2 X x (X.map (inc6 a b c h1 h2 h3).op τ) = Fv X x τ a b c := by
  rw [Fv, dif_pos ⟨h1, h2, h3⟩]

/-! ## Value lemmas for the maps occurring in the cup-`2` and cup-`1` products -/

@[simp] lemma cup2U_val (n m a b : ℕ) (ha : a + 2 ≤ n) (hb1 : 1 ≤ b) (hb3 : b + 1 ≤ m)
    (i : Fin (n+1)) :
    ((ConcreteCategory.hom (cup2U n m a b ha hb1 hb3)) i).val =
      (if i.val ≤ a then i.val else i.val + (b - 1)) := rfl

@[simp] lemma cup2V_val (n m a b : ℕ) (ha : a + 2 ≤ n) (hb1 : 1 ≤ b) (hb3 : b + 1 ≤ m)
    (i : Fin (m+1)) :
    ((ConcreteCategory.hom (cup2V n m a b ha hb1 hb3)) i).val =
      (if i.val ≤ b then a + i.val else i.val + (n - 2)) := rfl

@[simp] lemma inc3_val (a b c : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c ≤ 5) (i : Fin 3) :
    ((ConcreteCategory.hom (inc3 a b c h1 h2 h3)) i).val =
      (if i.val = 0 then a else if i.val = 1 then b else c) := rfl

@[simp] lemma frontIncl_val' (p n : ℕ) (h : p ≤ n) (i : Fin (p+1)) :
    ((ConcreteCategory.hom (frontIncl p n h)) i).val = i.val := rfl

@[simp] lemma backIncl_val' (p q : ℕ) (i : Fin (q+1)) :
    ((ConcreteCategory.hom (backIncl p q)) i).val = p + i.val := rfl

@[simp] lemma Fface_val' (n m s : ℕ) (h : s + n ≤ n + m - 1) (i : Fin (n+1)) :
    ((ConcreteCategory.hom (Fface n m s h)) i).val = s + i.val := rfl

@[simp] lemma Gface_val' (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) :
    ((ConcreteCategory.hom (Gface n m s h)) j).val =
      (if j.val ≤ s then j.val else j.val + n - 1) := by
  rw [show (ConcreteCategory.hom (Gface n m s h)) j = Gfun n m s h j from rfl]
  simp only [Gfun]
  split_ifs <;> rfl

/-- `shmap` at equal lengths is the identity. -/
lemma shmap_self (p : ℕ) (h : p = p) : shmap p p h = 𝟙 ⦋p⦌ := by
  have : h = rfl := Subsingleton.elim _ _
  subst this
  rw [shmap, eqToHom_refl]

/-- The identity `2 + 2 - 1 = 2 + 2 - 1` is `rfl`. -/
lemma shmap_three (h : 2 + 2 - 1 = 2 + 2 - 1) : shmap (2+2-1) (2+2-1) h = 𝟙 ⦋2+2-1⦌ :=
  shmap_self _ h

/-! ## Small helpers for the assembly -/

/-- Evaluation of a sum of cochains. -/
lemma genEval_add {n : ℕ} (f g : Cochain F2 X n) (σ : X _⦋n⦌) :
    genEval F2 X (f + g) σ = genEval F2 X f σ + genEval F2 X g σ := by
  simp only [genEval, LinearMap.add_apply]

/-- In `𝔽₂` every sign is `1`. -/
lemma neg_one_pow_F2 (k : ℕ) : (-1 : ZMod 2) ^ k = 1 := by simp

/-- The cup product with the Alexander–Whitney faces, evaluated at a generator, in the ring `𝔽₂`. -/
lemma cup_apply_F2 {n m : ℕ} (α : Cochain F2 X n) (β : Cochain F2 X m)
    (σ : X _⦋n + m⦌) :
    genEval F2 X (cup F2 X α β) σ =
      genEval F2 X α (X.map (frontIncl n (n + m) (Nat.le_add_right n m)).op σ) *
        genEval F2 X β (X.map (backIncl n m).op σ) := by
  have h := cup_apply F2 X α β σ
  simpa only [frontFace, backFace] using h

/-- The Alexander–Whitney cup product in degrees `(2,2)`, in `𝔽₂`. -/
lemma cup_apply_2_2 (x : Cochain F2 X 2) (σ : X _⦋4⦌) :
    genEval F2 X (cup F2 X x x) σ =
      genEval F2 X x (X.map (frontIncl 2 4 (by omega)).op σ) *
        genEval F2 X x (X.map (backIncl 2 2).op σ) := by
  have h := cup_apply F2 X x x σ
  simpa only [frontFace, backFace] using h

/-- The Alexander–Whitney cup product in degrees `(3,3)`, in `𝔽₂`. -/
lemma cup_apply_3_3 (α β : Cochain F2 X 3) (σ : X _⦋6⦌) :
    genEval F2 X (cup F2 X α β) σ =
      genEval F2 X α (X.map (frontIncl 3 6 (by omega)).op σ) *
        genEval F2 X β (X.map (backIncl 3 3).op σ) := by
  have h := cup_apply F2 X α β σ
  simpa only [frontFace, backFace] using h

/-- `genEval` of the cup-`1` product `x ∪₁ x` in degree `2` at a `3`-simplex, in `𝔽₂`:
the shuffle `shmap` at equal lengths is the identity. -/
lemma genEval_cup1m_2_2 (x : Cochain F2 X 2) (σ : X _⦋3⦌) :
    genEval F2 X (cup1m X 2 2 x x) σ = genEval F2 X (cup1 F2 X 2 2 x x) σ := by
  have h := genEval_cup1m X 2 2 x x σ
  have h2 : X.map (shmap (2+2-1) (2+2-1) (by omega : 2+2-1 = 2+2-1)).op σ = σ := by
    rw [show shmap (2+2-1) (2+2-1) (by omega : 2+2-1 = 2+2-1) = 𝟙 _ from
      shmap_self (2+2-1) _]
    simp
  simpa only [h2] using h

/-- `genEval_cup2` in the case `n = m = 4` and `σ` a `6`-simplex, with the sums over `Fin 3`
(so that the summands match the identification lemmas of `CartanCompute`). -/
lemma genEval_cup2_4_4 (u v : Cochain F2 X 4) (σ : X _⦋6⦌) :
    genEval F2 X (cup2 X 4 4 u v) σ =
      ∑ a : Fin 3, ∑ b : Fin 3,
        genEval F2 X u (X.map (cup2U 4 4 a.val (b.val + 1) (by omega) (by omega) (by omega)).op σ) *
          genEval F2 X v (X.map (cup2V 4 4 a.val (b.val + 1) (by omega) (by omega) (by omega)).op σ) := by
  simpa using genEval_cup2 X 4 4 u v σ

/-- The cup-`1` product in degree `2` at a `3`-simplex, evaluated. -/
lemma genEval_cup1_2_2 (x : Cochain F2 X 2) (σ : X _⦋3⦌) :
    genEval F2 X (cup1 F2 X 2 2 x x) σ =
      genEval F2 X x (X.map (Fface 2 2 0 (by omega)).op σ) *
        genEval F2 X x (X.map (Gface 2 2 0 (by omega)).op σ) +
      genEval F2 X x (X.map (Fface 2 2 1 (by omega)).op σ) *
        genEval F2 X x (X.map (Gface 2 2 1 (by omega)).op σ) := by
  rw [genEval_cup1]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, mul_one, Fin.val_one, neg_one_pow_F2, one_mul]

/-- Reduction of a natural number modulo `2` in `𝔽₂`. -/
lemma zmod2_natCast_mod (k : ℕ) : ((k : ZMod 2)) = ((k % 2 : ℕ) : ZMod 2) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val (k : ZMod 2)]
  rw [ZMod.val_natCast]

/-- Reduction of a numeral coefficient modulo `2` in `𝔽₂`. -/
lemma zmod2_ofNat_mod (k : ℕ) [k.AtLeastTwo] :
    (OfNat.ofNat k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
  rw [show (OfNat.ofNat k : ZMod 2) = ((k : ℕ) : ZMod 2) from rfl]
  exact zmod2_natCast_mod k

end

end Work.Pi6.SQ
