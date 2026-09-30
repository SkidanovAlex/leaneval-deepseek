import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cup1defs
import Submission.Work.Cohomology.cup1Cast
import Submission.Work.Cohomology.cupNaturalH
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Steenrod-lite: the mod-2 cup-2 product

This is the one new cochain-level operation the π₆ computation needs (`sqFacts`, crux A): for
cochains `u ∈ C^n`, `v ∈ C^m` on a simplicial set `X` we define Steenrod's cup-2 product
`u ∪₂ v ∈ C^{n+m-2}(X;𝔽₂)` by the interval formula.  For `σ : Δ^{n+m-2} → X` and cut points
`a, a+b` (`0 ≤ a ≤ n-2`, `1 ≤ b ≤ m-1`) the two vertex sets are

* `U = [0,a] ∪ [a+b, n-1+b]` (the even intervals, evaluated on `u`),
* `V = [a, a+b] ∪ [n-1+b, n+m-2]` (the odd intervals, evaluated on `v`),

and `(u ∪₂ v)(σ) = Σ u(σ|U)·v(σ|V)`.  The convention is *exactly* the one used to verify the
Cartan identity `δH(x) = (x∪x)∪₂(x∪x) + (x∪₁x)∪(x∪₁x)` in `REFS/pi6_cartan_verify.py` (the
script's `cupi(·,4,·,4,2,·)`), so that the lead's explicit 5-cochain `H` can be used as is.

The cup-1 product is the library's `Work.Cohomology.cup1`, which mod 2 agrees with the same
convention with the two arguments interchanged; since every formula we use is symmetric in the two
cup-1 terms, this is harmless.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ

noncomputable section

/-- The field `𝔽₂`. -/
abbrev F2 : Type := ZMod 2

open Work.Cohomology (Cochain genEval cochainDiff)

variable (X : SSet)

/-- The vertex map `⦋n⦌ → ⦋n+m-2⦌` with image `[0,a] ∪ [a+b, n-1+b]` (the "left" vertex set of
the `(a,b)`-term of the cup-2 product): `i ↦ i` for `i ≤ a` and `i ↦ i + (b-1)` for `i > a`. -/
def cup2U (n m a b : ℕ) (ha : a + 2 ≤ n) (hb1 : 1 ≤ b) (hb3 : b + 1 ≤ m) :
    ⦋n⦌ ⟶ ⦋n + m - 2⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨if i.val ≤ a then i.val else i.val + (b - 1), by
        split_ifs with h
        · have := i.isLt; simp only [SimplexCategory.len_mk] at this ⊢; omega
        · have := i.isLt; simp only [SimplexCategory.len_mk] at this ⊢; omega⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def] at hij ⊢
        by_cases h1 : i.val ≤ a <;> by_cases h2 : j.val ≤ a
        · rw [if_pos h1, if_pos h2]; omega
        · rw [if_pos h1, if_neg h2]; omega
        · omega
        · rw [if_neg h1, if_neg h2]; omega }

/-- The vertex map `⦋m⦌ → ⦋n+m-2⦌` with image `[a,a+b] ∪ [n-1+b, n+m-2]` (the "right" vertex set
of the `(a,b)`-term of the cup-2 product): `i ↦ a + i` for `i ≤ b` and `i ↦ i + (n-2)` for
`i > b`. -/
def cup2V (n m a b : ℕ) (ha : a + 2 ≤ n) (hb1 : 1 ≤ b) (hb3 : b + 1 ≤ m) :
    ⦋m⦌ ⟶ ⦋n + m - 2⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨if i.val ≤ b then a + i.val else i.val + (n - 2), by
        split_ifs with h
        · have := i.isLt; simp only [SimplexCategory.len_mk] at this ⊢; omega
        · have := i.isLt; simp only [SimplexCategory.len_mk] at this ⊢; omega⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def] at hij ⊢
        by_cases h1 : i.val ≤ b <;> by_cases h2 : j.val ≤ b
        · rw [if_pos h1, if_pos h2]; omega
        · rw [if_pos h1, if_neg h2]; omega
        · omega
        · rw [if_neg h1, if_neg h2]; omega }

/-- **The mod-2 cup-2 product** `u ∪₂ v ∈ C^{n+m-2}(X;𝔽₂)`, Steenrod's interval formula. -/
noncomputable def cup2Hom (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) :
    (X.chainComplex (ModuleCat.of F2 F2)).X (n + m - 2) ⟶ ModuleCat.of F2 F2 :=
  (X.isColimitChainComplexXCofan (ModuleCat.of F2 F2) (n + m - 2)).desc
    (Cofan.mk (ModuleCat.of F2 F2)
      (fun σ : X _⦋n + m - 2⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
          (∑ a : Fin (n - 1), ∑ b : Fin (m - 1),
            genEval F2 X u (X.map (cup2U n m a.val (b.val + 1) (by omega) (by omega)
              (by omega)).op σ) *
            genEval F2 X v (X.map (cup2V n m a.val (b.val + 1) (by omega) (by omega)
              (by omega)).op σ)))))

/-- **The mod-2 cup-2 product** `u ∪₂ v` of an `n`- and an `m`-cochain. -/
noncomputable def cup2 (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) :
    Cochain F2 X (n + m - 2) := (cup2Hom X n m u v).hom

@[simp]
theorem ιChainComplex_cup2Hom (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (σ : X _⦋n + m - 2⦌) :
    X.ιChainComplex (R := ModuleCat.of F2 F2) σ ≫ cup2Hom X n m u v =
      ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
        (∑ a : Fin (n - 1), ∑ b : Fin (m - 1),
          genEval F2 X u (X.map (cup2U n m a.val (b.val + 1) (by omega) (by omega)
            (by omega)).op σ) *
          genEval F2 X v (X.map (cup2V n m a.val (b.val + 1) (by omega) (by omega)
            (by omega)).op σ))) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of the cup-2 product on a simplex: the interval formula. -/
theorem genEval_cup2 (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (σ : X _⦋n + m - 2⦌) :
    genEval F2 X (cup2 X n m u v) σ =
      ∑ a : Fin (n - 1), ∑ b : Fin (m - 1),
        genEval F2 X u (X.map (cup2U n m a.val (b.val + 1) (by omega) (by omega)
          (by omega)).op σ) *
        genEval F2 X v (X.map (cup2V n m a.val (b.val + 1) (by omega) (by omega)
          (by omega)).op σ) := by
  have h2 := congrArg (fun (g : ModuleCat.of F2 F2 ⟶ ModuleCat.of F2 F2) => g.hom 1)
    (ιChainComplex_cup2Hom X n m u v σ)
  simpa only [cup2, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2



/-! ## The Cartan cochain `H(x)` (the lead's 31 quartic terms, `REFS/pi6_cartan_H.json`) -/

/-- The monotone injection `⦋2⦌ ⟶ ⦋5⦌` with `i ↦ t i`, for a strictly increasing triple with
values `≤ 5`. -/
def inc3 (a b c : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c ≤ 5) : ⦋2⦌ ⟶ ⦋5⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨if i.val = 0 then a else if i.val = 1 then b else c, by
        simp only [SimplexCategory.len_mk]
        split_ifs <;> omega⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def] at hij ⊢
        split_ifs <;> omega }

/-- The face `⦋2⦌ ⟶ ⦋5⦌` onto the vertices `{0,1,2}` of the 5-simplex. -/
def F012 : ⦋2⦌ ⟶ ⦋5⦌ := inc3 0 1 2 (by norm_num) (by norm_num) (by norm_num)

/-- The face `⦋2⦌ ⟶ ⦋5⦌` onto the vertices `{0,1,3}` of the 5-simplex. -/
def F013 : ⦋2⦌ ⟶ ⦋5⦌ := inc3 0 1 3 (by norm_num) (by norm_num) (by norm_num)

/-- The face `⦋2⦌ ⟶ ⦋5⦌` onto the vertices `{0,2,3}` of the 5-simplex. -/
def F023 : ⦋2⦌ ⟶ ⦋5⦌ := inc3 0 2 3 (by norm_num) (by norm_num) (by norm_num)

/-- The face `⦋2⦌ ⟶ ⦋5⦌` onto the vertices `{0,2,4}` of the 5-simplex. -/
def F024 : ⦋2⦌ ⟶ ⦋5⦌ := inc3 0 2 4 (by norm_num) (by norm_num) (by norm_num)

/-- The face `⦋2⦌ ⟶ ⦋5⦌` onto the vertices `{0,2,5}` of the 5-simplex. -/
def F025 : ⦋2⦌ ⟶ ⦋5⦌ := inc3 0 2 5 (by norm_num) (by norm_num) (by norm_num)

/-- The face `⦋2⦌ ⟶ ⦋5⦌` onto the vertices `{0,3,4}` of the 5-simplex. -/
def F034 : ⦋2⦌ ⟶ ⦋5⦌ := inc3 0 3 4 (by norm_num) (by norm_num) (by norm_num)

/-- The face `⦋2⦌ ⟶ ⦋5⦌` onto the vertices `{0,3,5}` of the 5-simplex. -/
def F035 : ⦋2⦌ ⟶ ⦋5⦌ := inc3 0 3 5 (by norm_num) (by norm_num) (by norm_num)

/-- The face `⦋2⦌ ⟶ ⦋5⦌` onto the vertices `{0,4,5}` of the 5-simplex. -/
def F045 : ⦋2⦌ ⟶ ⦋5⦌ := inc3 0 4 5 (by norm_num) (by norm_num) (by norm_num)

/-- **The Cartan 5-cochain `H(x)`** attached to a 2-cochain `x` (the lead's 31 quartic terms in the
values of `x` on the 2-faces `σ|0ab` of a 5-simplex). -/
noncomputable def cartanCochainHom (x : Cochain F2 X 2) :
    (X.chainComplex (ModuleCat.of F2 F2)).X 5 ⟶ ModuleCat.of F2 F2 :=
  (X.isColimitChainComplexXCofan (ModuleCat.of F2 F2) 5).desc
    (Cofan.mk (ModuleCat.of F2 F2)
      (fun σ : X _⦋5⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
          ((genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ))))))

/-- **The Cartan 5-cochain `H(x)`** attached to a 2-cochain `x`. -/
noncomputable def cartanCochain (x : Cochain F2 X 2) : Cochain F2 X 5 :=
  (cartanCochainHom X x).hom

@[simp]
theorem ιChainComplex_cartanCochainHom (x : Cochain F2 X 2) (σ : X _⦋5⦌) :
    X.ιChainComplex (R := ModuleCat.of F2 F2) σ ≫ cartanCochainHom X x =
      ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
        ((genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ)))) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `H(x)` on a 5-simplex: the 31-term polynomial. -/
theorem genEval_cartanCochain (x : Cochain F2 X 2) (σ : X _⦋5⦌) :
    genEval F2 X (cartanCochain X x) σ = ((genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F024.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F025.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F034.op σ) * genEval F2 X x (X.map F045.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F012.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F035.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F045.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F034.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F035.op σ)) +
      (genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F013.op σ) * genEval F2 X x (X.map F023.op σ) * genEval F2 X x (X.map F045.op σ))) := by
  have h2 := congrArg (fun (g : ModuleCat.of F2 F2 ⟶ ModuleCat.of F2 F2) => g.hom 1)
    (ιChainComplex_cartanCochainHom X x σ)
  simpa only [cartanCochain, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-! ## The cup-1 product in the (Python/Steenrod) convention -/

/-- The mod-2 cup-1 product `u ∪₁ v ∈ C^{n+m-1}` in Steenrod's convention used by
`REFS/pi6_cupi_check.py`: it is the library's `cup1` with the arguments interchanged. -/
noncomputable def cup1m (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) :
    Cochain F2 X (n + m - 1) :=
  (congrArg (fun k => k - 1) (Nat.add_comm m n)) ▸ (Work.Cohomology.cup1 F2 X m n v u)

/-- The value of the cup-1 product on a simplex, in terms of the library's `cup1` with the
arguments interchanged (and the induced map `shmap` on simplices). -/
theorem genEval_cup1m (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (σ : X _⦋n + m - 1⦌) :
    genEval F2 X (cup1m X n m u v) σ =
      genEval F2 X (Work.Cohomology.cup1 F2 X m n v u)
        (X.map (Work.Cohomology.shmap (m + n - 1) (n + m - 1)
          (congrArg (fun k => k - 1) (Nat.add_comm m n))).op σ) := by
  rw [cup1m, Work.Cohomology.genEval_cast]
end

end Work.Pi6.SQ
