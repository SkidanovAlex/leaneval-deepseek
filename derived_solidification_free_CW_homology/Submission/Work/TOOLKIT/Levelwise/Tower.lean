/-
AREA TOOLKIT/Levelwise — the tower of brutal truncations of a complex, its cocone into the
complex, and the short exact sequences `0 → T_mK → T_{m+1}K → K.X(-(m+1))[-m-1] → 0` together
with the morphism of short exact sequences induced by a map of complexes.
-/
import Submission.Work.TOOLKIT.Levelwise.Maps

open CategoryTheory Limits
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Work.TOOLKIT.Levelwise

attribute [local simp] CategoryTheory.eqToHom_trans

/-- The tower `T_m K = trunc (-(m:ℤ)) K` of brutal truncations of `K`, with the inclusions
`T_m K ⟶ T_{m+1} K` as transition maps.  Marked `@[reducible]` so that its objects and
structure maps unfold for unification at any transparency. -/
@[reducible] def truncTower (K : Cpx) : Functor ℕ Cpx where
  obj m := trunc (-(m : ℤ)) K
  map {m n} h := truncIncl (a := -(n : ℤ)) (b := -(m : ℤ)) (by
    have hmn : m ≤ n := leOfHom h
    omega) K
  map_id m := by
    show truncIncl (a := -(m : ℤ)) (b := -(m : ℤ)) _ K = 𝟙 (trunc (-(m : ℤ)) K)
    rw [truncIncl_self]
  map_comp {m n k} h h' := by
    show truncIncl (a := -(k : ℤ)) (b := -(m : ℤ)) _ K =
      truncIncl (a := -(n : ℤ)) (b := -(m : ℤ)) _ K ≫
        truncIncl (a := -(k : ℤ)) (b := -(n : ℤ)) _ K
    rw [truncIncl_comp]

@[simp]
lemma truncTower_obj (K : Cpx) (m : ℕ) : (truncTower K).obj m = trunc (-(m : ℤ)) K := rfl

/-- The inclusion of each stage of the tower into `K`. -/
def truncTowerToK (K : Cpx) (m : ℕ) : (truncTower K).obj m ⟶ K := truncIntoK (-(m : ℤ)) K

/-- The inclusions of the stages of the tower into `K`, as a natural transformation. -/
def truncTowerNat (K : Cpx) : truncTower K ⟶ (Functor.const ℕ).obj K where
  app m := truncTowerToK K m
  naturality {m n} h := by
    have h' : -(n : ℤ) ≤ -(m : ℤ) := by
      have hmn : m ≤ n := leOfHom h
      omega
    show truncIncl (a := -(n : ℤ)) (b := -(m : ℤ)) h' K ≫ truncIntoK (-(n : ℤ)) K =
      truncIntoK (-(m : ℤ)) K ≫ 𝟙 K
    rw [truncIncl_comp_truncIntoK, Category.comp_id]

/-- The tower of truncations of `K`, with the inclusions into `K` as a cocone. -/
def truncTowerCocone (K : Cpx) : Cocone (truncTower K) where
  pt := K
  ι := truncTowerNat K

/-- The short complex `0 → T_mK → T_{m+1}K → (single in degree -(m+1) of K.X (-(m+1))) → 0`. -/
def truncSES (m : ℕ) (K : Cpx) : ShortComplex Cpx :=
  ShortComplex.mk (truncIncl (show -(m + 1 : ℤ) ≤ -(m : ℤ) by omega) K)
    (truncProj K (-(m + 1 : ℤ)))
    (truncIncl_comp_truncProj (show -(m + 1 : ℤ) < -(m : ℤ) by omega) K)

@[simp]
lemma truncSES_X₁ (m : ℕ) (K : Cpx) : (truncSES m K).X₁ = trunc (-(m : ℤ)) K := rfl

@[simp]
lemma truncSES_X₂ (m : ℕ) (K : Cpx) : (truncSES m K).X₂ = trunc (-(m + 1 : ℤ)) K := rfl

@[simp]
lemma truncSES_X₃ (m : ℕ) (K : Cpx) :
    (truncSES m K).X₃ = (sng (-(m + 1 : ℤ))).obj (K.X (-(m + 1 : ℤ))) := rfl

@[simp]
lemma truncSES_f (m : ℕ) (K : Cpx) :
    (truncSES m K).f =
      truncIncl (show -(m + 1 : ℤ) ≤ -(m : ℤ) by omega) K := rfl

@[simp]
lemma truncSES_g (m : ℕ) (K : Cpx) :
    (truncSES m K).g = truncProj K (-(m + 1 : ℤ)) := rfl

/-- The morphism of short complexes induced by `φ : K ⟶ L`. -/
def truncSESMap {K L : Cpx} (φ : K ⟶ L) (m : ℕ) : truncSES m K ⟶ truncSES m L :=
  ShortComplex.homMk (truncMap φ (-(m : ℤ))) (truncMap φ (-(m + 1 : ℤ)))
    ((sng (-(m + 1 : ℤ))).map (φ.f (-(m + 1 : ℤ))))
    (truncIncl_naturality (show -(m + 1 : ℤ) ≤ -(m : ℤ) by omega) φ)
    (truncProj_naturality φ (-(m + 1 : ℤ)))

@[simp]
lemma truncSESMap_τ₁ {K L : Cpx} (φ : K ⟶ L) (m : ℕ) :
    (truncSESMap φ m).τ₁ = truncMap φ (-(m : ℤ)) := rfl

@[simp]
lemma truncSESMap_τ₂ {K L : Cpx} (φ : K ⟶ L) (m : ℕ) :
    (truncSESMap φ m).τ₂ = truncMap φ (-(m + 1 : ℤ)) := rfl

@[simp]
lemma truncSESMap_τ₃ {K L : Cpx} (φ : K ⟶ L) (m : ℕ) :
    (truncSESMap φ m).τ₃ = (sng (-(m + 1 : ℤ))).map (φ.f (-(m + 1 : ℤ))) := rfl

end Work.TOOLKIT.Levelwise
