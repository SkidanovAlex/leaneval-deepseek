import Mathlib
import Submission.Work.DSMX0U.ModelF

/-!
# DSMX0U — the chain map `towerModel hstep M s₀ ⟶ C` with prescribed components

The model complex `P = towerModel hstep M s₀` (`Submission/Work/DSMX0U/ModelF.lean`) is the tower
of cells extended along the embedding `embeddingUpIntLE M`, i.e. the level `k` of the tower sits in
cohomological degree `levelDeg M k - 1 = M - k` and `P` vanishes above `M`.  ModelF also defines
the components `towerModelMapF hstep M s₀ i : P.X i ⟶ C.X i` of the map we want, by transporting
the map `(tower k).φ` of the cell of level `k` along the canonical isomorphism
`towerModelXIso hstep M s₀ k` and the `XIsoOfEq`-transports of the two complexes.

This file proves that the components `towerModelMapF` are a chain map — so they assemble into a
morphism `P ⟶ C` — and that, at the degrees of the levels, this morphism has exactly the prescribed
components:

  `φ.f (levelDeg M k - 1) = (towerModelXIso hstep M s₀ k).hom ≫ (tower k).φ`.

## The mathematics

The chain-map condition in degree `i` (with `i + 1 = j`) is the square

```
P.X i   --P.d i j-->   P.X j
  |                      |
  φ_i                    φ_j = 0  (if j > M)
  v                      v
C.X i   --C.d i j-->   C.X j
```

* if `i` is the degree `levelDeg M k - 1` of the level `k ≻ 0` of the tower, then `j` is the degree
  of the level `k - 1` and the square is `cell_d_comm` (`s.d ≫ s.φprev = s.φ ≫ C.d`) at the cell of
  level `k`, read through the isomorphisms `towerModelXIso` and the formula `towerModel_d` for the
  differential of the extended complex;
* if `k = 0` then `i = M` and `j = M + 1 > M`, so the component in degree `j` vanishes and the
  square reduces to `(tower 0).φ ≫ C.d M (M+1) = 0`, which is precisely the hypothesis
  `TowerBaseCycle` — the base cell of the tower lands in the cycles of `C`;
* if `i > M` then both components vanish (the model is concentrated in degrees `≤ M`).

The proof of the *components* is a small well-definedness argument: the level sitting in a degree is
unique (`levelDeg M k - 1 = levelDeg M m - 1` forces `k = m`), so the `Exists.choose` hidden in the
definition `towerModelMapF` may be replaced by any explicit witness, and the `XIsoOfEq`-transports
along a self-equality are identities.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

set_option maxHeartbeats 800000

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-! ## The degree bookkeeping of the tower -/

/-- The levels of the tower are determined by the degrees they occupy: `levelDeg M ·` is injective
(because `levelDeg M k = M + 1 - k`). -/
theorem levelDeg_injective (M : ℤ) : Function.Injective (levelDeg M) := by
  intro m k h
  rw [levelDeg_eq, levelDeg_eq] at h
  have h2 : (m : ℤ) = (k : ℤ) := by omega
  exact_mod_cast h2

/-- An `XIsoOfEq`-transport along a self-equality of degrees is an identity. -/
theorem cochainXIsoOfEq_self {A : Type a} [CommRing A] (K : CochainComplex (ModuleCat.{a} A) ℤ)
    {p : ℤ} (h : p = p) : K.XIsoOfEq h = Iso.refl (K.X p) := by
  have hh : h = rfl := Subsingleton.elim h rfl
  rw [hh]
  exact K.XIsoOfEq_rfl p

/-! ## The value of the components at the levels -/

/-- The components `towerModelMapF` do not depend on the witness of the degree: for two levels `m`
and `k` sitting in the same degree the transported components agree.  This is the well-definedness
of the definition `towerModelMapF` (which uses `Exists.choose`). -/
theorem towerModelMapF_choose_congr (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s)
    (M : ℤ) (s₀ : Cell A C c₀ (M + 1)) {m k : ℕ}
    (hm : levelDeg M m - 1 = levelDeg M k - 1) :
    (HomologicalComplex.XIsoOfEq (towerModel hstep M s₀) hm.symm).hom ≫
      (towerModelXIso hstep M s₀ m).hom ≫ Cell.φ A (tower hstep M s₀ m) ≫
      (C.XIsoOfEq hm).hom
    = (towerModelXIso hstep M s₀ k).hom ≫ Cell.φ A (tower hstep M s₀ k) := by
  have hmk : m = k := levelDeg_injective M (by omega)
  subst hmk
  rw [cochainXIsoOfEq_self, cochainXIsoOfEq_self]
  simp

/-- **The component of the model map in the degree of a level** is the map of that cell into `C`,
transported along the canonical isomorphism of the level. -/
@[simp]
theorem towerModelMapF_level (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s)
    (M : ℤ) (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    towerModelMapF hstep M s₀ (levelDeg M k - 1) =
      (towerModelXIso hstep M s₀ k).hom ≫ Cell.φ A (tower hstep M s₀ k) := by
  rw [towerModelMapF_of_choose hstep M s₀ (i := levelDeg M k - 1) ⟨k, rfl⟩]
  exact towerModelMapF_choose_congr hstep M s₀
    (⟨k, rfl⟩ : ∃ m, levelDeg M m - 1 = levelDeg M k - 1).choose_spec

/-! ## The chain-map condition -/

/-- The chain-map condition of the model map, in the degrees of two consecutive levels: this is
`cell_d_comm` at the cell of level `k` (and the hypothesis `TowerBaseCycle` when `k = 0`, where the
next degree is `M + 1`, above the model). -/
theorem towerModelMapF_comm_level (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s)
    (M : ℤ) (s₀ : Cell A C c₀ (M + 1)) (hd : TowerBaseCycle hstep M s₀) (k : ℕ) :
    towerModelMapF hstep M s₀ (levelDeg M k - 1) ≫ C.d (levelDeg M k - 1) (levelDeg M k) =
      (towerModel hstep M s₀).d (levelDeg M k - 1) (levelDeg M k) ≫
        towerModelMapF hstep M s₀ (levelDeg M k) := by
  cases k with
  | zero =>
    -- the degree above the level `0` is `M + 1`, above the model: the component there is zero, and
    -- the square is the cycle condition of the base cell
    have hd' : (tower hstep M s₀ 0).φ A ≫ C.d (levelDeg M 0 - 1) (levelDeg M 0) = 0 := hd
    rw [towerModelMapF_level hstep M s₀ 0,
      towerModelMapF_eq_zero_of_gt hstep M s₀ (i := levelDeg M 0) (by rw [levelDeg_zero]; omega)]
    simp only [Category.assoc]
    rw [hd']
    rw [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.comp_zero]
  | succ k' =>
    -- both degrees are the degrees of the levels `k' + 1` and `k'`
    rw [towerModelMapF_level hstep M s₀ (k' + 1),
      towerModelMapF_level hstep M s₀ k', towerModel_d hstep M s₀ k']
    simp only [Category.assoc]
    rw [← cell_d_comm (s := tower hstep M s₀ (k' + 1))]
    simp

/-- **The components `towerModelMapF` form a chain map** `towerModel hstep M s₀ ⟶ C`. -/
theorem towerModelMapF_comm (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s)
    (M : ℤ) (s₀ : Cell A C c₀ (M + 1)) (hd : TowerBaseCycle hstep M s₀) :
    ∀ i j, (ComplexShape.up ℤ).Rel i j →
      towerModelMapF hstep M s₀ i ≫ C.d i j =
        (towerModel hstep M s₀).d i j ≫ towerModelMapF hstep M s₀ j := by
  intro i j hij
  rw [ComplexShape.up_Rel] at hij
  by_cases hi : ∃ k : ℕ, levelDeg M k - 1 = i
  · -- `i` is the degree of a level `k`, and then `j = i + 1` is the degree of the level `k`
    obtain ⟨k, hk⟩ := hi
    have hj : j = levelDeg M k := by rw [← hij, ← hk]; ring
    rw [hj, ← hk]
    exact towerModelMapF_comm_level hstep M s₀ hd k
  · -- `i > M`: the model vanishes in both degrees
    have hMi : M < i := gt_of_not_exists_levelOf M i hi
    have hMj : M < j := by omega
    rw [towerModelMapF_eq_zero_of_gt hstep M s₀ hMi,
      towerModelMapF_eq_zero_of_gt hstep M s₀ hMj]
    rw [CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

/-- **There is a morphism from the model to `C` with the prescribed components.**  It is the chain
map whose component in degree `i` is `towerModelMapF hstep M s₀ i`; restricted to the degree
`levelDeg M k - 1 = M - k` of the level `k` of the tower it is `(tower k).φ`, transported along the
canonical isomorphism `towerModelXIso hstep M s₀ k`. -/
theorem exists_towerModelMap {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Work.DSMX0U.Cell A C c₀ q), Work.DSMX0U.StepData A s)
    (M : ℤ) (s₀ : Work.DSMX0U.Cell A C c₀ (M + 1))
    (hd : Work.DSMX0U.TowerBaseCycle hstep M s₀) :
    ∃ φ : Work.DSMX0U.towerModel hstep M s₀ ⟶ C, ∀ k : ℕ,
      φ.f (Work.DSMX0U.levelDeg M k - 1) = CategoryTheory.CategoryStruct.comp
        (Work.DSMX0U.towerModelXIso hstep M s₀ k).hom (Work.DSMX0U.Cell.φ A (Work.DSMX0U.tower hstep M s₀ k)) := by
  exact ⟨{ f := towerModelMapF hstep M s₀,
           comm' := towerModelMapF_comm hstep M s₀ hd },
    fun k => towerModelMapF_level hstep M s₀ k⟩

end Work.DSMX0U
