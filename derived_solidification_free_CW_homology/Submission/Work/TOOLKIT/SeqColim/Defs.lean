/-
AREA TOOLKIT — the telescope of a sequential diagram of cochain complexes.

For a sequential diagram `F : ℕ ⥤ Cpx` (a "tower") with transition maps
`step F n := F.map (homOfLE (Nat.le_succ n)) : F.obj n ⟶ F.obj (n+1)`, let

* `A := ∐ n, F.obj n` be the small coproduct (`ℕ`-indexed);
* `telShift F : A ⟶ A` be the "shift" whose restriction to the `n`-th summand is
  `step F n` followed by the inclusion of the `(n+1)`-st summand;
* `telD F := 𝟙 A - telShift F` (the blueprint's `1 - shift`);
* `toColim F : A ⟶ colim F` the map out of the coproduct whose `n`-th component is the
  colimit cocone map `colimit.ι F n`.

Then `telD F ≫ toColim F = 0`, and the *telescope short complex*

  `telShort F := (A --telD F--> A --toColim F--> colim F)`

is short exact as soon as the transition maps are monomorphisms (this is proved in the
sibling files: `Mono (telD F)` by "coordinate" reasoning, and `toColim F` is the cokernel
of `telD F` by the universal property of the colimit).  The short exactness of `telShort`
is what turns a solid-equivalence of all the `τ.app n` into one of `colim.map τ`.

This file contains only the definitions and the elementary computations about them.
-/
import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.TOOLKIT.SeqColim

/-! ## Coordinates of a coproduct -/

/-- The `j`-th coordinate of a coproduct: the map `∐ X ⟶ X j` whose `k`-th component is the
identity if `k = j` and zero otherwise. -/
def coord {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type} (X : J → C)
    [HasCoproduct X] (j : J) : (∐ X) ⟶ X j := by
  classical
  exact Sigma.desc (fun k => if h : k = j then eqToHom (congrArg X h) else 0)

@[simp]
lemma coord_self {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type} (X : J → C)
    [HasCoproduct X] (j : J) : Sigma.ι X j ≫ coord X j = 𝟙 (X j) := by
  classical
  rw [coord, Sigma.ι_comp_desc]
  simp

lemma coord_eq_zero_of_ne {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type} (X : J → C)
    [HasCoproduct X] {k j : J} (h : k ≠ j) : Sigma.ι X k ≫ coord X j = 0 := by
  classical
  rw [coord, Sigma.ι_comp_desc]
  simp [h]

/-! ## The shift map and `1 - shift` for a tower of complexes -/

/-- The "shift" map on the coproduct of a tower, whose `n`-th component is the `n`-th
transition map followed by the inclusion of the `(n+1)`-st summand. -/
def towerShift (X : ℕ → Cpx) [HasCoproduct X] (i : ∀ n : ℕ, X n ⟶ X (n+1)) :
    (∐ X) ⟶ (∐ X) :=
  Sigma.desc (fun n => i n ≫ Sigma.ι X (n+1))

lemma Sigma_ι_towerShift (X : ℕ → Cpx) [HasCoproduct X] (i : ∀ n : ℕ, X n ⟶ X (n+1)) (n : ℕ) :
    Sigma.ι X n ≫ towerShift X i = i n ≫ Sigma.ι X (n+1) :=
  Sigma.ι_comp_desc _ n

/-- The blueprint's `1 - shift`. -/
def towerD (X : ℕ → Cpx) [HasCoproduct X] (i : ∀ n : ℕ, X n ⟶ X (n+1)) :
    (∐ X) ⟶ (∐ X) :=
  𝟙 (∐ X) - towerShift X i

lemma Sigma_ι_towerD (X : ℕ → Cpx) [HasCoproduct X] (i : ∀ n : ℕ, X n ⟶ X (n+1)) (n : ℕ) :
    Sigma.ι X n ≫ towerD X i = Sigma.ι X n - i n ≫ Sigma.ι X (n+1) := by
  rw [towerD, Preadditive.comp_sub, Sigma_ι_towerShift, Category.comp_id]

/-- The basic computation on coordinates: the `(n+1)`-st coordinate of the shift is the `n`-th
coordinate followed by the `n`-th transition map. -/
lemma towerShift_coord_succ (X : ℕ → Cpx) [HasCoproduct X] (i : ∀ n : ℕ, X n ⟶ X (n+1)) (n : ℕ) :
    towerShift X i ≫ coord X (n+1) = coord X n ≫ i n := by
  apply Sigma.hom_ext
  intro k
  rw [← Category.assoc, Sigma_ι_towerShift, Category.assoc]
  by_cases h : k = n
  · subst h
    rw [coord_self, Category.comp_id, ← Category.assoc, coord_self, Category.id_comp]
  · rw [coord_eq_zero_of_ne X (j := n+1) (k := k+1) (by omega), comp_zero,
      ← Category.assoc, coord_eq_zero_of_ne X (j := n) (k := k) h, zero_comp]

/-- The `0`-th coordinate of the shift vanishes. -/
lemma towerShift_coord_zero (X : ℕ → Cpx) [HasCoproduct X] (i : ∀ n : ℕ, X n ⟶ X (n+1)) :
    towerShift X i ≫ coord X 0 = 0 := by
  apply Sigma.hom_ext
  intro k
  rw [← Category.assoc, Sigma_ι_towerShift, Category.assoc,
    coord_eq_zero_of_ne X (k := k+1) (j := 0) (by omega)]
  simp

/-! ## The telescope of a sequential diagram -/

/-- The `n`-th transition map of a sequential diagram. -/
def step (F : ℕ ⥤ Cpx) (n : ℕ) : F.obj n ⟶ F.obj (n+1) :=
  F.map (homOfLE (Nat.le_succ n))

/-- `1 - shift` for the tower `F`. -/
def telD (F : ℕ ⥤ Cpx) : (∐ fun n => F.obj n) ⟶ (∐ fun n => F.obj n) :=
  towerD (fun n => F.obj n) (step F)

/-- The map from the coproduct of a tower to its colimit, induced by the colimit cocone. -/
def toColim (F : ℕ ⥤ Cpx) : (∐ fun n => F.obj n) ⟶ colim.obj F :=
  Sigma.desc (fun n => colimit.ι F n)

lemma Sigma_ι_toColim (F : ℕ ⥤ Cpx) (n : ℕ) :
    Sigma.ι (fun n => F.obj n) n ≫ toColim F = colimit.ι F n :=
  Sigma.ι_comp_desc _ n

/-- The composition `(1 - shift) ≫ toColim` vanishes. -/
lemma telD_toColim (F : ℕ ⥤ Cpx) : telD F ≫ toColim F = 0 := by
  have hshift : towerShift (fun n => F.obj n) (step F) ≫ toColim F = toColim F := by
    apply Sigma.hom_ext
    intro k
    rw [← Category.assoc, Sigma_ι_towerShift, Category.assoc, Sigma_ι_toColim, toColim,
      Sigma.ι_comp_desc, step]
    exact colimit.w F (homOfLE (Nat.le_succ k))
  rw [telD, towerD, Preadditive.sub_comp, Category.id_comp, hshift, sub_self]

/-- The **telescope short complex** of a sequential diagram of cochain complexes. -/
def telShort (F : ℕ ⥤ Cpx) : ShortComplex Cpx :=
  ShortComplex.mk (telD F) (toColim F) (telD_toColim F)

lemma telShort_f (F : ℕ ⥤ Cpx) : (telShort F).f = telD F := rfl

lemma telShort_g (F : ℕ ⥤ Cpx) : (telShort F).g = toColim F := rfl

/-- `toColim F` is an epimorphism: the colimit cocone maps are jointly epimorphic. -/
lemma epi_toColim (F : ℕ ⥤ Cpx) : Epi (toColim F) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z w hw
  refine Limits.colimit.hom_ext (fun n => ?_)
  have h1 : Sigma.ι (fun n => F.obj n) n ≫ (toColim F ≫ w) = 0 := by
    rw [hw, comp_zero]
  rw [← Category.assoc, Sigma_ι_toColim] at h1
  rw [h1, comp_zero]

end Work.TOOLKIT.SeqColim
