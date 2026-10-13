/-
Area DSCOH (curric-46) — the "degenerate simplices" homotopy, packaged as a Mathlib `Homotopy`.

The composite `ordProj ≫ ordIncl` (identity on the strictly increasing tuples, zero on the
nondecreasing tuples with an adjacent repetition) is homotopic to the identity of the semi-ordered
Čech complex, with components

`h(s)_x = 0` if `x` is strictly increasing, and
`h(s)_x = (-1)^a · s_{x with the a-th entry duplicated at position a}`

if the first repeat of `x` is at position `a` (this is `Work.DSCOH.Norm.semiHom`).  The degreewise
identity is `Work.DSCOH.Norm.SemiRaw.semiHom_comp_semiD`.  In degree `0` the homotopy component
vanishes (`semiHom 0 = 0`, since every `1`-tuple is strictly increasing) while `ordProj ≫ ordIncl`
is the identity (`ordProj_ordIncl_zero`); this is exactly the extra "augmentation" step that
Mathlib's `Homotopy` requires in degree `0`.  The package is then assembled by `homotopyOfRaw`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.HomoPair
import Submission.Work.DSCOH.Norm.Complexes

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [Fintype ι] [LinearOrder ι]
  [CategoryTheory.Limits.HasProducts (ModuleCat A)]

namespace SemiRaw

/-- A `1`-tuple is strictly increasing. -/
lemma strictMono_one (z : Fin 1 → ι) : StrictMono z := by
  intro a b hab
  exact absurd hab (by simp only [Fin.lt_def]; omega)

/-- **The raw "degenerate simplices" homotopy identity** for the homotopy `semiHom`. -/
theorem semiHom_comp_semiD (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    semiHom P U n ≫ semiD P U n + semiD P U (n + 1) ≫ semiHom P U (n + 1) =
      𝟙 (semiTerm P U (n + 1)) - (ordProj P U (n + 1) ≫ ordIncl P U (n + 1)) := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro y
  erw [lhs_eq_sum P U n y, rhs_comp P U n y]
  by_cases hy : StrictMono y.val
  · rw [dif_pos hy]
    have hD : (∑ b : Fin (n + 2), Dterm P U n y b) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      rw [Dterm, semiHomComp_of_strictMono P U (strictMono_del y.val b hy)]
      simp
    have hH : (∑ c : Fin (n + 3), Hterm P U n y c) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [Hterm]
      exact dif_pos hy
    rw [hD, hH, zero_add]
  · rw [dif_neg hy]
    exact pair_sum P U n y y.property hy

/-- The homotopy component in degree `0` vanishes. -/
lemma semiHom_zero (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) :
    semiHom P U 0 = 0 := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro z
  rw [semiHom_comp P U 0 z, semiHomComp_of_strictMono P U (strictMono_one z.val)]
  simp

/-- In degree `0` the composite `ordProj ≫ ordIncl` is the identity. -/
lemma ordProj_ordIncl_zero (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) :
    ordProj P U 0 ≫ ordIncl P U 0 = 𝟙 (semiTerm P U 0) := by
  apply CategoryTheory.Limits.Pi.hom_ext (f := fun z : SemiIdx ι 0 => tupleMod P U z.val)
  intro y
  have hz : StrictMono y.val := strictMono_one y.val
  erw [Category.assoc, ordIncl_comp_pi P U 0 y.val y.property, dif_pos hz]
  erw [ordProj_comp_pi P U 0 ⟨y.val, hz⟩, Category.id_comp]

/-- **The degenerate-simplices homotopy**, as a Mathlib `Homotopy` of cochain complexes:
`ordProj ≫ ordIncl` is homotopic to the identity of the semi-ordered Čech complex. -/
theorem semiHom_homotopy (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) :
    Nonempty (Homotopy (ordProjC P U ≫ ordInclC P U) (𝟙 (semiT P U))) := by
  refine ⟨(homotopyOfRaw (C := semiT P U) (D := semiT P U) (f := 𝟙 (semiT P U))
      (g := ordProjC P U ≫ ordInclC P U) (fun n => semiHom P U n) ?_ ?_).symm⟩
  · rw [HomologicalComplex.id_f, HomologicalComplex.comp_f, ordProjC_f, ordInclC_f]
    have hd : (semiT P U).d 0 1 = semiD P U 0 := semiT_d P U 0
    rw [hd, semiHom_zero P U, comp_zero, zero_add]
    exact (ordProj_ordIncl_zero P U).symm
  · intro n
    rw [HomologicalComplex.id_f, HomologicalComplex.comp_f, ordProjC_f, ordInclC_f]
    have hd1 : (semiT P U).d (n + 1) (n + 2) = semiD P U (n + 1) := semiT_d P U (n + 1)
    have hd0 : (semiT P U).d n (n + 1) = semiD P U n := semiT_d P U n
    rw [hd1, hd0]
    have h := semiHom_comp_semiD P U n
    rw [eq_sub_iff_add_eq] at h
    rw [← h]
    abel

end SemiRaw

end Work.DSCOH.Norm
