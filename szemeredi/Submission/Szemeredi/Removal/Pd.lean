import Mathlib
import Submission.Szemeredi.Removal.Increment
import Submission.Commons.Combinatorics.Finset.card_image_restrict_ratio

/-!
# Products over a sub-collection of coordinates

`Pd V e` is the product `∏_{i ∈ e} V i`, i.e. the space of "points" of the
hypergraph system restricted to the coordinates of the finset `e`.  `restrict`
maps a full point to its restriction, and `shadow e A` is the set of restrictions
of the points of `A`.

For a `coord e`-measurable set `A` (a subset of the full product determined by the
coordinates in `e`), membership of a restriction is equivalent to membership of any
extension, and the density of `A` equals the density of its shadow.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- The product of the vertex classes over the coordinates in `e`. -/
abbrev Pd (e : Finset ι) : Type _ := (i : {i : ι // i ∈ e}) → V i.val

/-- Restriction of a point to the coordinates in `e`. -/
def restrict (x : Pt V) (e : Finset ι) : Pd (V := V) e := fun i => x i.val

theorem restrict_apply (x : Pt V) (e : Finset ι) (i : {i : ι // i ∈ e}) :
    restrict x e i = x i.val := rfl

/-- The set of restrictions to `e` of the points of `A`. -/
def shadow (e : Finset ι) (A : Finset (Pt V)) : Finset (Pd (V := V) e) :=
  A.image (fun x => restrict x e)

theorem mem_shadow {e : Finset ι} {A : Finset (Pt V)} {w : Pd (V := V) e} :
    w ∈ shadow e A ↔ ∃ x ∈ A, restrict x e = w := by
  simp [shadow]

theorem shadow_mono {e : Finset ι} {A B : Finset (Pt V)} (h : A ⊆ B) :
    shadow e A ⊆ shadow e B := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := mem_shadow.mp hw
  exact mem_shadow.mpr ⟨x, h hx, rfl⟩

theorem restrict_mem_shadow {e : Finset ι} {A : Finset (Pt V)}
    (hA : (coord (V := V) e).IsMeas A) (x : Pt V) : restrict x e ∈ shadow e A ↔ x ∈ A := by
  rw [mem_shadow]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : ∀ i ∈ e, x i = y i := fun i hi => by
      have h := congrFun hyx ⟨i, hi⟩
      rw [restrict_apply, restrict_apply] at h
      exact h.symm
    exact ((coord_isMeas_iff.mp hA) x y (fun i hi => (hxy i hi).symm)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- For a `coord e`-measurable set, the indicator of the set at a restriction is
the indicator of the shadow at that restriction. -/
theorem indicator_shadow {e : Finset ι} {A : Finset (Pt V)}
    (hA : (coord (V := V) e).IsMeas A) (x : Pt V) :
    SigAlg.indicator (shadow e A) (restrict x e) = SigAlg.indicator A x := by
  by_cases hx : x ∈ A
  · have hw : restrict x e ∈ shadow e A := (restrict_mem_shadow hA x).mpr hx
    have h1 : SigAlg.indicator A x = 1 := by
      show (if x ∈ A then (1 : ℝ) else 0) = 1
      rw [if_pos hx]
    have h2 : SigAlg.indicator (shadow e A) (restrict x e) = 1 := by
      show (if restrict x e ∈ shadow e A then (1 : ℝ) else 0) = 1
      rw [if_pos hw]
    rw [h1, h2]
  · have hw : restrict x e ∉ shadow e A := fun h => hx ((restrict_mem_shadow hA x).mp h)
    have h1 : SigAlg.indicator A x = 0 := by
      show (if x ∈ A then (1 : ℝ) else 0) = 0
      rw [if_neg hx]
    have h2 : SigAlg.indicator (shadow e A) (restrict x e) = 0 := by
      show (if restrict x e ∈ shadow e A then (1 : ℝ) else 0) = 0
      rw [if_neg hw]
    rw [h1, h2]

theorem shadow_card_le {e : Finset ι} (A : Finset (Pt V)) : (shadow e A).card ≤ A.card :=
  Finset.card_image_le

theorem shadow_eq_image (e : Finset ι) (A : Finset (Pt V)) :
    shadow e A
      = A.image (fun x => fun i : {i : ι // i ∈ e} => x i.val) := rfl

/-- **The density of a `coord e`-measurable set equals the density of its shadow. -/
theorem avg_indicator_shadow {e : Finset ι} {A : Finset (Pt V)}
    (hA : (coord (V := V) e).IsMeas A) :
    avg (fun x : Pt V => SigAlg.indicator A x)
      = avg (fun w : Pd (V := V) e => SigAlg.indicator (shadow e A) w) := by
  have hsum : (∑ x : Pt V, SigAlg.indicator A x) = (A.card : ℝ) := by
    rw [show (∑ x : Pt V, SigAlg.indicator A x)
        = ∑ x : Pt V, (if x ∈ A then (1 : ℝ) else 0) from rfl]
    rw [Finset.sum_boole]
    have hfil : (Finset.univ.filter (fun x : Pt V => x ∈ A)) = A := by ext x; simp
    rw [hfil]
  have hsum2 : (∑ w : Pd (V := V) e, SigAlg.indicator (shadow e A) w)
      = ((shadow e A).card : ℝ) := by
    rw [show (∑ w : Pd (V := V) e, SigAlg.indicator (shadow e A) w)
        = ∑ w : Pd (V := V) e, (if w ∈ shadow e A then (1 : ℝ) else 0) from rfl]
    rw [Finset.sum_boole]
    have hfil : (Finset.univ.filter (fun w : Pd (V := V) e => w ∈ shadow e A))
        = shadow e A := by ext x; simp
    rw [hfil]
  unfold avg
  rw [hsum, hsum2, shadow_eq_image]
  exact Commons.Combinatorics.Finset.card_image_restrict_ratio e A
    (fun x y hxy => (coord_isMeas_iff.mp hA) x y hxy)

end Szemeredi.Removal
