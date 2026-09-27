import Mathlib
import Submission.Work.Mostow.axisDichotomy
import Submission.Work.Mostow.no_fpf_eq_of_ne_one

/-!
# A subgroup of `PO 1 1` all of whose elements are involutions

`PO 1 1` is the full isometry group of the hyperbolic line `ℍ¹`.  The line is modelled here by
the chart `E 1 = ℝ` with the signed distance `sc u = arsinh (u 0)`, in which the action of every
element `g` becomes an affine isometry `Phi g` of `ℝ` (`AxisDich.Phi_form`): either a translation
`x ↦ c + x` or a reflection `x ↦ c - x`.

Consequences used below:

* an involution `g * g = 1` is either the identity (a translation with `c = 0`) or a reflection,
  and a reflection fixes its centre `pt (c/2)`; hence every involution fixes a point of `ℍ¹`
  (`fixes_of_sq_eq_one`);
* by `no_fpf_eq_of_ne_one`, a subgroup all of whose elements fix a point has at most one
  non-trivial element, hence is finite.

So a subgroup of `PO 1 1` in which every element satisfies `g * g = 1` is finite, and each of its
elements fixes a point of `ℍ¹`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

open AxisDich

/-- An involution of `PO 1 1` fixes a point of `ℍ¹`.  Indeed `Phi g` is either a reflection,
which fixes its centre, or a translation by `0`, in which case `g = 1`. -/
theorem fixes_of_sq_eq_one (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (g : LeanEval.Geometry.MostowRigidity.PO 1 1) (h : g * g = 1) :
    ∃ x : Submission.Mostow.E 1, g • x = x := by
  have hA : POBasic 1 := POBasic.ofProp hA1
  have hI : HypIsoData 1 := HypIsoData.ofProp hI1
  rcases Phi_form hI g with ⟨c, hc | hc⟩
  · -- `g` acts by the translation `x ↦ c + x`; `g * g = 1` forces `c = 0`, hence `g = 1`.
    have hcomp0 : Phi (g * g) 0 = 2 * c := by
      rw [Phi_mul hA g g]
      show Phi g (Phi g 0) = 2 * c
      rw [hc, hc]
      ring
    have hid0 : Phi (g * g) 0 = 0 := by rw [h, Phi_one hA]; rfl
    have hc0 : c = 0 := by rw [hid0] at hcomp0; linarith
    have hg1 : g = 1 := (Phi_eq_one_iff hA hI g).mp (fun x => by rw [hc, hc0, zero_add])
    exact ⟨0, by rw [hg1, hA.one_smul]⟩
  · -- `g` acts by the reflection `x ↦ c - x`, which fixes the centre `c / 2`.
    refine ⟨pt (c / 2), ?_⟩
    rw [Phi_fix_iff hI g (pt (c / 2)), sc_pt, hc]
    ring

/-- A subgroup of `PO 1 1` in which every element is an involution is finite and each of its
elements fixes a point of `ℍ¹`. -/
theorem finite_fixes_of_sq_eq_one (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (G : Subgroup (LeanEval.Geometry.MostowRigidity.PO 1 1))
    (h : ∀ g ∈ G, g * g = 1) :
    Finite G ∧ ∀ g ∈ G, ∃ x : Submission.Mostow.E 1, g • x = x := by
  have hfix : ∀ g ∈ G, ∃ x : Submission.Mostow.E 1, g • x = x :=
    fun g hg => fixes_of_sq_eq_one hA1 hI1 g (h g hg)
  refine ⟨?_, hfix⟩
  -- every element of `G` fixes a point, so `G` has at most one non-trivial element
  have hatmost := no_fpf_eq_of_ne_one hA1 hI1 G hfix
  by_cases hex : ∃ g ∈ G, g ≠ 1
  · obtain ⟨g, hgG, hg1⟩ := hex
    have hsub : (G : Set (LeanEval.Geometry.MostowRigidity.PO 1 1)) ⊆
        ({1, g} : Set (LeanEval.Geometry.MostowRigidity.PO 1 1)) := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; simp
      · have hxg := hatmost x hx hx1 g hgG hg1
        rw [hxg]; simp
    exact Set.Finite.to_subtype
      (Set.Finite.subset (by simp : ({1, g} :
        Set (LeanEval.Geometry.MostowRigidity.PO 1 1)).Finite) hsub)
  · have hsub : (G : Set (LeanEval.Geometry.MostowRigidity.PO 1 1)) ⊆
        ({1} : Set (LeanEval.Geometry.MostowRigidity.PO 1 1)) := by
      intro x hx
      simp only [Set.mem_singleton_iff]
      by_contra hx1
      exact hex ⟨x, hx, hx1⟩
    exact Set.Finite.to_subtype
      (Set.Finite.subset (Set.finite_singleton 1) hsub)

end Work.Mostow
