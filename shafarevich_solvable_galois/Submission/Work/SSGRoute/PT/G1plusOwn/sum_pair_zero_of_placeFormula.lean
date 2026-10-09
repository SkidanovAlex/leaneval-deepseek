import Mathlib
import Submission.Work.SSGRoute.PT.classFormation_reciprocity_allPlaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

theorem sum_pair_zero_of_placeFormula
    (p : ℕ) [Fact p.Prime] (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (χ : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 → ZMod p)
    (hχadd : ∀ u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2,
      p • u = 0 → p • v = 0 → χ (u + v) = χ u + χ v)
    (Z : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2)
    (hZ0 : SSGRoute.PTExt.extToClasses (k := k) Z = 0) (hZpt : p • Z = 0)
    (R : Set (NK.GlobalCFT.Place L))
    (hR : ∀ w : NK.GlobalCFT.Place L, ∃! w' : R, ∃ σ : L ≃ₐ[k] L, σ • w = w'.1)
    (W : Finset R)
    (hvan : ∀ w : R, w ∉ W → SSGRoute.PTExt.extLoc (k := k) w.1 Z = 0) :
    ∑ w ∈ W, χ (Work.SSGRoute.PT.iota (k := k) (L := L) w.1
      (SSGRoute.PTExt.extLoc (k := k) w.1 Z)) = 0 := by
  classical
  -- Re-type the local component at `extH (localUnitsK w) 2`; the two are definitionally equal but
  -- only the `extH` form is syntactically the one the coefficient calculus applies to.
  change ∑ w ∈ W, χ (Work.SSGRoute.PT.iota (k := k) (L := L) w.1
    (Work.SSGRoute.PT.extLocH (k := k) (L := L) w.1 Z)) = 0
  -- the vanishing hypothesis, in the `extLocH` form
  have hvanH : ∀ w : R, w ∉ W → Work.SSGRoute.PT.extLocH (k := k) (L := L) w.1 Z = 0 :=
    fun w hw => hvan w hw
  -- the local components really are finitely supported: they vanish off the finite set `W`
  have hfin : {w : R | Work.SSGRoute.PT.extLocH (k := k) (L := L) w.1 Z ≠ 0}.Finite := by
    refine Set.Finite.subset W.finite_toSet ?_
    intro w hw
    by_contra hwW
    exact hw (hvanH w (by simpa [Finset.mem_coe] using hwW))
  -- the finsum form over the transversal: the class-formation reciprocity at all places
  have hsum0 : ∑ᶠ w : R, χ (Work.SSGRoute.PT.iota (k := k) (L := L) w.1
      (Work.SSGRoute.PT.extLocH (k := k) (L := L) w.1 Z)) = 0 :=
    Work.SSGRoute.PT.sum_chi_iota_eq_zero_of_extToClasses (k := k) (L := L) p χ hχadd
      Z hZ0 hZpt R hR hfin
  rw [← hsum0]
  -- the Finset sum over `W` is the finitely supported sum over `R`
  refine (finsum_eq_sum_of_support_subset
    (fun w : R => χ (Work.SSGRoute.PT.iota (k := k) (L := L) w.1
      (Work.SSGRoute.PT.extLocH (k := k) (L := L) w.1 Z))) ?_).symm
  intro w hw
  rw [Function.mem_support] at hw
  by_contra hwW
  refine hw ?_
  rw [hvanH w (by simpa [Finset.mem_coe] using hwW),
    Work.SSGRoute.PT.iota_zero (k := k) (L := L) w.1]
  exact Work.SSGRoute.PT.chi_zero_of_additive p χ hχadd

end Work.SSGRoute.PT.G1plusOwn
