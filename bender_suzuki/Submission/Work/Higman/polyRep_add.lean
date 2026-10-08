import Mathlib
import Submission.Work.Higman.QuadAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Additivity of the interpolation map `polyRep`

`Work.Higman.polyRep f` (defined in `Submission.Work.Higman.QuadAux`) is Lagrange
interpolation of `f` at the nodes `Finset.univ ⊆ F`.  Since Mathlib defines
`Lagrange.interpolate s v` as an `F`-linear map in the values, `polyRep` is itself
additive, and in fact linear.  This file records additivity (the requested statement)
together with the other consequences of linearity that later arguments use.
-/

namespace Work.Higman

theorem polyRep_add {F : Type*} [Field F] [Fintype F] [DecidableEq F] (f g : F → F) :
    polyRep (fun x => f x + g x) = polyRep f + polyRep g := by
  simp only [polyRep]
  exact map_add (Lagrange.interpolate Finset.univ id) f g

section Linear

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem polyRep_zero : polyRep (0 : F → F) = 0 := by
  simp only [polyRep]
  exact map_zero _

theorem polyRep_neg (f : F → F) : polyRep (-f) = -polyRep f := by
  simp only [polyRep]
  exact map_neg _ f

theorem polyRep_sub (f g : F → F) :
    polyRep (fun x => f x - g x) = polyRep f - polyRep g := by
  simp only [polyRep]
  exact map_sub (Lagrange.interpolate Finset.univ id) f g

theorem polyRep_smul (c : F) (f : F → F) :
    polyRep (fun x => c * f x) = c • polyRep f := by
  simp only [polyRep]
  exact map_smul (Lagrange.interpolate Finset.univ id) c f

theorem polyRep_sum {ι : Type*} (s : Finset ι) (f : ι → F → F) :
    polyRep (∑ i ∈ s, f i) = ∑ i ∈ s, polyRep (f i) := by
  simp only [polyRep]
  rw [map_sum]

end Linear

end Work.Higman
