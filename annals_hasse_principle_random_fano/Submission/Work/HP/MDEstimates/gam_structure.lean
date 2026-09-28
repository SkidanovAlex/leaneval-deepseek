import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Sig2.gam_rank_det

/-!
# Structure of `Γ_{x,y}`

For `ν(x), ν(y)` linearly independent (which holds when `x ≠ ±y` are primitive, see
`Work.HP.MDEstimates.veronese_linIndep`), the lattice
`Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)} = Work.HP.Gam d n x y ⊆ ℤ^{N_{d,n}}` is saturated and has rank
exactly `N_{d,n}-2`, and its covolume `Work.HP.detL` is positive.

Route.  `Work.HP.Sig2.gam_rank_det` (rank-nullity for the pair of linear forms `a ↦ ⟪a,ν(x)⟫`,
`a ↦ ⟪a,ν(y)⟫`) gives the rank and the positivity of the covolume; saturatedness is the elementary
fact that a kernel of a `ℤ`-linear map into the torsion-free `ℤ²` is pure.

**Implementation note.**  This file deliberately avoids `Submission.Work.HP.numaux.*`: the name
`Work.HP.orthLat` is declared both there and in `Submission.Work.HP.Vero`, so a file importing both
chains fails to build.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.MDEstimates

open Work.HP

theorem gam_structure (d n : ℕ) (x y : Fin (n + 1) → ℤ)
    (hxy : LinearIndependent ℤ ![veronese d n x, veronese d n y]) :
    rk (Gam d n x y) = NN d n - 2 ∧ IsPrimLat (Gam d n x y) ∧ 0 < detL (Gam d n x y) := by
  obtain ⟨hrk, hdet⟩ := Sig2.gam_rank_det d n x y hxy
  refine ⟨hrk, ?_, hdet⟩
  intro v m hm hv
  rw [Gam, Submodule.mem_inf] at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  constructor
  · have h := h1
    rw [latOrth, LinearMap.mem_ker] at h ⊢
    rw [map_zsmul] at h
    exact (smul_eq_zero.mp h).resolve_left hm
  · have h := h2
    rw [latOrth, LinearMap.mem_ker] at h ⊢
    rw [map_zsmul] at h
    exact (smul_eq_zero.mp h).resolve_left hm

end Work.HP.MDEstimates
