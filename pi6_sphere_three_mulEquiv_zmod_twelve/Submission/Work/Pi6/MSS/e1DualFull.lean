import Mathlib
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.Pi6.MSS.e1DualMain
import Submission.Work.Pi6.MSS.evS_bij
import Submission.Work.Pi6.MSS.coFiltAnn
import Submission.Work.SSSR.kF_eq_of_lift
import Submission.Work.SSSR.jF_eq_grFi
import Submission.Work.SSSR.d1_eqToHom_conj
import Submission.Work.SSSR.serreE2Defs
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `e1Dual`: the comparison map and its assembly

This file proves the missing half of `Work.Pi6.MSS.e1Dual` in a self-contained way, without going
through the delegated statement `Work.Pi6.MSS.e1CohDualB`: for a Serre fibration `p` with simply
connected base and any field `𝕜`, the cohomological `E_1` row `E1Row 𝕜 (serreCF 𝕜 E B p) q` is the
`𝕜`-dual of the chain level `E_1` row `E1Complex 𝕜 ξ q` of the Serre filtration.

The comparison map `EV` evaluates a class of the first page on the cycles of the graded piece; it is
an isomorphism because `Work.Pi6.MSS.evS_bij` says so, and the missing ingredient is the naturality
of `EV`, i.e. that it intertwines the cohomological differential `pD 1` with the transposed chain
level differential `d¹`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS.E1D

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The canonical isomorphism `H_n ≅ Z_n/B_n`** for a chain complex of `𝕜`-vector spaces: the
composite of the identification of the homology with the homology of the short complex
`E_{n+1} → E_n → E_{n-1}` and the explicit description of that homology as cycles modulo
boundaries. -/
noncomputable def homZ (𝕜 : Type) [Field 𝕜] (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    E.homology n ≅ ModuleCat.of 𝕜
      (↥(Work.StemsB.fdZ 𝕜 E n) ⧸ Work.StemsB.fdH 𝕜 E n) :=
  (E.homologyIsoSc' (n+1) n (n-1) (Work.Cohomology.down_prev n)
      (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso (E.sc' (n+1) n (n-1))


/-- **The abstract cycles of `E` identified with the explicit submodule `Z_n = ker d_n`**; the
identification does not change the underlying element of the complex. -/
noncomputable def cycIsoZ (𝕜 : Type) [Field 𝕜] (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    E.cycles n ≅ ↧(Work.StemsB.fdZ 𝕜 E n) :=
  (E.cyclesIsoSc' (n+1) n (n-1) (Work.Cohomology.down_prev n)
      (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatCyclesIso (E.sc' (n+1) n (n-1))

/-- `cycIsoZ` is compatible with the inclusions of the cycles. -/
theorem cycIsoZ_hom_i (𝕜 : Type) [Field 𝕜] (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    (cycIsoZ 𝕜 E n).hom ≫
        (ShortComplex.moduleCatLeftHomologyData (E.sc' (n+1) n (n-1))).i = E.iCycles n := by
  rw [cycIsoZ, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- `cycIsoZ` does not change the underlying element of the complex. -/
theorem cycIsoZ_val (𝕜 : Type) [Field 𝕜] (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ)
    (c : ↥(E.cycles n)) :
    (((cycIsoZ 𝕜 E n).hom c : ↥(Work.StemsB.fdZ 𝕜 E n)) : ↥(E.X n)) = (E.iCycles n).hom c := by
  have h := congrArg (fun (m : E.cycles n ⟶ E.X n) => (ModuleCat.Hom.hom m) c)
    (cycIsoZ_hom_i 𝕜 E n)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  have h2 : ModuleCat.Hom.hom
      (ShortComplex.moduleCatLeftHomologyData (E.sc' (n+1) n (n-1))).i
      = (Work.StemsB.fdZ 𝕜 E n).subtype := rfl
  rw [h2] at h
  simpa using h

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]


/-- **The comparison map on representatives**: the evaluation of a `1`-cocycle of the Serre
filtration on the cycles of the `s`-th graded piece, via the identification
`H_{q+s} ≅ Z_{q+s}/B_{q+s}`.  This is the map whose descent to the page is `EV`. -/
noncomputable def PhiR (p : C(E, B)) (q : ℕ)
    (hann : ∀ s n, Work.Pi6.MSS.coFilt 𝕜 (Work.Pi6.MSS.sF p) s n =
      Work.Pi6.MSS.compAnn 𝕜 (Work.StemsB.serreSubcomplex (Work.Pi6.MSS.sF p) s) n)
    (s : ℕ) :
    ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 1 s (q + s)) →ₗ[𝕜]
      ((Work.Pi6.MSS.Kg 𝕜 p s).homology (q + s) →ₗ[𝕜] 𝕜) :=
  (LinearMap.dualMap
      (ModuleCat.Hom.hom (homZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (q + s)).hom)).comp
    (Work.Pi6.MSS.evZ 𝕜 p s (q + s) hann)

/-- **The comparison map** `E_1^{s,q+s} ⟶ Hom_𝕜(H_{q+s}(gr_s),𝕜)`: the evaluation of a class of
the first page on the cycles of the `s`-th graded piece of the Serre chain filtration, transported
along the canonical isomorphism `homZ`. -/
noncomputable def EV (p : C(E, B)) (q : ℕ)
    (hann : ∀ s n, Work.Pi6.MSS.coFilt 𝕜 (Work.Pi6.MSS.sF p) s n =
      Work.Pi6.MSS.compAnn 𝕜 (Work.StemsB.serreSubcomplex (Work.Pi6.MSS.sF p) s) n)
    (s : ℕ) :
    Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 1 s (q + s) →ₗ[𝕜]
      ((Work.Pi6.MSS.Kg 𝕜 p s).homology (q + s) →ₗ[𝕜] 𝕜) :=
  (LinearMap.dualMap
      (ModuleCat.Hom.hom (homZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (q + s)).hom)).comp
    (Work.Pi6.MSS.evS 𝕜 p s (q + s) hann)

theorem EV_apply (p : C(E, B)) (q : ℕ)
    (hann : ∀ s n, Work.Pi6.MSS.coFilt 𝕜 (Work.Pi6.MSS.sF p) s n =
      Work.Pi6.MSS.compAnn 𝕜 (Work.StemsB.serreSubcomplex (Work.Pi6.MSS.sF p) s) n)
    (s : ℕ) (x : Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 1 s (q + s))
    (v : (Work.Pi6.MSS.Kg 𝕜 p s).homology (q + s)) :
    EV p q hann s x v = Work.Pi6.MSS.evS 𝕜 p s (q + s) hann x
      (ModuleCat.Hom.hom (homZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (q + s)).hom v) := by
  rw [EV, LinearMap.comp_apply, LinearMap.dualMap_apply]

end

end Work.Pi6.MSS.E1D
