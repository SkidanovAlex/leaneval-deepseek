import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.StemsB.SerreFiltration
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.coFiltAnn
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Shared vocabulary for the fibre kernel of the column `E_2^{0,q}`

This file collects the definitions used by `Work.Pi6.MSS.e2Col_fibre_kernel` and by the lemmas
proved underneath it (`Work.Pi6.MSS.fibre_to_pullback`, `Work.Pi6.MSS.horn_to_fibre`,
`Work.Pi6.MSS.vertical_decomp`, `Work.Pi6.MSS.exists_edge`, `Work.Pi6.MSS.pieceHorn_lift`).
It is deliberately kept free of any *results* beyond the two elementary computation lemmas
`Work.Pi6.MSS.F_eq_compAnn` and `Work.Pi6.MSS.dPrev_apply`, so that it can be imported by every
one of those lemmas without creating an import cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/- Auxiliary vocabulary for `Work.Pi6.MSS.e2Col_fibre_kernel`. -/
namespace E2cfk

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The singular chain complex of `E` with coefficients in `𝕜`, the ambient complex of the
cochains under consideration. -/
abbrev ECC (𝕜 : Type) [CommRing 𝕜] (E : Type) [TopologicalSpace E] :
    ChainComplex (ModuleCat 𝕜) ℕ :=
  (Work.SSS.sSing E).chainComplex (ModuleCat.of 𝕜 𝕜)

/-- The singular chain complex of the fibre `p⁻¹(b)`, with coefficients in `𝕜`. -/
abbrev fibCC (𝕜 : Type) [CommRing 𝕜] (p : C(E, B)) (b : B) :
    ChainComplex (ModuleCat 𝕜) ℕ :=
  (Work.SSS.sSing (Work.StemsB.fibre p b)).chainComplex (ModuleCat.of 𝕜 𝕜)

/-- The Serre subcomplex `f⁻¹(sk s)` of `Work.StemsB.serreSubcomplex`. -/
abbrev sser (p : C(E, B)) (s : ℕ) : (Work.SSS.sSing E).Subcomplex :=
  Work.StemsB.serreSubcomplex (Work.SSS.sSingP p) s

/-- The inclusion of the chains of the fibre over `b` into the chains of `E`. -/
abbrev fIncl (𝕜 : Type) [CommRing 𝕜] (p : C(E, B)) (b : B) : fibCC 𝕜 p b ⟶ ECC 𝕜 E :=
  SSet.chainComplexMap (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)) (ModuleCat.of 𝕜 𝕜)

/-- The inclusion of the chains of the `s`-th Serre subcomplex into the chains of `E`. -/
abbrev sserInc (𝕜 : Type) [CommRing 𝕜] (p : C(E, B)) (s : ℕ) :
    ((sser p s).toSSet).chainComplex (ModuleCat.of 𝕜 𝕜) ⟶ ECC 𝕜 E :=
  SSet.chainComplexMap (sser p s).ι (ModuleCat.of 𝕜 𝕜)

/-- The value of a simplex `σ : Δ[1] ⟶ Sing B` at the *last* vertex `v₁` of `Δ[1]`
(`SSet.stdSimplex.δ 0` picks the vertex `1`; see `Work.SSSR.sigmaVert_face`). -/
abbrev lastVert (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶
    Work.SSS.sSing B) : B :=
  Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := 0) 0 ≫ σ)

end E2cfk

open E2cfk

variable (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))

/-- The `s`-th step of the Serre cochain filtration is the annihilator of the chains of the `s`-th
Serre subcomplex. -/
theorem F_eq_compAnn (s n : ℕ) :
    (serreCF 𝕜 E B p).F s n = compAnn 𝕜 (sser p s) n := by
  rw [serreCF_F]
  exact coFiltAnn 𝕜 (Work.SSS.sSingP p) s n

/-! ## The incoming differential as a linear map between the cochain types

The library's `CohFilt.dPrev q` is a linear map `W.C.X (q-1) →ₗ[𝕜] W.C.X q` between the *objects*
`W.C.X n` of `ModuleCat 𝕜`, so that its values do not coerce to functions in the elaborator.  The
abbreviation `Work.Pi6.MSS.E2cfk.dPrevL` (and the abbreviation `Coh` for the type of cochains)
records the same map with the underlying types unfolded, which makes the value on a chain directly
applicable. -/

/-- The `𝕜`-cochains of `E` in degree `n` (the abbreviation `Work.Cohomology.Cochain`, with the
simplicial set fixed). -/
abbrev Coh (n : ℕ) : Type _ := Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n

/-- The incoming differential `C^{q-1} → C^q` of the Serre cochain filtration, as a linear map
between the (unfolded) cochain types. -/
def dPrevL (q : ℕ) : Coh 𝕜 E (q - 1) →ₗ[𝕜] Coh 𝕜 E q :=
  (serreCF 𝕜 E B p).dPrev q

@[simp] theorem dPrevL_eq_dPrev (q : ℕ) :
    dPrevL 𝕜 E B p q = (serreCF 𝕜 E B p).dPrev q := rfl

/-- The incoming differential vanishes in degree `0`. -/
theorem dPrevL_zero : dPrevL 𝕜 E B p 0 = 0 := by
  rw [dPrevL_eq_dPrev]
  rw [CohFilt.dPrev]
  have hshape : (serreCF 𝕜 E B p).C.d (0 - 1) 0 = 0 := by
    refine HomologicalComplex.shape _ _ _ ?_
    simp
  rw [hshape, ModuleCat.hom_zero]

/-- The incoming differential in degree `k+1` is the coboundary of the cochain complex. -/
theorem dPrevL_eq_cochainDiff_succ (k : ℕ) :
    dPrevL 𝕜 E B p (k + 1) = Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing E) k := by
  show ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).d k (k + 1)).hom = _
  rw [Work.Cohomology.SSetCochainComplex_d]
  rfl

/-- Evaluation of the incoming differential on a chain: `(dPrevL (k+1) w) γ = w (∂γ)`. -/
theorem dPrevL_apply_succ (k : ℕ) (w : Coh 𝕜 E k) (γ : (ECC 𝕜 E).X (k + 1)) :
    (dPrevL 𝕜 E B p (k + 1) w) γ = w ((ECC 𝕜 E).d (k + 1) k γ) := by
  rw [show dPrevL 𝕜 E B p (k + 1)
      = Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing E) k
      from dPrevL_eq_cochainDiff_succ 𝕜 E B p k]
  show (show (ECC 𝕜 E).X (k + 1) →ₗ[𝕜] 𝕜
      from (Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing E) k) w) γ
    = w ((ECC 𝕜 E).d (k + 1) k γ)
  rw [show (show (ECC 𝕜 E).X (k + 1) →ₗ[𝕜] 𝕜
      from (Work.Cohomology.cochainDiffLM 𝕜 (Work.SSS.sSing E) k) w)
      = Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) w from rfl]
  simp only [Work.Cohomology.cochainDiff, LinearMap.comp_apply]

end

end Work.Pi6.MSS
