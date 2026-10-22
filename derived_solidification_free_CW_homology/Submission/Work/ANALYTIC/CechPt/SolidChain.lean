import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualComplex
import Submission.Work.ANALYTIC.CechPt.dR_comp
import Submission.Work.REFL.Main

/-!
# The canonical comparison `ℤ[T_•] ⟶ ℤ■[T_•]` of the free Čech complex

This module builds, in the canonical double-dual model of
`Submission/Work/ANALYTIC/CechPt/DoubleDual.lean`, the free Čech complex
`R^p = ℤ[T_p]` of the Cantor cover (with the alternating sum of the face maps as differential)
and the solid Čech complex `D^p = (ℤ[T_p] ⟹ 𝟙) ⟹ 𝟙`, together with the canonical comparison
`cmp : R ⟶ D` whose components are the double-dual units `doubleDualUnit (ℤ[T_p])`.

The comparison is a chain map by naturality of the double-dual unit, and its components are
solid-equivalences (`Work.ANALYTIC.CechPt.doubleDualUnit_solidEquiv`), so `cmp` itself is a
solid-equivalence by `ToolkitProp.levelwise`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

open Work.ATOM

/-- The free Čech complex of the Cantor cover, as a chain complex in nonnegative degrees:
`R_p = ℤ[T_p]` with the alternating sum of the face maps. -/
noncomputable def Rchain : ChainComplex LightCondAb ℕ :=
  ChainComplex.of (fun p => zf (cechTerm p)) (fun p => dR p) (fun p => dR_comp p)

/-- The solid Čech complex of the Cantor cover, as a chain complex in nonnegative degrees:
`D_p = (ℤ[T_p] ⟹ 𝟙) ⟹ 𝟙` with the double dual of the Čech differential. -/
noncomputable def Dchain : ChainComplex LightCondAb ℕ :=
  ChainComplex.of (fun p => dd (zf (cechTerm p))) (fun p => ddFMap (dR p))
    (fun p => by
      show ddFMap (dR (p+1)) ≫ ddFMap (dR p) = 0
      rw [← ddFMap_comp, dR_comp, ddFMap_zero])

/-- The canonical comparison `R ⟶ D`: the double-dual unit componentwise. -/
noncomputable def cmpChain : Rchain ⟶ Dchain where
  f p := doubleDualUnit (zf (cechTerm p))
  comm' i j hij := by
    -- in a chain complex, `hij : j + 1 = i`; both sides are the naturality square of the
    -- double-dual unit at `dR j`
    obtain rfl : j + 1 = i := hij
    simp only [Rchain, Dchain, ChainComplex.of_d]
    exact (doubleDualUnit_natural (dR j)).symm

/-- The free Čech complex of the Cantor cover, as a cochain complex in degrees `≤ 0`. -/
noncomputable abbrev Rcpx : CochainComplex LightCondAb ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor LightCondAb).obj Rchain

/-- The solid Čech complex of the Cantor cover, as a cochain complex in degrees `≤ 0`. -/
noncomputable abbrev Dcpx : CochainComplex LightCondAb ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor LightCondAb).obj Dchain

/-- The canonical comparison of cochain complexes. -/
noncomputable abbrev cmpcpx : Rcpx ⟶ Dcpx :=
  (ComplexShape.embeddingDownNat.extendFunctor LightCondAb).map cmpChain

end Work.ANALYTIC.CechPt
