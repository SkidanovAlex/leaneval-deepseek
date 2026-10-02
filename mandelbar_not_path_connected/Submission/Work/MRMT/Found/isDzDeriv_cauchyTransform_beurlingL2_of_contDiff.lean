import Mathlib
import Submission.Work.MRMT.Found.CauchyPairingAux
import Submission.Work.MRMT.Found.beurlingL2_eq_cauchyTransform_dz
import Submission.Work.MRMT.Found.cauchyTransform_contDiff_one
import Submission.Work.MRMT.Weyl.isDzDeriv_moll_gen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- The Cauchy transform `C u` of a `C¹` compactly supported `L²` function `u` has weak
`∂`-derivative equal to the Beurling transform `S u` of `u`.

Three facts are combined.  `cauchyTransform_contDiff_one` gives that `C u` is `C¹` and that
its pointwise Wirtinger derivative is `∂(C u) = C(∂u)`; for a `C¹` function the pointwise and
distributional `∂`-derivatives agree (`Work.MRMT.Weyl.isDzDeriv_dz`), so `C u` has weak
`∂`-derivative `C(∂u)`.  Finally `beurlingL2_eq_cauchyTransform_dz` identifies the `L²`
function `S u` with `C(∂u)` almost everywhere, and the weak `∂`-relation is insensitive to
a.e. changes of the representing function (`isDzDeriv_congr_ae`). -/
theorem isDzDeriv_cauchyTransform_beurlingL2_of_contDiff {u : ℂ → ℂ}
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hLp : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    Work.MRMT.IsDzDeriv (Work.MRMT.cauchyTransform u)
      (((Work.MRMT.beurlingL2 (hLp.toLp u)) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) := by
  obtain ⟨hcd, -, hdz⟩ := cauchyTransform_contDiff_one hu hs
  -- the pointwise `∂` of `C u` is a weak `∂`-derivative of `C u`
  have hbase : Work.MRMT.IsDzDeriv (Work.MRMT.cauchyTransform u)
      (fun z => Work.MRMT.dz (Work.MRMT.cauchyTransform u) z) :=
    Work.MRMT.Weyl.isDzDeriv_dz hcd (by norm_num)
  -- replace the pointwise derivative by `C (∂u)`
  have h1 : Work.MRMT.IsDzDeriv (Work.MRMT.cauchyTransform u)
      (fun z => Work.MRMT.cauchyTransform (fun w => Work.MRMT.dz u w) z) :=
    Work.MRMT.Weyl.isDzDeriv_congr hbase hdz
  -- and `C (∂u) = S u` a.e.
  have hae := beurlingL2_eq_cauchyTransform_dz hu hs hLp
  exact isDzDeriv_congr_ae h1 hae.symm

end Work.MRMT.Found
