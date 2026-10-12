import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.KinPSuperadd

open MeasureTheory Submission BoseGases
open scoped Topology Real

/-- The `s`-slice, over the first block, of the square of the sector projection
`Q_j` (with `j` a slot of the *second* block) is integrable on the first block's
box.

The proof goes through the full centred box: `integrableOn_sq_aQ` gives
integrability of `x ↦ (aQ s (N1+N2) (natAdd N1 j) Φ x)²` on `abox (N1+N2) s`,
the measure-preserving block split `aboxSplit_measurePreserving_restrict`
transports it to the product measure `volume↾abox N1 s × volume↾abox N2 s`
(using `mergeBlock (firstBlock x, lastBlock x) = x`), and Fubini for integrable
functions (`Integrable.integral_prod_left`) yields integrability of the
`u`-parametrised `w`-integral. -/
theorem integrableSlice_snd {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) (j : Fin N2)
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun u : Submission.BoseGases.X N1 =>
      ∫ w in Submission.BoseGases.abox N2 s,
        (@Submission.BoseGases.aQ s (N1 + N2) (Fin.natAdd N1 j) Φ
          (Submission.BoseGases.mergeBlock N1 N2 (u, w)))^2)
      (Submission.BoseGases.abox N1 s) MeasureTheory.volume := by
  have hfull : IntegrableOn (fun x : X (N1 + N2) => (aQ s (Fin.natAdd N1 j) Φ x) ^ 2)
      (abox (N1 + N2) s) volume := integrableOn_sq_aQ hs (Fin.natAdd N1 j) hΦ
  have hmp := aboxSplit_measurePreserving_restrict N1 N2 s
  have hprod : Integrable (fun p : X N1 × X N2 =>
      (aQ s (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 p)) ^ 2)
      (((volume : Measure (X N1)).restrict (abox N1 s)).prod
        ((volume : Measure (X N2)).restrict (abox N2 s))) := by
    refine ((hmp.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding
      (g := fun p : X N1 × X N2 =>
        (aQ s (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 p)) ^ 2))).mp ?_
    change Integrable (fun x : X (N1 + N2) =>
      (aQ s (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))) ^ 2)
      (volume.restrict (abox (N1 + N2) s))
    have hpt : (fun x : X (N1 + N2) =>
        (aQ s (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))) ^ 2)
        = fun x : X (N1 + N2) => (aQ s (Fin.natAdd N1 j) Φ x) ^ 2 := by
      funext x
      rw [blockSplitEquiv_apply, mergeBlock_eq]
    rw [hpt]
    exact hfull
  have hslice := hprod.integral_prod_left
  simpa [IntegrableOn] using hslice

end Work.KinPSuperadd
