import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the square of a smooth state supported in a translated box

If `Ψ : X N → ℝ` is smooth and its (closed) support lies in a translate
`c + abox N L` of the centred `N`-particle box, then `Ψ²` is integrable for the
Lebesgue measure on `X N`.

Proof.  The map `x ↦ (fun i => c + x i)` is continuous and `abox N L` is compact
(`Work.UBBInputs9.B.abox_isCompact`, valid for every `L` — for `L < 0` the box is
empty), so the translated box is compact.  Hence `Ψ²` is a continuous function
whose closed support is contained in a compact set, i.e. it has compact support,
and a continuous compactly supported function is integrable.
-/

namespace Work.BoseKinLoc.Sector

open MeasureTheory

theorem integrable_sq_of_contDiff_tsupport {N : ℕ} {c : EuclideanSpace ℝ (Fin 3)} {L : ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
      Submission.BoseGases.abox N L) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (Ψ x) ^ 2) MeasureTheory.volume := by
  have hcont : Continuous (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) := by
    fun_prop
  have hK : IsCompact ((fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
      Submission.BoseGases.abox N L) :=
    (Work.UBBInputs9.B.abox_isCompact N L).image hcont
  have hf : Continuous (fun x : Submission.BoseGases.X N => (Ψ x) ^ 2) := hΨ.continuous.pow 2
  have hsub : tsupport (fun x : Submission.BoseGases.X N => (Ψ x) ^ 2) ⊆
      (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
        Submission.BoseGases.abox N L := by
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport Ψ)) hsupp
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport Ψ (Function.mem_support.mpr (fun h => hx (by rw [h]; norm_num)))
  exact hf.integrable_of_hasCompactSupport
    (hasCompactSupport_def.mpr (hK.of_isClosed_subset (isClosed_tsupport _) hsub))

end Work.BoseKinLoc.Sector
