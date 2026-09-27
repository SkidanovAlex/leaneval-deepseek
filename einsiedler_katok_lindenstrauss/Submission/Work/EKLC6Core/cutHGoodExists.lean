import Mathlib
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.shell_borel_cantelli

/-!
# `Work.EKLC6Core.cutHGoodExists` — the large Borel core of the cut good set

Pisa 7.31 in its quantitative form: for the measure-preserving diagonal flow `aDiag t`
and the cut good set `CutGood S t C μ0 N` of `Work.EKLC6Core.cutHDefs`, every `ε' > μ S.bad`
is exceeded by the measure of the complement of `CutGood S t C μ0 N` for all large `N`;
extracting the Borel core of the good set then gives a *Borel* set `H ⊆ CutGood S t C μ0 N`
with `μ Hᶜ < ε'`.

The proof combines three ingredients already available in the workspace:

* `Work.EKLC6Core.CutGood_measure_le`: the complement of the good set is contained in `bad`
  together with the set of points whose orbit meets the thin shell at some time `n ≥ N`;
* `Work.EKLC6Core.shellThin_bound`: the shell has linear measure `≤ C η`;
* `Work.EKLC6Core.exists_tail_iUnion_shell_lt`: the tail Borel–Cantelli estimate, which makes
  the measure of the latter set arbitrarily small as `N → ∞`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Work.EKLC6Core

open Work.EKLContract

theorem cutHGoodExists {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3} {ε : ℝ}
    (S : Work.EKLC6Core.CutData μ U ε) {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hfree : ∀ᵐ x ∂μ, x ∈ Work.EKLC6Core.cutFree U)
    {C μ0 : ℝ} (hC : 0 < C) (hμ0 : 0 < μ0) (hμ01 : μ0 < 1) {ε' : ENNReal}
    (hbad : μ S.bad < ε') :
    ∃ (N : ℕ) (H : Set Work.EKLContract.X3), MeasurableSet H ∧
      H ⊆ Work.EKLC6Core.CutGood S t C μ0 N ∧ μ Hᶜ < ε' := by
  -- the shell has linear measure: `μ (shellThin S η) ≤ C' η`
  obtain ⟨C', hC'pos, hC'thin⟩ := shellThin_bound S
  -- the gap `ε' - μ S.bad` is positive
  have hη : 0 < ε' - μ S.bad := tsub_pos_iff_lt.mpr hbad
  -- Borel–Cantelli: for large `N` the tail of shell-visiting orbits has measure `< ε' - μ S.bad`
  obtain ⟨N, hN⟩ := exists_tail_iUnion_shell_lt (μ := μ)
    (φ := fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
    hmp hC'pos (fun s hs => hC'thin s hs) hμ0 hμ01 hC (ε' - μ S.bad) hη
  -- hence the complement of the good set has measure `< ε'`
  have hlt : μ (CutGood S t C μ0 N)ᶜ < ε' := by
    refine lt_of_le_of_lt (CutGood_measure_le S t hmp hfree N) ?_
    have hbadtop : μ S.bad ≠ ⊤ := measure_ne_top μ _
    calc μ S.bad + μ (⋃ n ∈ Set.Ici N,
            ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
              shellThin S (C * μ0 ^ n))
        < μ S.bad + (ε' - μ S.bad) := ENNReal.add_lt_add_left hbadtop hN
      _ = ε' := add_tsub_cancel_of_le (le_of_lt hbad)
  exact ⟨N, exists_borel_subset_CutGood S hlt⟩

end Work.EKLC6Core
