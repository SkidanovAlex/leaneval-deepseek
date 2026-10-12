import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Almost everywhere measurability of the truncated pair interaction

For an almost everywhere measurable pair interaction `v : E3 → ℝ`, the configuration-space
function `x ↦ v (x i - x j)` is almost everywhere measurable with respect to Lebesgue measure
on `Conf N`, and consequently so are `Vpot N v` and its truncation `Vtrunc N v M`.

The point is that the difference map `x ↦ x i - x j` (for `i ≠ j`) is a *surjective* linear map
`Conf N →ₗ[ℝ] E3`, hence pushes the Lebesgue measure of `Conf N` (an additive Haar measure)
forward to a scalar multiple of the Lebesgue measure of `E3`
(`LinearMap.exists_map_addHaar_eq_smul_addHaar`).  A scalar multiple of a measure is absolutely
continuous with respect to it, so a.e. measurability is preserved by precomposition.
-/

/-! This file is a namespace-local copy of `Work.BoseSym.Form.aemeasurable_Vtrunc`
(`Submission/Work/BoseSym/Form/aemeasurable_Vtrunc.lean`) with the import of
`Work.BoseSym.Form.aemeasurable_Vpot` deleted.

It exists because the workspace contains two incompatible declarations of the name
`Work.BoseSym.Form.qmp_pair_pi`:
* `Submission/Work/BoseSym/Form/qmp_pair.lean` (the general `{ι} [Fintype ι]` form, used by
  the `Work.BoseFixGlue.Pot` chain, hence by the whole `Work.BoseFixKin` box chain), and
* `Submission/Work/BoseSym/Form/aemeasurable_Vpot.lean` (the `Fin N`-specialised form, imported
  by `Submission/Work/BoseSym/Main.lean`).

An environment cannot contain both, so `Work.BoseSym.Main` cannot be imported together with the
`LHYBoxB` chain — which is exactly what the wire `Work.BoseWire` must do.  The development below
therefore re-establishes the *tail* of the `BoseSym` chapter in this namespace, importing only the
leaf modules that are compatible with `Work.BoseSym.Form.qmp_pair`.  The proofs are those of the
`BoseSym` chapter, unchanged; only the names are local. -/

namespace Work.BoseWire.SymTail

open MeasureTheory
open Work.BoseSym

/-- For two distinct particles `i ≠ j`, the pair interaction `x ↦ v (x i - x j)` is almost
everywhere measurable as soon as `v` is. -/
theorem aemeasurable_pair {N : ℕ} {v : E3 → ℝ} (hv : AEMeas3 v) {i j : Fin N} (hij : i ≠ j) :
    AEMeas N (fun x : Conf N => v (x i - x j)) := by
  -- the difference of the two coordinate projections is a surjective linear map
  let L : Conf N →ₗ[ℝ] E3 :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => E3) i
      - LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => E3) j
  have hL : ∀ x : Conf N, L x = x i - x j := fun _ => rfl
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨Function.update (0 : Conf N) i y, ?_⟩
    rw [hL, Function.update_self, Function.update_of_ne (Ne.symm hij)]
    simp
  obtain ⟨c, -, hc⟩ :=
    L.exists_map_addHaar_eq_smul_addHaar (volume : Measure (Conf N)) (volume : Measure E3) hsurj
  -- the pushforward of Lebesgue measure under the difference map is a multiple of Lebesgue
  have hv' : AEMeasurable v (volume : Measure E3) := hv
  have hmeas : AEMeasurable v (Measure.map L (volume : Measure (Conf N))) := by
    rw [hc]
    exact hv'.smul_measure c
  have hf : AEMeasurable L (volume : Measure (Conf N)) :=
    L.continuous_of_finiteDimensional.measurable.aemeasurable
  exact hmeas.comp_aemeasurable' hf

/-- `Vpot N v` is almost everywhere measurable for an almost everywhere measurable `v`. -/
theorem aemeasurable_Vpot' {N : ℕ} {v : E3 → ℝ} (hv : AEMeas3 v) : AEMeas N (Vpot N v) := by
  have hsum : AEMeas N
      (∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
        fun x : Conf N => v (x p.1 - x p.2)) := by
    refine Finset.aemeasurable_sum
      (f := fun (p : Fin N × Fin N) (x : Conf N) => v (x p.1 - x p.2)) _ fun p hp => ?_
    exact aemeasurable_pair hv (ne_of_lt (Finset.mem_filter.mp hp).2)
  have hEq : (fun x : Conf N =>
        ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), v (x p.1 - x p.2))
      = (∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
        fun x : Conf N => v (x p.1 - x p.2)) := by
    funext x
    rw [Finset.sum_apply]
  rw [← hEq] at hsum
  exact hsum

/-- Alias of `aemeasurable_Vpot'` under the name the `BoseSym` chapter uses
(`Work.BoseSym.Form.aemeasurable_Vpot`), for callers who want the vocabulary of the original
chapter. -/
theorem aemeasurable_Vpot {N : ℕ} {v : E3 → ℝ} (hv : AEMeas3 v) : AEMeas N (Vpot N v) :=
  aemeasurable_Vpot' hv

theorem aemeasurable_Vtrunc {N : ℕ} {v : E3 → ℝ} (hv : AEMeas3 v) (M : ℝ) :
    AEMeas N (Vtrunc N v M) := by
  have h : AEMeas N (fun x : Conf N => min (Vpot N v x) M) :=
    (aemeasurable_Vpot' hv).min (aemeasurable_const (b := M))
  exact h

end Work.BoseWire.SymTail
