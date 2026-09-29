import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.D_ne_zero
import Submission.Work.A14D.om1_geometry

/-!
# `Work.A14D.jump_not_zero_Om1`

The jump `D = HU - HL` of `Hfun a b c` across the slit `(-∞,1]` does not vanish identically on the
slit plane `Om1 = {z | z.im ≠ 0 ∨ 1 < z.re}`.

This is the exact statement needed in `Work.A14D.kappa_jump_nnz`: the companion lemma
`kappaU_zero_jump_zero` derives `∀ z ∈ Om1, D z = 0` from the vanishing of the log-coefficient
`κU`, so a contradiction requires non-vanishing of `D` on `Om1` (and *not* merely `D ≠ 0` as a
function on `ℂ`, which is the stronger-looking but different statement proved in
`Work.A14D.D_ne_zero`).

The two statements are proved from the same analysis (the argument of `D_ne_zero` only ever uses
`D z = 0` at points of the wedge `SU ∩ SL`).  Here we reduce to `D_ne_zero` by modifying `D`
outside `Om1`: put `D̃ z = D z` for `z ∈ Om1` and `D̃ z = 0` otherwise.  Since `Om1` is open and
`SU ∩ SL ⊆ Om1`, all hypotheses of `D_ne_zero` transfer to `D̃` (the differential equation is a
local condition, so the derivatives of `D̃` and `D` agree on `Om1`), and `D̃ ≠ 0` says precisely
that `D` is not identically zero on `Om1`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

theorem jump_not_zero_Om1 (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (hb : b ≠ 0)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ Metric.ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ Metric.ball 0 1, HL z = Hfun a b c z)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z) :
    ¬ (∀ z ∈ Om1, D z = 0) := by
  classical
  -- `Om1` is open.
  have hOm1open : IsOpen Om1 := by
    have hset : Om1 = {z : ℂ | z.im ≠ 0} ∪ {z : ℂ | 1 < z.re} := rfl
    rw [hset]
    exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
      (isOpen_lt continuous_const Complex.continuous_re)
  -- The extension of `D` by `0` off `Om1`.
  set Dext : ℂ → ℂ := fun z => if z ∈ Om1 then D z else 0 with hDextdef
  have hDext_eq : ∀ z ∈ Om1, Dext z = D z := fun z hz => by
    show (if z ∈ Om1 then D z else 0) = D z
    rw [if_pos hz]
  have hDextd : DifferentiableOn ℂ Dext Om1 :=
    hD.congr (fun z hz => hDext_eq z hz)
  -- The equation transfers, since `LZ` is a local condition.
  have hDextL : ∀ z ∈ Om1, LZ Dext z = 0 := by
    intro z hz
    have hEv : Dext =ᶠ[𝓝 z] D := by
      filter_upwards [hOm1open.mem_nhds hz] with w hw
      exact hDext_eq w hw
    have h1 : deriv Dext z = deriv D z := hEv.deriv_eq
    have h2 : deriv (deriv Dext) z = deriv (deriv D) z := hEv.deriv.deriv_eq
    have h3 : Dext z = D z := hDext_eq z hz
    rw [LZ_def, h2, h1, h3]
    exact hDL z hz
  -- The wedge lies in `Om1`, so the junction condition transfers.
  have hDextj : ∀ z ∈ SU ∩ SL, Dext z = HU z - HL z := by
    intro z hz
    rw [hDext_eq z (SU_subset_Om1 hz.1)]
    exact hDj z hz
  have hne : Dext ≠ 0 :=
    D_ne_zero a b c h hb HU HL hHU hHL Dext hDextd hDextL hDextj
  intro h0
  apply hne
  funext z
  by_cases hz : z ∈ Om1
  · simp only [hDextdef, if_pos hz]
    exact h0 z hz
  · simp only [hDextdef, if_neg hz, Pi.zero_apply]

end Work.A14D
