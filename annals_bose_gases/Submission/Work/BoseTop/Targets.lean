import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseTop.PerN.HBoxGSym_of_HBoxGSymState
import Submission.Work.BoseTop.PerN.HBoxG_of_HBoxGState
import Submission.Work.BoseTop.PerN.HBoxGp_of_scaledState
import Submission.Work.BoseTop.PerN.gcTwoTerm_le_gcDensity_of_forall
import Submission.Work.BoseTop.Reduction
import Submission.Work.BoseTop.Util.eventually_gcTwoTerm_nonpos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseTop/Targets` — one-stop interfaces for the deep work

The B/C/S nodes of the audit deliver their output either as a per-state
canonical inequality (`HBoxGSymState`, or the same with the localisation volume
factor, `HBoxGSymStateScaled`) or as the all-functions per-`N` inequality
(`HBoxGState`).  This module bundles the conversions, so that a caller can go
from any of those *single* hypotheses to the challenge statement:

```
HBoxGSymState v η₀ Cw  --(HBoxGState_of_HBoxGSymState, uses symBoxReduction)--> HBoxGState
                       --(HBoxG_of_HBoxGState)                                 -> HBoxG     -> HBoxGTarget
                       --(HBoxGSym_of_HBoxGSymState)                           -> HBoxGSym  -> HBoxGSymTarget
HBoxGSymTarget v + symBoxReduction -> HBoxGTarget v -> HBoxGpTarget v -> challenge
```

No new mathematics: every step is an infimum over states/particle numbers, the
bosonic reduction `symBoxReduction`, or the pressure-vs-finite-`L` passage
`HBoxGp_of_HBoxG`.
-/

noncomputable section

open _root_.BoseGases
open Submission.BoseGases
set_option autoImplicit false

namespace Work.BoseTop

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## From the per-state symmetric handoff to the targets -/

/-- The symmetric per-state handoff plus the bosonic reduction gives the
all-functions per-`N` handoff: the infimum over symmetric states is
`symBoxEnergy`, which the reduction bounds by `boxEnergy`. -/
theorem HBoxGState_of_HBoxGSymState {v : ℝ³ → ℝ} (hred : symBoxReduction v)
    {η₀ Cw : ℝ} (h : HBoxGSymState v η₀ Cw) : HBoxGState v η₀ Cw := by
  filter_upwards [h] with ρ hρ
  rcases hρ with ⟨L₀, hL₀1, hL₀⟩
  refine ⟨L₀, hL₀1, fun L hL N hN => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hL₀1 hL)
  have hne : Nonempty (SymBox N L) := nonempty_SymBox N hLpos
  have hle : gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ * L ^ 3 + (8 * π * a v * ρ) * (N : ℝ) ≤
      symBoxEnergy N L v := by
    change _ ≤ ⨅ Ψ : SymBox N L, symQuot N L v Ψ
    exact le_ciInf (fun Ψ => hL₀ L hL N hN Ψ)
  have hredN : symBoxEnergy N L v ≤ boxEnergy N L v := hred N L hLpos
  linarith

/-- The symmetric per-state handoff at admissible parameters gives the
symmetric target bundle. -/
theorem HBoxGSymTarget_of_HBoxGSymState {v : ℝ³ → ℝ} {η₀ Cw : ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hCw : 0 ≤ Cw)
    (h : HBoxGSymState v η₀ Cw) : HBoxGSymTarget v :=
  ⟨η₀, Cw, hη₀, hη₀le, hCw, PerN.HBoxGSym_of_HBoxGSymState h⟩

/-- The symmetric per-state handoff plus the bosonic reduction gives the
finite-`L` target bundle. -/
theorem HBoxGTarget_of_HBoxGSymState {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hred : symBoxReduction v)
    (hav : 0 ≤ a v) {η₀ Cw : ℝ} (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hCw : 0 ≤ Cw)
    (h : HBoxGSymState v η₀ Cw) : HBoxGTarget v :=
  HBoxGTarget_of_HBoxGSymTarget hv hred hav (HBoxGSymTarget_of_HBoxGSymState hη₀ hη₀le hCw h)

/-- The symmetric per-state handoff plus the bosonic reduction gives the
pressure-level (recommended) target bundle. -/
theorem HBoxGpTarget_of_HBoxGSymState {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hred : symBoxReduction v) (hav : 0 ≤ a v) {η₀ Cw : ℝ} (hη₀ : 1 / 2000 < η₀)
    (hη₀le : η₀ ≤ 1 / 2) (hCw : 0 ≤ Cw) (h : HBoxGSymState v η₀ Cw) : HBoxGpTarget v :=
  HBoxGpTarget_of_HBoxGTarget hv hv1 hav
    (HBoxGTarget_of_HBoxGSymState hv hred hav hη₀ hη₀le hCw h)

/-! ## From the per-`N` all-functions handoff -/

/-- The per-`N` handoff at admissible parameters gives the finite-`L` target
bundle. -/
theorem HBoxGTarget_of_HBoxGState {v : ℝ³ → ℝ} {η₀ Cw : ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hCw : 0 ≤ Cw)
    (h : HBoxGState v η₀ Cw) : HBoxGTarget v :=
  ⟨η₀, Cw, hη₀, hη₀le, hCw, PerN.HBoxG_of_HBoxGState h⟩

/-! ## The challenge statement from the handoff predicates -/

/-- **The challenge statement from the symmetric per-state handoff** (the
primary interface for the FS §5--§11 work): the only research inputs are
`HBoxGSymState v η₀ Cw` (or its scaled companion) and the bosonic reduction
`symBoxReduction v` (node `S`). -/
theorem theorem_1_2_of_HBoxGSymState (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 ≤ a v)
    (hred : symBoxReduction v) {η₀ Cw : ℝ} (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2)
    (hCw : 0 ≤ Cw) (h : HBoxGSymState v η₀ Cw) :
    0 < etaBose ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v *
        (1 + (128 / (15 * √π)) * √(ρ * a v ^ 3) - 1 * (ρ * a v ^ 3) ^ (1 / 2 + etaBose)) :=
  theorem_1_2_of_HBoxG v hv_nonneg hv_memL1 hR hv_supp hav
    (HBoxGTarget_of_HBoxGSymState hv_nonneg hred hav hη₀ hη₀le hCw h)

/-- The challenge statement from the per-`N` all-functions handoff. -/
theorem theorem_1_2_of_HBoxGState (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 ≤ a v)
    {η₀ Cw : ℝ} (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hCw : 0 ≤ Cw)
    (h : HBoxGState v η₀ Cw) :
    0 < etaBose ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v *
        (1 + (128 / (15 * √π)) * √(ρ * a v ^ 3) - 1 * (ρ * a v ^ 3) ^ (1 / 2 + etaBose)) :=
  theorem_1_2_of_HBoxG v hv_nonneg hv_memL1 hR hv_supp hav
    (HBoxGTarget_of_HBoxGState hη₀ hη₀le hCw h)

/-! ## From the scaled (FS-shaped) symmetric handoff -/

/-- The scaled symmetric per-state handoff plus the bosonic reduction gives the
pressure-level target bundle (the limit `L → ∞` absorbs the localisation
factor). -/
theorem HBoxGpTarget_of_HBoxGSymStateScaled {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hred : symBoxReduction v) (hav : 0 ≤ a v) {η₀ Cw : ℝ} {ℓ : ℝ → ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hCw : 0 ≤ Cw)
    (h : HBoxGSymStateScaled v η₀ Cw ℓ) : HBoxGpTarget v :=
  ⟨η₀, Cw, hη₀, hη₀le, hCw, PerN.HBoxGp_of_scaledState hv hv1 hred hav h⟩

/-- **The challenge statement from the scaled (FS-shaped) symmetric per-state
handoff** — the primary interface for the `C`/`B` nodes: the only research
inputs are `HBoxGSymStateScaled v η₀ Cw ℓ` (the localisation comparison
`thm:CompareBoxEnergy` composed with the box theorem `thm:LHY-Box`, carrying the
volume factor `(L+ℓ)³`) and the bosonic reduction `symBoxReduction v` (node `S`). -/
theorem theorem_1_2_of_HBoxGSymStateScaled (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hav : 0 ≤ a v) (hred : symBoxReduction v) {η₀ Cw : ℝ} {ℓ : ℝ → ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hCw : 0 ≤ Cw)
    (h : HBoxGSymStateScaled v η₀ Cw ℓ) :
    0 < etaBose ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v *
        (1 + (128 / (15 * √π)) * √(ρ * a v ^ 3) - 1 * (ρ * a v ^ 3) ^ (1 / 2 + etaBose)) :=
  theorem_1_2_of_HBoxGp v hv_nonneg hv_memL1 hR hv_supp hav
    (HBoxGpTarget_of_HBoxGSymStateScaled hv_nonneg hv_memL1 hred hav hη₀ hη₀le hCw h)

/-! ## The handoff predicates are inhabited (`a v = 0`)

For `a v = 0` the two-term value vanishes identically, so the handoff
predicates reduce to the (proved) nonnegativity of the corpus energies.  This
certifies that the interfaces the `C`/`B` nodes must fill are not vacuous. -/

/-- The symmetric per-state handoff is inhabited when the scattering length
vanishes. -/
theorem HBoxGSymState_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hav : a v = 0) {η₀ Cw : ℝ} :
    HBoxGSymState v η₀ Cw := by
  filter_upwards [self_mem_nhdsWithin] with ρ _hρpos
  refine ⟨1, le_rfl, fun L hL1 N _hN Ψ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hlhs : gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ = 0 := by
    rw [hav]
    unfold gcTwoTerm
    ring
  have hμ : 8 * π * a v * ρ = 0 := by rw [hav]; ring
  rw [hlhs, hμ]
  simpa using symQuot_nonneg hLpos hv Ψ

/-- The scaled (FS-shaped) symmetric per-state handoff is inhabited when the
scattering length vanishes. -/
theorem HBoxGSymStateScaled_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hav : a v = 0)
    {η₀ Cw : ℝ} {ℓ : ℝ → ℝ} : HBoxGSymStateScaled v η₀ Cw ℓ := by
  filter_upwards [self_mem_nhdsWithin] with ρ _hρpos
  refine ⟨1, le_rfl, fun L hL1 N _hN Ψ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hlhs : gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ = 0 := by
    rw [hav]
    unfold gcTwoTerm
    ring
  have hμ : 8 * π * a v * ρ = 0 := by rw [hav]; ring
  rw [hlhs, hμ]
  simpa using symQuot_nonneg hLpos hv Ψ

/-- The per-`N` all-functions handoff is inhabited when the scattering length
vanishes. -/
theorem HBoxGState_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hav : a v = 0) {η₀ Cw : ℝ} :
    HBoxGState v η₀ Cw := by
  filter_upwards [self_mem_nhdsWithin] with ρ _hρpos
  refine ⟨1, le_rfl, fun L hL1 N _hN => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hlhs : gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ = 0 := by
    rw [hav]
    unfold gcTwoTerm
    ring
  have hμ : 8 * π * a v * ρ = 0 := by rw [hav]; ring
  rw [hlhs, hμ]
  simpa using boxEnergy_nonneg (v := v) hLpos hv

/-! ## Consistency of the two handoff predicates -/

/-- The *unscaled* symmetric per-state handoff implies the scaled one: for
`gcTwoTerm ≤ 0` and `ℓ ρ ≥ 0`, the volume factor only makes the (negative)
right-hand side smaller, so the scaled inequality is the weaker statement.
This records that the scaled handoff (`PerN/HBoxGp_of_scaledState`) loses
nothing that a deeper analysis might need. -/
theorem HBoxGSymStateScaled_of_HBoxGSymState {v : ℝ³ → ℝ} {η₀ Cw : ℝ} {ℓ : ℝ → ℝ}
    (hav : 0 < a v) (hCw : 0 ≤ Cw) (hη₀ : -1 / 2 < η₀)
    (hℓ : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 ≤ ℓ ρ) (h : HBoxGSymState v η₀ Cw) :
    HBoxGSymStateScaled v η₀ Cw ℓ := by
  have hneg : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ ≤ 0 :=
    Util.eventually_gcTwoTerm_nonpos hav hCw (by linarith)
  filter_upwards [h, hneg, hℓ, self_mem_nhdsWithin] with ρ hρ hΛ hℓρ hρpos
  rcases hρ with ⟨L₀, hL₀1, hL₀⟩
  refine ⟨L₀, hL₀1, fun L hL N hN Ψ => ?_⟩
  have hL0 : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_trans hL₀1 hL)
  have hpow : L ^ 3 ≤ (L + ℓ ρ) ^ 3 := by
    have h1 : L ≤ L + ℓ ρ := le_add_of_nonneg_right hℓρ
    exact pow_le_pow_left₀ hL0 h1 3
  have hmono : (L + ℓ ρ) ^ 3 * gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ ≤
      L ^ 3 * gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ :=
    mul_le_mul_of_nonpos_right hpow hΛ
  have hbase : L ^ 3 * gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ ≤
      symQuot N L v Ψ - (8 * π * a v * ρ) * (N : ℝ) := by
    have := hL₀ L hL N hN Ψ
    linarith
  exact le_trans hmono hbase

/-! ## The pressure-level target is inhabited (`a v = 0`) -/

/-- The pressure-level target holds when the scattering length vanishes
(the `N = 0`/empty-box mechanism: `gcTwoTerm 0 Cw s ρ = 0 ≤ gcPressure`, and
`gcPressure v ρmax 0 ≥ 0`). -/
theorem HBoxGp_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) (hav : a v = 0)
    {η₀ Cw : ℝ} : HBoxGp v η₀ Cw :=
  HBoxGp_of_HBoxG (v := v) hv hv1 (by rw [hav]) (HBoxG_of_av_zero hv hav)

/-- The pressure-level parameter bundle is inhabited when `a v = 0`. -/
theorem HBoxGpTarget_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hav : a v = 0) : HBoxGpTarget v :=
  ⟨1 / 4, 0, by norm_num, by norm_num, le_rfl, HBoxGp_of_av_zero hv hv1 hav⟩

end Work.BoseTop
