import ChallengeDeps
import Submission.Work.BoseBox.Word
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.Reduce` — the `G` node: from the per-state box bound to `HBoxG`

This module does the *wiring* of the chapter, and it is all proved here:

* `Rayl_eq_boxQuot` — `Work.UBB.Rayl` is the corpus's `boxQuot`, the quotient
  whose infimum is `boxEnergy` (so a per-state bound on `Rayl` is a lower bound
  on `boxEnergy`);
* `Lambda_eq_gcTwoTerm` — FS's shifted value `Λ A C η₀ ρ` at error exponent
  `η₀` *is* the grand-canonical two-term value `gcTwoTerm A C (1/2+η₀) ρ` (the
  `8πAρ²` chemical-potential shift between the two normalisations);
* `HBoxG_of_perStateBox` — **the `G`-node reduction**: the per-state canonical
  bound `PerStateBox` (every admissible state of every box has shifted energy at
  least `L³·gcTwoTerm`) gives `HBoxG` (the finite-volume Dirichlet
  LHY-Background, eventually in `L`, at `μ = 8πaρ`, `ρmax = 2ρ`).  This is the
  step the audit's `§4 G` describes; it is pure infimum arithmetic over
  `gcBox = sInf {boxEnergy N L v − μN : N ≤ ρmax L³}` and the corpus's
  `gcSet_nonempty`, `le_csInf`, `boxEnergy_eq_ciInf_boxQuot`;
* `hpres_of_HBoxG` — **the consumer wiring (audit `R0`)**: `HBoxG` plus the
  absorption of the `Cw`-error gives exactly the `hpres` shape consumed by
  `Submission.theorem_1_2`, via the closed interface
  `GCBoxBound.hpres_of_gcTwoTerm`.

With `Submission.Work.BoseBox.perStateBox_of_LHYBox_compareBox` (the `C`+`B`
assembly) this closes the chain

    LHYBox (FS thm:LHY-Box) + CompareBox (FS thm:CompareBoxEnergy)
      ⟹ PerStateBox ⟹ HBoxG ⟹ hpres.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox


open Filter Metric MeasureTheory
open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The dictionary identities -/

/-- The corpus's `boxQuot` is the `Rayl` of this chapter (same body). -/
lemma Rayl_eq_boxQuot (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : CInfty0Box N L) :
    Rayl N L v Ψ = boxQuot N L v Ψ := rfl

/-- FS's shifted two-term value equals the grand-canonical two-term value at
error exponent `1/2 + η₀` (they differ only by the `8πAρ²` chemical-potential
shift): `Λ A C η₀ ρ = gcTwoTerm A C (1/2+η₀) ρ`. -/
lemma Lambda_eq_gcTwoTerm (A C η₀ ρ : ℝ) :
    Lambda A C η₀ ρ = gcTwoTerm A C (1 / 2 + η₀) ρ := by
  dsimp [Lambda, gcTwoTerm, lhyC]
  ring

/-! ## 2. The `G`-node reduction -/

/-- `Cw·(ρA³)^e ≤ K` eventually in `ρ` for `e > 0`, `Cw ≥ 0`, `A > 0`
(re-exported from the closed interface, for the consumer's convenience). -/
lemma eventually_absorp_bosebox {Cw K A e : ℝ} (hCw : 0 ≤ Cw) (hK : 0 < K) (hA : 0 < A)
    (he : 0 < e) : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), Cw * (ρ * A ^ 3) ^ e ≤ K :=
  eventually_absorp hCw hK hA he

/-- **The `G`-node reduction**: the per-state canonical box bound implies the
finite-volume LHY-Background `HBoxG`.

The proof is the infimum bookkeeping: for admissible `N` (i.e.
`N ≤ (2ρ)L³`) and every state `Ψ` of the box `(N,L)` the hypothesis gives
`L³·gcTwoTerm ≤ Rayl Ψ − 8π(a v)ρN`; taking the infimum over `Ψ` bounds
`boxEnergy N L v`, then the infimum over admissible `N` bounds
`gcBox v (8π(a v)ρ) (2ρ) L`, and dividing by `L³` gives the density statement. -/
theorem HBoxG_of_perStateBox {v : ℝ³ → ℝ} {η₀ C : ℝ} (hps : PerStateBox v η₀ C) :
    HBoxG v η₀ C := by
  rcases hps with ⟨ε₀, hε₀, hps⟩
  have htend : Tendsto (fun ρ : ℝ => ρ * (a v) ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using hid.mul tendsto_const_nhds
  have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ * (a v) ^ 3 ≤ ε₀ :=
    htend.eventually (eventually_le_nhds hε₀)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ρ hρpos hρsmall
  have hρ0 : 0 < ρ := hρpos
  rcases hps ρ hρ0 hρsmall with ⟨L₀, hL₀1, hpsL⟩
  refine ⟨L₀, hL₀1, fun L hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hL₀1 hL)
  have hL3pos : 0 < L ^ 3 := pow_pos hLpos 3
  have hkey : L ^ 3 * gcTwoTerm (a v) C (1 / 2 + η₀) ρ
      ≤ gcBox v (8 * π * (a v) * ρ) (2 * ρ) L := by
    rw [gcBox]
    refine le_csInf (gcSet_nonempty (μ := 8 * π * (a v) * ρ) (by positivity) hLpos.le) ?_
    rintro b ⟨N, hNadm, rfl⟩
    have hN : (N : ℝ) ≤ 2 * ρ * L ^ 3 := hNadm
    haveI hne : Nonempty (CInfty0Box N L) := nonempty_CInfty0Box N hLpos
    have hgoal : L ^ 3 * gcTwoTerm (a v) C (1 / 2 + η₀) ρ + 8 * π * (a v) * ρ * (N : ℝ)
        ≤ boxEnergy N L v := by
      rw [boxEnergy_eq_ciInf_boxQuot]
      refine le_ciInf (fun Ψ => ?_)
      have hbound := hpsL L hL N hN Ψ
      rw [Rayl_eq_boxQuot] at hbound
      linarith
    linarith
  rw [gcDensity]
  rw [le_div_iff₀ hL3pos]
  linarith

/-! ## 3. The consumer wiring (audit `R0`) -/

/-- **`HBoxG` gives the `hpres` shape**: from the finite-volume LHY-Background at
`μ = 8π(a v)ρ` and truncation `ρmax = 2ρ` (plus the absorption of the `Cw`-error
by `(ρ(a v)³)^{η₀−η} → 0`), the pressure-level LHY-Background
`lhyRhs (a v) K (1/2+η) ρ ≤ gcPressure v (2ρ) (8π(a v)ρ) + 8π(a v)ρ²` holds
eventually.  This is exactly the hypothesis `hpres` of
`Submission.theorem_1_2` (verbatim, with `ρmax := 2ρ`), through the closed
interface `GCBoxBound.hpres_of_gcTwoTerm`. -/
theorem hpres_of_HBoxG {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {η₀ η Cw K : ℝ} (hη₀ : 0 < η₀) (hη : 0 < η) (hηlt : η < η₀)
    (hCw : 0 ≤ Cw) (hK : 0 < K) (hav : 0 < a v) (hboxg : HBoxG v η₀ Cw) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_gcTwoTerm hv hv1 hR hv_supp hav hη₀ hη hηlt hCw hK hboxg
    (eventually_absorp hCw hK hav (by linarith))

end Work.BoseBox
