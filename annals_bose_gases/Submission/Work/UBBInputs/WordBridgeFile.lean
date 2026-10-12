import ChallengeDeps
import Submission.Work.UBBInputs.Normalisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs.WordBridgeFile` — input (1): the word/Hamiltonian dictionary

`Work.UBB.WordBridge v h` is the per-box passage from the canonical (Dirichlet)
box Hamiltonian `𝓗`/`boxEnergy` of `ChallengeDeps` to the corpus per-box word
`wordInf = eB/L³`, with the exact chemical-potential shift `8π(a v)ρ²`:

    wordInf N L (dens N L) v h ≤ boxEnergy N L v / L³ − 8π(a v)(dens N L)² .

This module proves the **infimum step** from FS's per-state statement
(`WordBridgeResidual`): FS prove `e_Λ(ρ) + 8π(a v)ρ² ≤ e(ρ)` by showing, for
*every* admissible state `Ψ`, that the shifted canonical energy density
dominates the word infimum — and then taking the infimum over `Ψ`
(`boxEnergy` is the `ciInf` of `Rayl`, `Work.UBB.boxEnergy_eq_ciInf_Rayl`).
The two directions are proved, so the residual is *exactly* FS's content and not
a weakening (this is the honesty calibration of the ledger).

What remains beyond the delivered corpus, and is therefore *inside* the
residual (FS `thm:CompareBoxEnergy` + `eq:CompareGC`):

1. *(identification)* the corpus word `kinWord + qLHSword` at the chosen kernels
   `wPairC L v` / `wPairC L (g0 v h)` — with masses `∬w₁ = 8π(a v)L³`
   (`Q0Chosen.w1c_acube_integral`) — is the `H_Λ(ρ)` quadratic form of FS
   `eq:w_u`/`eq:defW_12`/`eq:DefU`; the corpus's localised-kernel telescoping
   (`Work.SmallBoxSliding.kinWordBoxInd_integral_u` for the kinetic half,
   `Work.SmallBoxSliding.qLHSwordB_integral_u` for the potential half) is the
   `u`-average form of the identification;
2. *(averaging)* `H_ρ ≥ ∫_u H_{Λ,u}(ρ) du` with `H_{Λ,u} ≥ E_Λ(ρ)·1` for every
   `u` (each `H_{Λ,u}` is unitarily equivalent to `H_{Λ,0}`, FS `eq:transInv`),
   together with the corpus/FS normalisation of the `u`-measure (total mass
   `1`, so that `∫_u w_u(x,y)du = v(x−y)`,
   `Work.LocPotential.locPotential_pair`).

Note (recorded as a trap by the UBB chapter's own roadmap): there is **no**
per-state *domination* `word(Ψ) ≤ (H_ρ-form)(Ψ)` in FS — only the averaged
inequality — so `WordBridgeResidual` cannot be strengthened to a pointwise
comparison at a fixed `u`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The exact chemical-potential shift: `8π(a v)ρ²L³ = 8π(a v)ρN` at
`ρ = dens N L` (the sector identity `H_Λ(ρ) = H_N − 8π(a v)ρN` per unit
volume). -/
lemma dens_sq_mul_volume {v : ℝ³ → ℝ} {N : ℕ} {L : ℝ} (hL : L ≠ 0) :
    8 * π * (a v) * (dens N L) ^ 2 * L ^ 3 = 8 * π * (a v) * dens N L * (N : ℝ) := by
  unfold dens
  field_simp

/-- **The infimum step**: FS `thm:CompareBoxEnergy` per state implies the
dictionary `Work.UBB.WordBridge`. -/
theorem wordBridge_of_residual {v : ℝ³ → ℝ} {h : ScatSol v}
    (hv : 0 ≤ v) (hres : WordBridgeResidual v h) : WordBridge v h := by
  intro L hL N
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  haveI : Nonempty (CInfty0Box N L) := nonempty_CInfty0Box N hLpos
  have hbdd : BddBelow (Set.range (fun Ψ : CInfty0Box N L => Rayl N L v Ψ)) :=
    ⟨0, by rintro y ⟨Ψ, rfl⟩; exact Rayl_nonneg hLpos hv Ψ⟩
  have hinf : wordInf N L (dens N L) v h + 8 * π * (a v) * (dens N L) ^ 2
      ≤ (⨅ Ψ : CInfty0Box N L, Rayl N L v Ψ) / L ^ 3 := by
    rw [ciInf_div_const (c := L ^ 3) hbdd (by positivity)]
    exact le_ciInf (fun Ψ => hres L hL N Ψ)
  rw [boxEnergy_eq_ciInf_Rayl]
  linarith [hinf]

/-- The converse (calibration): `Work.UBB.WordBridge` gives FS's per-state
statement, by `boxEnergy ≤ Rayl Ψ`.  Hence `WordBridgeResidual` is *exactly*
the delivered input, at the per-state level. -/
theorem wordBridgeResidual_of_wordBridge {v : ℝ³ → ℝ} {h : ScatSol v}
    (hv : 0 ≤ v) (hbr : WordBridge v h) : WordBridgeResidual v h := by
  intro L hL N Ψ
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  haveI : Nonempty (CInfty0Box N L) := nonempty_CInfty0Box N hLpos
  have hbdd : BddBelow (Set.range (fun Ψ : CInfty0Box N L => Rayl N L v Ψ)) :=
    ⟨0, by rintro y ⟨Ψ, rfl⟩; exact Rayl_nonneg hLpos hv Ψ⟩
  have hle : (⨅ Ψ : CInfty0Box N L, Rayl N L v Ψ) / L ^ 3 ≤ Rayl N L v Ψ / L ^ 3 :=
    div_le_div_of_nonneg_right (ciInf_le hbdd Ψ) (by positivity)
  have hbr' := hbr L hL N
  rw [boxEnergy_eq_ciInf_Rayl] at hbr'
  linarith [hle, hbr']

/-- **Calibration**: the residual is not a weakening of `Work.UBB.WordBridge` —
it is the same statement, factored at the per-state level. -/
theorem wordBridgeResidual_iff_wordBridge {v : ℝ³ → ℝ} {h : ScatSol v} (hv : 0 ≤ v) :
    WordBridgeResidual v h ↔ WordBridge v h :=
  ⟨wordBridge_of_residual hv, wordBridgeResidual_of_wordBridge hv⟩

end Work.UBBInputs
