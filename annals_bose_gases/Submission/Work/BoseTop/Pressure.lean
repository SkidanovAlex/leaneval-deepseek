import ChallengeDeps
import Submission.UBBtoGc
import Submission.Work.BoseTop.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseTop/Pressure` — the recommended (pressure-level) target

`Work.BoseTop.HBoxG` (audit node `G`) is a *finite-`L`* statement: for every
small density `ρ` and every large enough box side `L`, the finite-volume
grand-canonical density dominates `gcTwoTerm`.  FS's own route does not give
that directly: their localisation comparison
(`thm:CompareBoxEnergy`, proved by integrating the localised Hamiltonians over
the translations `u`) produces the *volume factor*
`|Ω + B(0,ℓ/2)|/|Ω| = ((L+ℓ)/L)³ ≥ 1`, which multiplies a **negative**
quantity, so at finite `L` it costs a *relative* amount `3ℓ/L`.  FS remove it
by passing to the thermodynamic limit first (`|Ω+B|/|Ω| → 1`), i.e. their
their result is stated at the level of `e_0(μ)`, the pressure.

Accordingly this module records the pressure-level (hence strictly weaker,
hence easier) target

* `HBoxGp v η₀ Cw : Prop` — for small `ρ`,
  `gcTwoTerm (a v) Cw (1/2+η₀) ρ ≤ gcPressure v (2ρ) (8π a v ρ)`,

which is **exactly** FS `thm:LHY-Background` at `μ = 8π a v ρ`
(`gcPressure v ρmax μ = gcLiminf v μ ρmax`, `Submission/GCPressure.lean:488`).

Relations proved here:

* `HBoxGp_of_HBoxG` — the audit's finite-`L` target implies the pressure-level
  one (`gcLiminf_ge_of_eventually_ge`);
* `hpres_of_HBoxGp` — the pressure-level target alone gives the corpus `hpres`
  (no `L₀`, no `gcTwoTerm_le` bookkeeping: take `ρmax := 2ρ`), hence the whole
  challenge statement (`Reduction/theorem_1_2_of_HBoxGp`);
* `HBoxGSymStateScaled` and the delegated composition
  `PerN/HBoxGp_of_scaledState` — the *realistic handoff* for the FS §5--§11
  analysis: the C/B nodes produce the per-state bound **with the localisation
  factor** `(L + ℓ ρ)³`, and the limit `L → ∞` absorbs it
  (`(1 + ℓ ρ/L)³ Λ → Λ`), so no slack bookkeeping is needed.  This is the
  route that avoids the extra work the finite-`L` form would require.
-/

noncomputable section

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
open Submission.BoseGases
set_option autoImplicit false

namespace Work.BoseTop

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The pressure-level target -/

/-- **The recommended single target** (FS `thm:LHY-Background`): for small
densities `ρ` the truncated grand-canonical *pressure* at chemical potential
`μ = 8π a v ρ` dominates the two-term LHY value
`gcTwoTerm (a v) Cw (1/2+η₀) ρ`.

This is implied by `HBoxG` (`HBoxGp_of_HBoxG`) and implies the corpus `hpres`
(`hpres_of_HBoxGp`).  It is the form in which FS's localisation argument
delivers the bound, because the volume factor `((L+ℓ)/L)³` of the localised
comparison is absorbed by the limit `L → ∞` and does *not* require the
finite-`L` slack that `HBoxG` needs. -/
def HBoxGp (v : ℝ³ → ℝ) (η₀ Cw : ℝ) : Prop :=
  ∀ᶠ ρ in 𝓝[>] (0 : ℝ), gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ ≤ gcPressure v (2 * ρ) (8 * π * a v * ρ)

/-- The parameter bundle for the pressure-level target (same numerical side
conditions as `HBoxGTarget`). -/
def HBoxGpTarget (v : ℝ³ → ℝ) : Prop :=
  ∃ η₀ Cw : ℝ, 1 / 2000 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 ≤ Cw ∧ HBoxGp v η₀ Cw

/-- The finite-`L` target implies the pressure-level one. -/
theorem HBoxGp_of_HBoxG {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) (hav : 0 ≤ a v)
    {η₀ Cw : ℝ} (h : HBoxG v η₀ Cw) : HBoxGp v η₀ Cw := by
  filter_upwards [h, self_mem_nhdsWithin] with ρ hρ hρpos
  rcases hρ with ⟨L₀, _hL₀1, hL₀⟩
  have hρ0 : 0 < ρ := hρpos
  have hμ : 0 ≤ 8 * π * a v * ρ := mul_nonneg (mul_nonneg (by positivity) hav) hρ0.le
  have hρmax : 0 ≤ 2 * ρ := by linarith
  exact gcLiminf_ge_of_eventually_ge (v := v) (μ := 8 * π * a v * ρ) (ρmax := 2 * ρ)
    hμ hv hv1 hρmax ((Filter.eventually_ge_atTop L₀).mono fun L hL => hL₀ L hL)

/-- The parameter bundles inherit the implication. -/
theorem HBoxGpTarget_of_HBoxGTarget {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hav : 0 ≤ a v) (h : HBoxGTarget v) : HBoxGpTarget v := by
  rcases h with ⟨η₀, Cw, h1, h2, h3, h4⟩
  exact ⟨η₀, Cw, h1, h2, h3, HBoxGp_of_HBoxG hv hv1 hav h4⟩

/-! ## The pressure-level target gives `hpres` -/

/-- The corpus pressure-level bound `hpres` from the pressure-level target: no
`L₀` and no per-box bookkeeping — take `ρmax := 2ρ` and absorb the coefficient
`Cw` into `K` with `eventually_absorp`. -/
theorem hpres_of_HBoxGp {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 ≤ a v)
    {η η₀ Cw K : ℝ} (hη : 0 < η) (hηlt : η < η₀) (hCw : 0 ≤ Cw) (hK : 0 < K)
    (hG : HBoxGp v η₀ Cw) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ ≤ gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ := by
  by_cases hav0 : a v = 0
  · exact hpres_of_av_zero (v := v) hv hv1 hR hv_supp hav0
  · have hA : 0 < a v := lt_of_le_of_ne hav (Ne.symm hav0)
    have hdom : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), Cw * (ρ * a v ^ 3) ^ (η₀ - η) ≤ K :=
      eventually_absorp hCw hK hA (by linarith)
    filter_upwards [self_mem_nhdsWithin, hG, hdom] with ρ hρpos hgp hdomρ
    have hρ0 : 0 < ρ := hρpos
    have hρA : 0 < ρ * a v ^ 3 := mul_pos hρ0 (pow_pos hA 3)
    refine ⟨2 * ρ, by linarith, by linarith, ?_⟩
    have hle : lhyRhs (a v) K (1 / 2 + η) ρ ≤ lhyRhs (a v) Cw (1 / 2 + η₀) ρ :=
      lhyRhs_le_of_domination hav hρA hdomρ
    have hchem : lhyRhs (a v) Cw (1 / 2 + η₀) ρ =
        gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ + 8 * π * a v * ρ * ρ :=
      (gcTwoTerm_add_chem (A := a v) (Cw := Cw) (s := 1 / 2 + η₀) (ρ := ρ)).symm
    calc
      lhyRhs (a v) K (1 / 2 + η) ρ ≤ lhyRhs (a v) Cw (1 / 2 + η₀) ρ := hle
      _ = gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ + 8 * π * a v * ρ * ρ := hchem
      _ ≤ gcPressure v (2 * ρ) (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ :=
            add_le_add hgp le_rfl

/-! ## The realistic handoff: the per-state bound *with* the localisation factor -/

/-- **The scaled per-state handoff**: for small `ρ`, all large `L`, all
admissible `N` and all symmetric trial states `Ψ`,
`(L + ℓ ρ)³ · gcTwoTerm (a v) Cw (1/2+η₀) ρ ≤ symQuot N L v Ψ − 8π a v ρ·N`.

This is the shape FS's §5--§11 analysis produces: the node `C` localisation
comparison (`thm:CompareBoxEnergy`) contributes the factor
`((L+ℓ)/ℓ)³` on the localised energy, the node `B` box theorem
(`thm:LHY-Box`) bounds the localised energy density by `gcTwoTerm`, and
`min(0, ·)` together with `gcTwoTerm ≤ 0` turns the product into
`((L+ℓ)/ℓ)³ ℓ³ gcTwoTerm = (L+ℓ)³ gcTwoTerm`. -/
def HBoxGSymStateScaled (v : ℝ³ → ℝ) (η₀ Cw : ℝ) (ℓ : ℝ → ℝ) : Prop :=
  ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ,
    gcAdmissible (2 * ρ) L N → ∀ Ψ : SymBox N L,
      (L + ℓ ρ) ^ 3 * gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ ≤
        symQuot N L v Ψ - (8 * π * a v * ρ) * (N : ℝ)

end Work.BoseTop
