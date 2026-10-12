import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseTop.Pressure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `HBoxGSymStateScaled ⟹ HBoxGp`: the localisation factor is absorbed in the limit

`Work.BoseTop.HBoxGSymStateScaled v η₀ Cw ℓ` is the per-state handoff produced by
the FS §5–§11 analysis *with* the localisation factor `(L + ℓ ρ)³` in place of the
box volume `L³` (the factor `|Ω + B(0,ℓ/2)|`/`|Ω|` of `thm:CompareBoxEnergy`,
`ℓ = ℓ(ρ)` the localisation length).  `Work.BoseTop.HBoxGp v η₀ Cw` is the
pressure-level LHY-Background bound, i.e. the statement that for small `ρ`

`gcTwoTerm (a v) Cw (1/2+η₀) ρ ≤ gcPressure v (2ρ) (8π a v ρ)`.

The content of this file is that the *volume factor costs nothing in the limit*:
dividing by `L³` gives, for all large `L`,

`(1 + ℓ ρ / L)³ · gcTwoTerm ≤ gcDensitySym v (8π a v ρ) (2ρ) L`

and the left-hand side tends to `gcTwoTerm`, while
`gcDensitySym ≤ gcDensity` (bosonic reduction) and `gcDensity → gcPressure`.
No sign condition on `ℓ ρ` is needed: only that the factor tends to `1`, so that
`(1 + ℓ ρ/L)³ gcTwoTerm → gcTwoTerm`, and hence that this value is an eventual
lower bound of `gcDensity`.

The two ingredients are isolated below: `gcBoxSym_ge_of_forall_symState` (the
infimum over admissible `N` and over symmetric trial states) and the
`ε`, `ε`-liminf assembly in `HBoxGp_of_scaledState`.
-/

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace Work.BoseTop.PerN

/-- **Infimum over the admissible particle numbers and the symmetric trial
states.**  If for a *fixed* constant `K` every admissible `N` and every
symmetric trial state `Ψ` satisfies `K + μ N ≤ symQuot N L v Ψ`, then `K` bounds
the symmetric grand-canonical energy `gcBoxSym v μ ρmax L` of the box.

(For the scaled handoff the constant is `K = (L + ℓ ρ)³ · gcTwoTerm … ρ`; the
unscaled version `K = gcTwoTerm … ρ * L³` is the case used by
`PerN/gcTwoTerm_le_gcDensity_of_forall`.) -/
theorem gcBoxSym_ge_of_forall_symState {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρmax L K : ℝ}
    (hρmax : 0 ≤ ρmax) (hL : 0 < L)
    (h : ∀ N : ℕ, Submission.BoseGases.gcAdmissible ρmax L N →
      ∀ Ψ : Submission.BoseGases.SymBox N L,
        K + μ * (N : ℝ) ≤ Submission.BoseGases.symQuot N L v Ψ) :
    K ≤ Work.BoseTop.gcBoxSym v μ ρmax L := by
  unfold Work.BoseTop.gcBoxSym
  refine le_csInf (Work.BoseTop.gcSetSym_nonempty hρmax hL.le) ?_
  rintro y ⟨N, hN, rfl⟩
  have hle : K + μ * (N : ℝ) ≤ Submission.BoseGases.symBoxEnergy N L v := by
    haveI : Nonempty (Submission.BoseGases.SymBox N L) :=
      Submission.BoseGases.nonempty_SymBox N hL
    change K + μ * (N : ℝ) ≤
      ⨅ Ψ : Submission.BoseGases.SymBox N L, Submission.BoseGases.symQuot N L v Ψ
    exact le_ciInf (fun Ψ => h N hN Ψ)
  linarith

/-- **The scaled per-state handoff implies the pressure-level target.**  See the
module docstring: the localisation factor `(1 + ℓ ρ / L)³` is sent to `1` along
`L → ∞`, using that the two-term value is a constant of the density `ρ`. -/
theorem HBoxGp_of_scaledState {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hred : Work.BoseTop.symBoxReduction v)
    (hav : 0 ≤ BoseGases.a v) {η₀ Cw : ℝ} {ℓ : ℝ → ℝ}
    (h : Work.BoseTop.HBoxGSymStateScaled v η₀ Cw ℓ) :
    Work.BoseTop.HBoxGp v η₀ Cw := by
  unfold Work.BoseTop.HBoxGp Work.BoseTop.HBoxGSymStateScaled at *
  filter_upwards [h, self_mem_nhdsWithin] with ρ hρ hρpos
  rcases hρ with ⟨L₀, _hL₀1, hL₀⟩
  have hρ0 : 0 < ρ := hρpos
  have hμ : 0 ≤ 8 * Real.pi * BoseGases.a v * ρ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hav) hρ0.le
  have hρmax : 0 ≤ 2 * ρ := by linarith
  -- the value to be bounded, as a local abbreviation
  set A : ℝ := Submission.BoseGases.gcTwoTerm (BoseGases.a v) Cw (1 / 2 + η₀) ρ with hA
  unfold Submission.BoseGases.gcPressure
  -- reduce to `A - ε ≤ gcLiminf` for every `ε > 0`
  apply le_of_forall_pos_le_add
  intro ε hε
  -- the localisation factor tends to `1`, so the left-hand side tends to `A`
  have hconv : Filter.Tendsto (fun L : ℝ => (1 + ℓ ρ / L) ^ 3 * A) Filter.atTop (𝓝 A) := by
    have h1 : Filter.Tendsto (fun L : ℝ => ℓ ρ / L) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Filter.Tendsto (fun L : ℝ => 1 + ℓ ρ / L) Filter.atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h1
    have h3 : Filter.Tendsto (fun L : ℝ => (1 + ℓ ρ / L) ^ 3) Filter.atTop (𝓝 ((1 + 0) ^ 3)) :=
      h2.pow 3
    have h4 := h3.mul_const A
    simpa using h4
  -- ... hence `A - ε` is an eventual lower bound of the gc density
  have hev : ∀ᶠ L : ℝ in Filter.atTop,
      A - ε ≤ Submission.BoseGases.gcDensity v (8 * Real.pi * BoseGases.a v * ρ) (2 * ρ) L := by
    have hevconv : ∀ᶠ L : ℝ in Filter.atTop, A - ε ≤ (1 + ℓ ρ / L) ^ 3 * A := by
      have hb := hconv.eventually (Metric.ball_mem_nhds A hε)
      filter_upwards [hb] with L hL
      rw [Real.dist_eq] at hL
      have hlow := (abs_lt.mp hL).1
      linarith
    have hperiod : ∀ᶠ L : ℝ in Filter.atTop, max L₀ 1 ≤ L := Filter.eventually_ge_atTop _
    filter_upwards [hperiod, hevconv] with L hLmax hconvL
    have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_right L₀ 1) hLmax
    have hL₀le : L₀ ≤ L := le_trans (le_max_left L₀ 1) hLmax
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    -- the per-state bound, with the factor converted to `(1 + ℓ ρ / L)³ L³`
    have hbox : (1 + ℓ ρ / L) ^ 3 * A * L ^ 3 ≤
        Work.BoseTop.gcBoxSym v (8 * Real.pi * BoseGases.a v * ρ) (2 * ρ) L := by
      refine gcBoxSym_ge_of_forall_symState hρmax hLpos ?_
      intro N hN Ψ
      have hps := hL₀ L hL₀le N hN Ψ
      have hid : (L + ℓ ρ) ^ 3 * A = (1 + ℓ ρ / L) ^ 3 * A * L ^ 3 := by
        field_simp
      rw [hid] at hps
      linarith
    -- divide by the volume and use `gcDensitySym ≤ gcDensity`
    have hdens : (1 + ℓ ρ / L) ^ 3 * A ≤
        Work.BoseTop.gcDensitySym v (8 * Real.pi * BoseGases.a v * ρ) (2 * ρ) L := by
      unfold Work.BoseTop.gcDensitySym
      rw [le_div_iff₀ (pow_pos hLpos 3)]
      exact hbox
    exact le_trans hconvL (le_trans hdens
      (Work.BoseTop.gcDensitySym_le_gcDensity hv hred hμ hρmax hLpos))
  have hlim := Submission.BoseGases.gcLiminf_ge_of_eventually_ge (v := v)
    (μ := 8 * Real.pi * BoseGases.a v * ρ) (ρmax := 2 * ρ) hμ hv hv1 hρmax hev
  linarith

end Work.BoseTop.PerN
