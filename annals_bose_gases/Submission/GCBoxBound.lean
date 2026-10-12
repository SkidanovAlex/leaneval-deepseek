import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.GCPressure
import Submission.UniformBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The per-box grand-canonical two-term bound implies `hpres` (interface)

The single remaining `sorry` of `theorem_1_2` is `hpres` (the pressure-level
LHY-Background at the FS chemical potential `μ_corpus := 8πa v · ρ`).  This
module records the *final assembly step* for the eventual Fournais--Solovej
box analysis: it suffices to prove the **per-box grand-canonical two-term
lower bound** (their Theorem LHY-Box / eq. (eq:EnergyBoxRes1), in corpus
form), i.e. for the fixed potential `v`, `A := a v > 0`, some *uniform*
error coefficient `Cw ≥ 0` and exponent `s₀ := 1/2 + η₀`, and the
truncation `ρmax := 2ρ`:

    ∀ᶠ ρ in 𝓝[>] 0, ∃ L₀ ≥ 1, ∀ L ≥ L₀ :
        gcTwoTerm A Cw (1/2 + η₀) ρ ≤ gcDensity v (8πAρ) (2ρ) L

where `gcTwoTerm A Cw s ρ := 4πAρ²·(−1 + c·√(ρA³) − Cw·(ρA³)^s)`
(with `c := 128/(15√π)`), plus the absorption domination
`Cw·(ρA³)^(η₀−η) ≤ K` eventually in `ρ` (automatic for fixed `K > 0`
because `(ρA³)^(η₀−η) → 0`).

The chain (all machine-checked here):
  1. `gcLiminf_ge_of_eventually_ge` (corpus) lifts the eventual per-box
     bound to `gcPressure v (2ρ) (8πAρ) ≥ gcTwoTerm A Cw (1/2+η₀) ρ`;
  2. algebra: `gcTwoTerm A Cw s ρ + 8πAρ² = lhyRhs A Cw s ρ`;
  3. `UniformBox.lhyRhs_le_of_domination` absorbs the `Cw`-error into the
     final `K`-coefficient (exponent `1/2 + η`, `0 < η < η₀`);
  giving exactly `hpres` at `ρmax := 2ρ`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The per-box grand-canonical two-term bound right-hand side (corpus form of
FS eq:EnergyBoxRes1 at chemical potential `8πAρ`): with `c := 128/(15√π)`,
`gcTwoTerm A Cw s ρ := 4πAρ²·(−1 + c·√(ρA³) − Cw·(ρA³)^s)`. -/
noncomputable def gcTwoTerm (A Cw s : ℝ) (ρ : ℝ) : ℝ :=
  (4 * π * A * ρ ^ 2) *
    (-1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - Cw * (ρ * A ^ 3) ^ s)

/-- Adding the FS chemical-potential term `8πAρ·ρ` converts the two-term
grand-canonical value into the canonical LHY right-hand side:
`gcTwoTerm A Cw s ρ + 8πAρ² = lhyRhs A Cw s ρ`. -/
lemma gcTwoTerm_add_chem {A Cw s ρ : ℝ} :
    gcTwoTerm A Cw s ρ + 8 * π * A * ρ * ρ = lhyRhs A Cw s ρ := by
  dsimp [gcTwoTerm, lhyRhs]
  ring

/-- Asymptotic absorption: for fixed `0 ≤ Cw`, `0 < K`, `0 < A` and exponent
`e := η₀ − η > 0`, `Cw·(ρA³)^e ≤ K` holds eventually as `ρ → 0⁺`. -/
lemma eventually_absorp {Cw K A e : ℝ} (hCw : 0 ≤ Cw) (hK : 0 < K) (hA : 0 < A)
    (he : 0 < e) : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), Cw * (ρ * A ^ 3) ^ e ≤ K := by
  by_cases hCw0 : Cw = 0
  · filter_upwards [self_mem_nhdsWithin] with ρ hρ
    simp [hCw0]
    exact hK.le
  · have hCwpos : 0 < Cw := lt_of_le_of_ne hCw (Ne.symm hCw0)
    let δ : ℝ := K / Cw
    have hδpos : 0 < δ := div_pos hK hCwpos
    have hbase : Tendsto (fun ρ : ℝ => ρ * A ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hid : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      have hc : Tendsto (fun _ : ℝ => A ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 (A ^ 3)) :=
        tendsto_const_nhds
      simpa using hid.mul hc
    have hrpow : Tendsto (fun ρ : ℝ => (ρ * A ^ 3) ^ e) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ e)) := by
      exact hbase.rpow tendsto_const_nhds (Or.inr he)
    have hzero : (0 : ℝ) ^ e = 0 := Real.zero_rpow (ne_of_gt he)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (ρ * A ^ 3) ^ e < δ := by
      have hb : ∀ᶠ y : ℝ in 𝓝 ((0 : ℝ) ^ e), y < δ := by
        rw [hzero]
        exact isOpen_Iio.mem_nhds hδpos
      exact hrpow.eventually hb
    have hnonneg : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 ≤ (ρ * A ^ 3) ^ e := by
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact Real.rpow_nonneg (mul_nonneg hρ.le (pow_nonneg hA.le 3)) e
    filter_upwards [hsmall, hnonneg] with ρ hlt hnon
    have hmul : Cw * (ρ * A ^ 3) ^ e < Cw * δ := mul_lt_mul_of_pos_left hlt hCwpos
    have hfin : Cw * (ρ * A ^ 3) ^ e < K := by
      calc
        Cw * (ρ * A ^ 3) ^ e < Cw * δ := hmul
        _ = K := by
          dsimp [δ]
          field_simp [ne_of_gt hCwpos]
    exact le_of_lt hfin

/-- The per-box grand-canonical two-term bound (with truncation `ρmax := 2ρ`)
plus the absorption domination yields `hpres` (with `ρmax := 2ρ`), i.e. the
pressure-level LHY-Background at `μ_corpus := 8πAρ`. -/
theorem hpres_of_gcTwoTerm {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {A η₀ η Cw K : ℝ} (hA : 0 < A) (hη₀ : 0 < η₀) (hη : 0 < η) (hηlt : η < η₀)
    (hCw : 0 ≤ Cw) (hK : 0 < K)
    (hboxg : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ L →
        gcTwoTerm A Cw (1 / 2 + η₀) ρ ≤ gcDensity v (8 * π * A * ρ) (2 * ρ) L)
    (hdom : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), Cw * (ρ * A ^ 3) ^ (η₀ - η) ≤ K) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs A K (1 / 2 + η) ρ ≤ gcPressure v ρmax (8 * π * A * ρ) + 8 * π * A * ρ * ρ := by
  filter_upwards [self_mem_nhdsWithin, hboxg, hdom] with ρ hρpos hboxgρ hdomρ
  have hρ0 : 0 < ρ := by simpa using hρpos
  rcases hboxgρ with ⟨L₀, hL₀1, hbox⟩
  let ρmax : ℝ := 2 * ρ
  have hρmax0 : 0 < ρmax := by
    dsimp [ρmax]
    exact mul_pos (by norm_num) hρ0
  have hρlt : ρ < ρmax := by
    dsimp [ρmax]
    linarith
  have hμ0 : 0 ≤ 8 * π * A * ρ := by
    have h8 : 0 ≤ 8 * π * A := mul_nonneg (by positivity) hA.le
    exact mul_nonneg h8 hρ0.le
  have hρmax0' : 0 ≤ ρmax := hρmax0.le
  have hge : gcTwoTerm A Cw (1 / 2 + η₀) ρ ≤ gcPressure v ρmax (8 * π * A * ρ) := by
    dsimp [ρmax]
    apply gcLiminf_ge_of_eventually_ge (v := v) (μ := 8 * π * A * ρ) (ρmax := 2 * ρ)
      hμ0 hv hv1 (by positivity)
    have hLev : ∀ᶠ L : ℝ in atTop, L₀ ≤ L := Filter.eventually_ge_atTop L₀
    exact hLev.mono (fun L hL => hbox L hL)
  have hdom' : 0 < ρ * A ^ 3 := mul_pos hρ0 (pow_pos hA 3)
  have hle : lhyRhs A K (1 / 2 + η) ρ ≤ lhyRhs A Cw (1 / 2 + η₀) ρ :=
    lhyRhs_le_of_domination (A := A) (C := Cw) (K := K) (η₀ := η₀) (η := η) hA.le hdom' hdomρ
  refine ⟨ρmax, hρmax0, hρlt, ?_⟩
  calc
    lhyRhs A K (1 / 2 + η) ρ ≤ lhyRhs A Cw (1 / 2 + η₀) ρ := hle
    _ = gcTwoTerm A Cw (1 / 2 + η₀) ρ + 8 * π * A * ρ * ρ := (gcTwoTerm_add_chem (A := A) (Cw := Cw) (s := 1 / 2 + η₀) (ρ := ρ)).symm
    _ ≤ gcPressure v ρmax (8 * π * A * ρ) + 8 * π * A * ρ * ρ := add_le_add_left hge (8 * π * A * ρ * ρ)

end Submission.BoseGases
