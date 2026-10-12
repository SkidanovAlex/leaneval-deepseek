import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.DiagLimits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — the upper side of the diagonal limit.

The single quantitative estimate behind the upper side of the diagonal
limit is the *grid-cover* inequality of `DiagUpper` (`diag_le_grid_cover`):
a box of side `L ∈ [G_m, G_{m+1}]`, `G_m := mℓ + (m−1)R`, holding
`⌊ρL³⌋` particles, is covered by the `m³` cells of the grid of side `ℓ`
with spacing `ℓ + R`; every cell takes

    nbar_m := ⌊ρ·G_{m+1}³/m³⌋ + 2

particles.  Dividing through and letting `m → ∞` (with `ℓ`, `R` fixed)
gives, for every cell size `ℓ > 0`:

    diagLimsup v ρ ≤ E(⌊ρ(ℓ+R)³⌋ + 4, ℓ) / (ℓ+R)³            (diagLimsup_le_cell)

because `(m/G_m)³ → (ℓ+R)^{-3}` and `nbar_m` is eventually bounded by
`⌊ρ(ℓ+R)³⌋ + 4`.  Comparing the cell of side `ℓ` with a box of side `ℓ`
at the higher density `ρ' > ρ` (so that `⌊ρ(ℓ+R)³⌋ + 4 ≤ ⌊ρ'ℓ³⌋` for
all large `ℓ`) yields the *upper-side inequality*

    ρ < ρ'  ⟹  diagLimsup v ρ ≤ diagLiminf v ρ'              (diagLimsup_le_diagLiminf_of_lt)

i.e. the limsup of the diagonal at density `ρ` never exceeds the liminf
of the diagonal at any strictly higher density.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Generic eps-argument and elementary floor bounds -/

/-- From `L ≤ (1+δ)·B` for every `δ > 0` (with `0 ≤ B`) conclude `L ≤ B`. -/
lemma le_of_forall_pos_le_smul {L B : ℝ} (hB : 0 ≤ B)
    (h : ∀ δ : ℝ, 0 < δ → L ≤ (1 + δ) * B) : L ≤ B := by
  by_contra hnot
  have hBlt : B < L := lt_of_not_ge hnot
  by_cases hB0 : B = 0
  · have h1 := h 1 (by norm_num)
    have : L ≤ 0 := by simpa [hB0] using h1
    linarith
  · have hBpos : 0 < B := lt_of_le_of_ne hB (by intro hb; exact hB0 hb.symm)
    let δ : ℝ := (L - B) / (2 * B)
    have hδ0 : 0 < δ := by
      dsimp [δ]
      exact div_pos (sub_pos.mpr hBlt) (mul_pos (by norm_num) hBpos)
    have hδ := h δ hδ0
    have hcalc : (1 + δ) * B < L := by
      dsimp [δ]
      field_simp [hB0]
      nlinarith
    linarith

/-- `⌊x+1⌋ = ⌊x⌋ + 1` for `0 ≤ x`. -/
lemma Nat_floor_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.floor (x + 1) = Nat.floor x + 1 := by
  apply le_antisymm
  · have hle0 : 0 ≤ x + 1 := by linarith
    have hfl : (Nat.floor (x + 1) : ℝ) ≤ x + 1 := Nat.floor_le hle0
    have hx2 : x + 1 < (Nat.floor x : ℝ) + 2 := by
      have hlt := Nat.lt_floor_add_one x
      nlinarith
    have h : (Nat.floor (x + 1) : ℝ) < (Nat.floor x : ℝ) + 2 := lt_of_le_of_lt hfl hx2
    have hh : Nat.floor (x + 1) < Nat.floor x + 2 := by exact_mod_cast h
    omega
  · have hle0 : 0 ≤ x + 1 := by linarith
    apply (Nat.le_floor_iff hle0).2
    have hfl : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
    -- ((⌊x⌋+1 : ℕ) : ℝ) ≤ x + 1
    have hh : ((Nat.floor x + 1 : ℕ) : ℝ) ≤ x + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith
    simpa [Nat.cast_add, Nat.cast_one] using hh

/-- If `a ≤ x + 1` and `0 ≤ x` then `⌊a⌋ + 2 ≤ ⌊x⌋ + 4`. -/
lemma floor_add_two_le_add_four {a x : ℝ} (ha : a ≤ x + 1) (hx : 0 ≤ x) :
    Nat.floor a + 2 ≤ Nat.floor x + 4 := by
  by_cases ha0 : 0 ≤ a
  · have hfl : (Nat.floor a : ℝ) ≤ a := Nat.floor_le ha0
    have hx4 : x + 1 + 2 ≤ (Nat.floor x : ℝ) + 4 := by
      have hlt := Nat.lt_floor_add_one x
      nlinarith
    have hmain : (Nat.floor a : ℝ) + 2 ≤ (Nat.floor x : ℝ) + 4 := by nlinarith
    exact_mod_cast hmain
  · have hneg : a < 0 := lt_of_not_ge ha0
    have hfa : Nat.floor a = 0 := by
      apply le_antisymm
      · -- floor a ≤ 0: since a < 0, floor is 0 (clamped)
        have : Nat.floor a < 1 := by
          -- floor a < 1 since a < 1;  a < 0 ≤ ...: floor_lt with 0 ≤ a fails (a<0). Use: floor a ≤ 0:
          -- ⌊a⌋₊ ≤ ⌊0⌋₊? floor_mono: a ≤ 0 ⟹ floor a ≤ floor 0 = 0
          have hm := Nat.floor_mono (a := a) (b := 0) (le_of_lt hneg)
          simpa using hm
        omega
      · exact Nat.zero_le _
    omega

/-- An integer `m ≤ y` with `0 ≤ y` satisfies `m ≤ ⌊y⌋`: applied to
`m = ⌊x⌋+4` under the real bound `x + 4 ≤ y`. -/
lemma floor_add_four_le_floor {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + 4 ≤ y) :
    Nat.floor x + 4 ≤ Nat.floor y := by
  have hxfl : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
  have hm : (Nat.floor x : ℝ) + 4 ≤ y := by nlinarith
  apply (Nat.le_floor_iff hy).2
  have hc : ((Nat.floor x + 4 : ℕ) : ℝ) = (Nat.floor x : ℝ) + 4 := by
    rw [Nat.cast_add, Nat.cast_ofNat]
  rw [hc]
  exact hm

/-- Density drift for the cell particle number: under the real arithmetic
condition `ρ(ℓ+R)³ + 4 ≤ ρ'ℓ³`, the cell number `⌊ρ(ℓ+R)³⌋+4` fits in a box
of side `ℓ` at density `ρ'`. -/
lemma cell_particles_density_drift {ρ ρ' ℓ R : ℝ} (hρ : 0 ≤ ρ) (hρρ' : ρ < ρ')
    (hR : 0 ≤ R) (hℓ : 0 < ℓ) (hcond : ρ * (ℓ + R) ^ 3 + 4 ≤ ρ' * ℓ ^ 3) :
    Nat.floor (ρ * (ℓ + R) ^ 3) + 4 ≤ Nat.floor (ρ' * ℓ ^ 3) := by
  have hρ' : 0 ≤ ρ' := le_of_lt (lt_of_le_of_lt hρ hρρ')
  have hx : 0 ≤ ρ * (ℓ + R) ^ 3 := mul_nonneg hρ (pow_nonneg (by linarith) 3)
  have hy : 0 ≤ ρ' * ℓ ^ 3 := mul_nonneg hρ' (pow_nonneg hℓ.le 3)
  exact floor_add_four_le_floor hx hy hcond

/-- Arithmetic lemma: for `1 ≤ ℓ`, `R ≤ ℓ`, `ℓ₂ ≤ ℓ` with
`ℓ₂ = (12ρR + 4)/(ρ'−ρ)`, one has `ρ(ℓ+R)³ + 4 ≤ ρ'ℓ³`. -/
lemma cell_cond_of_large {ρ ρ' ℓ R : ℝ} (hρ : 0 ≤ ρ) (hρρ' : ρ < ρ') (hR : 0 ≤ R)
    (hℓ1 : 1 ≤ ℓ) (hℓR : R ≤ ℓ) :
    (ρ' - ρ) * ℓ ≥ 12 * ρ * R + 4 → ρ * (ℓ + R) ^ 3 + 4 ≤ ρ' * ℓ ^ 3 := by
  intro hbig
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hℓp : 0 < ℓ := by linarith
  have hsq : (ℓ + R) ^ 2 ≤ 4 * ℓ ^ 2 := by
    have h1 : 2 * ℓ * R ≤ 2 * ℓ ^ 2 := by
      have hlr : ℓ * R ≤ ℓ ^ 2 := by
        simpa [pow_two] using mul_le_mul_of_nonneg_left hℓR hℓ0
      nlinarith
    have h2 : R ^ 2 ≤ ℓ ^ 2 := by
      have hm := mul_le_mul hℓR hℓR hR hℓ0
      simpa [pow_two] using hm
    nlinarith
  have hdiff : (ℓ + R) ^ 3 - ℓ ^ 3 ≤ 3 * R * (ℓ + R) ^ 2 := by
    have hmain : (ℓ + R) ^ 3 - ℓ ^ 3 = 3 * ℓ ^ 2 * R + 3 * ℓ * R ^ 2 + R ^ 3 := by ring
    have hrhs : 3 * R * (ℓ + R) ^ 2 = 3 * ℓ ^ 2 * R + 6 * ℓ * R ^ 2 + 3 * R ^ 3 := by ring
    rw [hmain, hrhs]
    have hRR : 0 ≤ R ^ 2 := sq_nonneg R
    nlinarith [mul_nonneg hℓ0 hRR, mul_nonneg hR hRR]
  have hdiff' : (ℓ + R) ^ 3 - ℓ ^ 3 ≤ 12 * R * ℓ ^ 2 := by
    have hle : 3 * R * (ℓ + R) ^ 2 ≤ 12 * R * ℓ ^ 2 := by
      have hR3 : 0 ≤ 3 * R := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq hR3]
    nlinarith
  -- (ρ'−ρ)ℓ ≥ 12ρR + 4 ⟹ (ρ'−ρ)ℓ³ ≥ 12ρRℓ² + 4
  have hbig3 : (ρ' - ρ) * ℓ ^ 3 ≥ 12 * ρ * R * ℓ ^ 2 + 4 := by
    have hm : (ρ' - ρ) * ℓ * ℓ ^ 2 ≥ (12 * ρ * R + 4) * ℓ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hbig (sq_nonneg ℓ)
    have hquad : (12 * ρ * R + 4) * ℓ ^ 2 ≥ 12 * ρ * R * ℓ ^ 2 + 4 := by
      have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith [sq_nonneg ℓ]  -- 1 ≤ ℓ ⟹ 1 ≤ ℓ²: (ℓ−1)(ℓ+1) ≥ 0
      nlinarith
    nlinarith
  nlinarith

/-- Density drift, eventual form: for `ρ' > ρ ≥ 0`, for all sufficiently large
`ℓ`, `⌊ρ(ℓ+R)³⌋+4 ≤ ⌊ρ'ℓ³⌋`. -/
lemma cell_particles_density_drift_eventually {ρ ρ' R : ℝ} (hρ : 0 ≤ ρ) (hρρ' : ρ < ρ')
    (hR : 0 ≤ R) :
    ∀ᶠ ℓ : ℝ in atTop,
      Nat.floor (ρ * (ℓ + R) ^ 3) + 4 ≤ Nat.floor (ρ' * ℓ ^ 3) := by
  have hdiffpos : 0 < ρ' - ρ := sub_pos.mpr hρρ'
  let ℓ₂ : ℝ := (12 * ρ * R + 4) / (ρ' - ρ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop R,
    eventually_ge_atTop ℓ₂] with ℓ hℓ1 hℓR hℓ2
  have hbig : (ρ' - ρ) * ℓ ≥ 12 * ρ * R + 4 := by
    have hc := (div_le_iff₀ hdiffpos).mp hℓ2
    -- hℓ2 : ℓ₂ ≤ ℓ i.e. (12ρR+4)/(ρ'−ρ) ≤ ℓ: multiply
    have hm := mul_le_mul_of_nonneg_right hc hdiffpos.le
    field_simp [hdiffpos.ne'] at hm
    -- hm : 12ρR+4 ≤ (ρ'-ρ)·ℓ  hmm orientation
    nlinarith
  have hcond := cell_cond_of_large hρ hρρ' hR hℓ1 hℓR hbig
  have hℓpos : 0 < ℓ := by linarith
  exact cell_particles_density_drift hρ hρρ' hR hℓpos hcond

/-! ## Grid rescaling and cell bound -/

/-- The cell ratio `G_{m+1}³/m³ → (ℓ+R)³` (for `ℓ > 0`). -/
lemma tendsto_cell_ratio {ℓ R : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun m : ℕ => gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3) atTop
      (𝓝 ((ℓ + R) ^ 3)) := by
  have hℓdiv : Tendsto (fun m : ℕ => ℓ / (m : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ℓ
  have hs : Tendsto (fun m : ℕ => (ℓ + R) + ℓ / (m : ℝ)) atTop (𝓝 (ℓ + R)) := by
    simpa using (tendsto_const_nhds.add hℓdiv)
  have hsc : Tendsto (fun m : ℕ => ((ℓ + R) + ℓ / (m : ℝ)) ^ 3) atTop (𝓝 ((ℓ + R) ^ 3)) := by
    simpa using hs.pow 3
  apply hsc.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hm))
  have hsm : (ℓ + R) + ℓ / (m : ℝ) = gridSide (m + 1) ℓ R / (m : ℝ) := by
    unfold gridSide
    push_cast
    field_simp [hmne]
    ring
  rw [hsm]
  ring

/-- Eventual bound on the cell particle number from below by the asymptotic
value: `nbar_m ≤ ⌊ρ(ℓ+R)³⌋ + 4` eventually in `m`. -/
lemma cell_nbar_eventually_le {ρ ℓ R : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < ℓ) (hR : 0 ≤ R) :
    ∀ᶠ m : ℕ in atTop,
      Nat.floor (ρ * gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3) + 2 ≤
        Nat.floor (ρ * (ℓ + R) ^ 3) + 4 := by
  have hcell := tendsto_cell_ratio (ℓ := ℓ) (R := R) hℓ
  have ha : Tendsto (fun m : ℕ => ρ * gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3) atTop
      (𝓝 (ρ * (ℓ + R) ^ 3)) := by
    simpa [div_eq_mul_inv, mul_assoc] using hcell.const_mul ρ
  have hx0 : 0 ≤ ρ * (ℓ + R) ^ 3 := mul_nonneg hρ (pow_nonneg (by linarith : 0 ≤ ℓ + R) 3)
  have hlt : ρ * (ℓ + R) ^ 3 < ρ * (ℓ + R) ^ 3 + 1 := by linarith
  have hev : ∀ᶠ m : ℕ in atTop,
      ρ * gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3 < ρ * (ℓ + R) ^ 3 + 1 :=
    ha.eventually (isOpen_Iio.mem_nhds hlt)
  filter_upwards [hev] with m ham
  have hamle : ρ * gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3 ≤ ρ * (ℓ + R) ^ 3 + 1 := le_of_lt ham
  exact floor_add_two_le_add_four hamle hx0

/-- Grid-cell upper bound on the limsup of the diagonal: with cells of side
`ℓ` placed on the `(ℓ+R)`-grid, a density-`ρ` box is no worse than its cells.
-/
lemma diagLimsup_le_cell {v : ℝ³ → ℝ} {ρ ℓ R : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρ : 0 ≤ ρ) (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    diagLimsup v ρ ≤ boxEnergy (Nat.floor (ρ * (ℓ + R) ^ 3) + 4) ℓ v / (ℓ + R) ^ 3 := by
  let ncell : ℕ := Nat.floor (ρ * (ℓ + R) ^ 3) + 4
  let Ecell : ℝ := boxEnergy ncell ℓ v
  let B : ℝ := Ecell * ((ℓ + R) ^ 3)⁻¹
  have hE0 : 0 ≤ Ecell := boxEnergy_nonneg hℓ hv
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hE0 (inv_nonneg.mpr (pow_nonneg (by linarith : 0 ≤ ℓ + R) 3))
  have hmain : ∀ δ : ℝ, 0 < δ → diagLimsup v ρ ≤ (1 + δ) * B := by
    intro δ hδ
    -- combine the eventual-in-m facts into a pointwise window bound
    have hnb := cell_nbar_eventually_le hρ hℓ hR
    have hcb := grid_cube_eventually_le hℓ hR hδ
    have hall : ∀ᶠ m : ℕ in atTop,
        ∀ (L : ℝ), gridSide m ℓ R ≤ L → L ≤ gridSide (m + 1) ℓ R →
          diag v ρ L ≤ (1 + δ) * B := by
      filter_upwards [hnb, hcb, eventually_ge_atTop (1 : ℕ)] with m hnb' hcb' hm1
      intro L hLlo hLhi
      have hLpos : 0 < L := lt_of_lt_of_le hℓ (by
        -- gridSide m ≥ gridSide 1 = ℓ (m ≥ 1)
        have hm1' : 1 ≤ m := hm1
        have hmono := gridSide_mono (m := 1) (n := m) hℓ.le hR hm1'
        rw [gridSide_one] at hmono
        exact le_trans hmono hLlo)
      have hGpos : 0 < gridSide m ℓ R := gridSide_pos hm1 hℓ hR
      have hcov := diag_le_grid_cover (ρ := ρ) (L := L) (ℓ := ℓ) (R := R) (m := m)
        hρ hm1 hℓ hR hLpos hGpos hLlo hLhi (v := v) hv hv1 hsupp
      have hN : Nat.floor (ρ * gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3) + 2 ≤ ncell := by
        dsimp [ncell]
        exact hnb'
      have hEn : boxEnergy (Nat.floor (ρ * gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3) + 2) ℓ v ≤ Ecell := by
        dsimp [Ecell]
        exact boxEnergy_mono_N hℓ hv hv1 hN
      have hcm : (m : ℝ) ^ 3 / gridSide m ℓ R ^ 3 ≤ (1 + δ) * ((ℓ + R) ^ 3)⁻¹ := hcb'
      have hc0 : 0 ≤ (m : ℝ) ^ 3 / gridSide m ℓ R ^ 3 := by
        have hmr : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm1)
        exact div_nonneg (pow_nonneg hmr.le 3) (pow_nonneg hGpos.le 3)
      calc
        diag v ρ L ≤ ((m : ℝ) ^ 3 / gridSide m ℓ R ^ 3) *
            boxEnergy (Nat.floor (ρ * gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3) + 2) ℓ v := hcov
        _ ≤ ((m : ℝ) ^ 3 / gridSide m ℓ R ^ 3) * Ecell :=
          mul_le_mul_of_nonneg_left hEn hc0
        _ ≤ (1 + δ) * ((ℓ + R) ^ 3)⁻¹ * Ecell := by
          exact mul_le_mul_of_nonneg_right hcm hE0
        _ = (1 + δ) * B := by
          dsimp [B]
          ring
    -- limsup ≤ (1+δ)B from the eventual window bound
    have hev : ∀ᶠ L : ℝ in atTop, diag v ρ L ≤ (1 + δ) * B := by
      rcases eventually_atTop.mp hall with ⟨M₀, hM₀⟩
      refine eventually_atTop.mpr ⟨gridSide (M₀ + 1) ℓ R, ?_⟩
      intro L hLbig
      let m := gridWinIdx ℓ R L
      have hLge1 : ℓ ≤ L := by
        have hmono := gridSide_mono (m := 1) (n := M₀ + 1) hℓ.le hR (by omega)
        rw [gridSide_one] at hmono
        exact le_trans hmono hLbig
      have hmM : M₀ ≤ m := by
        have hmm := gridWinIdx_ge_of_gridSide hℓ hR hLbig
        dsimp [m]
        omega
      have hlo : gridSide m ℓ R ≤ L := gridWinIdx_lower hℓ hR hLge1
      have hhi : L ≤ gridSide (m + 1) ℓ R := gridWinIdx_upper hℓ hR hLge1
      have hMm : ∀ (L' : ℝ), gridSide m ℓ R ≤ L' → L' ≤ gridSide (m + 1) ℓ R →
          diag v ρ L' ≤ (1 + δ) * B := hM₀ m hmM
      exact hMm L hlo hhi
    unfold diagLimsup
    exact limsup_le_of_eventually_le (u := fun L : ℝ => diag v ρ L) (B := (1 + δ) * B)
      hev (diag_eventually_nonneg hv)
  have hfinal : diagLimsup v ρ ≤ B := le_of_forall_pos_le_smul hB0 hmain
  -- conclusion with division instead of inverse
  simpa [ncell, Ecell, B, div_eq_mul_inv] using hfinal

/-! ## Upper-side inequality of the diagonal limit -/

/-- The limsup of the diagonal at density `ρ` is no larger than the liminf of
the diagonal at any strictly larger density. -/
lemma diagLimsup_le_diagLiminf_of_lt {v : ℝ³ → ℝ} {ρ ρ' : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hρ : 0 ≤ ρ) (hρρ' : ρ < ρ') : diagLimsup v ρ ≤ diagLiminf v ρ' := by
  let x : ℝ := diagLimsup v ρ
  have hρ' : 0 ≤ ρ' := le_of_lt (lt_of_le_of_lt hρ hρρ')
  -- for every large cell size ℓ: x ≤ diag v ρ' ℓ
  have hev : ∀ᶠ ℓ : ℝ in atTop, x ≤ diag v ρ' ℓ := by
    filter_upwards [cell_particles_density_drift_eventually (ρ := ρ) (ρ' := ρ') hρ hρρ' hR,
      eventually_ge_atTop (1 : ℝ)] with ℓ hdr hℓ1
    have hℓ : 0 < ℓ := by linarith
    have hcell := diagLimsup_le_cell (v := v) (ρ := ρ) (ℓ := ℓ) (R := R) hv hv1 hρ hℓ hR hsupp
    have hN : Nat.floor (ρ * (ℓ + R) ^ 3) + 4 ≤ Nat.floor (ρ' * ℓ ^ 3) := hdr
    have hmono : boxEnergy (Nat.floor (ρ * (ℓ + R) ^ 3) + 4) ℓ v ≤
        boxEnergy (Nat.floor (ρ' * ℓ ^ 3)) ℓ v :=
      boxEnergy_mono_N hℓ hv hv1 hN
    have hpart : boxEnergy (Nat.floor (ρ * (ℓ + R) ^ 3) + 4) ℓ v / (ℓ + R) ^ 3 ≤
        (ℓ / (ℓ + R)) ^ 3 * diag v ρ' ℓ := by
      have hEq : boxEnergy (Nat.floor (ρ' * ℓ ^ 3)) ℓ v / (ℓ + R) ^ 3 =
          (ℓ / (ℓ + R)) ^ 3 * diag v ρ' ℓ := by
        dsimp [diag]
        field_simp [pow_ne_zero 3 (ne_of_gt hℓ)]
      calc
        boxEnergy (Nat.floor (ρ * (ℓ + R) ^ 3) + 4) ℓ v / (ℓ + R) ^ 3
            ≤ boxEnergy (Nat.floor (ρ' * ℓ ^ 3)) ℓ v / (ℓ + R) ^ 3 :=
              div_le_div_of_nonneg_right hmono (pow_nonneg (by linarith : 0 ≤ ℓ + R) 3)
        _ = (ℓ / (ℓ + R)) ^ 3 * diag v ρ' ℓ := hEq
    have hsmall : (ℓ / (ℓ + R)) ^ 3 * diag v ρ' ℓ ≤ diag v ρ' ℓ := by
      have hc : (ℓ / (ℓ + R)) ^ 3 ≤ 1 := by
        have hle1 : ℓ / (ℓ + R) ≤ 1 := by
          rw [div_le_one₀ (by linarith : 0 < ℓ + R)]
          linarith
        exact pow_le_one₀ (by positivity) hle1
      have hd : 0 ≤ diag v ρ' ℓ := diag_nonneg hv hℓ
      nlinarith [mul_le_mul_of_nonneg_right hc hd]
    have htr : diagLimsup v ρ ≤ (ℓ / (ℓ + R)) ^ 3 * diag v ρ' ℓ := le_trans hcell hpart
    -- (ℓ/(ℓ+R))^3 * diag ≤ diag ≤ ... hmm need: x ≤ diag
    have hfin : diagLimsup v ρ ≤ diag v ρ' ℓ := le_trans htr hsmall
    dsimp [x]
    exact hfin
  -- x ∈ {a | ∀ᶠ ℓ, a ≤ diag v ρ' ℓ}, and that set is bounded above
  rw [diagLiminf, liminf_eq]
  apply le_csSup
  · rcases diag_eventually_bdd_above (v := v) (ρ := ρ') hv1 hρ' with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro a ha
    exact atTop_le_of_eventually ha hB
  · simpa [x] using hev

end BoseGases

end Submission
