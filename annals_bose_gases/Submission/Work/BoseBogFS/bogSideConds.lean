import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogCellBounds
import Submission.Work.BoseBogFS.honestFsCutoffRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogSideConds` — the four side conditions of the bulk cells

`Work.BoseBogFS.bogCellAll` (the assembled per-cell bound of the clean Riemann row)
consumes four side conditions on the *far* cells (region C, `16√Vs < r_hi`):

* `0 < bogULot v ρ μ n` (`= τ_s(r_lo) > 0`),
* `bogUHit v ρ μ n ≤ (bogRLot v ρ μ n)²`,
* `0 < bogULot v ρ μ n + 2·bogVlot v h R ρ μ n` (`τ_s(r_lo) + 2β_lo > 0`),
* `2·bogBs v R ≤ bogULot v ρ μ n`.

This module proves that all four hold *automatically* on the far cells, uniformly in the state:
there is a diluteness threshold `X₀ > 0` (here `1/1000`) such that for every admissible data
(`Core v R μ ρ`, `fsX v μ ≤ X₀`, `R ≤ ℓ·chiR0`) and every far cell `n ≠ 0`
(`bogBigThr v R ρ μ < bogRHit v ρ μ n`), the four conditions hold.

## The mathematics

Write `Δ = bogHalf v ρ μ`, `δ = bogMesh v ρ μ`, `cᵢ = bogCᵢ v ρ μ`, `X = fsX v μ`,
`ε_T = (paramsAt μ (a v)).eT`, `Vs = bogVs v R ρ μ` (so `bogBigThr = 16√Vs`).

* The **mesh identity** `Δ = 2π√3·X·c₁` (from `c₁ = (2 s ℓ √(ρa))⁻¹`, `δ = (2π/ℓ)/√(ρa)`
  and `s = X`, the field `s` of the parameter block): so `2Δ = 4π√3Xc₁` and `4Δ = 8π√3Xc₁`.
* `Vs ≥ bogBs ≥ 1` and `c₁ ≤ 1` (`Core`); hence with `X ≤ 1/1000`:
  `2Δ + 2c₁ ≤ 4 ≤ 4√Vs`.
* The far condition gives `r_lo = r_hi - 2Δ > 16√Vs - 2Δ ≥ 12√Vs + 2c₁`, so
  `r_lo - 2c₁ ≥ 12√Vs`; the profile kink bound `c²τ̃(r/c) ≥ (max 0 (r-2c))²` then gives

      bogULot = τ_s(r_lo) ≥ (1-ε_T)·144·Vs .

  Since `1 - ε_T ≥ 1/2` and `Vs ≥ bogBs + bogOm`, this yields conditions 1, 3, 4
  (`|β| ≤ bogBs` supplies `bogVlot ≥ -bogBs - bogOm`).
* For condition 2 the *deficit* row is used instead: for `r ≥ c₁`,
  `r² - τ_s(r) ≥ (1-ε_T)c₁r` (from `τ̃(u) ≤ (max 0 (u-1))²` on the first term and
  `τ̃(u) ≤ u²`, `ε_T ≥ 0` on the second).  With `4Δ ≤ (1-ε_T)c₁` (again `X ≤ 1/1000`)
  and `r_hi ≥ ‖tSca‖` this gives `r_hi² - bogUHit ≥ 4Δ‖tSca‖ = r_hi² - r_lo²`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary profile and `Core` rows -/

lemma sb_tauProf_nonneg (u : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf u := by
  have h := Work.BoseBoxFock.tauProf_spec.2.2.1 u
  nlinarith [sq_nonneg (max 0 (u - 2))]

/-- The profile kink bound `(max 0 (r-2c))² ≤ c²τ̃(r/c)` for `c > 0`. -/
lemma sb_kink {c r : ℝ} (hc : 0 < c) :
    (max 0 (r - 2 * c)) ^ 2 ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) := by
  have h1 : (max 0 (r / c - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf (r / c) :=
    Work.BoseBoxFock.tauProf_spec.2.2.1 (r / c)
  have h2 : max 0 (r - 2 * c) = c * max 0 (r / c - 2) := by
    rw [mul_max_of_nonneg 0 (r / c - 2) hc.le]
    congr 1
    · ring
    · field_simp
  rw [h2]
  calc (c * max 0 (r / c - 2)) ^ 2 = c ^ 2 * (max 0 (r / c - 2)) ^ 2 := by ring
    _ ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg c)

/-- The `c₀`-free upper row: `c²τ̃(r/c) ≤ r²` for `c > 0`. -/
lemma sb_tau_le_sq {c r : ℝ} (hc : 0 < c) :
    c ^ 2 * Work.BoseBoxFock.tauProf (r / c) ≤ r ^ 2 := by
  have h := Work.BoseBoxFock.tauProf_le_max_sq (r / c)
  rcases le_or_gt 0 (r / c) with h0 | h0
  · have h2 : max 0 (r / c - 1) ≤ r / c := max_le h0 (by linarith)
    have h3 : (max 0 (r / c - 1)) ^ 2 ≤ (r / c) ^ 2 := pow_le_pow_left₀ (le_max_left _ _) h2 2
    have h4 : c ^ 2 * (r / c) ^ 2 = r ^ 2 := by field_simp
    calc c ^ 2 * Work.BoseBoxFock.tauProf (r / c)
        ≤ c ^ 2 * (r / c) ^ 2 := mul_le_mul_of_nonneg_left (le_trans h h3) (sq_nonneg c)
      _ = r ^ 2 := h4
  · have hmax : max 0 (r / c - 1) = 0 := max_eq_left (by linarith)
    rw [hmax] at h
    have hz : Work.BoseBoxFock.tauProf (r / c) = 0 :=
      le_antisymm (by simpa using h) (sb_tauProf_nonneg _)
    rw [hz, mul_zero]
    exact sq_nonneg r

/-- **The lower kink row of the symbol**: `(1-ε_T)(max 0 (r-2c₁))² ≤ τ_s(r)`. -/
lemma sb_tau_ge_shift {v : E3 → ℝ} {ρ μ : ℝ} (hP : 0 < ρ * a v)
    (hc1 : 0 < bogC1 v ρ μ) (heT0 : 0 ≤ (paramsAt μ (a v)).eT)
    (heT1 : (paramsAt μ (a v)).eT ≤ 1) (r : ℝ) :
    (1 - (paramsAt μ (a v)).eT) * (max 0 (r - 2 * bogC1 v ρ μ)) ^ 2 ≤ tauScRad v ρ μ r := by
  rw [tauScRad_eq v hP r]
  have hkey := sb_kink (c := bogC1 v ρ μ) (r := r) hc1
  have hw : 0 ≤ 1 - (paramsAt μ (a v)).eT := by linarith
  have hT2 : 0 ≤ (paramsAt μ (a v)).eT * bogC2 v ρ μ ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (sb_tauProf_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hkey hw, hT2]

/-- **The deficit row of the symbol**: for `r ≥ c₁`, `(1-ε_T)c₁r ≤ r² - τ_s(r)`. -/
lemma sb_tau_sub_ge {v : E3 → ℝ} {ρ μ : ℝ} (hP : 0 < ρ * a v)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1)
    {r : ℝ} (hr : bogC1 v ρ μ ≤ r) :
    (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ * r ≤ r ^ 2 - tauScRad v ρ μ r := by
  rw [tauScRad_eq v hP r]
  set eT := (paramsAt μ (a v)).eT with heTdef
  set c1 := bogC1 v ρ μ with hc1def
  set c2 := bogC2 v ρ μ with hc2def
  have hw : 0 ≤ 1 - eT := by rw [heTdef]; linarith
  have hm1 : max 0 (r / c1 - 1) = (r - c1) / c1 := by
    have hge : (0 : ℝ) ≤ r / c1 - 1 := by
      rw [sub_nonneg, le_div_iff₀ hc1]; linarith
    rw [max_eq_right hge]; field_simp
  have hA : c1 ^ 2 * Work.BoseBoxFock.tauProf (r / c1) ≤ r ^ 2 - c1 * r := by
    have h := Work.BoseBoxFock.tauProf_le_max_sq (r / c1)
    rw [hm1] at h
    have h2 : c1 ^ 2 * ((r - c1) / c1) ^ 2 = (r - c1) ^ 2 := by field_simp
    have h3 : (r - c1) ^ 2 ≤ r ^ 2 - c1 * r := by nlinarith [hr, hc1]
    calc c1 ^ 2 * Work.BoseBoxFock.tauProf (r / c1)
        ≤ c1 ^ 2 * ((r - c1) / c1) ^ 2 := mul_le_mul_of_nonneg_left h (sq_nonneg c1)
      _ = (r - c1) ^ 2 := h2
      _ ≤ r ^ 2 - c1 * r := h3
  have hB : c2 ^ 2 * Work.BoseBoxFock.tauProf (r / c2) ≤ r ^ 2 := sb_tau_le_sq hc2
  have hA' : (1 - eT) * (c1 ^ 2 * Work.BoseBoxFock.tauProf (r / c1))
      ≤ (1 - eT) * (r ^ 2 - c1 * r) := mul_le_mul_of_nonneg_left hA hw
  have hB' : eT * (c2 ^ 2 * Work.BoseBoxFock.tauProf (r / c2)) ≤ eT * r ^ 2 :=
    mul_le_mul_of_nonneg_left hB (by rw [heTdef]; exact heT0)
  nlinarith [hA', hB']

/-- `ℓ > 0` from `Core`. -/
lemma sb_ell_pos {v : E3 → ℝ} {R μ ρ : ℝ} (hav : 0 < a v) (hC : Core v R μ ρ) :
    0 < ell v μ := by
  rw [ell_eq_boxSide]
  exact mul_pos (by rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos hC.hD0 _)
    (Real.rpow_pos_of_pos (mul_pos hC.hμ hav) _)

/-- `c₁ > 0` from `Core`. -/
lemma sb_c1_pos {v : E3 → ℝ} {R μ ρ : ℝ} (hav : 0 < a v) (hC : Core v R μ ρ) :
    0 < bogC1 v ρ μ := by
  rw [bogC1_eq_dil v ρ μ hav hC.hμ hC.hρ0 hC.hD0]
  have h1 : 0 < (dil v μ) ^ ((1 : ℝ) / 646) := Real.rpow_pos_of_pos hC.hD0 _
  have h2 : 0 < Real.sqrt (μ / ρ) := Real.sqrt_pos.mpr (div_pos hC.hμ hC.hρ0)
  positivity

/-- `c₂ > 0` from `Core`. -/
lemma sb_c2_pos {v : E3 → ℝ} {R μ ρ : ℝ} (hav : 0 < a v) (hC : Core v R μ ρ) :
    0 < bogC2 v ρ μ := by
  rw [bogC2_eq_dil v ρ μ hav hC.hμ hC.hρ0 hC.hD0]
  have h1 : 0 < (dil v μ) ^ (-(11 / 646) : ℝ) := Real.rpow_pos_of_pos hC.hD0 _
  have h2 : 0 < Real.sqrt (μ / ρ) := Real.sqrt_pos.mpr (div_pos hC.hμ hC.hρ0)
  positivity

/-- `c₁ ≤ 1` from `Core`. -/
lemma sb_c1_le_one {v : E3 → ℝ} {R μ ρ : ℝ} (hav : 0 < a v) (hC : Core v R μ ρ) :
    bogC1 v ρ μ ≤ 1 := by
  rw [bogC1_eq_dil v ρ μ hav hC.hμ hC.hρ0 hC.hD0]
  have h1 : (dil v μ) ^ ((1 : ℝ) / 646) ≤ 1 :=
    Real.rpow_le_one hC.hD0.le hC.hD1 (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.sqrt (μ / ρ) := Real.sqrt_nonneg _
  nlinarith [h1, h2, hC.hρsqrt]

/-- `ε_T ≤ 1/2` from `Core`. -/
lemma sb_eT_half {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    (paramsAt μ (a v)).eT ≤ 1 / 2 := by
  rw [paramsAt_eT]
  have h23 : (dil v μ) ^ ((23 : ℝ) / 1292) ≤ (dil v μ) ^ ((1 : ℝ) / 1292) :=
    Real.rpow_le_rpow_of_exponent_ge hC.hD0 hC.hD1 (by norm_num)
  linarith [h23, hC.hDs]

/-- `0 ≤ fsX v μ`. -/
lemma sb_fsX_nonneg {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    0 ≤ Work.BoseFixR.fsX v μ := by
  rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp]
  exact Real.rpow_nonneg (mul_pos hμ (pow_pos hav 3)).le _

/-- `bogOm v h R ρ μ n ≤ bogOscM v R ρ μ`. -/
lemma sb_om_le_oscM {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hR : 0 ≤ R) (hρ : 0 < ρ) (hav : 0 < a v) (hδ : 0 < bogMesh v ρ μ) (hn : n ≠ 0) :
    bogOm v h R ρ μ n ≤ bogOscM v R ρ μ := by
  rw [bogOm, bogOscK, bogOscM]
  have hrlo : 0 ≤ bogRLot v ρ μ n := (bogRLo_pos hδ hn).le
  have hnum : 0 ≤ bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ :=
    mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3))
      (Real.sqrt_nonneg _)) (bogHalf_pos hδ).le
  have hden : 1 ≤ 1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n := by
    have := mul_nonneg (Real.sqrt_nonneg (ρ * a v)) hrlo
    linarith
  exact div_le_self hnum hden

/-! ## 2. The mesh/cutoff identity `2Δ = 4π√3·X·c₁` -/

/-- **The mesh identity**: `2·bogHalf v ρ μ = 4π√3·X·bogC1 v ρ μ` with `X = fsX v μ`
(here `bogHalf = δ√3/2`, `δ = (2π/ℓ)/√(ρa)`, `c₁ = (2Xℓ√(ρa))⁻¹` and `X` is the field
`s` of the parameter block). -/
theorem sb_half_eq {v : E3 → ℝ} {ρ μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hℓ : 0 < ell v μ) :
    2 * bogHalf v ρ μ = (4 * Real.pi * Real.sqrt 3 * Work.BoseFixR.fsX v μ) * bogC1 v ρ μ := by
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hs : (paramsAt μ (a v)).s = Work.BoseFixR.fsX v μ := rfl
  have hsq : Real.sqrt (ρ * a v) ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  have hX : Work.BoseFixR.fsX v μ ≠ 0 := by
    rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp]
    exact (Real.rpow_pos_of_pos (mul_pos hμ (pow_pos hav 3)) _).ne'
  rw [bogHalf, bogMesh, bogC1, hs]
  field_simp
  ring

/-! ## 3. The side conditions -/

theorem bogSideConds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ {h : Work.UBB.ScatSol v} {ρ μ : ℝ} {n : Fin 3 → ℤ},
      Work.BoseBogFS.Core v R μ ρ → n ≠ 0 → Work.BoseFixR.fsX v μ ≤ X₀ →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      Work.BoseBogFS.bogBigThr v R ρ μ < Work.BoseBogFS.bogRHit v ρ μ n →
      (0 < Work.BoseBogFS.bogULot v ρ μ n
        ∧ Work.BoseBogFS.bogUHit v ρ μ n ≤ (Work.BoseBogFS.bogRLot v ρ μ n) ^ 2
        ∧ 0 < Work.BoseBogFS.bogULot v ρ μ n + 2 * Work.BoseBogFS.bogVlot v h R ρ μ n
        ∧ 2 * Work.BoseBogFS.bogBs v R ≤ Work.BoseBogFS.bogULot v ρ μ n) := by
  refine ⟨1 / 1000, by norm_num, ?_⟩
  intro h ρ μ n hC hn hX hRℓ hfar
  -- ## regime rows
  have hμ : 0 < μ := hC.hμ
  have hρ : 0 < ρ := hC.hρ0
  have hℓ : 0 < ell v μ := sb_ell_pos hav hC
  have hc1 : 0 < bogC1 v ρ μ := sb_c1_pos hav hC
  have hc1le : bogC1 v ρ μ ≤ 1 := sb_c1_le_one hav hC
  have hc2 : 0 < bogC2 v ρ μ := sb_c2_pos hav hC
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have heT0 : 0 ≤ (paramsAt μ (a v)).eT := Real.rpow_nonneg hC.hD0.le _
  have heT12 : (paramsAt μ (a v)).eT ≤ 1 / 2 := sb_eT_half hC
  have heT1 : (paramsAt μ (a v)).eT ≤ 1 := by linarith
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hρ hav hℓ
  have hΔ0 : 0 ≤ bogHalf v ρ μ := (bogHalf_pos hδ).le
  have hX0 : 0 ≤ fsX v μ := sb_fsX_nonneg hμ hav
  have hXle : fsX v μ ≤ 1 / 1000 := hX
  -- ## `Vs ≥ 1`
  have hVs1 : 1 ≤ bogVs v R ρ μ := by
    have h1 : (1 : ℝ) ≤ bogBs v R := le_max_left 1 _
    have h2 : bogBs v R ≤ bogVs v R ρ μ := by
      rw [bogVs]; exact le_add_of_nonneg_right (le_max_left 0 _)
    linarith
  have hVs0 : 0 < bogVs v R ρ μ := lt_of_lt_of_le one_pos hVs1
  have hsqVs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hVs1
  -- ## the numeric rows
  have hπ : Real.pi ≤ 4 := Real.pi_le_four
  have hs3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hπ3 : Real.pi * Real.sqrt 3 ≤ 8 := by
    have h := mul_le_mul hπ hs3 (Real.sqrt_nonneg 3) (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have h4π3 : 4 * Real.pi * Real.sqrt 3 ≤ 32 := by
    calc 4 * Real.pi * Real.sqrt 3 = 4 * (Real.pi * Real.sqrt 3) := by ring
      _ ≤ 4 * 8 := mul_le_mul_of_nonneg_left hπ3 (by norm_num)
      _ = 32 := by norm_num
  have h4π3X : 4 * Real.pi * Real.sqrt 3 * fsX v μ ≤ 1 / 2 := by
    have h1 : 4 * Real.pi * Real.sqrt 3 * fsX v μ ≤ 32 * fsX v μ :=
      mul_le_mul_of_nonneg_right h4π3 hX0
    have h2 : 32 * fsX v μ ≤ 32 * (1 / 1000) := by linarith [hXle]
    linarith [h1, h2]
  have hrel : 2 * bogHalf v ρ μ = (4 * Real.pi * Real.sqrt 3 * fsX v μ) * bogC1 v ρ μ :=
    sb_half_eq hav hμ hρ hℓ
  have h4Δle : 4 * bogHalf v ρ μ ≤ (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ := by
    have h8 : 8 * Real.pi * Real.sqrt 3 * fsX v μ ≤ 1 - (paramsAt μ (a v)).eT := by
      have hπ38 : 8 * Real.pi * Real.sqrt 3 ≤ 64 := by
        calc 8 * Real.pi * Real.sqrt 3 = 8 * (Real.pi * Real.sqrt 3) := by ring
          _ ≤ 8 * 8 := mul_le_mul_of_nonneg_left hπ3 (by norm_num)
          _ = 64 := by norm_num
      have h1 : 8 * Real.pi * Real.sqrt 3 * fsX v μ ≤ 64 * fsX v μ :=
        mul_le_mul_of_nonneg_right hπ38 hX0
      have h2 : 64 * fsX v μ ≤ 64 * (1 / 1000) := by linarith [hXle]
      linarith [h1, h2, heT12]
    calc 4 * bogHalf v ρ μ = 2 * (2 * bogHalf v ρ μ) := by ring
      _ = 2 * ((4 * Real.pi * Real.sqrt 3 * fsX v μ) * bogC1 v ρ μ) := by rw [hrel]
      _ = (8 * Real.pi * Real.sqrt 3 * fsX v μ) * bogC1 v ρ μ := by ring
      _ ≤ (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ := mul_le_mul_of_nonneg_right h8 hc1.le
  have h2Δ4 : 2 * bogHalf v ρ μ + 2 * bogC1 v ρ μ ≤ 4 := by
    have h : 2 * bogHalf v ρ μ ≤ (1 / 2) * bogC1 v ρ μ := by
      calc 2 * bogHalf v ρ μ = (4 * Real.pi * Real.sqrt 3 * fsX v μ) * bogC1 v ρ μ := hrel
        _ ≤ (1 / 2) * bogC1 v ρ μ := mul_le_mul_of_nonneg_right h4π3X hc1.le
    linarith [h, hc1le]
  have h2Δ4Vs : 2 * bogHalf v ρ μ + 2 * bogC1 v ρ μ ≤ 4 * Real.sqrt (bogVs v R ρ μ) := by
    nlinarith [h2Δ4, hsqVs]
  have hfar' : 16 * Real.sqrt (bogVs v R ρ μ) < bogRHit v ρ μ n := hfar
  have hΔeq : bogRLot v ρ μ n = bogRHit v ρ μ n - 2 * bogHalf v ρ μ := by
    rw [bogRLot, bogRHit]; ring
  -- ## the radius row
  have hrlo : 12 * Real.sqrt (bogVs v R ρ μ) + 2 * bogC1 v ρ μ ≤ bogRLot v ρ μ n := by
    rw [hΔeq]; linarith [hfar', h2Δ4Vs]
  -- ## the lower bound on the symbol at `r_lo`
  have hu_lo : (1 - (paramsAt μ (a v)).eT) * (12 * Real.sqrt (bogVs v R ρ μ)) ^ 2
      ≤ bogULot v ρ μ n := by
    have hshift := sb_tau_ge_shift (v := v) (ρ := ρ) (μ := μ) hP hc1 heT0 heT1 (bogRLot v ρ μ n)
    have hmax : 12 * Real.sqrt (bogVs v R ρ μ)
        ≤ max 0 (bogRLot v ρ μ n - 2 * bogC1 v ρ μ) := by
      have h : 12 * Real.sqrt (bogVs v R ρ μ)
          ≤ bogRLot v ρ μ n - 2 * bogC1 v ρ μ := by linarith [hrlo]
      exact le_trans h (le_max_right 0 _)
    have hsq : (12 * Real.sqrt (bogVs v R ρ μ)) ^ 2
        ≤ (max 0 (bogRLot v ρ μ n - 2 * bogC1 v ρ μ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hmax 2
    have hw : 0 ≤ 1 - (paramsAt μ (a v)).eT := by linarith [heT1]
    calc (1 - (paramsAt μ (a v)).eT) * (12 * Real.sqrt (bogVs v R ρ μ)) ^ 2
        ≤ (1 - (paramsAt μ (a v)).eT)
            * (max 0 (bogRLot v ρ μ n - 2 * bogC1 v ρ μ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hw
      _ ≤ bogULot v ρ μ n := hshift
  have h144 : (1 - (paramsAt μ (a v)).eT) * 144 * bogVs v R ρ μ ≤ bogULot v ρ μ n := by
    have heq : (1 - (paramsAt μ (a v)).eT) * (12 * Real.sqrt (bogVs v R ρ μ)) ^ 2
        = (1 - (paramsAt μ (a v)).eT) * 144 * bogVs v R ρ μ := by
      rw [mul_pow, Real.sq_sqrt hVs0.le]
      ring
    linarith [hu_lo, heq.le, heq.ge]
  have hhalf : 144 * (1 - (paramsAt μ (a v)).eT) * bogVs v R ρ μ
      ≤ bogULot v ρ μ n := by
    have heq : (1 - (paramsAt μ (a v)).eT) * 144 * bogVs v R ρ μ
        = 144 * (1 - (paramsAt μ (a v)).eT) * bogVs v R ρ μ := by ring
    linarith [h144, heq.le, heq.ge]
  -- ## the `β`-rows
  have hβ := bogBeta_le (h := h) hR hρ hav hv hvrad hv_supp hRℓ (tSca v ρ μ n)
  have hVlot_ge : -(bogBs v R) - bogOm v h R ρ μ n ≤ bogVlot v h R ρ μ n := by
    have hβ' := (abs_le.mp hβ).1
    rw [bogVlot, bogVNt]; linarith
  have h2BsOm : 2 * bogBs v R + 2 * bogOm v h R ρ μ n ≤ 2 * bogVs v R ρ μ := by
    have hom : bogOm v h R ρ μ n ≤ bogOscM v R ρ μ := sb_om_le_oscM hR.le hρ hav hδ hn
    have h2 : bogBs v R + bogOm v h R ρ μ n ≤ bogVs v R ρ μ := by
      have hmax := le_max_right (0 : ℝ) (bogOscM v R ρ μ)
      rw [bogVs]
      linarith
    linarith
  have hBsVs : bogBs v R ≤ bogVs v R ρ μ := by
    have hmax := le_max_left (0 : ℝ) (bogOscM v R ρ μ)
    rw [bogVs]
    linarith
  -- ## conclusion 1
  have h1 : 0 < bogULot v ρ μ n := by
    have hpos : (0 : ℝ) < 144 * (1 - (paramsAt μ (a v)).eT) * bogVs v R ρ μ := by
      have hlt : 0 < 1 - (paramsAt μ (a v)).eT := by linarith [heT12]
      positivity
    linarith [hhalf]
  -- ## conclusion 2
  have hrhi_c1 : bogC1 v ρ μ ≤ bogRHit v ρ μ n := by
    have h16 : (16 : ℝ) ≤ 16 * Real.sqrt (bogVs v R ρ μ) := by linarith [hsqVs]
    linarith [hfar', hc1le]
  have hsub := sb_tau_sub_ge (v := v) (ρ := ρ) (μ := μ) hP hc1 hc2 heT0 heT1 hrhi_c1
  have hnorm_le : ‖tSca v ρ μ n‖ ≤ bogRHit v ρ μ n := by
    rw [bogRHit]; linarith [hΔ0]
  have hφnn : 0 ≤ (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ :=
    mul_nonneg (by linarith [heT1]) hc1.le
  have hkey : 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖
      ≤ (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ * bogRHit v ρ μ n := by
    calc 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖
        ≤ ((1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ) * ‖tSca v ρ μ n‖ :=
          mul_le_mul_of_nonneg_right h4Δle (norm_nonneg _)
      _ ≤ ((1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ) * bogRHit v ρ μ n :=
          mul_le_mul_of_nonneg_left hnorm_le hφnn
      _ = (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ * bogRHit v ρ μ n := by ring
  have hsqdiff : (bogRHit v ρ μ n) ^ 2 - (bogRLot v ρ μ n) ^ 2
      = 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖ := by
    rw [bogRHit, bogRLot]; ring
  have h2 : bogUHit v ρ μ n ≤ (bogRLot v ρ μ n) ^ 2 := by
    rw [bogUHit]
    linarith [hsub, hkey, hsqdiff]
  -- ## conclusion 3
  have h72 : 72 * bogVs v R ρ μ ≤ (1 - (paramsAt μ (a v)).eT) * 144 * bogVs v R ρ μ := by
    have h1 : (72 : ℝ) ≤ (1 - (paramsAt μ (a v)).eT) * 144 := by
      have h2 : 1 - (paramsAt μ (a v)).eT ≤ 1 := by linarith
      nlinarith [heT12]
    have h3 : 72 * bogVs v R ρ μ ≤ ((1 - (paramsAt μ (a v)).eT) * 144) * bogVs v R ρ μ :=
      mul_le_mul_of_nonneg_right h1 hVs0.le
    linarith [h3]
  have h3 : 0 < bogULot v ρ μ n + 2 * bogVlot v h R ρ μ n := by
    linarith [h144, hVlot_ge, h2BsOm, h72, hVs0]
  -- ## conclusion 4
  have h4 : 2 * bogBs v R ≤ bogULot v ρ μ n := by
    have h2Vs : 2 * bogBs v R ≤ 72 * bogVs v R ρ μ := by
      have h2 : 2 * bogBs v R ≤ 2 * bogVs v R ρ μ := by linarith [hBsVs]
      nlinarith [h2, hVs0]
    linarith [hhalf, h72, h2Vs]
  exact ⟨h1, h2, h3, h4⟩

end Work.BoseBogFS
