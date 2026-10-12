import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.BogFSCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.psiSc_tail_le` — the pointwise tail bound for the scaled clean bracket

The target is the "tail" row of FS `lem:BogIntegral`: for momenta where the pairing coefficient
`β = betaSc` is much smaller than the radius `r = ‖t‖` (the hypotheses `h1`, `h2` say exactly
`B_β + ηr ≤ min(r/100, 100κr)`, and `hbu` says `|β| ≤ B_β + ηr`), the scaled clean bracket

`psiSc t = (τ_s + β) − √((τ_s+β)² − β²) − β²/(2r²)`

is dominated by `1000·κ·β²/r³`, where `κ = bogKappa = (1−ε_T)c₁ + ε_Tc₂` is the deficit coefficient
of the kinetic symbol (`r² − τ_s(r) ≤ 3κr`, `tauScRad_deficit`).

## The mathematics (three ingredients)

* `betaSc` is small: `|β| ≤ min(r/100, 100κr)` (`hbu` with `h1`, `h2`);
* the kinetic symbol is *not* too small: `τ_s ≥ r²/100`
  (`tauScRad_ge_hundredth_local`), a consequence of the profile bound
  `τ̃(u) ≥ (max 0 (u−2))²` and of the two parameter relations `c₂ = c₁/d`, `ε_T = d^{23/24}`
  that `paramsAt μ (a v) = fsParams (μ (a v)³)` imposes on `c₁, c₂, ε_T, d`;
* `τ_s` is close to `r²` from below: `r² − τ_s ≤ 3κr` (`tauScRad_deficit`, imported).

Writing `A = τ_s + β` and `L = A + √(A²−β²)`, the identities `A − √(A²−β²) = β²/L` and
`2r² − L = 2(r²−A) + β²/L` reduce the claim to `r(2r²−L) ≤ 2000κL`; both `1/r²` singularities
cancel and only the deficits `r² − τ_s ≤ 3κr` and `|β| ≲ κr` survive.  This pure-real core is
`psiSc_tail_alg_local`, proved with the case split `κr ≤ r²/20`: for small `κ` the deficit bound
gives `L ≥ 4r²/5`, for large `κ` one simply has `κ ≥ r/20 ≥ 125`, so `2000κL` dominates.

Two further observations pin the hypotheses down.  First, `8π ≤ B_β = bogBb R ℓ chiTC` (because
`chiTC ≥ 0`), so `h1` gives `r ≥ 800π ≥ 2513` and `h2` gives `κr ≥ 8π/100 > 1/4`; the hypotheses
therefore already place us in the large-radius regime.  Second, `bogC1 > 0` forces `μ > 0`
(`mu_pos_of_bogC1`) and `a v > 0` (`a_pos_of_bogC1`), which is what allows the parameter block of
`fsParams` to be interpreted at a *positive* diluteness `μ(a v)³` — the only place where the
unfolded definitions (rather than the stated hypotheses) are used.

(The two analytic inputs are also filed as reviewable siblings,
`Submission/Work/BoseBogFS/tauScRad_ge_twelfth.lean` (the sharper constant `1/12`) and
`Submission/Work/BoseBogFS/psiSc_tail_alg.lean`; this file is self-contained and does not need
them.)
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

namespace Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Two elementary consequences of the parameters -/

/-- `bogC1 v ρ μ > 0` forces `μ > 0`: if `μ ≤ 0` then `μ * (a v) ≤ 0`, hence the possibly
junk value `(μ * (a v)) ^ (-(1/2))` vanishes (`cos (-(1/2)π) = 0`), so the box side
`ell v μ = 𝓚_ℓ (μ a v)^{-1/2}` vanishes and with it `bogC1`. -/
lemma mu_pos_of_bogC1 {v : E3 → ℝ} {ρ μ : ℝ}
    (hav : 0 < a v) (hc1 : 0 < bogC1 v ρ μ) : 0 < μ := by
  by_contra h
  push_neg at h
  have hμa : μ * a v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hav.le
  have hcos : Real.cos (-(1 / 2 : ℝ) * π) = 0 := by
    rw [show (-(1 / 2 : ℝ)) * π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  have hz : (μ * a v) ^ (-(1 / 2 : ℝ)) = 0 := by
    rw [Real.rpow_def_of_nonpos hμa]
    by_cases h0 : μ * a v = 0
    · rw [if_pos h0, if_neg (by norm_num : ¬(-(1 / 2 : ℝ) = 0))]
    · rw [if_neg h0, hcos, mul_zero]
  have hℓ : ell v μ = 0 := by
    rw [ell, sideAt, boxSide, hz, mul_zero]
  have hc : bogC1 v ρ μ = 0 := by
    rw [bogC1, hℓ]
    simp
  linarith

/-- `bogC1 v ρ μ > 0` forces `a v > 0` (same argument: `μ * (a v) ≤ 0` kills the box side). -/
lemma a_pos_of_bogC1 {v : E3 → ℝ} {ρ μ : ℝ}
    (hμ : 0 < μ) (hc1 : 0 < bogC1 v ρ μ) : 0 < a v := by
  by_contra h
  push_neg at h
  have hμa : μ * a v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ.le h
  have hcos : Real.cos (-(1 / 2 : ℝ) * π) = 0 := by
    rw [show (-(1 / 2 : ℝ)) * π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  have hz : (μ * a v) ^ (-(1 / 2 : ℝ)) = 0 := by
    rw [Real.rpow_def_of_nonpos hμa]
    by_cases h0 : μ * a v = 0
    · rw [if_pos h0, if_neg (by norm_num : ¬(-(1 / 2 : ℝ) = 0))]
    · rw [if_neg h0, hcos, mul_zero]
  have hℓ : ell v μ = 0 := by
    rw [ell, sideAt, boxSide, hz, mul_zero]
  have hc : bogC1 v ρ μ = 0 := by
    rw [bogC1, hℓ]
    simp
  linarith

/-- The constant of `bogBb` is at least `8π` (because `chiTC ≥ 0`). -/
lemma eight_pi_le_bogBb (R ℓ : ℝ) : 8 * Real.pi ≤ bogBb R ℓ chiTC := by
  have h2 : 0 ≤ chiTC * (R / ℓ) ^ 2 := mul_nonneg chiTC_nonneg (sq_nonneg _)
  rw [bogBb]
  nlinarith [Real.pi_pos, h2]

/-! ## 0b. The two analytic inputs -/

/-- The profile lower bound `c²τ̃(r/c) ≥ (max 0 (r−2c))²` (`τ̃ ≥ ((·−2)₊)²`,
`tauProf_spec`). -/
lemma sq_mul_tauProf_ge {c r : ℝ} (hc : 0 < c) :
    (max 0 (r - 2 * c)) ^ 2 ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) := by
  have h := Work.BoseBoxFock.tauProf_spec.2.2.1 (r / c)
  have hmul : c * max 0 (r / c - 2) = max 0 (r - 2 * c) := by
    rw [mul_max_of_nonneg _ _ hc.le, mul_sub, mul_div_cancel₀ r hc.ne', mul_zero]
    ring
  calc (max 0 (r - 2 * c)) ^ 2 = (c * max 0 (r / c - 2)) ^ 2 := by rw [hmul]
    _ = c ^ 2 * (max 0 (r / c - 2)) ^ 2 := by ring
    _ ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) := mul_le_mul_of_nonneg_left h (sq_nonneg c)

/-- **The kinetic symbol is not small**: `τ_s,r ≥ r²/100` (`τ_s,r = tauScRad v ρ μ r`).

Everything comes from the parameter block `paramsAt μ (a v) = fsParams (μ (a v)³)`, which ties
`d = X⁶` to `ε_T = X^{23/4}`, i.e. `ε_T = d^{23/24}`.  Writing `d = X⁶`, `c₂ = c₁/d`, the profile
bound `τ̃ ≥ ((·−2)₊)²` and `r ≥ 4c₁` give

`τ_s,r ≥ (1−ε_T)(r−2c₁)² + ε_T(max 0 (r−2c₂))² ≥ (1−ε_T)r²/4`.

If `ε_T ≤ 9/10` this is `≥ r²/40`.  If `ε_T ≥ 9/10` then `d = ε_T^{24/23} ≥ (9/10)² = 81/100 ≥ 4/5`
(monotonicity of `x ↦ x^{24/23}` on `[0,1]`), so `2c₂ ≤ 2c₁/d ≤ 5r/8` and the second term alone
gives `≥ (9/10)(3r/8)² = 81r²/640 ≥ r²/100`. -/
lemma tauScRad_ge_hundredth_local {v : E3 → ℝ} {ρ μ : ℝ}
    (hP : 0 < ρ * a v) (hμ : 0 < μ)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1)
    {r : ℝ} (hr : 4 * bogC1 v ρ μ ≤ r) :
    r ^ 2 / 100 ≤ tauScRad v ρ μ r := by
  have hav : 0 < a v := a_pos_of_bogC1 hμ hc1
  have ht : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  -- the two relations of the parameter block
  have heT_eq : (paramsAt μ (a v)).eT = (paramsAt μ (a v)).d ^ (23 / 24 : ℝ) := by
    simp only [paramsAt, fsParams, fsXp]
    rw [← Real.rpow_mul ht.le]
    congr 1
    norm_num
  have hdpos : 0 < (paramsAt μ (a v)).d := by
    simp only [paramsAt, fsParams, fsXp]
    exact Real.rpow_pos_of_pos ht _
  have hd_eq : (paramsAt μ (a v)).d = (paramsAt μ (a v)).eT ^ (24 / 23 : ℝ) := by
    rw [heT_eq, ← Real.rpow_mul hdpos.le,
      show (23 / 24 : ℝ) * (24 / 23) = 1 by norm_num, Real.rpow_one]
  have hc2_eq : bogC2 v ρ μ = bogC1 v ρ μ / (paramsAt μ (a v)).d := by
    rw [bogC1, bogC2]
    field_simp
  -- the two term bounds of `tauScRad_eq`
  have hterm1 : (max 0 (r - 2 * bogC1 v ρ μ)) ^ 2
      ≤ (bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ) :=
    sq_mul_tauProf_ge hc1
  have hterm2 : (max 0 (r - 2 * bogC2 v ρ μ)) ^ 2
      ≤ (bogC2 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ) :=
    sq_mul_tauProf_ge hc2
  have hτ1 : tauScRad v ρ μ r
      = (1 - (paramsAt μ (a v)).eT) * (bogC1 v ρ μ) ^ 2
          * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)
        + (paramsAt μ (a v)).eT * (bogC2 v ρ μ) ^ 2
          * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ) := tauScRad_eq v hP r
  have ht1nn : 0 ≤ (1 - (paramsAt μ (a v)).eT) * (bogC1 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ) :=
    mul_nonneg (mul_nonneg (by linarith only [heT1]) (sq_nonneg _))
      (Work.BoseBoxFock.tauProf_nonneg _)
  have ht2nn : 0 ≤ (paramsAt μ (a v)).eT * (bogC2 v ρ μ) ^ 2
      * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (Work.BoseBoxFock.tauProf_nonneg _)
  have hr0 : 0 < r := by linarith only [hr, hc1]
  have hmax1 : (r / 2) ^ 2 ≤ (max 0 (r - 2 * bogC1 v ρ μ)) ^ 2 := by
    have h0 : 0 ≤ r / 2 := by linarith only [hr0]
    have h1 : r / 2 ≤ r - 2 * bogC1 v ρ μ := by linarith only [hr]
    have h2 : r - 2 * bogC1 v ρ μ ≤ max 0 (r - 2 * bogC1 v ρ μ) := le_max_right _ _
    exact pow_le_pow_left₀ h0 (le_trans h1 h2) 2
  rcases le_or_gt ((paramsAt μ (a v)).eT) (9 / 10) with hcase | hcase
  · -- `ε_T ≤ 9/10`: the first term alone gives `r²/40`
    rw [hτ1]
    have hbig : (r / 2) ^ 2 ≤ (bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ) :=
      le_trans hmax1 hterm1
    have h1 : (1 - (paramsAt μ (a v)).eT) * (r / 2) ^ 2
        ≤ (1 - (paramsAt μ (a v)).eT) * ((bogC1 v ρ μ) ^ 2
            * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)) :=
      mul_le_mul_of_nonneg_left hbig (by linarith only [hcase])
    nlinarith only [h1, ht2nn, hcase, hr]
  · -- `ε_T ≥ 9/10`: then `d ≥ 4/5` and the second term alone gives `81r²/640`
    have hd45 : (4 / 5 : ℝ) ≤ (paramsAt μ (a v)).d := by
      rw [hd_eq]
      have h1 : (9 / 10 : ℝ) ^ ((24 : ℝ) / 23) ≤ (paramsAt μ (a v)).eT ^ ((24 : ℝ) / 23) :=
        Real.rpow_le_rpow (x := (9 / 10 : ℝ)) (y := (paramsAt μ (a v)).eT)
          (z := (24 / 23 : ℝ)) (by norm_num) hcase.le (by norm_num)
      have h2 : (9 / 10 : ℝ) ^ (2 : ℝ) ≤ (9 / 10 : ℝ) ^ ((24 : ℝ) / 23) :=
        Real.rpow_le_rpow_of_exponent_ge (x := (9 / 10 : ℝ)) (y := (2 : ℝ))
          (z := (24 / 23 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
      linarith only [h1, h2]
    have hc2le : bogC2 v ρ μ ≤ 5 * bogC1 v ρ μ / 4 := by
      rw [hc2_eq, div_le_iff₀ hdpos]
      nlinarith only [hd45, hc1]
    have hc2r : 2 * bogC2 v ρ μ ≤ 5 * r / 8 := by linarith only [hr, hc2le]
    have hmax2 : (3 * r / 8) ^ 2 ≤ (max 0 (r - 2 * bogC2 v ρ μ)) ^ 2 := by
      have h0 : 0 ≤ 3 * r / 8 := by linarith only [hr0]
      have h1 : 3 * r / 8 ≤ r - 2 * bogC2 v ρ μ := by linarith only [hc2r]
      have h2 : r - 2 * bogC2 v ρ μ ≤ max 0 (r - 2 * bogC2 v ρ μ) := le_max_right _ _
      exact pow_le_pow_left₀ h0 (le_trans h1 h2) 2
    rw [hτ1]
    have hbig : (3 * r / 8) ^ 2 ≤ (bogC2 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ) :=
      le_trans hmax2 hterm2
    have h1 : (paramsAt μ (a v)).eT * (3 * r / 8) ^ 2
        ≤ (paramsAt μ (a v)).eT * ((bogC2 v ρ μ) ^ 2
            * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ)) :=
      mul_le_mul_of_nonneg_left hbig heT0
    nlinarith only [h1, ht1nn, hcase, hr]

/-- The pure real core of the tail bound (see `Submission/Work/BoseBogFS/psiSc_tail_alg.lean`).

Write `A = τ + β`, `s = √(A²−β²)`, `L = A + s`.  The identities `A − s = β²/L`
(from `(A−s)(A+s) = A²−s² = β²`) and `2r² − L = 2(r²−A) + β²/L` reduce the claim to
`r(2r²−L) ≤ 2000κL`, i.e. to `6κr² + 2r|β| + rβ²/L ≤ 2000κL`.  Since `r² − A ≤ 3κr + |β|` and
`L ≥ τ − |β|`, two cases finish: for `κr ≤ r²/20` the deficit bound `τ ≥ r² − 3κr` gives
`L ≥ 4r²/5` and `|β| ≤ 100κr ≪ r` kills the `κ²r` term; for `κr > r²/20` one has `κ > r/20`, so
`2000κL` already dominates everything. -/
lemma psiSc_tail_alg_local {τ β r κ : ℝ} (hr : 2513 ≤ r) (hκ : 0 < κ) (hκr : 1 / 4 ≤ κ * r)
    (hτ : r ^ 2 / 100 ≤ τ) (hdef : r ^ 2 - τ ≤ 3 * κ * r)
    (hb1 : |β| ≤ r / 100) (hb2 : |β| ≤ 100 * κ * r) :
    (τ + β) - Real.sqrt ((τ + β) ^ 2 - β ^ 2) - β ^ 2 / (2 * r ^ 2)
      ≤ 1000 * κ * β ^ 2 / r ^ 3 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hτ0 : 0 ≤ τ := by nlinarith only [hτ, hr]
  set M : ℝ := min (r / 100) (100 * κ * r) with hMdef
  have hMr : M ≤ r / 100 := by rw [hMdef]; exact min_le_left _ _
  have hMk : M ≤ 100 * κ * r := by rw [hMdef]; exact min_le_right _ _
  have hβM : |β| ≤ M := by rw [hMdef]; exact le_min hb1 hb2
  have hMnn : 0 ≤ M := le_trans (abs_nonneg β) hβM
  have hβl : -M ≤ β := by have h := (abs_le.mp hβM).1; linarith only [h]
  have hA : 0 < τ + β := by nlinarith only [hτ, hβl, hMr, hr]
  have hA2 : 0 < τ + 2 * β := by nlinarith only [hτ, hβl, hMr, hr]
  have hsq : 0 ≤ (τ + β) ^ 2 - β ^ 2 := by
    have h : (τ + β) ^ 2 - β ^ 2 = τ * (τ + 2 * β) := by ring
    rw [h]; exact mul_nonneg hτ0 hA2.le
  set s : ℝ := Real.sqrt ((τ + β) ^ 2 - β ^ 2) with hsdef
  have hs2 : s ^ 2 = (τ + β) ^ 2 - β ^ 2 := by rw [hsdef]; exact Real.sq_sqrt hsq
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  set L : ℝ := (τ + β) + s with hLdef
  have hL0 : 0 < L := by rw [hLdef]; linarith only [hA, hs0]
  have hkey : (τ + β) - s = β ^ 2 / L := by
    rw [eq_div_iff (ne_of_gt hL0), hLdef]
    nlinarith only [hs2]
  have hLA : τ - M ≤ L := by rw [hLdef]; linarith only [hβl, hs0]
  have hβ2M : β ^ 2 ≤ M ^ 2 := by
    have hab : |β| ^ 2 ≤ M ^ 2 := by nlinarith only [hβM, hMnn, abs_nonneg β]
    rwa [sq_abs] at hab
  have hdef2 : r ^ 2 - (τ + β) ≤ 3 * κ * r + M := by linarith only [hdef, hβl]
  have hbig : r * (2 * r ^ 2 - L) ≤ 6 * κ * r ^ 2 + 2 * r * M + r * (M ^ 2 / L) := by
    have hid : 2 * r ^ 2 - L = 2 * (r ^ 2 - (τ + β)) + β ^ 2 / L := by
      have h : 2 * r ^ 2 - L = 2 * (r ^ 2 - (τ + β)) + ((τ + β) - s) := by
        rw [hLdef]; ring
      rw [h, hkey]
    rw [hid, mul_add]
    have h1 : 2 * r * (r ^ 2 - (τ + β)) ≤ 2 * r * (3 * κ * r + M) :=
      mul_le_mul_of_nonneg_left hdef2 (by linarith only [hr0])
    have h2 : r * (β ^ 2 / L) ≤ r * (M ^ 2 / L) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hβ2M hL0.le) hr0.le
    nlinarith only [h1, h2]
  have htarget : r * (2 * r ^ 2 - L) ≤ 2000 * κ * L := by
    refine le_trans hbig ?_
    rcases le_or_gt (κ * r) (r ^ 2 / 20) with hcas | hcas
    · have hLval : (8 / 10 : ℝ) * r ^ 2 ≤ L := by nlinarith only [hLA, hdef, hMr, hcas, hr]
      have h2rM : 2 * r * M ≤ 200 * κ * r ^ 2 := by nlinarith only [hMk, hr0]
      have hM2 : M ^ 2 ≤ (100 * κ * r) ^ 2 := by nlinarith only [hMk, hMnn]
      have hMP : r * (M ^ 2 / L) ≤ 12500 * κ ^ 2 * r := by
        rw [← mul_div_assoc, div_le_iff₀ (by nlinarith only [hLval, hr])]
        nlinarith only [hM2, hLval, hr0]
      have hprod : 12500 * κ ^ 2 * r ≤ 1394 * κ * r ^ 2 := by
        nlinarith only [hcas, hκ, hr0]
      nlinarith only [hLval, h2rM, hMP, hcas, hr, hκ, hr0, hprod]
    · have hLval : (1 / 100 : ℝ) * r ^ 2 - r / 100 ≤ L := by linarith only [hLA, hτ, hMr]
      have hLval2 : (1 / 101 : ℝ) * r ^ 2 ≤ L := by nlinarith only [hLval, hr]
      have h2rM : 2 * r * M ≤ (1 / 50 : ℝ) * r ^ 2 := by nlinarith only [hMr, hr0]
      have hM2 : M ^ 2 ≤ (r / 100) ^ 2 := by nlinarith only [hMr, hMnn]
      have hMP : r * (M ^ 2 / L) ≤ 101 * r / 10000 := by
        rw [← mul_div_assoc, div_le_iff₀ (by nlinarith only [hLval2, hr])]
        nlinarith only [hM2, hLval2, hr0]
      have h1r : (0 : ℝ) ≤ 1 / r := by positivity
      have hkbig : r / 20 < κ := by nlinarith only [hcas, hr0, h1r]
      nlinarith only [hLval2, h2rM, hMP, hcas, hr, hκ, hr0, h1r, hkbig]
  rw [hkey]
  have hsplit : β ^ 2 / L - β ^ 2 / (2 * r ^ 2)
      = β ^ 2 * (r * (2 * r ^ 2 - L)) / (2 * r ^ 3 * L) := by
    field_simp; try ring
  rw [hsplit]
  have hstep : β ^ 2 * (r * (2 * r ^ 2 - L)) ≤ β ^ 2 * (2000 * κ * L) :=
    mul_le_mul_of_nonneg_left htarget (sq_nonneg β)
  calc β ^ 2 * (r * (2 * r ^ 2 - L)) / (2 * r ^ 3 * L)
      ≤ β ^ 2 * (2000 * κ * L) / (2 * r ^ 3 * L) :=
        div_le_div_of_nonneg_right hstep (by positivity)
    _ = 1000 * κ * β ^ 2 / r ^ 3 := by
        field_simp; try ring

/-! ## 1. The target -/

theorem psiSc_tail_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ρ μ : ℝ} {t : EuclideanSpace ℝ (Fin 3)}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    (hκ : 0 ≤ Work.BoseBogFS.bogKappa v ρ μ)
    (h1 : Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
        + Work.BoseBogFS.bogEta v R ρ * ‖t‖ ≤ ‖t‖ / 100)
    (h2 : Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
        + Work.BoseBogFS.bogEta v R ρ * ‖t‖ ≤ 100 * Work.BoseBogFS.bogKappa v ρ μ * ‖t‖)
    (h3 : 4 * Work.BoseBogFS.bogC1 v ρ μ ≤ ‖t‖)
    (hbu : |Work.BoseBogFS.betaSc v h ρ μ t|
      ≤ Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
        + Work.BoseBogFS.bogEta v R ρ * ‖t‖) :
    Work.BoseBogFS.psiSc v h ρ μ t
      ≤ 1000 * Work.BoseBogFS.bogKappa v ρ μ
          * (Work.BoseBogFS.betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3 := by
  have hP : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ hav
  -- the two `β`-hypotheses, made explicit
  have hη : 0 ≤ bogEta v R ρ * ‖t‖ :=
    mul_nonneg (bogEta_nonneg (v := v) hR.le hρ.le) (norm_nonneg t)
  have hBb := eight_pi_le_bogBb R (ell v μ)
  have hβ1 : |betaSc v h ρ μ t| ≤ ‖t‖ / 100 := le_trans hbu h1
  have hβ2 : |betaSc v h ρ μ t| ≤ 100 * bogKappa v ρ μ * ‖t‖ := le_trans hbu h2
  -- the regime facts forced by `8π ≤ B_β` together with `h1`, `h2`
  have hr : (2513 : ℝ) ≤ ‖t‖ := by
    have h8 : 8 * Real.pi ≤ ‖t‖ / 100 := by linarith
    nlinarith [Real.pi_gt_d6]
  have hκr : (1 : ℝ) / 4 ≤ bogKappa v ρ μ * ‖t‖ := by
    have h8 : 8 * Real.pi ≤ 100 * bogKappa v ρ μ * ‖t‖ := by linarith
    nlinarith [Real.pi_gt_d6]
  have hκpos : 0 < bogKappa v ρ μ := by nlinarith [norm_nonneg t, hr, hκr]
  -- the parameter facts: `μ > 0`, the τ-bound and the τ-deficit
  have hμpos : 0 < μ := mu_pos_of_bogC1 hav hc1
  have hτ12 : ‖t‖ ^ 2 / 100 ≤ tauScRad v ρ μ ‖t‖ :=
    tauScRad_ge_hundredth_local hP hμpos hc1 hc2 heT0 heT1 h3
  have hdef : ‖t‖ ^ 2 - tauScRad v ρ μ ‖t‖ ≤ 3 * bogKappa v ρ μ * ‖t‖ :=
    tauScRad_deficit v hP hc1 hc2 heT0 heT1 (norm_nonneg t)
  have hpsi : psiSc v h ρ μ t = (tauScRad v ρ μ ‖t‖ + betaSc v h ρ μ t)
      - Real.sqrt ((tauScRad v ρ μ ‖t‖ + betaSc v h ρ μ t) ^ 2
          - (betaSc v h ρ μ t) ^ 2)
      - (betaSc v h ρ μ t) ^ 2 / (2 * ‖t‖ ^ 2) := by
    rw [psiSc, Work.BoseB6.bogZeroPoint, tauSc_eq_tauScRad]
  rw [hpsi]
  exact psiSc_tail_alg_local hr hκpos hκr hτ12 hdef hβ1 hβ2

end Work.BoseBogFS
