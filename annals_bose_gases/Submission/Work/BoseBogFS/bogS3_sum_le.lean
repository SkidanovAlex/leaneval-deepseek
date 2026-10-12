import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.absorb_arith
import Submission.Work.BoseBogFS.bogMajC_core
import Submission.Work.BoseBogFS.bogSideConds
import Submission.Work.BoseBogFS.bogVmaxt_le_decay
import Submission.Work.BoseBogFS.summable_profile_three
import Submission.Work.BoseBogFS.tauScRad_diff_le
import Submission.Work.BoseBogFS.tauScRad_diff_le_quad
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogS3_sum_le` — the region-C lattice sum of the clean Riemann row

We bound the gated bulk majorant `bogS3 v h R ρ μ` (definitionally the piece `bogT3` of
`bogCellDefs`, i.e. the region `16√Vs < r_hi` of the per-cell majorant `bogMajC`) by an
explicit `X`-power, `2000·X^{-43/10}` with `X = fsX v μ = (dil v μ)^{1/323}`, uniformly over
the states `(ρ, μ)` of `Core v R μ ρ` with `dil v μ ≤ ε₃` (and `R ≤ ℓ·chiR0`).

## Structure of the proof

In region C the gate `16√Vs < r_hi` forces `r = ‖tSca‖ ≥ 15√Vs ≥ 15`, so the mesh is small
compared with `r`: `2Δ ≤ r` and `r_lo ≥ r/2`.  With `V = bogVmaxt`, `u = τ_s`, `v = β_s`, and
the per-cell bounds of `bogCellDefs`, the three pieces of `bogMajC` are bounded by

* `M1 = 2(V²/(S_lo W_lo))(u_hi − u_lo) ≤ 65536·Vs²·(u_hi − u_lo)/((1+m‖n‖)²r⁴)`
  (using `S_lo W_lo ≥ u_lo²/2` and `u_lo ≥ r_lo²/8`);
* `M2 = 2(A + B)(v_hi − v_lo)`, with `v_hi − v_lo = 2·bogOm` the (decaying) `β`-oscillation;
* `M3 = V²(r_hi² − r_lo²)/(r_lo²r_hi²) ≤ 1024·Vs²·Δ/((1+m‖n‖)²r³)`,

and the increment is controlled in two cases: for `2c₂ ≤ r_lo` the profile `τ̃` is exactly
quadratic on the cell, so `u_hi − u_lo ≤ r_hi² − r_lo² = 4Δr`; in the remaining (small) case
`r_lo < 2c₂` one adds the kink term `ε_T·(max 0 (r_hi − c₂))² ≤ 4ε_T r²`, whose lattice sum
is controlled by the counting bound (that region has `‖n‖ ≤ 3c₂/δ`).

The lattice sums are the three standard profiles
`Σ_n 1/((1+m‖n‖)²‖n‖³) ≤ 100(1+log(2+1/m))`, `Σ_n 1/((1+m‖n‖)²‖n‖²) ≤ 100(1+1/m)`,
`Σ_n 1/((1+m‖n‖)³‖n‖⁴) ≤ 100` of `latticeSumBounds`, and the final arithmetic is the
absorption `K·Vs²·(X^{-3}(C + log(1/X)) + X^{-17/4}) ≤ 2000·X^{-43/10}` for small `X`.

## The regime data

`RegimeC v R ρ μ` collects the `X`-power form of the parameters: `δ = 2π√(μ/ρ)·X^{3/2}`,
`Δ = δ√3/2`, `c₁ = ½√(μ/ρ)X^{1/2}`, `c₂ = ½√(μ/ρ)X^{-11/2}`, `ε_T = X^{23/4}`,
`√(ρ/a)·Δ ≤ 8X^{163}/(a v)²`, together with the identity `√(ρ·a v)·δ = 2π/ℓ` that converts
the scaled radius into the lattice norm.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Vocabulary -/

/-- The lattice momentum scale `m = 2π/ℓ` of the clean Riemann row. -/
def bogM (v : E3 → ℝ) (μ : ℝ) : ℝ := 2 * Real.pi / ell v μ

/-- The `r^{-3}`-decaying lattice profile of region C (with the `m‖n‖` decay factor). -/
def bogP1 (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  1 / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 3)

/-- The `r^{-2}`-decaying lattice profile of region C. -/
def bogP2 (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  1 / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 2)

/-- The `r^{-4}`-decaying lattice profile of region C, with the cubic decay factor. -/
def bogP3 (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  1 / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 3 * ‖tSca v ρ μ n‖ ^ 4)

/-- **The region-C regime data**, in `X`-power form.  Every field is a consequence of
`Core v R μ ρ` and of the smallness `fsX v μ ≤ min (1/1000) ((a v)²/8)`. -/
structure RegimeC (v : E3 → ℝ) (R ρ μ : ℝ) : Prop where
  hμ0 : 0 < μ
  hρ0 : 0 < ρ
  hXpos : 0 < fsX v μ
  hXle : fsX v μ ≤ 1
  hXlt : fsX v μ ≤ 1 / 1000
  hδpos : 0 < bogMesh v ρ μ
  hδlow : 5 * (fsX v μ) ^ (3 / 2 : ℝ) ≤ bogMesh v ρ μ
  hδhigh : bogMesh v ρ μ ≤ 8 * (fsX v μ) ^ (3 / 2 : ℝ)
  hΔpos : 0 < bogHalf v ρ μ
  hΔle : bogHalf v ρ μ ≤ 1
  hΔhigh : bogHalf v ρ μ ≤ 7 * (fsX v μ) ^ (3 / 2 : ℝ)
  hc1pos : 0 < bogC1 v ρ μ
  hc1le : bogC1 v ρ μ ≤ (fsX v μ) ^ (1 / 2 : ℝ)
  hc2pos : 0 < bogC2 v ρ μ
  hc12 : bogC1 v ρ μ ≤ bogC2 v ρ μ
  hc2high : bogC2 v ρ μ ≤ (fsX v μ) ^ (-(11 / 2) : ℝ)
  heThigh : (paramsAt μ (a v)).eT ≤ (fsX v μ) ^ (23 / 4 : ℝ)
  heTpos : 0 ≤ (paramsAt μ (a v)).eT
  heThalf : (paramsAt μ (a v)).eT ≤ 1 / 2
  hOspos : 0 ≤ Real.sqrt (ρ / a v) * bogHalf v ρ μ
  hOs : Real.sqrt (ρ / a v) * bogHalf v ρ μ ≤ 8 * (fsX v μ) ^ (163 : ℝ) / (a v) ^ 2
  hOs1 : Real.sqrt (ρ / a v) * bogHalf v ρ μ ≤ 1
  hmpos : 0 < bogM v μ
  hmesh : Real.sqrt (ρ * a v) * bogMesh v ρ μ = bogM v μ
  hVs1 : 1 ≤ bogVs v R ρ μ
  hOscM : bogOscM v R ρ μ ≤ 8 * bogKOs * (1 + R) ^ 3 * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2)

/-! ## 2. Elementary conversions -/

/-- The scaled radius is the mesh times the lattice norm. -/
lemma norm_tSca_eq {v : E3 → ℝ} {ρ μ : ℝ} (hδ : 0 ≤ bogMesh v ρ μ) (n : Fin 3 → ℤ) :
    ‖tSca v ρ μ n‖ = bogMesh v ρ μ * ‖lpt 1 n‖ := by
  rw [tSca_eq_lpt]
  exact norm_lpt_eq _ hδ n

/-- `√(ρ·a v)` times the scaled radius is `m` times the lattice norm. -/
lemma sqrtRa_mul_norm {v : E3 → ℝ} {R ρ μ : ℝ} (hreg : RegimeC v R ρ μ) (n : Fin 3 → ℤ) :
    Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖ = bogM v μ * ‖lpt 1 n‖ := by
  rw [norm_tSca_eq hreg.hδpos.le n, ← mul_assoc, hreg.hmesh]

/-- The gate forces the region-C radius relations. -/
lemma gate_facts {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hreg : RegimeC v R ρ μ) (hgate : bogBigThr v R ρ μ < bogRHit v ρ μ n) :
    15 * Real.sqrt (bogVs v R ρ μ) ≤ ‖tSca v ρ μ n‖
      ∧ 14 * Real.sqrt (bogVs v R ρ μ) ≤ bogRLot v ρ μ n
      ∧ 2 * bogHalf v ρ μ ≤ ‖tSca v ρ μ n‖
      ∧ 4 * bogC1 v ρ μ ≤ bogRLot v ρ μ n := by
  have hs1 : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
  have hbig : 16 * Real.sqrt (bogVs v R ρ μ) < bogRHit v ρ μ n := hgate
  have hΔ := hreg.hΔle
  have hrlo : bogRLot v ρ μ n = bogRHit v ρ μ n - 2 * bogHalf v ρ μ := by
    rw [bogRLot, bogRHit]; ring
  have hrhi : bogRHit v ρ μ n = ‖tSca v ρ μ n‖ + bogHalf v ρ μ := rfl
  have h14 : 14 * Real.sqrt (bogVs v R ρ μ) ≤ bogRLot v ρ μ n := by
    rw [hrlo]; linarith
  have h15 : 15 * Real.sqrt (bogVs v R ρ μ) ≤ ‖tSca v ρ μ n‖ := by linarith
  have h2Δ : 2 * bogHalf v ρ μ ≤ ‖tSca v ρ μ n‖ := by linarith
  refine ⟨h15, h14, h2Δ, ?_⟩
  have hc1 : 4 * bogC1 v ρ μ ≤ 4 * (fsX v μ) ^ (1 / 2 : ℝ) := by linarith [hreg.hc1le]
  have hXh : (fsX v μ) ^ (1 / 2 : ℝ) ≤ 1 := by
    calc (fsX v μ) ^ (1 / 2 : ℝ) ≤ 1 ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hreg.hXpos.le hreg.hXle (by norm_num)
      _ = 1 := Real.one_rpow _
  linarith

/-- **Negative-power monotonicity of the mesh.**  From `X^a ≤ δ` and `0 < X`, `0 < δ` one gets
`δ^{-k} ≤ X^{-(a k)}`. -/
lemma rpow_neg_le_of_le {δ X a : ℝ} {k : ℕ} (hX0 : 0 < X) (hδ0 : 0 < δ)
    (h : X ^ a ≤ δ) (hk : 0 < k) : δ ^ (-(k : ℝ)) ≤ X ^ (-(a * k)) := by
  have h1 : X ^ (a * k) ≤ δ ^ k := by
    have h2 : (X ^ a) ^ k ≤ δ ^ k := pow_le_pow_left₀ (Real.rpow_nonneg hX0.le a) h k
    have h3 : X ^ (a * k) = (X ^ a) ^ k := by
      rw [← Real.rpow_natCast (X ^ a) k, ← Real.rpow_mul hX0.le]
    linarith [h2, h3.le, h3.ge]
  have hgoal : (δ ^ k)⁻¹ ≤ (X ^ (a * (k : ℝ)))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hX0 _) h1
  have e1 : δ ^ (-(k : ℝ)) = (δ ^ k)⁻¹ := by
    rw [Real.rpow_neg hδ0.le, Real.rpow_natCast]
  have e2 : X ^ (-(a * (k : ℝ))) = (X ^ (a * (k : ℝ)))⁻¹ := Real.rpow_neg hX0.le _
  rw [e1, e2]
  exact hgoal

/-- The quadratic mesh bound.  From `5 X^{3/2} ≤ δ` (and `0 < X`, `0 < δ`) one gets
`δ^{-2} ≤ X^{-3}/25`. -/
lemma mesh_inv_sq_le {δ X : ℝ} (hX0 : 0 < X) (hδ0 : 0 < δ) (h : 5 * X ^ (3 / 2 : ℝ) ≤ δ) :
    δ ^ (-(2 : ℝ)) ≤ X ^ (-(3 : ℝ)) / 25 := by
  have h5 : (0 : ℝ) < 5 * X ^ (3 / 2 : ℝ) := by positivity
  have hδ2' : 25 * X ^ (3 : ℝ) ≤ δ ^ (2 : ℝ) := by
    have h2le : (5 * X ^ (3 / 2 : ℝ)) ^ (2 : ℝ) ≤ δ ^ (2 : ℝ) :=
      Real.rpow_le_rpow h5.le h (by norm_num)
    have hbase : (5 * X ^ (3 / 2 : ℝ)) ^ (2 : ℝ) = 25 * X ^ (3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hX0.le _)]
      rw [show (X ^ (3 / 2 : ℝ)) ^ (2 : ℝ) = X ^ (3 : ℝ) by
        rw [← Real.rpow_mul hX0.le]; congr 1; norm_num]
      rw [show (5 : ℝ) ^ (2 : ℝ) = 25 by rw [Real.rpow_two]; norm_num]
    linarith [h2le, hbase.le, hbase.ge]
  have hpos : 0 < 25 * X ^ (3 : ℝ) := by positivity
  rw [Real.rpow_neg hδ0.le (2 : ℝ), Real.rpow_neg hX0.le (3 : ℝ)]
  calc (δ ^ (2 : ℝ))⁻¹ ≤ (25 * X ^ (3 : ℝ))⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hpos hδ2'
    _ = (X ^ (3 : ℝ))⁻¹ / 25 := by rw [mul_inv]; ring

/-! ## 3. The per-cell bound of region C

The three pieces of `bogMajC` (with `V = bogVmaxt`, `u = τ_s`, `v = β_s`, `s = 1 + m‖n‖`,
`r = ‖tSca‖`, `W = √(u_lo² + 2u_lo v_lo)`, `S = u_lo + v_lo + W`, `D = max 0 (r_hi² − u_lo)`):

* `M1 = 2(V²/(SW))(u_hi − u_lo)`,
* `M2 = 2(V(2D+2V)/(r_lo²S) + V²(1+u_hi/W)/S²)(v_hi − v_lo)`,
* `M3 = V²(r_hi² − r_lo²)/(r_lo²r_hi²)`.

On region C (`r_hi > 16√Vs`) we have `r ≥ 15√Vs ≥ 15`, `r_lo ≥ 14√Vs`, `2Δ ≤ r`, so
`r_lo ≥ r/2` and `u_lo ≥ r_lo²/8 ≥ 24Vs`.  Hence `a := u_lo + 2v_lo ≥ u_lo − 4Vs ≥ 5u_lo/6`,
so `W² = u_lo a ≥ u_lo²/2` and `S ≥ W`, giving `SW ≥ u_lo²/2`, `1/(SW) ≤ 4096/r⁴`;
moreover `1/S ≤ 32√2/r²`, `u_hi/W ≤ 8√2`, `u_hi ≤ r_lo² ≤ r²`, `D ≤ 9r²/4` and
`2D + 2V ≤ 5r²`.  This yields the bound below with the *constants* `2·10⁵`, `10⁷`, `10⁵`
(and `2·10³` for `M3`). -/
lemma bogMajC_le_of_inc {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    {inc : ℝ} (hreg : RegimeC v R ρ μ) (hR : 0 < R) (hav : 0 < a v)
    (hgate : bogBigThr v R ρ μ < bogRHit v ρ μ n)
    (hulo8 : (bogRLot v ρ μ n) ^ 2 / 8 ≤ bogULot v ρ μ n)
    (huhi : bogUHit v ρ μ n ≤ (bogRLot v ρ μ n) ^ 2)
    (hV : bogVmaxt v h R ρ μ n ≤ 4 * bogVs v R ρ μ / (1 + bogM v μ * ‖lpt 1 n‖))
    (hvl : -(2 * bogVs v R ρ μ) ≤ bogVlot v h R ρ μ n)
    (hinc : bogUHit v ρ μ n - bogULot v ρ μ n ≤ inc) (hinc0 : 0 ≤ inc) :
    bogMajC v h R ρ μ n ≤
        (2 * 10 ^ 5 * (bogVs v R ρ μ) ^ 2 * inc)
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 4)
      + (10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n))
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 4)
      + (10 ^ 5 * bogVs v R ρ μ * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n))
            / ((1 + bogM v μ * ‖lpt 1 n‖) * ‖tSca v ρ μ n‖ ^ 2)
      + (2 * 10 ^ 3 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 3) := by
  obtain ⟨hr15, hrlo14, h2Δ, h4c1⟩ := gate_facts (h := h) hreg hgate
  have hn : n ≠ 0 := by
    intro h0
    have hrh : bogRHit v ρ μ n = bogHalf v ρ μ := by
      rw [h0, bogRHit, norm_tSca, norm_lpt_eq (bogMesh v ρ μ) hreg.hδpos.le, norm_lpt_zero,
        mul_zero, zero_add]
    have h1 : bogHalf v ρ μ ≤ 7 * (fsX v μ) ^ (3 / 2 : ℝ) := hreg.hΔhigh
    have h2 : (fsX v μ) ^ (3 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one hreg.hXpos.le hreg.hXle (by norm_num)
    have h4 : (16 : ℝ) ≤ bogBigThr v R ρ μ := by
      rw [bogBigThr]
      have hs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
      linarith
    linarith [hgate, hrh, h1, h2, h4]
  have hVs0 : 0 < bogVs v R ρ μ := lt_of_lt_of_le one_pos hreg.hVs1
  have hr0 : 0 < ‖tSca v ρ μ n‖ := by
    have hs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
    nlinarith [hr15, hs]
  have hulo16 : 16 * bogVs v R ρ μ ≤ bogULot v ρ μ n := by
    have h2 : (14 * Real.sqrt (bogVs v R ρ μ)) ^ 2 ≤ (bogRLot v ρ μ n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hrlo14 2
    have h3 : (14 * Real.sqrt (bogVs v R ρ μ)) ^ 2 = 196 * bogVs v R ρ μ := by
      rw [mul_pow, Real.sq_sqrt hVs0.le]
      norm_num
    linarith [hulo8, h2, h3.le, h3.ge]
  have huv : bogULot v ρ μ n / 2 ≤ bogULot v ρ μ n + 2 * bogVlot v h R ρ μ n := by
    linarith [hvl, hulo16]
  have hD : 2 * max 0 ((bogRHit v ρ μ n) ^ 2 - bogULot v ρ μ n)
      + 2 * bogVmaxt v h R ρ μ n ≤ 5 * ‖tSca v ρ μ n‖ ^ 2 := by
    have hulo0 : 0 ≤ bogULot v ρ μ n := le_trans (by linarith [hVs0]) hulo16
    have h1 : max 0 ((bogRHit v ρ μ n) ^ 2 - bogULot v ρ μ n) ≤ (bogRHit v ρ μ n) ^ 2 :=
      max_le (by positivity) (by linarith)
    have h2 : (bogRHit v ρ μ n) ^ 2 ≤ (3 / 2 * ‖tSca v ρ μ n‖) ^ 2 :=
      pow_le_pow_left₀ (by rw [bogRHit]; linarith [hreg.hΔpos.le])
        (by rw [bogRHit]; linarith [h2Δ]) 2
    have hs1 : (1 : ℝ) ≤ 1 + bogM v μ * ‖lpt 1 n‖ := by
      have h : 0 ≤ bogM v μ * ‖lpt 1 n‖ := mul_nonneg hreg.hmpos.le (norm_nonneg _)
      linarith
    have h3 : bogVmaxt v h R ρ μ n ≤ 4 * bogVs v R ρ μ := by
      calc bogVmaxt v h R ρ μ n ≤ 4 * bogVs v R ρ μ / (1 + bogM v μ * ‖lpt 1 n‖) := hV
        _ ≤ 4 * bogVs v R ρ μ := div_le_self (by positivity) hs1
    have h4 : 16 * bogVs v R ρ μ ≤ ‖tSca v ρ μ n‖ ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 15 * Real.sqrt (bogVs v R ρ μ))
        hr15 2
      have h3' : (15 * Real.sqrt (bogVs v R ρ μ)) ^ 2 = 225 * bogVs v R ρ μ := by
        rw [mul_pow, Real.sq_sqrt hVs0.le]
        norm_num
      linarith [h, h3'.le, h3'.ge]
    linarith [h1, h2, h3, h4]
  have hdv : 0 ≤ bogVhit v h R ρ μ n - bogVlot v h R ρ μ n := by
    have hom := bogOm_nonneg (h := h) hreg.hρ0 hav hR.le hreg.hδpos hn
    have h2 : bogVhit v h R ρ μ n - bogVlot v h R ρ μ n = 2 * bogOm v h R ρ μ n := by
      rw [bogVhit, bogVlot]; ring
    rw [h2]; linarith
  have hV0 : 0 ≤ bogVmaxt v h R ρ μ n := by
    rw [bogVmaxt]
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hs0 : 0 < 1 + bogM v μ * ‖lpt 1 n‖ := by
    have h : 0 ≤ bogM v μ * ‖lpt 1 n‖ := mul_nonneg hreg.hmpos.le (norm_nonneg _)
    linarith
  exact bogMajC_core hr0 hreg.hΔpos.le h2Δ rfl rfl hulo8 huv rfl rfl hV0 hV hs0 huhi hvl hdv hD
    hinc hinc0

/-- **The sharp per-cell bound** (case `2c₂ ≤ r_lo`): no `ε_T`-term is needed. -/
lemma bogMajC_le_sharp {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hreg : RegimeC v R ρ μ) (hR : 0 < R) (hav : 0 < a v)
    (hgate : bogBigThr v R ρ μ < bogRHit v ρ μ n)
    (hulo8 : (bogRLot v ρ μ n) ^ 2 / 8 ≤ bogULot v ρ μ n)
    (huhi : bogUHit v ρ μ n ≤ (bogRLot v ρ μ n) ^ 2)
    (hV : bogVmaxt v h R ρ μ n ≤ 4 * bogVs v R ρ μ / (1 + bogM v μ * ‖lpt 1 n‖))
    (hvl : -(2 * bogVs v R ρ μ) ≤ bogVlot v h R ρ μ n)
    (hcase : 2 * bogC2 v ρ μ ≤ bogRLot v ρ μ n) :
    bogMajC v h R ρ μ n ≤
        (10 ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 3)
      + (10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n))
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 4)
      + (10 ^ 5 * bogVs v R ρ μ * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n))
            / ((1 + bogM v μ * ‖lpt 1 n‖) * ‖tSca v ρ μ n‖ ^ 2) := by
  have hρ := hreg.hρ0
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hxle : bogRLot v ρ μ n ≤ bogRHit v ρ μ n := by
    rw [bogRLot, bogRHit]; linarith [hreg.hΔpos.le]
  have hdiff : bogUHit v ρ μ n - bogULot v ρ μ n
      ≤ (bogRHit v ρ μ n) ^ 2 - (bogRLot v ρ μ n) ^ 2 := by
    have h := tauScRad_diff_le_quad (v := v) (ρ := ρ) (μ := μ) hP hreg.heTpos
      (le_trans hreg.heThalf (by norm_num)) hreg.hc1pos hreg.hc2pos hreg.hc12 hcase hxle
    simpa only [bogUHit, bogULot] using h
  have hyx : (bogRHit v ρ μ n) ^ 2 - (bogRLot v ρ μ n) ^ 2
      = 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖ := by
    rw [bogRHit, bogRLot]; ring
  have hinc : bogUHit v ρ μ n - bogULot v ρ μ n ≤ 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖ := by
    linarith [hdiff, hyx.le]
  have hinc0 : 0 ≤ 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖ := by
    have h1 : 0 ≤ bogHalf v ρ μ * ‖tSca v ρ μ n‖ :=
      mul_nonneg hreg.hΔpos.le (norm_nonneg _)
    linarith
  have hcore := bogMajC_le_of_inc hreg hR hav hgate hulo8 huhi hV hvl hinc hinc0
  refine le_trans hcore ?_
  have hVs0 : 0 < bogVs v R ρ μ := lt_of_lt_of_le one_pos hreg.hVs1
  have hΔ0 : 0 ≤ bogHalf v ρ μ := hreg.hΔpos.le
  have hr0 : 0 < ‖tSca v ρ μ n‖ := by
    have h := (gate_facts (h := h) hreg hgate).1
    have hs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
    nlinarith [h, hs]
  have hs0 : 0 < 1 + bogM v μ * ‖lpt 1 n‖ := by
    have h : 0 ≤ bogM v μ * ‖lpt 1 n‖ := mul_nonneg hreg.hmpos.le (norm_nonneg _)
    linarith
  field_simp
  nlinarith [hVs0, hΔ0, hr0, hs0, mul_pos hs0 hr0, pow_pos hs0 2, pow_pos hr0 3]


lemma bogMajC_le_crude {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hreg : RegimeC v R ρ μ) (hR : 0 < R) (hav : 0 < a v)
    (hgate : bogBigThr v R ρ μ < bogRHit v ρ μ n)
    (hulo8 : (bogRLot v ρ μ n) ^ 2 / 8 ≤ bogULot v ρ μ n)
    (huhi : bogUHit v ρ μ n ≤ (bogRLot v ρ μ n) ^ 2)
    (hV : bogVmaxt v h R ρ μ n ≤ 4 * bogVs v R ρ μ / (1 + bogM v μ * ‖lpt 1 n‖))
    (hvl : -(2 * bogVs v R ρ μ) ≤ bogVlot v h R ρ μ n) :
    bogMajC v h R ρ μ n ≤
        (10 ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 3)
      + (10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n))
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 4)
      + (10 ^ 5 * bogVs v R ρ μ * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n))
            / ((1 + bogM v μ * ‖lpt 1 n‖) * ‖tSca v ρ μ n‖ ^ 2)
      + (10 ^ 6 * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT)
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 2) := by
  have hP : 0 < ρ * a v := mul_pos hreg.hρ0 hav
  have hc1pos : 0 < bogC1 v ρ μ := hreg.hc1pos
  obtain ⟨hr15, hrlo14, h2Δ, h4c1⟩ := gate_facts (h := h) hreg hgate
  have hxle : bogRLot v ρ μ n ≤ bogRHit v ρ μ n := by
    rw [bogRLot, bogRHit]; linarith [hreg.hΔpos.le]
  have hdiff : bogUHit v ρ μ n - bogULot v ρ μ n
      ≤ ((bogRHit v ρ μ n) ^ 2 - (bogRLot v ρ μ n) ^ 2)
        + (paramsAt μ (a v)).eT * (max 0 (bogRHit v ρ μ n - bogC2 v ρ μ)) ^ 2 := by
    have h := tauScRad_diff_le (v := v) (ρ := ρ) (μ := μ) hP hreg.heTpos
      (le_trans hreg.heThalf (by norm_num)) hreg.hc1pos hreg.hc2pos
      (x := bogRLot v ρ μ n) (y := bogRHit v ρ μ n) (by linarith [hc1pos]) hxle
    simpa only [bogUHit, bogULot] using h
  have hyx : (bogRHit v ρ μ n) ^ 2 - (bogRLot v ρ μ n) ^ 2
      = 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖ := by
    rw [bogRHit, bogRLot]; ring
  have hr0 : 0 < ‖tSca v ρ μ n‖ := by
    have hs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
    nlinarith [hr15, hs]
  have hmax2 : (max 0 (bogRHit v ρ μ n - bogC2 v ρ μ)) ^ 2 ≤ 4 * ‖tSca v ρ μ n‖ ^ 2 := by
    have h1 : max 0 (bogRHit v ρ μ n - bogC2 v ρ μ) ≤ bogRHit v ρ μ n :=
      max_le (by rw [bogRHit]; linarith [hreg.hΔpos.le]) (by linarith [hreg.hc2pos.le])
    have h2 : bogRHit v ρ μ n ≤ 3 / 2 * ‖tSca v ρ μ n‖ := by
      rw [bogRHit]; linarith [h2Δ]
    have h3 : 0 ≤ max 0 (bogRHit v ρ μ n - bogC2 v ρ μ) := le_max_left _ _
    have h4 : (bogRHit v ρ μ n) ^ 2 ≤ (3 / 2 * ‖tSca v ρ μ n‖) ^ 2 :=
      pow_le_pow_left₀ (by rw [bogRHit]; linarith [hreg.hΔpos.le]) h2 2
    nlinarith [pow_le_pow_left₀ h3 h1 2, h4, hr0]
  have hinc : bogUHit v ρ μ n - bogULot v ρ μ n
      ≤ 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖ + 4 * (paramsAt μ (a v)).eT * ‖tSca v ρ μ n‖ ^ 2 := by
    have h1 : (paramsAt μ (a v)).eT * (max 0 (bogRHit v ρ μ n - bogC2 v ρ μ)) ^ 2
        ≤ (paramsAt μ (a v)).eT * (4 * ‖tSca v ρ μ n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmax2 hreg.heTpos
    linarith [hdiff, h1, hyx]
  have hinc0 : 0 ≤ 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖
      + 4 * (paramsAt μ (a v)).eT * ‖tSca v ρ μ n‖ ^ 2 := by
    have h1 : 0 ≤ 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖ :=
      mul_nonneg (mul_nonneg (by norm_num) hreg.hΔpos.le) (norm_nonneg _)
    have h2 : 0 ≤ 4 * (paramsAt μ (a v)).eT * ‖tSca v ρ μ n‖ ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hreg.heTpos) (sq_nonneg _)
    linarith
  have hcore := bogMajC_le_of_inc hreg hR hav hgate hulo8 huhi hV hvl hinc hinc0
  refine le_trans hcore ?_
  have hVs0 : 0 < bogVs v R ρ μ := lt_of_lt_of_le one_pos hreg.hVs1
  have hΔ0 : 0 ≤ bogHalf v ρ μ := hreg.hΔpos.le
  have heT0 : 0 ≤ (paramsAt μ (a v)).eT := hreg.heTpos
  have hr0 : 0 < ‖tSca v ρ μ n‖ := by
    have hs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
    nlinarith [hr15, hs]
  have hs0 : 0 < 1 + bogM v μ * ‖lpt 1 n‖ := by
    have h : 0 ≤ bogM v μ * ‖lpt 1 n‖ := mul_nonneg hreg.hmpos.le (norm_nonneg _)
    linarith
  field_simp
  nlinarith [hVs0, hΔ0, heT0, hr0, hs0, mul_pos hs0 hr0, pow_pos hs0 2, pow_pos hr0 3,
    mul_nonneg (mul_nonneg hVs0.le hΔ0) (norm_nonneg (tSca v ρ μ n)),
    mul_nonneg (mul_nonneg hVs0.le (sq_nonneg (‖tSca v ρ μ n‖))) heT0]

/-! ## 4. The lattice majorant of the region-C sum -/

/-- The summable majorant of the region-C sum: the three profiles with the decayed
coefficients, plus the `ε_T`-kink term (only on the cells with `r_lo < 2c₂`, whose number is
controlled by the counting bound). -/
def bogG (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  (10 ^ 6) * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ * bogP1 v ρ μ n
    + (4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ * bogP3 v ρ μ n
    + (4 * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ * bogP2 v ρ μ n
    + (if bogRLot v ρ μ n < 2 * bogC2 v ρ μ then
        (10 ^ 6) * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT * bogP2 v ρ μ n
      else 0)

/-- The four summands of `bogG`, named so that the `tsum` decomposition is syntactic. -/
def bogG1 (v : E3 → ℝ) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  (10 ^ 6) * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ * bogP1 v ρ μ n

def bogG2 (v : E3 → ℝ) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  (4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ * bogP3 v ρ μ n

def bogG3 (v : E3 → ℝ) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  (4 * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ * bogP2 v ρ μ n

def bogG4 (v : E3 → ℝ) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if bogRLot v ρ μ n < 2 * bogC2 v ρ μ then
    (10 ^ 6) * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT * bogP2 v ρ μ n
  else 0

lemma bogG_eq (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) :
    bogG v h R ρ μ n = bogG1 v R ρ μ n + bogG2 v R ρ μ n + bogG3 v R ρ μ n
      + bogG4 v R ρ μ n := rfl

/-- **The pointwise domination** of the region-C sum by the lattice majorant `bogG`. -/
lemma bogS3_le_bogG {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ}
    (hreg : RegimeC v R ρ μ) (hC : Core v R μ ρ) (hR : 0 < R) (hav : 0 < a v)
    (hv : ∀ x, 0 ≤ v x) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) (n : Fin 3 → ℤ) :
    bogS3 v h R ρ μ n ≤ bogG v h R ρ μ n := by
  have hP : 0 < ρ * a v := mul_pos hreg.hρ0 hav
  have hK0 : 0 ≤ bogOscM v R ρ μ := bogOscM_nonneg hR.le hav hreg.hρ0 hreg.hδpos
  have hVs0 : 0 < bogVs v R ρ μ := lt_of_lt_of_le one_pos hreg.hVs1
  have hVsnn : 0 ≤ bogVs v R ρ μ := hVs0.le
  have hΔ0 : 0 ≤ bogHalf v ρ μ := hreg.hΔpos.le
  have heT0 : 0 ≤ (paramsAt μ (a v)).eT := hreg.heTpos
  have hP1nn : ∀ m : Fin 3 → ℤ, 0 ≤ bogP1 v ρ μ m := fun m => by
    rw [bogP1]
    exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
      (mul_nonneg hreg.hmpos.le (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 3))
  have hP2nn : ∀ m : Fin 3 → ℤ, 0 ≤ bogP2 v ρ μ m := fun m => by
    rw [bogP2]
    exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
      (mul_nonneg hreg.hmpos.le (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 2))
  have hP3nn : ∀ m : Fin 3 → ℤ, 0 ≤ bogP3 v ρ μ m := fun m => by
    rw [bogP3]
    exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
      (mul_nonneg hreg.hmpos.le (norm_nonneg _))) 3) (pow_nonneg (norm_nonneg _) 4))
  have hGnn : ∀ m : Fin 3 → ℤ, 0 ≤ bogG v h R ρ μ m := fun m => by
    rw [bogG]
    have h1 : 0 ≤ (10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ * bogP1 v ρ μ m :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hΔ0) (hP1nn m)
    have h2 : 0 ≤ (4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ * bogP3 v ρ μ m :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hK0) (hP3nn m)
    have h3 : 0 ≤ (4 * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ * bogP2 v ρ μ m :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hVsnn) hK0) (hP2nn m)
    have h4 : 0 ≤ (if bogRLot v ρ μ m < 2 * bogC2 v ρ μ then
        (10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT * bogP2 v ρ μ m
        else 0) := by
      by_cases hq : bogRLot v ρ μ m < 2 * bogC2 v ρ μ
      · rw [if_pos hq]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) heT0) (hP2nn m)
      · rw [if_neg hq]
    linarith
  by_cases hn : n = 0
  · subst hn
    rw [bogS3, if_neg (not_lt.mpr ?_)]
    · exact hGnn 0
    · rw [bogRHit, norm_tSca, norm_lpt_eq (bogMesh v ρ μ) hreg.hδpos.le, norm_lpt_zero,
        mul_zero, zero_add]
      have h1 : bogHalf v ρ μ ≤ 7 * (fsX v μ) ^ (3 / 2 : ℝ) := hreg.hΔhigh
      have h2 : (fsX v μ) ^ (3 / 2 : ℝ) ≤ 1 :=
        Real.rpow_le_one hreg.hXpos.le hreg.hXle (by norm_num)
      have h4 : (16 : ℝ) ≤ bogBigThr v R ρ μ := by
        rw [bogBigThr]
        have hs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
        linarith
      linarith [h1, h2, h4]
  · rw [bogS3]
    by_cases hgate : bogBigThr v R ρ μ < bogRHit v ρ μ n
    · rw [if_pos hgate]
      obtain ⟨hr15, hrlo14, h2Δ, h4c1⟩ := gate_facts (h := h) hreg hgate
      have hℓ : 0 < ell v μ := sb_ell_pos hav hC
      have hVMD := bogVmaxt_le_decay (h := h) hR hreg.hρ0 hav hv hvrad hv_supp hRℓ
        hreg.hδpos hn h2Δ hreg.hOs1
      have he : Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖ = bogM v μ * ‖lpt 1 n‖ := by
        rw [norm_tSca_eq hreg.hδpos.le n, ← mul_assoc, hreg.hmesh]
      have hV : bogVmaxt v h R ρ μ n ≤ 4 * bogVs v R ρ μ / (1 + bogM v μ * ‖lpt 1 n‖) := by
        have h := hVMD.1
        rwa [he] at h
      have hvl : -(2 * bogVs v R ρ μ) ≤ bogVlot v h R ρ μ n := hVMD.2.1
      have hdv : bogVhit v h R ρ μ n - bogVlot v h R ρ μ n
          ≤ 4 * bogOscM v R ρ μ / (1 + bogM v μ * ‖lpt 1 n‖) := by
        have h := hVMD.2.2
        rwa [he] at h
      have hulo8 : (bogRLot v ρ μ n) ^ 2 / 8 ≤ bogULot v ρ μ n :=
        tauScRad_ge_eighth hP hreg.hc1pos hreg.heTpos hreg.heThalf h4c1
      have huhi : bogUHit v ρ μ n ≤ (bogRLot v ρ μ n) ^ 2 := by
        have hrel : 2 * bogHalf v ρ μ = (4 * Real.pi * Real.sqrt 3 * fsX v μ) * bogC1 v ρ μ :=
          sb_half_eq hav hreg.hμ0 hreg.hρ0 hℓ
        have h4Δle : 4 * bogHalf v ρ μ ≤ (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ := by
          have h8 : 8 * Real.pi * Real.sqrt 3 * fsX v μ ≤ 1 - (paramsAt μ (a v)).eT := by
            have hπ3 : Real.pi * Real.sqrt 3 ≤ 8 := by
              have h3 : Real.sqrt 3 ≤ 2 := by
                nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
              have h := mul_le_mul Real.pi_le_four h3 (Real.sqrt_nonneg 3)
                (by norm_num : (0 : ℝ) ≤ 4)
              linarith
            have h1 : 8 * Real.pi * Real.sqrt 3 * fsX v μ ≤ 64 * fsX v μ := by
              have h64 : 8 * Real.pi * Real.sqrt 3 ≤ 64 := by
                calc 8 * Real.pi * Real.sqrt 3 = 8 * (Real.pi * Real.sqrt 3) := by ring
                  _ ≤ 8 * 8 := mul_le_mul_of_nonneg_left hπ3 (by norm_num)
                  _ = 64 := by norm_num
              exact mul_le_mul_of_nonneg_right h64 hreg.hXpos.le
            have h2 : 64 * fsX v μ ≤ 64 * (1 / 1000) := by linarith [hreg.hXlt]
            linarith [h1, h2, hreg.heThalf]
          calc 4 * bogHalf v ρ μ = 2 * (2 * bogHalf v ρ μ) := by ring
            _ = 2 * ((4 * Real.pi * Real.sqrt 3 * fsX v μ) * bogC1 v ρ μ) := by rw [hrel]
            _ = (8 * Real.pi * Real.sqrt 3 * fsX v μ) * bogC1 v ρ μ := by ring
            _ ≤ (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ :=
                mul_le_mul_of_nonneg_right h8 hreg.hc1pos.le
        have hrhi_c1 : bogC1 v ρ μ ≤ bogRHit v ρ μ n := by
          have h16 : (16 : ℝ) ≤ 16 * Real.sqrt (bogVs v R ρ μ) := by
            have hs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
            linarith
          have hXh : (fsX v μ) ^ (1 / 2 : ℝ) ≤ 1 :=
            Real.rpow_le_one hreg.hXpos.le hreg.hXle (by norm_num)
          rw [bogBigThr] at hgate
          linarith [hgate, hreg.hc1le, hXh]
        have hsub := sb_tau_sub_ge (v := v) (ρ := ρ) (μ := μ) hP hreg.hc1pos hreg.hc2pos
          hreg.heTpos (le_trans hreg.heThalf (by norm_num)) hrhi_c1
        have hnorm_le : ‖tSca v ρ μ n‖ ≤ bogRHit v ρ μ n := by
          rw [bogRHit]; linarith [hreg.hΔpos.le]
        have hφnn : 0 ≤ (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ :=
          mul_nonneg (by linarith [hreg.heThalf]) hreg.hc1pos.le
        have hkey : 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖
            ≤ (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ * bogRHit v ρ μ n := by
          calc 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖
              ≤ ((1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ) * ‖tSca v ρ μ n‖ :=
                mul_le_mul_of_nonneg_right h4Δle (norm_nonneg _)
            _ ≤ ((1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ) * bogRHit v ρ μ n :=
                mul_le_mul_of_nonneg_left hnorm_le hφnn
            _ = (1 - (paramsAt μ (a v)).eT) * bogC1 v ρ μ * bogRHit v ρ μ n := by ring
        have hsqdiff : (bogRHit v ρ μ n) ^ 2 - (bogRLot v ρ μ n) ^ 2
            = 4 * bogHalf v ρ μ * ‖tSca v ρ μ n‖ := by rw [bogRHit, bogRLot]; ring
        rw [bogUHit]
        linarith [hsub, hkey, hsqdiff]
      refine max_le (hGnn n) ?_
      have hr0 : 0 < ‖tSca v ρ μ n‖ := by
        have hs : 1 ≤ Real.sqrt (bogVs v R ρ μ) := Real.one_le_sqrt.mpr hreg.hVs1
        nlinarith [hr15, hs]
      have hs0 : 0 < 1 + bogM v μ * ‖lpt 1 n‖ := by
        have h : 0 ≤ bogM v μ * ‖lpt 1 n‖ := mul_nonneg hreg.hmpos.le (norm_nonneg _)
        linarith
      have hdv' : (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n)
          * (1 + bogM v μ * ‖lpt 1 n‖) ≤ 4 * bogOscM v R ρ μ := by
        rw [← le_div_iff₀ hs0]; exact hdv
      have e1 : 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n)
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 4)
          ≤ 4 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 3 * ‖tSca v ρ μ n‖ ^ 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n)
              * ((1 + bogM v μ * ‖lpt 1 n‖) ^ 3 * ‖tSca v ρ μ n‖ ^ 4)
            = (10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (1 + bogM v μ * ‖lpt 1 n‖) ^ 2
                * ‖tSca v ρ μ n‖ ^ 4)
              * ((bogVhit v h R ρ μ n - bogVlot v h R ρ μ n)
                * (1 + bogM v μ * ‖lpt 1 n‖)) := by ring
          _ ≤ (10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (1 + bogM v μ * ‖lpt 1 n‖) ^ 2
                * ‖tSca v ρ μ n‖ ^ 4) * (4 * bogOscM v R ρ μ) :=
              mul_le_mul_of_nonneg_left hdv' (by positivity)
          _ = 4 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ
                * ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 4) := by ring
      have e2 : 10 ^ 5 * bogVs v R ρ μ * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n)
            / ((1 + bogM v μ * ‖lpt 1 n‖) * ‖tSca v ρ μ n‖ ^ 2)
          ≤ 4 * 10 ^ 5 * bogVs v R ρ μ * bogOscM v R ρ μ
            / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc 10 ^ 5 * bogVs v R ρ μ * (bogVhit v h R ρ μ n - bogVlot v h R ρ μ n)
              * ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖tSca v ρ μ n‖ ^ 2)
            = (10 ^ 5 * bogVs v R ρ μ * (1 + bogM v μ * ‖lpt 1 n‖) * ‖tSca v ρ μ n‖ ^ 2)
              * ((bogVhit v h R ρ μ n - bogVlot v h R ρ μ n)
                * (1 + bogM v μ * ‖lpt 1 n‖)) := by ring
          _ ≤ (10 ^ 5 * bogVs v R ρ μ * (1 + bogM v μ * ‖lpt 1 n‖) * ‖tSca v ρ μ n‖ ^ 2)
                * (4 * bogOscM v R ρ μ) := mul_le_mul_of_nonneg_left hdv' (by positivity)
          _ = 4 * 10 ^ 5 * bogVs v R ρ μ * bogOscM v R ρ μ
                * ((1 + bogM v μ * ‖lpt 1 n‖) * ‖tSca v ρ μ n‖ ^ 2) := by ring
      by_cases hcase : 2 * bogC2 v ρ μ ≤ bogRLot v ρ μ n
      · have hb := bogMajC_le_sharp (h := h) hreg hR hav hgate hulo8 huhi hV hvl hcase
        rw [bogG, bogP1, bogP2, bogP3, if_neg (not_lt.mpr hcase)]
        ring_nf at hb e1 e2 ⊢
        linarith
      · have hcase' : bogRLot v ρ μ n < 2 * bogC2 v ρ μ := lt_of_not_ge hcase
        have hb := bogMajC_le_crude (h := h) hreg hR hav hgate hulo8 huhi hV hvl
        rw [bogG, bogP1, bogP2, bogP3, if_pos hcase']
        ring_nf at hb e1 e2 ⊢
        linarith
    · rw [if_neg hgate]
      exact hGnn n

/-! ## 5. The three profile sums -/

lemma bogP1_nonneg {v : E3 → ℝ} {ρ μ : ℝ} (hm : 0 ≤ bogM v μ) (n : Fin 3 → ℤ) :
    0 ≤ bogP1 v ρ μ n := by
  rw [bogP1]
  exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
    (mul_nonneg hm (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 3))

lemma bogP2_nonneg {v : E3 → ℝ} {ρ μ : ℝ} (hm : 0 ≤ bogM v μ) (n : Fin 3 → ℤ) :
    0 ≤ bogP2 v ρ μ n := by
  rw [bogP2]
  exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
    (mul_nonneg hm (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 2))

lemma bogP3_nonneg {v : E3 → ℝ} {ρ μ : ℝ} (hm : 0 ≤ bogM v μ) (n : Fin 3 → ℤ) :
    0 ≤ bogP3 v ρ μ n := by
  rw [bogP3]
  exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
    (mul_nonneg hm (norm_nonneg _))) 3) (pow_nonneg (norm_nonneg _) 4))

/-- The elementary factoring of a `1/(K·(δx)^j)` into `δ^{-j}` times the profile. -/
private lemma inv_factor (K δ x : ℝ) (j : ℕ) :
    1 / (K * (δ * x) ^ j) = (δ ^ (j : ℝ))⁻¹ * (1 / (K * x ^ j)) := by
  rw [Real.rpow_natCast δ j, one_div, one_div, ← mul_inv]
  congr 1
  rw [mul_pow]
  ring

/-- The pointwise profile identity of `bogP1`. -/
lemma bogP1_eq {v : E3 → ℝ} {R ρ μ : ℝ} (hreg : RegimeC v R ρ μ) (n : Fin 3 → ℤ) :
    bogP1 v ρ μ n = (bogMesh v ρ μ) ^ (-(3 : ℝ))
      * (1 / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 3)) := by
  have hδ := hreg.hδpos
  rw [bogP1, norm_tSca_eq hδ.le n, Real.rpow_neg hδ.le]
  exact inv_factor _ _ _ 3

/-- The pointwise profile identity of `bogP2`. -/
lemma bogP2_eq {v : E3 → ℝ} {R ρ μ : ℝ} (hreg : RegimeC v R ρ μ) (n : Fin 3 → ℤ) :
    bogP2 v ρ μ n = (bogMesh v ρ μ) ^ (-(2 : ℝ))
      * (1 / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 2)) := by
  have hδ := hreg.hδpos
  rw [bogP2, norm_tSca_eq hδ.le n, Real.rpow_neg hδ.le]
  exact inv_factor _ _ _ 2

/-- The pointwise profile identity of `bogP3`. -/
lemma bogP3_eq {v : E3 → ℝ} {R ρ μ : ℝ} (hreg : RegimeC v R ρ μ) (n : Fin 3 → ℤ) :
    bogP3 v ρ μ n = (bogMesh v ρ μ) ^ (-(4 : ℝ))
      * (1 / ((1 + bogM v μ * ‖lpt 1 n‖) ^ 3 * ‖lpt 1 n‖ ^ 4)) := by
  have hδ := hreg.hδpos
  rw [bogP3, norm_tSca_eq hδ.le n, Real.rpow_neg hδ.le]
  exact inv_factor _ _ _ 4

/-- `Σ'bogP1 ≤ δ^{-3}·100(1+log(2+1/m))`. -/
lemma tsum_bogP1_le {v : E3 → ℝ} {R ρ μ : ℝ} (hreg : RegimeC v R ρ μ) :
    (∑' n : Fin 3 → ℤ, bogP1 v ρ μ n)
      ≤ (bogMesh v ρ μ) ^ (-(3 : ℝ)) * (100 * (1 + Real.log (2 + 1 / bogM v μ))) := by
  have hδ := hreg.hδpos
  rw [tsum_congr (fun n => bogP1_eq hreg n), tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_two_cube (bogM v μ) hreg.hmpos)
    (Real.rpow_nonneg hδ.le _)

/-- `Σ'bogP2 ≤ δ^{-2}·100(1+1/m)`. -/
lemma tsum_bogP2_le {v : E3 → ℝ} {R ρ μ : ℝ} (hreg : RegimeC v R ρ μ) :
    (∑' n : Fin 3 → ℤ, bogP2 v ρ μ n)
      ≤ (bogMesh v ρ μ) ^ (-(2 : ℝ)) * (100 * (1 / bogM v μ + 1)) := by
  have hδ := hreg.hδpos
  rw [tsum_congr (fun n => bogP2_eq hreg n), tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_two_sq (bogM v μ) hreg.hmpos)
    (Real.rpow_nonneg hδ.le _)

/-- `Σ'bogP3 ≤ δ^{-4}·100`. -/
lemma tsum_bogP3_le {v : E3 → ℝ} {R ρ μ : ℝ} (hreg : RegimeC v R ρ μ) :
    (∑' n : Fin 3 → ℤ, bogP3 v ρ μ n) ≤ (bogMesh v ρ μ) ^ (-(4 : ℝ)) * 100 := by
  have hδ := hreg.hδpos
  rw [tsum_congr (fun n => bogP3_eq hreg n), tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_three_four (bogM v μ) hreg.hmpos)
    (Real.rpow_nonneg hδ.le _)

/-! ## 4b. The `X`-power form of the parameter block -/

/-- `dil^c = X^{323c}` with `X = fsX v μ = dil^{1/323}`. -/
lemma rpow_dil {v : E3 → ℝ} {R ρ μ : ℝ} (hC : Core v R μ ρ) (c : ℝ) :
    (dil v μ) ^ c = (fsX v μ) ^ (323 * c) := by
  have hX0 : 0 ≤ fsX v μ := Real.rpow_nonneg hC.hD0.le _
  rw [← fsX_rpow_323 hC.hD0, ← Real.rpow_mul hX0]

lemma kl_eq_fsX {v : E3 → ℝ} {R ρ μ : ℝ} (hC : Core v R μ ρ) :
    (paramsAt μ (a v)).Kl = (fsX v μ) ^ (-(3 / 2 : ℝ)) := by
  rw [paramsAt_Kl, rpow_dil hC]
  norm_num

lemma sKl_inv_eq {v : E3 → ℝ} {R ρ μ : ℝ} (hC : Core v R μ ρ) :
    ((paramsAt μ (a v)).Kl * (paramsAt μ (a v)).s)⁻¹ = (fsX v μ) ^ (1 / 2 : ℝ) := by
  have h : (paramsAt μ (a v)).Kl * (paramsAt μ (a v)).s
      = (paramsAt μ (a v)).s * (paramsAt μ (a v)).Kl := by ring
  rw [h, sKl_inv v μ hC.hD0, rpow_dil hC]
  norm_num

lemma dsKl_inv_eq {v : E3 → ℝ} {R ρ μ : ℝ} (hC : Core v R μ ρ) :
    ((paramsAt μ (a v)).Kl * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s)⁻¹
      = (fsX v μ) ^ (-(11 / 2 : ℝ)) := by
  have h : (paramsAt μ (a v)).Kl * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s
      = (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * (paramsAt μ (a v)).Kl := by ring
  have hXpos : 0 < fsX v μ := Real.rpow_pos_of_pos hC.hD0 _
  rw [h, dsKl_eq v μ hC.hD0, rpow_dil hC, Real.rpow_neg hXpos.le]
  norm_num

lemma eT_eq_fsX {v : E3 → ℝ} {R ρ μ : ℝ} (hC : Core v R μ ρ) :
    (paramsAt μ (a v)).eT = (fsX v μ) ^ (23 / 4 : ℝ) := by
  rw [paramsAt_eT, rpow_dil hC]
  norm_num

/-- The ratio `√(μ/ρ)` is trapped in `[9/10, 11/10]`. -/
lemma sqrt_ratio_bounds {v : E3 → ℝ} {R ρ μ : ℝ} (hC : Core v R μ ρ) :
    (9 / 10 : ℝ) ≤ Real.sqrt (μ / ρ) ∧ Real.sqrt (μ / ρ) ≤ 11 / 10 := by
  have hρ := hC.hρ0
  have hratio_lo : (10 / 11 : ℝ) ≤ μ / ρ := by
    rw [le_div_iff₀ hρ]; linarith [hC.hρhi]
  have hratio_hi : μ / ρ ≤ 10 / 9 := by
    rw [div_le_iff₀ hρ]; linarith [hC.hρlo]
  constructor
  · have h : Real.sqrt (10 / 11) ≤ Real.sqrt (μ / ρ) := Real.sqrt_le_sqrt hratio_lo
    have h2 : (9 / 10 : ℝ) ≤ Real.sqrt (10 / 11) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 / 11 by norm_num),
        Real.sqrt_nonneg (10 / 11)]
    linarith
  · have h : Real.sqrt (μ / ρ) ≤ Real.sqrt (10 / 9) := Real.sqrt_le_sqrt hratio_hi
    have h2 : Real.sqrt (10 / 9) ≤ 11 / 10 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 / 9 by norm_num),
        Real.sqrt_nonneg (10 / 9)]
    linarith

/-- The mesh in `X`-power form: `δ = 2π√(μ/ρ)·X^{3/2}`. -/
lemma bogMesh_eq_para {v : E3 → ℝ} {R ρ μ : ℝ} (hav : 0 < a v) (hC : Core v R μ ρ) :
    bogMesh v ρ μ = 2 * Real.pi * Real.sqrt (μ / ρ) * (fsX v μ) ^ (3 / 2 : ℝ) := by
  have hμ := hC.hμ
  have hρ := hC.hρ0
  have hXpos : 0 < fsX v μ := Real.rpow_pos_of_pos hC.hD0 _
  have hkey := invsqrt_mul_sqrt v ρ μ hav hμ hρ
  have hℓ : ell v μ * Real.sqrt (ρ * a v)
      = (fsX v μ) ^ (-(3 / 2 : ℝ)) * Real.sqrt (ρ / μ) := by
    rw [hC.hℓ, ← hkey]
    rw [← mul_assoc, kl_eq_fsX hC]
  rw [bogMesh, div_div, hℓ, Real.rpow_neg hXpos.le]
  have hsinv : (Real.sqrt (ρ / μ))⁻¹ = Real.sqrt (μ / ρ) := by
    rw [← Real.sqrt_inv]
    congr 1
    field_simp
  rw [div_eq_mul_inv, mul_inv_rev, hsinv, inv_inv]
  ring

/-- The first cutoff in `X`-power form: `c₁ = ½√(μ/ρ)·X^{1/2}`. -/
lemma bogC1_eq_para {v : E3 → ℝ} {R ρ μ : ℝ} (hav : 0 < a v) (hC : Core v R μ ρ) :
    bogC1 v ρ μ = 1 / 2 * Real.sqrt (μ / ρ) * (fsX v μ) ^ (1 / 2 : ℝ) := by
  rw [bogC1_eq v ρ μ hav hC.hμ hC.hρ0, sKl_inv_eq hC]
  ring

/-- The second cutoff in `X`-power form: `c₂ = ½√(μ/ρ)·X^{-11/2}`. -/
lemma bogC2_eq_para {v : E3 → ℝ} {R ρ μ : ℝ} (hav : 0 < a v) (hC : Core v R μ ρ) :
    bogC2 v ρ μ = 1 / 2 * Real.sqrt (μ / ρ) * (fsX v μ) ^ (-(11 / 2 : ℝ)) := by
  rw [bogC2_eq v ρ μ hav hC.hμ hC.hρ0, dsKl_inv_eq hC]
  ring

/-- **The regime data from `Core`**: the `X`-power bounds of the parameter block. -/
theorem regimeC_of_core {v : E3 → ℝ} {R ρ μ : ℝ} (hR : 0 < R) (hav : 0 < a v)
    (hC : Core v R μ ρ) (hX1 : fsX v μ ≤ 1 / 1000) (hXa : fsX v μ ≤ (a v) ^ 2 / 8) :
    RegimeC v R ρ μ := by
  have hμ := hC.hμ
  have hρ := hC.hρ0
  have hXpos : 0 < fsX v μ := Real.rpow_pos_of_pos hC.hD0 _
  have hXle : fsX v μ ≤ 1 := le_trans hX1 (by norm_num)
  have hX3 : (0 : ℝ) < (fsX v μ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hXpos _
  obtain ⟨hsq_lo, hsq_hi⟩ := sqrt_ratio_bounds hC
  have hδeq := bogMesh_eq_para hav hC
  have hδpos : 0 < bogMesh v ρ μ := by
    rw [hδeq]; positivity
  have hδlow : 5 * (fsX v μ) ^ (3 / 2 : ℝ) ≤ bogMesh v ρ μ := by
    rw [hδeq]
    have hπ : (5 : ℝ) ≤ 2 * Real.pi * (9 / 10) := by nlinarith [Real.pi_gt_three]
    calc 5 * (fsX v μ) ^ (3 / 2 : ℝ)
        ≤ (2 * Real.pi * (9 / 10)) * (fsX v μ) ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hπ hX3.le
      _ ≤ (2 * Real.pi * Real.sqrt (μ / ρ)) * (fsX v μ) ^ (3 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hX3.le
          exact mul_le_mul_of_nonneg_left hsq_lo (by positivity)
      _ = 2 * Real.pi * Real.sqrt (μ / ρ) * (fsX v μ) ^ (3 / 2 : ℝ) := by ring
  have hδhigh : bogMesh v ρ μ ≤ 8 * (fsX v μ) ^ (3 / 2 : ℝ) := by
    rw [hδeq]
    calc 2 * Real.pi * Real.sqrt (μ / ρ) * (fsX v μ) ^ (3 / 2 : ℝ)
        ≤ (2 * Real.pi * (11 / 10)) * (fsX v μ) ^ (3 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hX3.le
          exact mul_le_mul_of_nonneg_left hsq_hi (by positivity)
      _ ≤ 8 * (fsX v μ) ^ (3 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hX3.le
          nlinarith [Real.pi_lt_d4]
  have hΔpos : 0 < bogHalf v ρ μ := by
    rw [bogHalf]; positivity
  have hΔhigh : bogHalf v ρ μ ≤ 7 * (fsX v μ) ^ (3 / 2 : ℝ) := by
    rw [bogHalf]
    have h3 : Real.sqrt 3 ≤ 7 / 4 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    calc bogMesh v ρ μ * Real.sqrt 3 / 2
        ≤ (8 * (fsX v μ) ^ (3 / 2 : ℝ)) * (7 / 4) / 2 := by
          refine div_le_div_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul hδhigh h3 (Real.sqrt_nonneg 3) (by positivity)
      _ = 7 * (fsX v μ) ^ (3 / 2 : ℝ) := by ring
  have hΔle : bogHalf v ρ μ ≤ 1 := by
    refine le_trans hΔhigh ?_
    have h1 : (fsX v μ) ^ (3 / 2 : ℝ) ≤ 1 / 1000 := by
      refine le_trans (Real.rpow_le_rpow hXpos.le hX1 (by norm_num)) ?_
      have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 1000)
        (by norm_num : (1 / 1000 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 3 / 2)
      simpa using h
    have h7 : (7 : ℝ) * (1 / 1000) ≤ 1 := by norm_num
    nlinarith [h1, h7, hX3]
  have hc1pos : 0 < bogC1 v ρ μ := sb_c1_pos hav hC
  have hc1le : bogC1 v ρ μ ≤ (fsX v μ) ^ (1 / 2 : ℝ) := by
    rw [bogC1_eq_para hav hC]
    have hXh : (0 : ℝ) ≤ (fsX v μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hXpos.le _
    have hc : (1 / 2 : ℝ) * Real.sqrt (μ / ρ) ≤ 1 := by linarith [hsq_hi]
    calc 1 / 2 * Real.sqrt (μ / ρ) * (fsX v μ) ^ (1 / 2 : ℝ)
        = (1 / 2 * Real.sqrt (μ / ρ)) * (fsX v μ) ^ (1 / 2 : ℝ) := by ring
      _ ≤ 1 * (fsX v μ) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hc hXh
      _ = (fsX v μ) ^ (1 / 2 : ℝ) := by ring
  have hc2pos : 0 < bogC2 v ρ μ := sb_c2_pos hav hC
  have hc2high : bogC2 v ρ μ ≤ (fsX v μ) ^ (-(11 / 2 : ℝ)) := by
    rw [bogC2_eq_para hav hC]
    have hXh : (0 : ℝ) ≤ (fsX v μ) ^ (-(11 / 2 : ℝ)) := Real.rpow_nonneg hXpos.le _
    have hc : (1 / 2 : ℝ) * Real.sqrt (μ / ρ) ≤ 1 := by linarith [hsq_hi]
    calc 1 / 2 * Real.sqrt (μ / ρ) * (fsX v μ) ^ (-(11 / 2) : ℝ)
        = (1 / 2 * Real.sqrt (μ / ρ)) * (fsX v μ) ^ (-(11 / 2) : ℝ) := by ring
      _ ≤ 1 * (fsX v μ) ^ (-(11 / 2) : ℝ) := mul_le_mul_of_nonneg_right hc hXh
      _ = (fsX v μ) ^ (-(11 / 2) : ℝ) := by ring
  have hc12 : bogC1 v ρ μ ≤ bogC2 v ρ μ := by
    rw [bogC1_eq_para hav hC, bogC2_eq_para hav hC]
    have hle : (fsX v μ) ^ (1 / 2 : ℝ) ≤ (fsX v μ) ^ (-(11 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hXpos hXle (by norm_num)
    have hc : 0 ≤ 1 / 2 * Real.sqrt (μ / ρ) := by positivity
    exact mul_le_mul_of_nonneg_left hle hc
  have heThigh : (paramsAt μ (a v)).eT ≤ (fsX v μ) ^ (23 / 4 : ℝ) := le_of_eq (eT_eq_fsX hC)
  have heThalf : (paramsAt μ (a v)).eT ≤ 1 / 2 := sb_eT_half hC
  have hOspos : 0 ≤ Real.sqrt (ρ / a v) * bogHalf v ρ μ :=
    mul_nonneg (Real.sqrt_nonneg _) hΔpos.le
  have hdiv : Real.sqrt (ρ / a v) = Real.sqrt (ρ * a v) / a v := by
    rw [Real.sqrt_div (by positivity) (a v), Real.sqrt_mul (by positivity) (a v)]
    field_simp
    exact (Real.sq_sqrt hav.le).symm
  have hsqrt_rhoa : Real.sqrt (ρ * a v)
      ≤ Real.sqrt (11 / 10) * (fsX v μ) ^ (323 / 2 : ℝ) / a v := by
    have h1 := hC.hsqρa
    rw [show (dil v μ) ^ ((1 : ℝ) / 2) = (fsX v μ) ^ (323 / 2 : ℝ) by
      rw [rpow_dil hC]; norm_num] at h1
    exact h1
  have hsplit : (fsX v μ) ^ (323 / 2 : ℝ) * (fsX v μ) ^ (3 / 2 : ℝ)
      = (fsX v μ) ^ (163 : ℝ) := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have h7 : Real.sqrt (11 / 10) * 7 ≤ 8 := by
    have h : Real.sqrt (11 / 10) ≤ 11 / 10 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 11 / 10 by norm_num),
        Real.sqrt_nonneg (11 / 10)]
    nlinarith [h]
  have hOs : Real.sqrt (ρ / a v) * bogHalf v ρ μ ≤ 8 * (fsX v μ) ^ (163 : ℝ) / (a v) ^ 2 := by
    rw [hdiv]
    have h1 : Real.sqrt (ρ * a v) / a v * bogHalf v ρ μ
        ≤ (Real.sqrt (11 / 10) * (fsX v μ) ^ (323 / 2 : ℝ) / a v ^ 2)
          * (7 * (fsX v μ) ^ (3 / 2 : ℝ)) := by
      refine mul_le_mul ?_ hΔhigh hΔpos.le (by positivity)
      calc Real.sqrt (ρ * a v) / a v
          ≤ (Real.sqrt (11 / 10) * (fsX v μ) ^ (323 / 2 : ℝ) / a v) / a v :=
            div_le_div_of_nonneg_right hsqrt_rhoa hav.le
        _ = Real.sqrt (11 / 10) * (fsX v μ) ^ (323 / 2 : ℝ) / a v ^ 2 := by ring
    refine le_trans h1 ?_
    have hfac : Real.sqrt (11 / 10) * (fsX v μ) ^ (323 / 2 : ℝ) / a v ^ 2
          * (7 * (fsX v μ) ^ (3 / 2 : ℝ))
        = Real.sqrt (11 / 10) * 7 * (fsX v μ) ^ (163 : ℝ) / a v ^ 2 := by
      rw [← hsplit]
      ring
    rw [hfac, div_le_div_iff₀ (by positivity : (0 : ℝ) < (a v) ^ 2)
      (by positivity : (0 : ℝ) < (a v) ^ 2)]
    have hX163 : 0 < (fsX v μ) ^ (163 : ℝ) := Real.rpow_pos_of_pos hXpos _
    have hpos : 0 < (fsX v μ) ^ (163 : ℝ) * a v ^ 2 := mul_pos hX163 (pow_pos hav 2)
    nlinarith [h7, hpos]
  have hOs1 : Real.sqrt (ρ / a v) * bogHalf v ρ μ ≤ 1 := by
    have h163 : (fsX v μ) ^ (163 : ℝ) ≤ fsX v μ := by
      have h := Real.rpow_le_rpow_of_exponent_ge (x := fsX v μ) (y := 163) (z := 1)
        hXpos hXle (by norm_num)
      simpa using h
    have h2 : (8 : ℝ) * fsX v μ ≤ (a v) ^ 2 := by
      have h8 : (0 : ℝ) ≤ 8 := by norm_num
      have hm := mul_le_mul_of_nonneg_left hXa h8
      linarith [hm]
    have h4 : 8 * (fsX v μ) ^ (163 : ℝ) / (a v) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (a v) ^ 2)]
      linarith [h163, h2]
    exact le_trans hOs h4
  have hmpos : 0 < bogM v μ := by
    rw [bogM]
    exact div_pos (by positivity) (sb_ell_pos hav hC)
  have hmesh : Real.sqrt (ρ * a v) * bogMesh v ρ μ = bogM v μ := by
    rw [bogM, bogMesh]
    field_simp
  have hVs1 : 1 ≤ bogVs v R ρ μ := by
    have h1 : (1 : ℝ) ≤ bogBs v R := le_max_left 1 _
    have h2 : bogBs v R ≤ bogVs v R ρ μ := by
      rw [bogVs]; exact le_add_of_nonneg_right (le_max_left 0 _)
    linarith
  have hOscM : bogOscM v R ρ μ
      ≤ 8 * bogKOs * (1 + R) ^ 3 * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2) := by
    rw [bogOscM]
    have h1 : bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ
        = bogKOs * (1 + R) ^ 3 * (Real.sqrt (ρ / a v) * bogHalf v ρ μ) := by ring
    rw [h1]
    have hK : 0 ≤ bogKOs * (1 + R) ^ 3 :=
      mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3)
    calc bogKOs * (1 + R) ^ 3 * (Real.sqrt (ρ / a v) * bogHalf v ρ μ)
        ≤ bogKOs * (1 + R) ^ 3 * (8 * (fsX v μ) ^ (163 : ℝ) / (a v) ^ 2) :=
          mul_le_mul_of_nonneg_left hOs hK
      _ = 8 * bogKOs * (1 + R) ^ 3 * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2) := by ring
  exact
    { hμ0 := hμ, hρ0 := hρ, hXpos := hXpos, hXle := hXle, hXlt := hX1,
      hδpos := hδpos, hδlow := hδlow, hδhigh := hδhigh,
      hΔpos := hΔpos, hΔle := hΔle, hΔhigh := hΔhigh,
      hc1pos := hc1pos, hc1le := hc1le, hc2pos := hc2pos, hc12 := hc12,
      hc2high := hc2high, heThigh := heThigh, heThalf := heThalf,
      heTpos := Real.rpow_nonneg hC.hD0.le _,
      hOspos := hOspos, hOs := hOs, hOs1 := hOs1, hmpos := hmpos, hmesh := hmesh,
      hVs1 := hVs1, hOscM := hOscM }

/-- `bogVs` is bounded by the *fixed* constant `bogBs v R + max 0 (8·bogKOs(1+R)³/(a v)²)`
independent of `ρ` and `μ`. -/
lemma bogVs_le_Vs0 {v : E3 → ℝ} {R ρ μ : ℝ} (hR : 0 < R) (hreg : RegimeC v R ρ μ) :
    bogVs v R ρ μ ≤ bogBs v R + max 0 (8 * (bogKOs * (1 + R) ^ 3) / (a v) ^ 2) := by
  have hKw0 : 0 ≤ bogKOs * (1 + R) ^ 3 :=
    mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3)
  have h2 : (fsX v μ) ^ (163 : ℝ) ≤ 1 :=
    Real.rpow_le_one hreg.hXpos.le hreg.hXle (by norm_num)
  have h3 : (fsX v μ) ^ (163 : ℝ) / (a v) ^ 2 ≤ 1 / (a v) ^ 2 :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : bogOscM v R ρ μ ≤ 8 * (bogKOs * (1 + R) ^ 3) / (a v) ^ 2 := by
    refine le_trans hreg.hOscM ?_
    rw [show 8 * bogKOs * (1 + R) ^ 3 * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2)
        = (8 * (bogKOs * (1 + R) ^ 3)) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2) by ring]
    calc (8 * (bogKOs * (1 + R) ^ 3)) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2)
        ≤ (8 * (bogKOs * (1 + R) ^ 3)) * (1 / (a v) ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by linarith [hKw0])
      _ = 8 * (bogKOs * (1 + R) ^ 3) / (a v) ^ 2 := by ring
  have hmax : max 0 (bogOscM v R ρ μ) ≤ max 0 (8 * (bogKOs * (1 + R) ^ 3) / (a v) ^ 2) :=
    max_le (le_max_left 0 _) (le_trans h4 (le_max_right 0 _))
  rw [bogVs]
  linarith [hmax]

/-- **The sum of the majorant `bogG`.**  With `X = fsX v μ` and a constant `Cst` dominating
`1`, `1 + log(2 + a v/(2π))`, `bogKOs(1+R)³/(a v)²` and `bogKOs(1+R)³/a v`, the lattice sum of
`bogG` is at most `10¹⁰·Vs²·(X^{-3}(Cst + log(1/X)) + X^{-17/4})`. -/
lemma tsum_bogG_le {v : E3 → ℝ} {h : ScatSol v} {R ρ μ Cst : ℝ}
    (hR : 0 < R) (hav : 0 < a v)
    (hC1 : 1 ≤ Cst)
    (hC2 : 1 + Real.log (2 + a v / (2 * Real.pi)) ≤ Cst)
    (hC3 : bogKOs * (1 + R) ^ 3 / (a v) ^ 2 ≤ Cst)
    (hC4 : bogKOs * (1 + R) ^ 3 / (a v) ≤ Cst)
    (hC : Core v R μ ρ) (hreg : RegimeC v R ρ μ) :
    Summable (bogG v h R ρ μ) ∧
    (∑' n : Fin 3 → ℤ, bogG v h R ρ μ n)
      ≤ 10 ^ 10 * (bogVs v R ρ μ) ^ 2 *
          ((fsX v μ) ^ (-(3 : ℝ)) * (Cst + Real.log (1 / fsX v μ))
            + (fsX v μ) ^ (-(17 / 4 : ℝ))) := by
  have hX0 : 0 < fsX v μ := hreg.hXpos
  have hXnn : 0 ≤ fsX v μ := hX0.le
  have hX1 : fsX v μ ≤ 1 := hreg.hXle
  have hm0 : 0 < bogM v μ := hreg.hmpos
  have hδ0 : 0 < bogMesh v ρ μ := hreg.hδpos
  have hVs1 : 1 ≤ bogVs v R ρ μ := hreg.hVs1
  have hVs0 : 0 < bogVs v R ρ μ := lt_of_lt_of_le one_pos hVs1
  have hVsnn : 0 ≤ bogVs v R ρ μ := hVs0.le
  have hVssq : 0 ≤ (bogVs v R ρ μ) ^ 2 := sq_nonneg _
  have hΔ0 : 0 ≤ bogHalf v ρ μ := hreg.hΔpos.le
  have hK0 : 0 ≤ bogOscM v R ρ μ := bogOscM_nonneg hR.le hav hreg.hρ0 hδ0
  have hKwnn : 0 ≤ bogKOs * (1 + R) ^ 3 :=
    mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3)
  have heT0 : 0 ≤ (paramsAt μ (a v)).eT := hreg.heTpos
  have hCst0 : 0 ≤ Cst := le_trans zero_le_one hC1
  have hL : 0 ≤ Real.log (1 / fsX v μ) := by
    refine Real.log_nonneg ?_
    rw [one_div]
    exact (one_le_inv₀ hX0).mpr hX1
  have hX3 : 0 ≤ (fsX v μ) ^ (-(3 : ℝ)) := Real.rpow_nonneg hXnn _
  have hX174 : 0 ≤ (fsX v μ) ^ (-(17 / 4 : ℝ)) := Real.rpow_nonneg hXnn _
  -- ## the identity `1/bogM = (a v) X^{-163}/(2π)`
  have hmun : (μ * a v) ^ (-(1 / 2 : ℝ)) = (a v) * (fsX v μ) ^ (-(323 / 2 : ℝ)) := by
    have hav2 : (0 : ℝ) < (a v) ^ 2 := by positivity
    have heq1 : μ * a v = dil v μ / (a v) ^ 2 := by rw [dil]; field_simp
    rw [heq1, Real.div_rpow hC.hD0.le hav2.le]
    have h1 : ((a v) ^ 2) ^ (-(1 / 2 : ℝ)) = (a v)⁻¹ := by
      rw [← Real.rpow_natCast (a v) 2, ← Real.rpow_mul hav.le,
        show ((2 : ℕ) : ℝ) * (-(1 / 2)) = -1 by norm_num, Real.rpow_neg_one]
    rw [h1, div_inv_eq_mul]
    have h2 : (dil v μ) ^ (-(1 / 2 : ℝ)) = (fsX v μ) ^ (-(323 / 2 : ℝ)) := by
      rw [rpow_dil hC]; norm_num
    rw [h2]; ring
  have hell_eq : ell v μ = a v * (fsX v μ) ^ (-(163 : ℝ)) := by
    rw [hC.hℓ, kl_eq_fsX hC, hmun]
    have hrp : (fsX v μ) ^ (-(3 / 2 : ℝ)) * (fsX v μ) ^ (-(323 / 2 : ℝ))
        = (fsX v μ) ^ (-(163 : ℝ)) := by
      rw [← Real.rpow_add hX0]; norm_num
    calc (fsX v μ) ^ (-(3 / 2 : ℝ)) * ((a v) * (fsX v μ) ^ (-(323 / 2 : ℝ)))
        = (a v) * ((fsX v μ) ^ (-(3 / 2 : ℝ)) * (fsX v μ) ^ (-(323 / 2 : ℝ))) := by ring
      _ = (a v) * (fsX v μ) ^ (-(163 : ℝ)) := by rw [hrp]
  have hminv : 1 / bogM v μ = a v * (fsX v μ) ^ (-(163 : ℝ)) / (2 * Real.pi) := by
    rw [bogM, hell_eq, one_div, inv_div]
  have hX163 : (1 : ℝ) ≤ (fsX v μ) ^ (-(163 : ℝ)) := by
    rw [Real.rpow_neg hXnn, one_le_inv₀ (Real.rpow_pos_of_pos hX0 _)]
    exact Real.rpow_le_one hXnn hX1 (by norm_num)
  have hlog1m : 1 + Real.log (2 + 1 / bogM v μ)
      ≤ (1 + Real.log (2 + a v / (2 * Real.pi))) + 163 * Real.log (1 / fsX v μ) := by
    have hpos : (0 : ℝ) < 2 + a v / (2 * Real.pi) := by positivity
    have hnum : (0 : ℝ) < 2 + 1 / bogM v μ := by
      have h1 : 0 ≤ 1 / bogM v μ := by positivity
      linarith
    have hkey : 2 + 1 / bogM v μ ≤ (2 + a v / (2 * Real.pi)) * (fsX v μ) ^ (-(163 : ℝ)) := by
      rw [hminv]
      calc 2 + a v * (fsX v μ) ^ (-(163 : ℝ)) / (2 * Real.pi)
          = 2 + (a v / (2 * Real.pi)) * (fsX v μ) ^ (-(163 : ℝ)) := by ring
        _ ≤ 2 * (fsX v μ) ^ (-(163 : ℝ))
              + (a v / (2 * Real.pi)) * (fsX v μ) ^ (-(163 : ℝ)) := by linarith [hX163]
        _ = (2 + a v / (2 * Real.pi)) * (fsX v μ) ^ (-(163 : ℝ)) := by ring
    have hlog := Real.log_le_log hnum hkey
    rw [Real.log_mul (ne_of_gt hpos) (ne_of_gt (Real.rpow_pos_of_pos hX0 _)),
      Real.log_rpow hX0] at hlog
    have hlogX : Real.log (fsX v μ) ≤ 0 := Real.log_nonpos hXnn hX1
    have hinv : Real.log (1 / fsX v μ) = -Real.log (fsX v μ) := by
      rw [one_div, Real.log_inv]
    rw [hinv]
    linarith [hlog, hlogX]
  have hlog1m' : 1 + Real.log (2 + 1 / bogM v μ) ≤ Cst + 163 * Real.log (1 / fsX v μ) := by
    linarith [hlog1m, hC2]
  -- ## the mesh rows
  have hΔδ3 : bogHalf v ρ μ * (bogMesh v ρ μ) ^ (-(3 : ℝ)) ≤ (fsX v μ) ^ (-(3 : ℝ)) / 25 := by
    rw [bogHalf]
    have hrp : bogMesh v ρ μ * (bogMesh v ρ μ) ^ (-(3 : ℝ))
        = (bogMesh v ρ μ) ^ (-(2 : ℝ)) := by
      have h := Real.rpow_add hδ0 1 (-(3 : ℝ))
      rw [Real.rpow_one] at h
      rw [show (1 : ℝ) + (-(3 : ℝ)) = -(2 : ℝ) by norm_num] at h
      exact h.symm
    have hsq := mesh_inv_sq_le (δ := bogMesh v ρ μ) (X := fsX v μ) hX0 hδ0 hreg.hδlow
    have h3 : Real.sqrt 3 / 2 ≤ 1 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    calc bogMesh v ρ μ * Real.sqrt 3 / 2 * (bogMesh v ρ μ) ^ (-(3 : ℝ))
        = Real.sqrt 3 / 2 * (bogMesh v ρ μ * (bogMesh v ρ μ) ^ (-(3 : ℝ))) := by ring
      _ = Real.sqrt 3 / 2 * (bogMesh v ρ μ) ^ (-(2 : ℝ)) := by rw [hrp]
      _ ≤ Real.sqrt 3 / 2 * ((fsX v μ) ^ (-(3 : ℝ)) / 25) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ (fsX v μ) ^ (-(3 : ℝ)) / 25 := by
          have hnn : 0 ≤ (fsX v μ) ^ (-(3 : ℝ)) / 25 := by positivity
          calc Real.sqrt 3 / 2 * ((fsX v μ) ^ (-(3 : ℝ)) / 25)
              ≤ 1 * ((fsX v μ) ^ (-(3 : ℝ)) / 25) := mul_le_mul_of_nonneg_right h3 hnn
            _ = (fsX v μ) ^ (-(3 : ℝ)) / 25 := by ring
  have hδ2 : (bogMesh v ρ μ) ^ (-(2 : ℝ)) ≤ (fsX v μ) ^ (-(3 : ℝ)) / 25 :=
    mesh_inv_sq_le (δ := bogMesh v ρ μ) (X := fsX v μ) hX0 hδ0 hreg.hδlow
  have hδ4 : (bogMesh v ρ μ) ^ (-(4 : ℝ)) ≤ (fsX v μ) ^ (-(6 : ℝ)) / 625 := by
    have h := mesh_inv_sq_le (δ := bogMesh v ρ μ) (X := fsX v μ) hX0 hδ0 hreg.hδlow
    have h2 : ((bogMesh v ρ μ) ^ (-(2 : ℝ))) ^ 2 ≤ ((fsX v μ) ^ (-(3 : ℝ)) / 25) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    have e1 : ((bogMesh v ρ μ) ^ (-(2 : ℝ))) ^ 2 = (bogMesh v ρ μ) ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_natCast ((bogMesh v ρ μ) ^ (-(2 : ℝ))) 2, ← Real.rpow_mul hδ0.le]
      norm_num
    have e2 : ((fsX v μ) ^ (-(3 : ℝ)) / 25) ^ 2 = (fsX v μ) ^ (-(6 : ℝ)) / 625 := by
      rw [div_pow]
      congr 1
      · rw [← Real.rpow_natCast ((fsX v μ) ^ (-(3 : ℝ))) 2, ← Real.rpow_mul hXnn]
        norm_num
      · norm_num
    linarith [h2, e1.le, e1.ge, e2.le, e2.ge]
  -- ## the oscillation row, reorganised
  have hOscM' : bogOscM v R ρ μ
      ≤ 8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2) := by
    calc bogOscM v R ρ μ
        ≤ 8 * bogKOs * (1 + R) ^ 3 * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2) := hreg.hOscM
      _ = 8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2) := by ring
  -- ## the rpow bookkeeping lemmas
  have hrp163_3 : (fsX v μ) ^ (163 : ℝ) * (fsX v μ) ^ (-(3 : ℝ))
      = (fsX v μ) ^ (160 : ℝ) := by rw [← Real.rpow_add hX0]; norm_num
  have hrp163_6 : (fsX v μ) ^ (163 : ℝ) * (fsX v μ) ^ (-(6 : ℝ))
      = (fsX v μ) ^ (157 : ℝ) := by rw [← Real.rpow_add hX0]; norm_num
  have hrp160_163 : (fsX v μ) ^ (160 : ℝ) * (fsX v μ) ^ (-(163 : ℝ))
      = (fsX v μ) ^ (-(3 : ℝ)) := by rw [← Real.rpow_add hX0]; norm_num
  have hrp11_7 : (fsX v μ) ^ (11 / 4 : ℝ) * (fsX v μ) ^ (-(7 : ℝ))
      = (fsX v μ) ^ (-(17 / 4 : ℝ)) := by rw [← Real.rpow_add hX0]; norm_num
  have h157 : (fsX v μ) ^ (157 : ℝ) ≤ (fsX v μ) ^ (-(3 : ℝ)) := by
    calc (fsX v μ) ^ (157 : ℝ)
        = (fsX v μ) ^ (-(3 : ℝ)) * (fsX v μ) ^ (160 : ℝ) := by
          rw [← Real.rpow_add hX0]; norm_num
      _ ≤ (fsX v μ) ^ (-(3 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hXnn hX1 (by norm_num)) hX3
      _ = (fsX v μ) ^ (-(3 : ℝ)) := by ring
  have h160 : (fsX v μ) ^ (160 : ℝ) ≤ (fsX v μ) ^ (-(3 : ℝ)) := by
    calc (fsX v μ) ^ (160 : ℝ)
        = (fsX v μ) ^ (-(3 : ℝ)) * (fsX v μ) ^ (163 : ℝ) := by
          rw [← Real.rpow_add hX0]; norm_num
      _ ≤ (fsX v μ) ^ (-(3 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hXnn hX1 (by norm_num)) hX3
      _ = (fsX v μ) ^ (-(3 : ℝ)) := by ring
  -- ## summability
  have hs1 : Summable (bogP1 v ρ μ) :=
    (Summable.mul_left ((bogMesh v ρ μ) ^ (-(3 : ℝ)))
      (summable_two_cube_profile (bogM v μ) hm0)).congr (fun n => (bogP1_eq hreg n).symm)
  have hs2 : Summable (bogP2 v ρ μ) :=
    (Summable.mul_left ((bogMesh v ρ μ) ^ (-(2 : ℝ)))
      (summable_two_sq_profile (bogM v μ) hm0)).congr (fun n => (bogP2_eq hreg n).symm)
  have hs3 : Summable (bogP3 v ρ μ) :=
    (Summable.mul_left ((bogMesh v ρ μ) ^ (-(4 : ℝ)))
      (summable_three_four_profile (bogM v μ) hm0)).congr (fun n => (bogP3_eq hreg n).symm)
  have hGs1 : Summable (fun n => bogG1 v R ρ μ n) :=
    (Summable.mul_left (((10 : ℝ) ^ 6) * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ) hs1).congr
      (fun n => rfl)
  have hGs2 : Summable (fun n => bogG2 v R ρ μ n) :=
    (Summable.mul_left (((4 : ℝ) * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ) hs3).congr
      (fun n => rfl)
  have hGs3 : Summable (fun n => bogG3 v R ρ μ n) :=
    (Summable.mul_left (((4 : ℝ) * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ) hs2).congr
      (fun n => rfl)
  have hGs4 : Summable (fun n => bogG4 v R ρ μ n) := by
    have hb4 : (fun n => bogG4 v R ρ μ n)
        = (fun n => if bogRLot v ρ μ n < 2 * bogC2 v ρ μ then
            (10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT * bogP2 v ρ μ n
          else 0) := by
      funext n; rw [bogG4]
    rw [hb4]
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (Summable.mul_left (((10 : ℝ) ^ 6) * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT) hs2)
    · by_cases hq : bogRLot v ρ μ n < 2 * bogC2 v ρ μ
      · rw [if_pos hq]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hVssq) heT0) (by
          rw [bogP2]
          exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
            (mul_nonneg hreg.hmpos.le (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 2)))
      · rw [if_neg hq]
    · by_cases hq : bogRLot v ρ μ n < 2 * bogC2 v ρ μ
      · rw [if_pos hq]
      · rw [if_neg hq]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hVssq) heT0) (by
          rw [bogP2]
          exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
            (mul_nonneg hreg.hmpos.le (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 2)))
  have hGsum : Summable (bogG v h R ρ μ) :=
    (((hGs1.add hGs2).add hGs3).add hGs4).congr (fun n => (bogG_eq v h R ρ μ n).symm)
  -- ## the four term bounds
  have hT1 : (∑' n : Fin 3 → ℤ, bogG1 v R ρ μ n)
      ≤ 9.2 * 10 ^ 8 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
          * (Cst + Real.log (1 / fsX v μ)) := by
    have hΔδ : ((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
          * (bogMesh v ρ μ) ^ (-(3 : ℝ)) ≤ 4 * 10 ^ 4 * (bogVs v R ρ μ) ^ 2
            * (fsX v μ) ^ (-(3 : ℝ)) := by
      calc ((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
            * (bogMesh v ρ μ) ^ (-(3 : ℝ))
          = (10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2
              * (bogHalf v ρ μ * (bogMesh v ρ μ) ^ (-(3 : ℝ))) := by ring
        _ ≤ (10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * ((fsX v μ) ^ (-(3 : ℝ)) / 25) :=
            mul_le_mul_of_nonneg_left hΔδ3 (by positivity)
        _ = 4 * 10 ^ 4 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ)) := by ring
    have h100 : 0 ≤ 100 * (Cst + 163 * Real.log (1 / fsX v μ)) := by nlinarith [hCst0, hL]
    calc (∑' n : Fin 3 → ℤ, bogG1 v R ρ μ n)
        = ((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ) * (∑' n, bogP1 v ρ μ n) := by
          have hh : (∑' n : Fin 3 → ℤ, bogG1 v R ρ μ n)
              = (∑' n, ((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
                  * bogP1 v ρ μ n) := tsum_congr (fun n => rfl)
          rw [hh, tsum_mul_left]
      _ ≤ ((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
            * ((bogMesh v ρ μ) ^ (-(3 : ℝ))
              * (100 * (1 + Real.log (2 + 1 / bogM v μ)))) :=
          mul_le_mul_of_nonneg_left (tsum_bogP1_le hreg) (by positivity)
      _ ≤ ((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
            * ((bogMesh v ρ μ) ^ (-(3 : ℝ))
              * (100 * (Cst + 163 * Real.log (1 / fsX v μ)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by linarith [hlog1m']) (by positivity)) (by positivity)
      _ = (((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * bogHalf v ρ μ)
            * (bogMesh v ρ μ) ^ (-(3 : ℝ))) * (100 * (Cst + 163 * Real.log (1 / fsX v μ))) :=
          by ring
      _ ≤ (4 * 10 ^ 4 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ)))
            * (100 * (Cst + 163 * Real.log (1 / fsX v μ))) :=
          mul_le_mul_of_nonneg_right hΔδ h100
      _ = 4 * 10 ^ 6 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
            * (Cst + 163 * Real.log (1 / fsX v μ)) := by ring
      _ ≤ 9.2 * 10 ^ 8 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
            * (Cst + Real.log (1 / fsX v μ)) := by
          have hXX : 0 ≤ (fsX v μ) ^ (-(3 : ℝ)) * (bogVs v R ρ μ) ^ 2 :=
            mul_nonneg hX3 hVssq
          have key : 4 * 10 ^ 6 * (Cst + 163 * Real.log (1 / fsX v μ))
              ≤ 9.2 * 10 ^ 8 * (Cst + Real.log (1 / fsX v μ)) := by
            linarith [hCst0, hL]
          calc 4 * 10 ^ 6 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
                * (Cst + 163 * Real.log (1 / fsX v μ))
              = ((fsX v μ) ^ (-(3 : ℝ)) * (bogVs v R ρ μ) ^ 2)
                * (4 * 10 ^ 6 * (Cst + 163 * Real.log (1 / fsX v μ))) := by ring
            _ ≤ ((fsX v μ) ^ (-(3 : ℝ)) * (bogVs v R ρ μ) ^ 2)
                * (9.2 * 10 ^ 8 * (Cst + Real.log (1 / fsX v μ))) :=
                mul_le_mul_of_nonneg_left key hXX
            _ = 9.2 * 10 ^ 8 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
                * (Cst + Real.log (1 / fsX v μ)) := by ring
  have hT2 : (∑' n : Fin 3 → ℤ, bogG2 v R ρ μ n)
      ≤ 5.2 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
          * (Cst + Real.log (1 / fsX v μ)) := by
    have h1 : bogOscM v R ρ μ * (bogMesh v ρ μ) ^ (-(4 : ℝ))
        ≤ 8 * (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (157 : ℝ) / 625 := by
      have h2 : (8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2))
            * ((fsX v μ) ^ (-(6 : ℝ)) / 625)
          = 8 * (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (157 : ℝ) / 625 := by
        calc (8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2))
              * ((fsX v μ) ^ (-(6 : ℝ)) / 625)
            = 8 * (bogKOs * (1 + R) ^ 3) / (a v) ^ 2
                * ((fsX v μ) ^ (163 : ℝ) * (fsX v μ) ^ (-(6 : ℝ))) / 625 := by ring
          _ = 8 * (bogKOs * (1 + R) ^ 3) / (a v) ^ 2 * (fsX v μ) ^ (157 : ℝ) / 625 := by
              rw [hrp163_6]
          _ = 8 * (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (157 : ℝ) / 625 := by ring
      calc bogOscM v R ρ μ * (bogMesh v ρ μ) ^ (-(4 : ℝ))
          ≤ (8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2))
            * ((fsX v μ) ^ (-(6 : ℝ)) / 625) :=
            mul_le_mul hOscM' hδ4 (by positivity) (by positivity)
        _ = 8 * (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (157 : ℝ) / 625 := h2
    have hstep2 : (4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ
          * (bogMesh v ρ μ) ^ (-(4 : ℝ))
        ≤ 5.2 * 10 ^ 5 * (bogVs v R ρ μ) ^ 2 * Cst * (fsX v μ) ^ (-(3 : ℝ)) := by
      calc (4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ
            * (bogMesh v ρ μ) ^ (-(4 : ℝ))
          = 4 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2
              * (bogOscM v R ρ μ * (bogMesh v ρ μ) ^ (-(4 : ℝ))) := by ring
        _ ≤ 4 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2
              * (8 * (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (157 : ℝ) / 625) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 5.12 * 10 ^ 5 * (bogVs v R ρ μ) ^ 2
              * ((bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (157 : ℝ)) := by ring
        _ ≤ 5.12 * 10 ^ 5 * (bogVs v R ρ μ) ^ 2 * (Cst * (fsX v μ) ^ (-(3 : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul hC3 h157 (Real.rpow_nonneg hXnn _) hCst0
        _ ≤ 5.2 * 10 ^ 5 * (bogVs v R ρ μ) ^ 2 * Cst * (fsX v μ) ^ (-(3 : ℝ)) := by
            have h5 : (5.12 : ℝ) * 10 ^ 5 ≤ 5.2 * 10 ^ 5 := by norm_num
            have hnn : 0 ≤ (bogVs v R ρ μ) ^ 2 * (Cst * (fsX v μ) ^ (-(3 : ℝ))) :=
              mul_nonneg hVssq (mul_nonneg hCst0 hX3)
            calc 5.12 * 10 ^ 5 * (bogVs v R ρ μ) ^ 2 * (Cst * (fsX v μ) ^ (-(3 : ℝ)))
                = ((bogVs v R ρ μ) ^ 2 * (Cst * (fsX v μ) ^ (-(3 : ℝ)))) * (5.12 * 10 ^ 5) := by
                  ring
              _ ≤ ((bogVs v R ρ μ) ^ 2 * (Cst * (fsX v μ) ^ (-(3 : ℝ)))) * (5.2 * 10 ^ 5) :=
                  mul_le_mul_of_nonneg_left h5 hnn
              _ = 5.2 * 10 ^ 5 * (bogVs v R ρ μ) ^ 2 * Cst * (fsX v μ) ^ (-(3 : ℝ)) := by ring
    calc (∑' n : Fin 3 → ℤ, bogG2 v R ρ μ n)
        = ((4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ) * (∑' n, bogP3 v ρ μ n) := by
          have hh : (∑' n : Fin 3 → ℤ, bogG2 v R ρ μ n)
              = (∑' n, ((4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ)
                  * bogP3 v ρ μ n) := tsum_congr (fun n => rfl)
          rw [hh, tsum_mul_left]
      _ ≤ ((4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ)
            * ((bogMesh v ρ μ) ^ (-(4 : ℝ)) * 100) :=
          mul_le_mul_of_nonneg_left (tsum_bogP3_le hreg) (by positivity)
      _ = ((4 * 10 ^ 7) * (bogVs v R ρ μ) ^ 2 * bogOscM v R ρ μ
            * (bogMesh v ρ μ) ^ (-(4 : ℝ))) * 100 := by ring
      _ ≤ (5.2 * 10 ^ 5 * (bogVs v R ρ μ) ^ 2 * Cst * (fsX v μ) ^ (-(3 : ℝ))) * 100 :=
          mul_le_mul_of_nonneg_right hstep2 (by norm_num)
      _ = 5.2 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * Cst * (fsX v μ) ^ (-(3 : ℝ)) := by ring
      _ ≤ 5.2 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
            * (Cst + Real.log (1 / fsX v μ)) := by
          have hct : Cst ≤ Cst + Real.log (1 / fsX v μ) := by linarith [hL]
          have hXX : 0 ≤ (fsX v μ) ^ (-(3 : ℝ)) * (bogVs v R ρ μ) ^ 2 := mul_nonneg hX3 hVssq
          calc 5.2 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * Cst * (fsX v μ) ^ (-(3 : ℝ))
              = ((fsX v μ) ^ (-(3 : ℝ)) * (bogVs v R ρ μ) ^ 2) * (5.2 * 10 ^ 7 * Cst) := by ring
            _ ≤ ((fsX v μ) ^ (-(3 : ℝ)) * (bogVs v R ρ μ) ^ 2)
                * (5.2 * 10 ^ 7 * (Cst + Real.log (1 / fsX v μ))) :=
                mul_le_mul_of_nonneg_left (by linarith [hct]) hXX
            _ = 5.2 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
                * (Cst + Real.log (1 / fsX v μ)) := by ring
  have hT3 : (∑' n : Fin 3 → ℤ, bogG3 v R ρ μ n)
      ≤ 3 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
          * (Cst + Real.log (1 / fsX v μ)) := by
    have haux : (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (a v / (2 * Real.pi)) ≤ Cst := by
      have hfac : (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (a v / (2 * Real.pi))
          = (bogKOs * (1 + R) ^ 3 / (a v)) * (1 / (2 * Real.pi)) := by
        field_simp
      rw [hfac]
      have h2 : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by linarith [Real.pi_gt_three] : (0 : ℝ) < 2 * Real.pi)]
        linarith [Real.pi_gt_three]
      calc (bogKOs * (1 + R) ^ 3 / (a v)) * (1 / (2 * Real.pi))
          ≤ Cst * 1 := mul_le_mul hC4 h2 (by positivity) hCst0
        _ = Cst := by ring
    have hA : (8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2))
          * ((fsX v μ) ^ (-(3 : ℝ)) / 25)
        = 8 * (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ) / 25 := by
      calc (8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2))
            * ((fsX v μ) ^ (-(3 : ℝ)) / 25)
          = 8 * (bogKOs * (1 + R) ^ 3) / (a v) ^ 2
              * ((fsX v μ) ^ (163 : ℝ) * (fsX v μ) ^ (-(3 : ℝ))) / 25 := by ring
        _ = 8 * (bogKOs * (1 + R) ^ 3) / (a v) ^ 2 * (fsX v μ) ^ (160 : ℝ) / 25 := by
            rw [hrp163_3]
        _ = 8 * (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ) / 25 := by ring
    have hB : (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ)
          * (a v * (fsX v μ) ^ (-(163 : ℝ)) / (2 * Real.pi))
        = ((bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (a v / (2 * Real.pi)))
          * (fsX v μ) ^ (-(3 : ℝ)) := by
      calc (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ)
            * (a v * (fsX v μ) ^ (-(163 : ℝ)) / (2 * Real.pi))
          = ((bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (a v / (2 * Real.pi)))
            * ((fsX v μ) ^ (160 : ℝ) * (fsX v μ) ^ (-(163 : ℝ))) := by ring
        _ = ((bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (a v / (2 * Real.pi)))
            * (fsX v μ) ^ (-(3 : ℝ)) := by rw [hrp160_163]
    have hK160 : (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ)
        ≤ Cst * (fsX v μ) ^ (-(3 : ℝ)) := by
      calc (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ)
          ≤ Cst * (fsX v μ) ^ (160 : ℝ) :=
            mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg hXnn _)
        _ ≤ Cst * (fsX v μ) ^ (-(3 : ℝ)) := mul_le_mul_of_nonneg_left h160 hCst0
    calc (∑' n : Fin 3 → ℤ, bogG3 v R ρ μ n)
        = ((4 * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ) * (∑' n, bogP2 v ρ μ n) := by
          have hh : (∑' n : Fin 3 → ℤ, bogG3 v R ρ μ n)
              = (∑' n, ((4 * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ)
                  * bogP2 v ρ μ n) := tsum_congr (fun n => rfl)
          rw [hh, tsum_mul_left]
      _ ≤ ((4 * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ)
            * ((bogMesh v ρ μ) ^ (-(2 : ℝ)) * (100 * (1 / bogM v μ + 1))) :=
          mul_le_mul_of_nonneg_left (tsum_bogP2_le hreg) (by positivity)
      _ = ((4 * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ * (bogMesh v ρ μ) ^ (-(2 : ℝ)))
            * (100 * (1 / bogM v μ + 1)) := by ring
      _ ≤ ((4 * 10 ^ 5) * bogVs v R ρ μ
            * ((8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2))
              * ((fsX v μ) ^ (-(3 : ℝ)) / 25)))
            * (100 * (1 / bogM v μ + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · have h1 : bogOscM v R ρ μ * (bogMesh v ρ μ) ^ (-(2 : ℝ))
                ≤ (8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2))
                  * ((fsX v μ) ^ (-(3 : ℝ)) / 25) :=
              mul_le_mul hOscM' hδ2 (Real.rpow_nonneg hδ0.le _)
                (mul_nonneg (mul_nonneg (by norm_num) hKwnn)
                  (div_nonneg (Real.rpow_nonneg hXnn (163 : ℝ)) (sq_nonneg _)))
            calc (4 * 10 ^ 5) * bogVs v R ρ μ * bogOscM v R ρ μ
                  * (bogMesh v ρ μ) ^ (-(2 : ℝ))
                = 4 * 10 ^ 5 * bogVs v R ρ μ
                    * (bogOscM v R ρ μ * (bogMesh v ρ μ) ^ (-(2 : ℝ))) := by ring
              _ ≤ 4 * 10 ^ 5 * bogVs v R ρ μ
                    * ((8 * (bogKOs * (1 + R) ^ 3) * ((fsX v μ) ^ (163 : ℝ) / (a v) ^ 2))
                      * ((fsX v μ) ^ (-(3 : ℝ)) / 25)) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
          · have hb : 0 ≤ 1 / bogM v μ := div_nonneg zero_le_one hm0.le
            linarith
      _ = 1.28 * 10 ^ 5 * bogVs v R ρ μ
            * ((bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ)) * 100
            * (1 / bogM v μ + 1) := by
          rw [hA]; ring
      _ = 1.28 * 10 ^ 5 * bogVs v R ρ μ
            * ((bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ)
                * (a v * (fsX v μ) ^ (-(163 : ℝ)) / (2 * Real.pi))
              + (bogKOs * (1 + R) ^ 3 / (a v) ^ 2) * (fsX v μ) ^ (160 : ℝ)) * 100 := by
          rw [hminv]; ring
      _ ≤ 1.28 * 10 ^ 5 * bogVs v R ρ μ
            * (Cst * (fsX v μ) ^ (-(3 : ℝ)) + Cst * (fsX v μ) ^ (-(3 : ℝ))) * 100 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (by norm_num)
          rw [hB]
          exact add_le_add (mul_le_mul_of_nonneg_right haux hX3) hK160
      _ ≤ 3 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
            * (Cst + Real.log (1 / fsX v μ)) := by
          have key : 1.28 * 10 ^ 5 * (Cst + Cst) * 100
              ≤ 3 * 10 ^ 7 * (Cst + Real.log (1 / fsX v μ)) := by
            linarith [hCst0, hL]
          calc 1.28 * 10 ^ 5 * bogVs v R ρ μ
                * (Cst * (fsX v μ) ^ (-(3 : ℝ)) + Cst * (fsX v μ) ^ (-(3 : ℝ))) * 100
              = ((fsX v μ) ^ (-(3 : ℝ)) * bogVs v R ρ μ)
                * (1.28 * 10 ^ 5 * (Cst + Cst) * 100) := by ring
            _ ≤ ((fsX v μ) ^ (-(3 : ℝ)) * bogVs v R ρ μ)
                * (3 * 10 ^ 7 * (Cst + Real.log (1 / fsX v μ))) :=
                mul_le_mul_of_nonneg_left key (mul_nonneg hX3 hVsnn)
            _ ≤ 3 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
                * (Cst + Real.log (1 / fsX v μ)) := by
                have hVsle : bogVs v R ρ μ ≤ (bogVs v R ρ μ) ^ 2 := by nlinarith [hVs1]
                calc ((fsX v μ) ^ (-(3 : ℝ)) * bogVs v R ρ μ)
                      * (3 * 10 ^ 7 * (Cst + Real.log (1 / fsX v μ)))
                    = 3 * 10 ^ 7 * ((fsX v μ) ^ (-(3 : ℝ)) * bogVs v R ρ μ)
                      * (Cst + Real.log (1 / fsX v μ)) := by ring
                  _ ≤ 3 * 10 ^ 7 * ((fsX v μ) ^ (-(3 : ℝ)) * (bogVs v R ρ μ) ^ 2)
                      * (Cst + Real.log (1 / fsX v μ)) := by
                      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num))
                        (by linarith [hCst0, hL])
                      exact mul_le_mul_of_nonneg_left hVsle hX3
                  _ = 3 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
                      * (Cst + Real.log (1 / fsX v μ)) := by ring
  have hT4 : (∑' n : Fin 3 → ℤ, bogG4 v R ρ μ n)
      ≤ 2.4 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(17 / 4 : ℝ)) := by
    have hXm7 : (2 : ℝ) ≤ (fsX v μ) ^ (-(7 : ℝ)) := by
      have hle : (fsX v μ) ^ (7 : ℝ) ≤ (1 / 2 : ℝ) := by
        have h1 : (fsX v μ) ^ (7 : ℝ) ≤ (1 / 1000 : ℝ) ^ (7 : ℝ) :=
          Real.rpow_le_rpow hXnn hreg.hXlt (by norm_num)
        have h2 : (1 / 1000 : ℝ) ^ (7 : ℝ) = (1 / 1000 : ℝ) ^ 7 := Real.rpow_natCast _ 7
        rw [h2] at h1
        have h3 : (1 / 1000 : ℝ) ^ 7 ≤ 1 / 2 := by norm_num
        linarith
      calc (2 : ℝ) = 1 / (1 / 2 : ℝ) := by norm_num
        _ ≤ 1 / (fsX v μ) ^ (7 : ℝ) :=
            one_div_le_one_div_of_le (Real.rpow_pos_of_pos hX0 _) hle
        _ = (fsX v μ) ^ (-(7 : ℝ)) := by rw [one_div, ← Real.rpow_neg hXnn]
    have hgeo : ∀ m : Fin 3 → ℤ, bogRLot v ρ μ m < 2 * bogC2 v ρ μ →
        ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ)) := by
      intro m hm
      have h1 : bogMesh v ρ μ * (‖lpt 1 m‖ - Real.sqrt 3 / 2) < 2 * bogC2 v ρ μ := by
        rw [← bogRLot_eq v ρ μ m hδ0.le]; exact hm
      have h2 : bogMesh v ρ μ * (‖lpt 1 m‖ - Real.sqrt 3 / 2)
          < 2 * (fsX v μ) ^ (-(11 / 2 : ℝ)) :=
        lt_of_lt_of_le h1 (by linarith [hreg.hc2high])
      have h3 : ‖lpt 1 m‖ - Real.sqrt 3 / 2
          < 2 * (fsX v μ) ^ (-(11 / 2 : ℝ)) / bogMesh v ρ μ :=
        (lt_div_iff₀ hδ0).mpr (by rw [mul_comm]; exact h2)
      have h4 : 2 * (fsX v μ) ^ (-(11 / 2 : ℝ)) / bogMesh v ρ μ
          ≤ (fsX v μ) ^ (-(7 : ℝ)) / 2 := by
        rw [div_le_div_iff₀ hδ0 (by norm_num : (0 : ℝ) < 2)]
        have hrp : (fsX v μ) ^ (-(7 : ℝ)) * (fsX v μ) ^ (3 / 2 : ℝ)
            = (fsX v μ) ^ (-(11 / 2 : ℝ)) := by
          rw [← Real.rpow_add hX0]; norm_num
        have hpos11 : 0 < (fsX v μ) ^ (-(11 / 2 : ℝ)) := Real.rpow_pos_of_pos hX0 _
        have hpos7 : 0 ≤ (fsX v μ) ^ (-(7 : ℝ)) := Real.rpow_nonneg hXnn _
        nlinarith [hreg.hδlow, hrp.le, hrp.ge, hpos11, hpos7]
      have h5 : ‖lpt 1 m‖ < (fsX v μ) ^ (-(7 : ℝ)) := by
        have h6 : ‖lpt 1 m‖ < (fsX v μ) ^ (-(7 : ℝ)) / 2 + Real.sqrt 3 / 2 := by
          linarith [h3, h4]
        have h7 : Real.sqrt 3 / 2 ≤ (fsX v μ) ^ (-(7 : ℝ)) / 2 := by
          have h8 : Real.sqrt 3 ≤ 2 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
          linarith [hXm7, h8]
        linarith [h6, h7]
      exact le_of_lt h5
    have hp2 : ∀ m : Fin 3 → ℤ, bogP2 v ρ μ m
        ≤ (bogMesh v ρ μ) ^ (-(2 : ℝ)) * (1 / ‖lpt 1 m‖ ^ 2) := by
      intro m
      rw [bogP2_eq hreg m]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hδ0.le _)
      by_cases hy : ‖lpt 1 m‖ = 0
      · rw [hy]; simp
      · have hy2 : 0 < ‖lpt 1 m‖ ^ 2 := by positivity
        have hs : 1 ≤ (1 + bogM v μ * ‖lpt 1 m‖) ^ 2 := by
          have h1 : 1 ≤ 1 + bogM v μ * ‖lpt 1 m‖ := by
            have := mul_nonneg hm0.le (norm_nonneg (lpt 1 m)); linarith
          nlinarith [h1]
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith [hs, hy2]
    have hX7nn : 0 ≤ (fsX v μ) ^ (-(7 : ℝ)) := Real.rpow_nonneg hXnn _
    have hFsum : Summable (fun m : Fin 3 → ℤ =>
        if ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ)) then (1 : ℝ) / ‖lpt 1 m‖ ^ 2 else 0) := by
      refine summable_of_ne_finset_zero (s := cube ⌈(fsX v μ) ^ (-(7 : ℝ))⌉₊) (fun m hm => ?_)
      exact if_neg (fun hle => hm (mem_cube.mpr (mn_le_ceil_of_norm_le hle)))
    have hFbound : (∑' m : Fin 3 → ℤ,
        (if ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ)) then (1 : ℝ) / ‖lpt 1 m‖ ^ 2 else 0))
        ≤ 300 * ((fsX v μ) ^ (-(7 : ℝ)) + 1) :=
      (count_bounds ((fsX v μ) ^ (-(7 : ℝ))) hX7nn).2.1
    have hsum1 : Summable (fun m : Fin 3 → ℤ =>
        if ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ)) then bogP2 v ρ μ m else 0) :=
      Summable.of_nonneg_of_le (fun m => by
          by_cases hq : ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ))
          · rw [if_pos hq]
            rw [bogP2]
            exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
              (mul_nonneg hm0.le (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 2))
          · rw [if_neg hq])
        (fun m => by
          by_cases hq : ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ))
          · rw [if_pos hq, if_pos hq]
            exact hp2 m
          · rw [if_neg hq, if_neg hq, mul_zero])
        (Summable.mul_left _ hFsum)
    have hY : (fsX v μ) ^ (-(7 : ℝ)) + 1 ≤ 2 * (fsX v μ) ^ (-(7 : ℝ)) := by
      have h1 : (1 : ℝ) ≤ (fsX v μ) ^ (-(7 : ℝ)) := by
        rw [Real.rpow_neg hXnn, one_le_inv₀ (Real.rpow_pos_of_pos hX0 _)]
        exact Real.rpow_le_one hXnn hX1 (by norm_num)
      linarith
    have hsumA : Summable (fun m : Fin 3 → ℤ =>
        if bogRLot v ρ μ m < 2 * bogC2 v ρ μ then bogP2 v ρ μ m else 0) :=
      Summable.of_nonneg_of_le (fun m => by
          by_cases hq : bogRLot v ρ μ m < 2 * bogC2 v ρ μ
          · rw [if_pos hq]
            rw [bogP2]
            exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
              (mul_nonneg hm0.le (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 2))
          · rw [if_neg hq])
        (fun m => by
          by_cases hq : bogRLot v ρ μ m < 2 * bogC2 v ρ μ
          · rw [if_pos hq]
          · rw [if_neg hq]
            rw [bogP2]
            exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (add_nonneg zero_le_one
              (mul_nonneg hm0.le (norm_nonneg _))) 2) (pow_nonneg (norm_nonneg _) 2)))
        hs2
    calc (∑' n : Fin 3 → ℤ, bogG4 v R ρ μ n)
        = (10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT
            * (∑' m, (if bogRLot v ρ μ m < 2 * bogC2 v ρ μ then bogP2 v ρ μ m else 0)) := by
          have hh : (∑' n : Fin 3 → ℤ, bogG4 v R ρ μ n)
              = (∑' n, (((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT)
                  * (if bogRLot v ρ μ n < 2 * bogC2 v ρ μ then bogP2 v ρ μ n else 0))) := by
            refine tsum_congr (fun n => ?_)
            rw [bogG4]
            by_cases hq : bogRLot v ρ μ n < 2 * bogC2 v ρ μ
            · rw [if_pos hq, if_pos hq]
            · simp [if_neg hq]
          rw [hh, tsum_mul_left]
      _ ≤ (10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT
            * ((bogMesh v ρ μ) ^ (-(2 : ℝ)) * (300 * (2 * (fsX v μ) ^ (-(7 : ℝ))))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (∑' m, (if bogRLot v ρ μ m < 2 * bogC2 v ρ μ then bogP2 v ρ μ m else 0))
              ≤ (∑' m, ((bogMesh v ρ μ) ^ (-(2 : ℝ)) *
                  (if ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ)) then 1 / ‖lpt 1 m‖ ^ 2 else 0))) := by
                refine Summable.tsum_le_tsum (fun m => ?_) hsumA
                  (Summable.mul_left _ hFsum)
                by_cases hq : bogRLot v ρ μ m < 2 * bogC2 v ρ μ
                · rw [if_pos hq, if_pos (hgeo m hq)]
                  exact hp2 m
                · rw [if_neg hq]
                  refine mul_nonneg (Real.rpow_nonneg hδ0.le _) ?_
                  by_cases h2 : ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ))
                  · rw [if_pos h2]; positivity
                  · rw [if_neg h2]
            _ = (bogMesh v ρ μ) ^ (-(2 : ℝ)) *
                  (∑' m, (if ‖lpt 1 m‖ ≤ (fsX v μ) ^ (-(7 : ℝ)) then 1 / ‖lpt 1 m‖ ^ 2 else 0)) :=
                tsum_mul_left
            _ ≤ (bogMesh v ρ μ) ^ (-(2 : ℝ)) * (300 * ((fsX v μ) ^ (-(7 : ℝ)) + 1)) :=
                mul_le_mul_of_nonneg_left hFbound (Real.rpow_nonneg hδ0.le _)
            _ ≤ (bogMesh v ρ μ) ^ (-(2 : ℝ)) * (300 * (2 * (fsX v μ) ^ (-(7 : ℝ)))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hY (by norm_num)) (Real.rpow_nonneg hδ0.le _)
      _ ≤ 2.4 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(17 / 4 : ℝ)) := by
          have h1 : (paramsAt μ (a v)).eT * (bogMesh v ρ μ) ^ (-(2 : ℝ))
              ≤ (fsX v μ) ^ (11 / 4 : ℝ) / 25 := by
            calc (paramsAt μ (a v)).eT * (bogMesh v ρ μ) ^ (-(2 : ℝ))
                ≤ (fsX v μ) ^ (23 / 4 : ℝ) * ((fsX v μ) ^ (-(3 : ℝ)) / 25) :=
                  mul_le_mul hreg.heThigh hδ2 (by positivity) (by positivity)
              _ = (fsX v μ) ^ (11 / 4 : ℝ) / 25 := by
                  have hrr : (fsX v μ) ^ (23 / 4 : ℝ) * (fsX v μ) ^ (-(3 : ℝ))
                      = (fsX v μ) ^ (11 / 4 : ℝ) := by
                    rw [← Real.rpow_add hX0]; norm_num
                  calc (fsX v μ) ^ (23 / 4 : ℝ) * ((fsX v μ) ^ (-(3 : ℝ)) / 25)
                      = ((fsX v μ) ^ (23 / 4 : ℝ) * (fsX v μ) ^ (-(3 : ℝ))) / 25 := by ring
                    _ = (fsX v μ) ^ (11 / 4 : ℝ) / 25 := by rw [hrr]
          calc (10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2 * (paramsAt μ (a v)).eT
                * ((bogMesh v ρ μ) ^ (-(2 : ℝ)) * (300 * (2 * (fsX v μ) ^ (-(7 : ℝ)))))
              = ((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2)
                  * ((paramsAt μ (a v)).eT * (bogMesh v ρ μ) ^ (-(2 : ℝ)))
                  * (600 * (fsX v μ) ^ (-(7 : ℝ))) := by ring
            _ ≤ ((10 : ℝ) ^ 6 * (bogVs v R ρ μ) ^ 2) * ((fsX v μ) ^ (11 / 4 : ℝ) / 25)
                  * (600 * (fsX v μ) ^ (-(7 : ℝ))) := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity))
                  (by positivity)
            _ = 2.4 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2
                  * ((fsX v μ) ^ (11 / 4 : ℝ) * (fsX v μ) ^ (-(7 : ℝ))) := by ring
            _ = 2.4 * 10 ^ 7 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(17 / 4 : ℝ)) := by rw [hrp11_7]
  -- ## assemble
  refine ⟨hGsum, ?_⟩
  have hsplit : (∑' n : Fin 3 → ℤ, bogG v h R ρ μ n)
      = (∑' n, bogG1 v R ρ μ n) + (∑' n, bogG2 v R ρ μ n)
        + (∑' n, bogG3 v R ρ μ n) + (∑' n, bogG4 v R ρ μ n) := by
    rw [show (∑' n : Fin 3 → ℤ, bogG v h R ρ μ n)
        = (∑' n : (Fin 3 → ℤ), (((bogG1 v R ρ μ n + bogG2 v R ρ μ n) + bogG3 v R ρ μ n)
            + bogG4 v R ρ μ n))
        from tsum_congr (fun n => bogG_eq v h R ρ μ n),
      Summable.tsum_add ((hGs1.add hGs2).add hGs3) hGs4,
      Summable.tsum_add (hGs1.add hGs2) hGs3, Summable.tsum_add hGs1 hGs2]
  have hub : (∑' n : Fin 3 → ℤ, bogG1 v R ρ μ n) + (∑' n, bogG2 v R ρ μ n)
        + (∑' n, bogG3 v R ρ μ n) + (∑' n, bogG4 v R ρ μ n)
      ≤ 10 ^ 10 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
          * (Cst + Real.log (1 / fsX v μ))
        + 10 ^ 10 * (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(17 / 4 : ℝ)) := by
    have hTnn : 0 ≤ (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(3 : ℝ))
        * (Cst + Real.log (1 / fsX v μ)) :=
      mul_nonneg (mul_nonneg hVssq hX3) (by linarith [hCst0, hL])
    have hUnn : 0 ≤ (bogVs v R ρ μ) ^ 2 * (fsX v μ) ^ (-(17 / 4 : ℝ)) :=
      mul_nonneg hVssq hX174
    linarith [hT1, hT2, hT3, hT4, hTnn, hUnn]
  rw [hsplit]
  refine le_trans hub ?_
  linarith [hX3, hVssq, hX174]

theorem bogS3_sum_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ ε₃ : ℝ, 0 < ε₃ ∧ ∀ {ρ μ : ℝ}, Work.BoseBogFS.Core v R μ ρ →
      Work.BoseFixR.dil v μ ≤ ε₃ →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      Summable (fun n : Fin 3 → ℤ => Work.BoseBogFS.bogS3 v h R ρ μ n) ∧
      (∑' n : Fin 3 → ℤ, Work.BoseBogFS.bogS3 v h R ρ μ n)
        ≤ 2000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) := by
  set Kw : ℝ := bogKOs * (1 + R) ^ 3 with hKw
  have hKw0 : 0 ≤ Kw := by
    rw [hKw]; exact mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3)
  set Cst : ℝ := 1 + (1 + Real.log (2 + a v / (2 * Real.pi))) + Kw / (a v) + Kw / (a v) ^ 2
    with hCst
  have hCst1 : 1 ≤ Cst := by
    rw [hCst]
    have hlog : 0 ≤ 1 + Real.log (2 + a v / (2 * Real.pi)) := by
      have h1 : (0 : ℝ) ≤ a v / (2 * Real.pi) := div_nonneg hav.le (by positivity)
      have : (1 : ℝ) ≤ 2 + a v / (2 * Real.pi) := by linarith
      linarith [Real.log_nonneg this]
    have h2 : 0 ≤ Kw / (a v) := div_nonneg hKw0 hav.le
    have h3 : 0 ≤ Kw / (a v) ^ 2 := div_nonneg hKw0 (sq_nonneg _)
    linarith
  have hCst2 : 1 + Real.log (2 + a v / (2 * Real.pi)) ≤ Cst := by
    rw [hCst]
    have h2 : 0 ≤ Kw / (a v) := div_nonneg hKw0 hav.le
    have h3 : 0 ≤ Kw / (a v) ^ 2 := div_nonneg hKw0 (sq_nonneg _)
    linarith
  have hCst3 : bogKOs * (1 + R) ^ 3 / (a v) ^ 2 ≤ Cst := by
    rw [hCst, hKw]
    have hlog : 0 ≤ 1 + (1 + Real.log (2 + a v / (2 * Real.pi))) := by
      have h1 : (0 : ℝ) ≤ a v / (2 * Real.pi) := div_nonneg hav.le (by positivity)
      have : (1 : ℝ) ≤ 2 + a v / (2 * Real.pi) := by linarith
      linarith [Real.log_nonneg this]
    have h2 : 0 ≤ Kw / (a v) := div_nonneg hKw0 hav.le
    linarith
  have hCst4 : bogKOs * (1 + R) ^ 3 / (a v) ≤ Cst := by
    rw [hCst, hKw]
    have hlog : 0 ≤ 1 + (1 + Real.log (2 + a v / (2 * Real.pi))) := by
      have h1 : (0 : ℝ) ≤ a v / (2 * Real.pi) := div_nonneg hav.le (by positivity)
      have : (1 : ℝ) ≤ 2 + a v / (2 * Real.pi) := by linarith
      linarith [Real.log_nonneg this]
    have h3 : 0 ≤ Kw / (a v) ^ 2 := div_nonneg hKw0 (sq_nonneg _)
    linarith
  have hCst0 : 0 ≤ Cst := le_trans zero_le_one hCst1
  set Vs0 : ℝ := bogBs v R + max 0 (8 * Kw / (a v) ^ 2) with hVs0
  have hVs01 : 1 ≤ Vs0 := by
    have h1 : (1 : ℝ) ≤ bogBs v R := le_max_left 1 _
    have h2 : (0 : ℝ) ≤ max 0 (8 * Kw / (a v) ^ 2) := le_max_left 0 _
    rw [hVs0]; linarith
  obtain ⟨X0, hX0pos, hX0⟩ := absorb_arith (K := (10 : ℝ) ^ 10) (Vs := Vs0) (C := Cst)
    (by norm_num) hVs01 hCst0
  set Xs : ℝ := min (min (1 / 1000) ((a v) ^ 2 / 8)) ((1 / 2 : ℝ) ^ (2 / 11 : ℝ)) with hXs
  have hXspos : 0 < Xs := by
    rw [hXs]
    exact lt_min (lt_min (by norm_num) (by positivity))
      (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨min (Xs ^ (323 : ℝ)) (X0 ^ (323 : ℝ)),
    lt_min (Real.rpow_pos_of_pos hXspos _) (Real.rpow_pos_of_pos hX0pos _), ?_⟩
  intro ρ μ hC hdil hRℓ
  have hdil0 : 0 < dil v μ := hC.hD0
  have hfsX : fsX v μ = (dil v μ) ^ (1 / 323 : ℝ) := rfl
  have hpow : ∀ {Y : ℝ}, 0 < Y → (Y ^ (323 : ℝ)) ^ (1 / 323 : ℝ) = Y := by
    intro Y hY
    rw [← Real.rpow_mul hY.le]
    rw [show (323 : ℝ) * (1 / 323) = 1 by norm_num, Real.rpow_one]
  have hXle_s : fsX v μ ≤ Xs := by
    have h : dil v μ ≤ Xs ^ (323 : ℝ) := le_trans hdil (min_le_left _ _)
    rw [hfsX]
    exact le_trans (Real.rpow_le_rpow hdil0.le h (by norm_num)) (le_of_eq (hpow hXspos))
  have hXle_0 : fsX v μ ≤ X0 := by
    have h : dil v μ ≤ X0 ^ (323 : ℝ) := le_trans hdil (min_le_right _ _)
    rw [hfsX]
    exact le_trans (Real.rpow_le_rpow hdil0.le h (by norm_num)) (le_of_eq (hpow hX0pos))
  have hXpos : 0 < fsX v μ := by rw [hfsX]; exact Real.rpow_pos_of_pos hdil0 _
  have hXlt : fsX v μ ≤ 1 / 1000 :=
    le_trans hXle_s (le_trans (min_le_left _ _) (min_le_left _ _))
  have hXa : fsX v μ ≤ (a v) ^ 2 / 8 :=
    le_trans hXle_s (le_trans (min_le_left _ _) (min_le_right _ _))
  have hreg : RegimeC v R ρ μ := regimeC_of_core hR hav hC hXlt hXa
  obtain ⟨hGsum, hGle⟩ := tsum_bogG_le hR hav hCst1 hCst2 hCst3 hCst4 hC hreg
  have hbS : Summable (fun n : Fin 3 → ℤ => bogS3 v h R ρ μ n) :=
    Summable.of_nonneg_of_le (fun n => bogS3_nonneg v h R ρ μ n)
      (fun n => bogS3_le_bogG hreg hC hR hav hv hvrad hv_supp hRℓ n) hGsum
  refine ⟨hbS, ?_⟩
  have h1 : (∑' n : Fin 3 → ℤ, bogS3 v h R ρ μ n)
      ≤ (∑' n : Fin 3 → ℤ, bogG v h R ρ μ n) :=
    hbS.tsum_le_tsum (fun n => bogS3_le_bogG hreg hC hR hav hv hvrad hv_supp hRℓ n) hGsum
  have hVs : bogVs v R ρ μ ≤ Vs0 := by
    rw [hVs0, hKw]
    exact bogVs_le_Vs0 hR hreg
  have hVsnn : 0 ≤ bogVs v R ρ μ := le_trans zero_le_one hreg.hVs1
  have hXle1 : fsX v μ ≤ 1 :=
    le_trans hXle_s (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (by norm_num)))
  have hlognn : 0 ≤ Real.log (1 / fsX v μ) := by
    refine Real.log_nonneg ?_
    rw [one_div]
    exact (one_le_inv₀ hXpos).mpr hXle1
  have hCnn : 0 ≤ Cst + Real.log (1 / fsX v μ) := by linarith
  have hbnn : 0 ≤ (fsX v μ) ^ (-(3 : ℝ)) * (Cst + Real.log (1 / fsX v μ))
      + (fsX v μ) ^ (-(17 / 4 : ℝ)) :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg hXpos.le _) hCnn)
      (Real.rpow_nonneg hXpos.le _)
  have hVsq : (bogVs v R ρ μ) ^ 2 ≤ Vs0 ^ 2 := pow_le_pow_left₀ hVsnn hVs 2
  have h2 : 10 ^ 10 * (bogVs v R ρ μ) ^ 2 *
        ((fsX v μ) ^ (-(3 : ℝ)) * (Cst + Real.log (1 / fsX v μ))
          + (fsX v μ) ^ (-(17 / 4 : ℝ)))
      ≤ (10 : ℝ) ^ 10 * Vs0 ^ 2 *
        ((fsX v μ) ^ (-(3 : ℝ)) * (Cst + Real.log (1 / fsX v μ))
          + (fsX v μ) ^ (-(17 / 4 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hbnn
    exact mul_le_mul_of_nonneg_left hVsq (by positivity)
  have h3 := hX0 (fsX v μ) hXpos hXle_0
  linarith [h1, hGle, h2, h3]

end Work.BoseBogFS
