import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.NWindow_bp_N_le
import Submission.Work.BoseB7A.NWindow_linear_bound
import Submission.Work.BoseB7A.NWindow_shift
import Submission.Work.BoseB7A.PH_subset_PHq_sub
import Submission.Work.BoseB7A.Prep
import Submission.Work.BoseB7A.Q3fourT_eq_weight_sum
import Submission.Work.BoseB7A.errA_bounds
import Submission.Work.BoseB7A.kernel_basic
import Submission.Work.BoseB7A.smallness_ratios
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.estQ3fourA` — FS `eq:EstimateQ3Tilde4`, absolute

The fourth estimate of FS `lem:EstimatesOnQ3-js` (FS ll. 2790–2870): the
commutator piece `Q₃⁽⁴⁾` together with the linear term
`ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂²_Λ(s)(ã_s†+ã_s)ds` and the kinetic reserve
`(b/100)ℓ⁻²n₊` is bounded below by `-e4A·‖Φ‖²` on FS's window.

## The structure of the proof

`Q3fourT_eq_weight_sum` writes `Q₃⁽⁴⁾` as the linear word
`(z/ℓ³)Σ_s q3fourWeightSplit(s)·(ã_s†+ã_s)`, and `T.linOpT` is
`(ρ_zzŴ₁ω(0))Σ_sχ̂²(s)·(ã_s†+ã_s)`, so

  `Q₃⁽⁴⁾ + linOp = Σ_s c_s·(ã_s†+ã_s)`,
  `c_s = (z/ℓ³)q3fourWeightSplit(s) + ρ_zzŴ₁ω(0)χ̂²(s) = (z/ℓ³)·(kA1+kA2+kA3+kA4)`

where the four pieces come from FS's `eq:1Q-integral`/`eq:1Q-integral2`
decomposition of the `k`-sum (the cancellation of the `k`-sum against
`ρ_zℓ³Ŵ₁ω(0)` is `lem:EstimateIntegral` plus the `(1-α_{s-k}α_k)𝒟_{sk}-1`
remainder):

* `kA1 = (1-f_L(s))ρ_zℓ³Ŵ₁ω(0)χ̂²(s)` — the tail of `χ̂²`, bounded by
  `Q3Kernel.tail_hatChiSq`;
* `kA2 = f_L(s)χ̂²(s)[ρ_zℓ³Ŵ₁ω(0) - Σ_{k∈P_H}Ŵ₁(k)α_k]` — the
  `lem:EstimateIntegral` remainder `K_H⁻¹`;
* `kA3 = -f_L(s)χ̂²(s)Σ_{k∈P_H}Ŵ₁(k)α_k(𝒟_{sk}(1-α_{s-k}α_k)-1)` — the
  `O(𝓁²)` remainder, charged to the kinetic reserve by the `ε`-trick;
* `kA4 = f_L(s)Σ_{k∈P_H}Ŵ₁(k)α_k𝒟_{sk}(χ̂(s-k)χ̂(-k) - α_{s-k}α_{-k}χ̂(k)χ̂(k-s))`
  — `eq:1Q-integral2`, exponentially small (`hatChi_small`).

The first three pieces together give `2√𝓜` times
`2K₀²(𝓜/z²)^{1/2}ρ_z²aℓ³(K_H⁻¹ + (K_ℓK_L)^{-M})` and `E₀K_ℓ²𝓁⁴/b`, and the
linear-form bound `NWindow_linear_bound` turns the four into the estimate.
-/

noncomputable section

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The coefficient of the combined linear word -/

/-- **The coefficient of `ã_s†+ã_s` in `Q₃⁽⁴⁾ + linOp`**:
`(z/ℓ³)q3fourWeightSplit(s) + ρ_zzŴ₁ω(0)χ̂²(s)`. -/
noncomputable def q3fourCoefA (F : FockData Mode) (E : Q3Env Mode) (s : Mode) : ℝ :=
  E.z / E.ell ^ 3 * F.q3fourWeightSplit E s + E.rho * E.z * E.W1omega0 * E.hatChiSq s

/-- `kA1(s) = (1-f_L(s))ρ_zℓ³Ŵ₁ω(0)χ̂²(s)`: the part of `q3fourWeightSplit + χ̂²`
where the `χ̂²`-tail is not seen by `f_L`. -/
noncomputable def kA1 (F : FockData Mode) (E : Q3Env Mode) (s : Mode) : ℝ :=
  (1 - E.fL s) * (E.rho * E.ell ^ 3 * E.W1omega0) * E.hatChiSq s

/-- `kA2(s) = f_L(s)χ̂²(s)[ρ_zℓ³Ŵ₁ω(0) - Σ_{k∈P_H}Ŵ₁(k)α_k]`: the
`lem:EstimateIntegral` remainder. -/
noncomputable def kA2 (F : FockData Mode) (E : Q3Env Mode) (s : Mode) : ℝ :=
  E.fL s * E.hatChiSq s *
    ((E.rho * E.ell ^ 3 * E.W1omega0) - ∑ k ∈ F.PHset E, E.W1 k * E.alpha k)

/-- `kA3(s) = -f_L(s)χ̂²(s)Σ_{k∈P_H}Ŵ₁(k)α_k(𝒟_{sk}(1-α_{s-k}α_{-k})-1)`: the
`eq:1Q-integral` remainder (of order `𝓁²`, charged to the kinetic reserve). -/
noncomputable def kA3 (F : FockData Mode) (E : Q3Env Mode) (s : Mode) : ℝ :=
  - (E.fL s * E.hatChiSq s *
      ∑ k ∈ F.PHset E,
        E.W1 k * E.alpha k *
          (E.q3Denom s k * (1 - E.alpha (s - k) * E.alpha (-k)) - 1))

/-- `kA4(s)`: the `eq:1Q-integral2` word,
`f_L(s)Σ_{k∈P_H}Ŵ₁(k)α_k𝒟_{sk}(χ̂(s-k)χ̂(-k) - α_{s-k}α_{-k}χ̂(k)χ̂(k-s))`. -/
noncomputable def kA4 (F : FockData Mode) (E : Q3Env Mode) (s : Mode) : ℝ :=
  E.fL s *
    ∑ k ∈ F.PHset E,
      E.W1 k * E.alpha k * E.q3Denom s k *
        (E.hatChi (s - k) * E.hatChi (-k)
          - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s)))

/-- **FS's `eq:1Q-integral`/`eq:1Q-integral2` decomposition of the weight.**
The weight `q3fourWeightSplit(s) + ρ_zℓ³Ŵ₁ω(0)χ̂²(s)` (i.e. `c_s` before the
factor `z/ℓ³`) is the sum of the four pieces `kA1 … kA4`. -/
theorem kA_decomp (F : FockData Mode) (E : Q3Env Mode) (s : Mode) :
    F.q3fourWeightSplit E s + E.rho * E.ell ^ 3 * E.W1omega0 * E.hatChiSq s
      = kA1 F E s + kA2 F E s + kA3 F E s + kA4 F E s := by
  -- the `k`-sum of `q3fourWeightSplit`, split into the three sums of the pieces
  have hS : (∑ k ∈ F.PHset E,
        ((1 - E.alpha (s - k) * E.alpha (-k)) * E.hatChiSq s
            - E.hatChi (s - k) * E.hatChi (-k)
            + E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s)))
          * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)))
      = (∑ k ∈ F.PHset E, -(E.fL s * E.hatChiSq s * (E.W1 k * E.alpha k)))
        + (∑ k ∈ F.PHset E, -(E.fL s * E.hatChiSq s *
            (E.W1 k * E.alpha k *
              (E.q3Denom s k * (1 - E.alpha (s - k) * E.alpha (-k)) - 1))))
        + (∑ k ∈ F.PHset E, E.fL s * (E.W1 k * E.alpha k * E.q3Denom s k *
            (E.hatChi (s - k) * E.hatChi (-k)
              - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have h2 : kA2 F E s = E.fL s * E.hatChiSq s * (E.rho * E.ell ^ 3 * E.W1omega0)
      + (∑ k ∈ F.PHset E, -(E.fL s * E.hatChiSq s * (E.W1 k * E.alpha k))) := by
    rw [kA2, mul_sub, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have h3 : kA3 F E s = ∑ k ∈ F.PHset E, -(E.fL s * E.hatChiSq s *
      (E.W1 k * E.alpha k *
        (E.q3Denom s k * (1 - E.alpha (s - k) * E.alpha (-k)) - 1))) := by
    rw [kA3, Finset.mul_sum, ← Finset.sum_neg_distrib]
  have h4 : kA4 F E s = ∑ k ∈ F.PHset E, E.fL s * (E.W1 k * E.alpha k *
      E.q3Denom s k *
        (E.hatChi (s - k) * E.hatChi (-k)
          - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s)))) := by
    rw [kA4, Finset.mul_sum]
  rw [kA1, Work.BoseB7.FockData.q3fourWeightSplit, hS, h2, h3, h4]
  ring

/-- **The coefficient of the linear word, split.**  `q3fourCoefA` is `z/ℓ³` times
the weight `q3fourWeightSplit + ρ_zℓ³Ŵ₁ω(0)χ̂²`, hence `z/ℓ³` times the four
pieces. -/
theorem q3fourCoefA_eq (F : FockData Mode) (E : Q3Env Mode) (s : Mode) (hell : E.ell ≠ 0) :
    q3fourCoefA F E s
      = E.z / E.ell ^ 3 * (kA1 F E s + kA2 F E s + kA3 F E s + kA4 F E s) := by
  have h : E.z / E.ell ^ 3 * F.q3fourWeightSplit E s
        + E.rho * E.z * E.W1omega0 * E.hatChiSq s
      = E.z / E.ell ^ 3 *
          (F.q3fourWeightSplit E s + E.rho * E.ell ^ 3 * E.W1omega0 * E.hatChiSq s) := by
    rw [mul_add]
    congr 1
    rw [div_eq_mul_inv,
      show E.z * (E.ell ^ 3)⁻¹ * (E.rho * E.ell ^ 3 * E.W1omega0 * E.hatChiSq s)
        = E.rho * E.z * E.W1omega0 * E.hatChiSq s * ((E.ell ^ 3)⁻¹ * E.ell ^ 3) by ring,
      inv_mul_cancel₀ (pow_ne_zero 3 hell), mul_one]
  rw [q3fourCoefA, h, ← kA_decomp]

/-- **`Q₃⁽⁴⁾ + linOpT` is one linear word.**  Under the algebra hypotheses
`SubstHyp` (which FS supply through `Q3Kernel` at small `t`), the sum of the
commutator piece and the linear term is `Σ_s c_s(ã_s†+ã_s)` with
`c_s = q3fourCoefA`. -/
theorem Q3fourT_add_linOpT (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (h : SubstHyp F T E) :
    T.Q3fourT E + T.linOpT E
      = ∑ s ∈ excited Mode, (q3fourCoefA F E s) • (T.taDag s + T.ta s) := by
  rw [Q3fourT_eq_weight_sum F T E h, TildeData.linOpT, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [q3fourCoefA]
  ext x
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, smul_add, smul_smul]
  module

/-! ## 2. Form bounds and the `ε`-absorption -/

/-- **Cauchy–Schwarz for a finite family**: `√(Σ f²) ≤ Σ |f|`. -/
theorem sqrt_sum_sq_le_sum_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, f i ^ 2) ≤ ∑ i ∈ s, |f i| := by
  have h0 : 0 ≤ ∑ i ∈ s, |f i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h : (∑ i ∈ s, f i ^ 2) ≤ (∑ i ∈ s, |f i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have h2 : |f i| * |f i| ≤ ∑ j ∈ s, |f i| * |f j| :=
      Finset.single_le_sum (f := fun j => |f i| * |f j|)
        (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hi
    calc f i ^ 2 = |f i| * |f i| := by rw [← sq_abs, sq]
      _ ≤ ∑ j ∈ s, |f i| * |f j| := h2
  calc Real.sqrt (∑ i ∈ s, f i ^ 2) ≤ Real.sqrt ((∑ i ∈ s, |f i|) ^ 2) := Real.sqrt_le_sqrt h
    _ = ∑ i ∈ s, |f i| := Real.sqrt_sq h0

/-- **`2√x√y ≤ εx + ε⁻¹y`** for `x,y ≥ 0`, `ε > 0` (the `ε`-trick). -/
theorem two_sqrt_mul_sqrt_le {x y ε : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hε : 0 < ε) :
    2 * Real.sqrt x * Real.sqrt y ≤ ε * x + ε⁻¹ * y := by
  have hsne : Real.sqrt ε ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hε)
  have hs2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hsinv : ((Real.sqrt ε)⁻¹) ^ 2 = ε⁻¹ := by rw [inv_pow, hs2]
  -- the cross term
  have hcross : 2 * (Real.sqrt ε * Real.sqrt x) * ((Real.sqrt ε)⁻¹ * Real.sqrt y)
      = 2 * Real.sqrt x * Real.sqrt y := by
    rw [show 2 * (Real.sqrt ε * Real.sqrt x) * ((Real.sqrt ε)⁻¹ * Real.sqrt y)
        = 2 * (Real.sqrt ε * (Real.sqrt ε)⁻¹) * (Real.sqrt x * Real.sqrt y) by ring,
      mul_inv_cancel₀ hsne]
    ring
  have hsquare := sq_nonneg (Real.sqrt ε * Real.sqrt x - (Real.sqrt ε)⁻¹ * Real.sqrt y)
  rw [sub_sq, mul_pow, mul_pow, hs2, hx2, hy2, hsinv, hcross] at hsquare
  linarith [hsquare]

/-- **The linear word on the window.**  For `Φ = 1_{[0,𝓜]}(n₊)Φ`, the quadratic
form of `Σ_s c_s(ã_s†+ã_s)` is controlled by the `ℓ²`-norm of the coefficients
(`NWindow_linear_bound`). -/
theorem linear_word_bound (F : FockData Mode) (T : TildeData F) {M : ℝ} (hM : 0 ≤ M)
    {Φ : F.H} (hΦ : T.NWindow M Φ) (c : Mode → ℝ) :
    |F.qw Φ (∑ s ∈ excited Mode, (c s) • (T.taDag s + T.ta s))|
      ≤ 2 * Real.sqrt M * Real.sqrt (∑ s ∈ excited Mode, c s ^ 2) * F.normSq Φ :=
  NWindow_linear_bound F T hM hΦ (excited Mode)
    (fun s hs => (Finset.mem_erase.mp hs).1) c

/-- **The quadratic form of a linear word is additive in the coefficients.** -/
theorem qw_linear_smul_finset (F : FockData Mode) (T : TildeData F) (S : Finset Mode) (Φ : F.H)
    (c : Mode → ℝ) :
    F.qw Φ (∑ s ∈ S, (c s) • (T.taDag s + T.ta s))
      = ∑ s ∈ S, c s * F.qw Φ (T.taDag s + T.ta s) := by
  simp only [FockData.qw, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    smul_eq_mul]

/-- **The kinetic-reserve absorption.**  For a coefficient family `c` on a
finite family `S ∌ 0` of θ-modes, bounded by `M₀ ≥ 0`, the quadratic form of the
linear word `Σ_{s∈S} c_s(ã_s†+ã_s)` is bounded below by the negative of the
kinetic reserve `(b/100)ℓ⁻²n₊` plus an `O(M₀ Σ|c|ℓ²/b)‖Φ‖²`: the `ε`-trick with
`ε = (b/100)ℓ⁻²/M₀`. -/
theorem qw_gap_absorb (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hb : 0 < E.b) (hell : 0 < E.ell) (S : Finset Mode) (hS : ∀ s ∈ S, s ≠ 0)
    {c : Mode → ℝ} {M₀ : ℝ} (hM₀nn : 0 ≤ M₀) (hM₀ : ∀ s ∈ S, |c s| ≤ M₀) (Φ : F.H) :
    - (E.b / 100) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ
        - M₀ * (100 / E.b) * E.ell ^ 2 * (∑ s ∈ S, |c s|) * F.normSq Φ
      ≤ F.qw Φ (∑ s ∈ S, (c s) • (T.taDag s + T.ta s)) := by
  rcases eq_or_lt_of_le hM₀nn with h0 | hpos
  · -- `M₀ = 0`: all coefficients vanish
    subst h0
    have hc : ∀ s ∈ S, c s = 0 := fun s hs => abs_eq_zero.mp (le_antisymm (hM₀ s hs) (abs_nonneg _))
    have hsum0 : (∑ s ∈ S, (c s) • (T.taDag s + T.ta s)) = 0 :=
      Finset.sum_eq_zero fun s hs => by rw [hc s hs]; simp
    rw [hsum0]
    simp only [FockData.qw, map_zero, LinearMap.zero_apply, FockData.normSq, abs_zero,
      Finset.sum_const_zero, mul_zero, sub_zero]
    have h1 : 0 ≤ (E.b / 100) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ :=
      mul_nonneg (mul_nonneg (by positivity) (Work.BoseB7.rpow_neg_two_nonneg _)) (T.N_nonneg Φ)
    linarith
  · -- `M₀ > 0`: the `ε`-trick
    set ε : ℝ := (E.b / 100) * E.ell ^ (-(2 : ℝ)) / M₀ with hε
    have hεpos : 0 < ε := by
      rw [hε]
      exact div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hell _)) hpos
    have hεM : ε * M₀ = (E.b / 100) * E.ell ^ (-(2 : ℝ)) := by
      rw [hε, div_mul_cancel₀ _ (ne_of_gt hpos)]
    have hεinv : ε⁻¹ = M₀ * (100 / E.b) * E.ell ^ 2 := by
      rw [hε, inv_div]
      have hpow : E.ell ^ (-(2 : ℝ)) = (E.ell ^ 2)⁻¹ := by
        rw [Real.rpow_neg hell.le, Real.rpow_two]
      rw [hpow]
      field_simp
    -- the per-mode bound
    have hper : ∀ s ∈ S,
        c s * F.qw Φ (T.taDag s + T.ta s)
          ≥ -(ε * |c s|) * F.bp (T.ta s Φ) (T.ta s Φ) - (ε⁻¹ * |c s|) * F.normSq Φ := by
      intro s _
      have hadj : F.bp (T.taDag s Φ) Φ = F.bp (T.ta s Φ) Φ := by
        rw [T.taDag_adjoint, F.bp_symm]
      have hq : F.qw Φ (T.taDag s + T.ta s) = 2 * F.bp (T.ta s Φ) Φ := by
        simp only [FockData.qw, LinearMap.add_apply, map_add, hadj]
        ring
      have hcs : |F.bp (T.ta s Φ) Φ| ≤ Real.sqrt (F.bp (T.ta s Φ) (T.ta s Φ))
          * Real.sqrt (F.normSq Φ) := by
        rw [FockData.normSq]
        exact bp_cauchy_abs F (T.ta s Φ) Φ
      have hkey : 2 * |F.bp (T.ta s Φ) Φ|
          ≤ ε * F.bp (T.ta s Φ) (T.ta s Φ) + ε⁻¹ * F.normSq Φ := by
        have h1 := two_sqrt_mul_sqrt_le (x := F.bp (T.ta s Φ) (T.ta s Φ))
          (y := F.normSq Φ) (F.bp_nonneg _) (F.normSq_nonneg Φ) hεpos
        calc 2 * |F.bp (T.ta s Φ) Φ|
            ≤ 2 * (Real.sqrt (F.bp (T.ta s Φ) (T.ta s Φ)) * Real.sqrt (F.normSq Φ)) :=
              by linarith [hcs]
          _ = 2 * Real.sqrt (F.bp (T.ta s Φ) (T.ta s Φ)) * Real.sqrt (F.normSq Φ) := by ring
          _ ≤ ε * F.bp (T.ta s Φ) (T.ta s Φ) + ε⁻¹ * F.normSq Φ := h1
      have h4 : c s * F.qw Φ (T.taDag s + T.ta s) ≥ -|c s| * (2 * |F.bp (T.ta s Φ) Φ|) := by
        rw [hq]
        have h := neg_abs_le (c s * F.bp (T.ta s Φ) Φ)
        rw [abs_mul] at h
        linarith [h]
      have h5 := mul_le_mul_of_nonneg_left hkey (abs_nonneg (c s))
      linarith [h4, h5]
    rw [qw_linear_smul_finset F T S Φ c]
    have h5 : ∑ s ∈ S, (-(ε * |c s|) * F.bp (T.ta s Φ) (T.ta s Φ)
          - (ε⁻¹ * |c s|) * F.normSq Φ)
        ≤ ∑ s ∈ S, c s * F.qw Φ (T.taDag s + T.ta s) :=
      Finset.sum_le_sum hper
    -- `Σ_s ‖ã_sΦ‖² ≤ ⟨n₊Φ,Φ⟩` (the θ-modes are orthonormal and count at most `n₊`)
    have hN : ∑ s ∈ S, F.bp (T.ta s Φ) (T.ta s Φ) ≤ F.bp (T.N Φ) Φ := by
      have hkey : F.bp ((∑ s ∈ S, T.taDag s ∘ₗ T.ta s) Φ) Φ
          = ∑ s ∈ S, F.bp (T.ta s Φ) (T.ta s Φ) := by
        rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun s _ => by
          simp only [LinearMap.comp_apply]
          exact T.taDag_adjoint s (T.ta s Φ) Φ
      rw [← hkey]
      exact T.ta_le_N S hS Φ
    have h6 : ∑ s ∈ S, (-(ε * |c s|) * F.bp (T.ta s Φ) (T.ta s Φ)
          - (ε⁻¹ * |c s|) * F.normSq Φ)
        = -(∑ s ∈ S, (ε * |c s|) * F.bp (T.ta s Φ) (T.ta s Φ))
          - (∑ s ∈ S, (ε⁻¹ * |c s|) * F.normSq Φ) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    have h7 : (∑ s ∈ S, (ε * |c s|) * F.bp (T.ta s Φ) (T.ta s Φ))
        ≤ ε * M₀ * F.bp (T.N Φ) Φ := by
      have hle : (∑ s ∈ S, (ε * |c s|) * F.bp (T.ta s Φ) (T.ta s Φ))
          ≤ ∑ s ∈ S, (ε * M₀) * F.bp (T.ta s Φ) (T.ta s Φ) := by
        refine Finset.sum_le_sum fun s hs => ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM₀ s hs) hεpos.le) (F.bp_nonneg _)
      rw [← Finset.mul_sum] at hle
      exact hle.trans (mul_le_mul_of_nonneg_left hN (mul_nonneg hεpos.le hM₀nn))
    have h8 : (∑ s ∈ S, (ε⁻¹ * |c s|) * F.normSq Φ)
        = ε⁻¹ * (∑ s ∈ S, |c s|) * F.normSq Φ := by
      calc ∑ s ∈ S, (ε⁻¹ * |c s|) * F.normSq Φ
          = (∑ s ∈ S, ε⁻¹ * |c s|) * F.normSq Φ := (Finset.sum_mul _ _ _).symm
        _ = ε⁻¹ * (∑ s ∈ S, |c s|) * F.normSq Φ := by
            rw [Finset.mul_sum]
    have hsplit : -(∑ s ∈ S, (ε * |c s|) * F.bp (T.ta s Φ) (T.ta s Φ))
          - (∑ s ∈ S, (ε⁻¹ * |c s|) * F.normSq Φ)
        ≤ ∑ s ∈ S, c s * F.qw Φ (T.taDag s + T.ta s) := by
      rw [← h6]; exact h5
    rw [h8, hεinv] at hsplit
    have h7' : -(ε * M₀ * F.bp (T.N Φ) Φ)
        ≤ -(∑ s ∈ S, (ε * |c s|) * F.bp (T.ta s Φ) (T.ta s Φ)) := neg_le_neg h7
    rw [hεM] at h7'
    linarith [hsplit, h7']

/-! ## 3. The scalar facts at FS's parameter point -/

/-- `𝓁 ≥ 0` at FS's parameter point. -/
theorem lille_nonneg (E : Q3Env Mode) (hv : FSParamsView E) : 0 ≤ E.lille := by
  rw [Work.BoseB7.lille_val E hv]
  exact Work.BoseBox.fsXp_nonneg hv.t_pos.le

/-- `η ≥ 0` at FS's parameter point. -/
theorem eta_nonneg (E : Q3Env Mode) (hv : FSParamsView E) : 0 ≤ eta E := by
  rw [errA_eta E hv]
  exact Work.BoseBox.fsXp_nonneg hv.t_pos.le

/-- `η ≤ 1` at FS's parameter point. -/
theorem eta_le_one (E : Q3Env Mode) (hv : FSParamsView E) : eta E ≤ 1 := by
  rw [errA_eta E hv]
  exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)

/-- `0 ≤ K₀` is forced by `Q3Kernel`: the lattice count `count_PL` bounds a
non-negative cardinality by `K₀(K_ℓK_L)³` and `K_ℓK_L ≥ 1`. -/
theorem K0_nonneg_of_kernel (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hv : FSParamsView E) (hK : Q3Kernel K₀ F T E) : 0 ≤ K₀ := by
  by_contra hneg
  have hneg' : K₀ < 0 := not_le.mp hneg
  have hcp := hK.count_PL
  have hcard : (0 : ℝ) ≤
      (((Work.BoseB7.excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hKl : 0 < E.Kl := lt_of_lt_of_le zero_lt_one hv.one_le_Kl
  have hKL : 0 < E.KL := lt_of_lt_of_le zero_lt_one hv.one_le_KL
  have hpos : 0 < (E.Kl * E.KL) ^ 3 := pow_pos (mul_pos hKl hKL) 3
  have hneg2 : K₀ * (E.Kl * E.KL) ^ 3 < 0 := mul_neg_of_neg_of_pos hneg' hpos
  linarith

/-- `K_ℓ² = ℓ²μa`: `ℓ = K_ℓ(μa)^{-1/2}` (`FSParamsView.ell_eq`). -/
theorem Kl_sq_eq (E : Q3Env Mode) (hv : FSParamsView E) :
    E.Kl ^ 2 = E.ell ^ 2 * (E.mu * E.aScat) := by
  have hμa : 0 < E.mu * E.aScat := mul_pos (Work.BoseB7.mu_pos E hv) hv.a_pos
  have hell : E.ell = E.Kl * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by
    rw [hv.ell_eq, Work.BoseB7.side]
  have hsqa : ((E.mu * E.aScat) ^ (-(1 / 2 : ℝ))) ^ 2 = (E.mu * E.aScat)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμa.le,
      show -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [hell, mul_pow, hsqa, mul_assoc, inv_mul_cancel₀ (ne_of_gt hμa), mul_one]

/-- **The `e4A` factor.**  `ρ_z²aℓ³√(𝓜/z²) = √𝓜|z|ρ_za` (`z² = ρ_zℓ³`). -/
theorem e4A_factor_eq (E : Q3Env Mode) (hv : FSParamsView E) :
    E.rho ^ 2 * E.aScat * E.ell ^ 3 * Real.sqrt (E.bigM / E.z ^ 2)
      = Real.sqrt E.bigM * |E.z| * E.rho * E.aScat := by
  have hz2 : E.z ^ 2 = E.rho * E.ell ^ 3 := Work.BoseB7.zsq_eq E hv
  have hρℓ : 0 < E.rho * E.ell ^ 3 :=
    mul_pos (Work.BoseB7.rho_pos E hv) (pow_pos (Work.BoseB7.ell_pos E hv) 3)
  have hsqrt : Real.sqrt (E.bigM / E.z ^ 2) = Real.sqrt E.bigM / |E.z| := by
    rw [Real.sqrt_div (Work.BoseB7.bigM_nonneg E hv), Real.sqrt_sq_eq_abs]
  have hzabs : |E.z| = Real.sqrt (E.rho * E.ell ^ 3) := by
    rw [← hz2, Real.sqrt_sq_eq_abs]
  rw [hsqrt, hzabs]
  set S := Real.sqrt (E.rho * E.ell ^ 3) with hS
  have hSpos : 0 < S := Real.sqrt_pos.mpr hρℓ
  have hS2 : S * S = E.rho * E.ell ^ 3 := by
    rw [hS]; exact Real.mul_self_sqrt hρℓ.le
  have h1 : E.rho ^ 2 * E.aScat * E.ell ^ 3 * (Real.sqrt E.bigM / S) * S
      = E.rho ^ 2 * E.aScat * E.ell ^ 3 * Real.sqrt E.bigM := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hSpos)]
  have h2 : Real.sqrt E.bigM * S * E.rho * E.aScat * S
      = E.rho ^ 2 * E.aScat * E.ell ^ 3 * Real.sqrt E.bigM := by
    rw [show Real.sqrt E.bigM * S * E.rho * E.aScat * S
        = Real.sqrt E.bigM * (S * S) * (E.rho * E.aScat) by ring, hS2]
    ring
  exact mul_right_cancel₀ (ne_of_gt hSpos) (h1.trans h2.symm)

/-- `e4A` with its first factor split off. -/
theorem e4A_eq (E : Q3Env Mode) (hv : FSParamsView E) :
    e4A E = Real.sqrt E.bigM * |E.z| * E.rho * E.aScat *
        (E.KH⁻¹ + (E.Kl * E.KL) ^ (-(E.intM : ℝ)) + (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E)
      + E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b := by
  rw [e4A, e4A_factor_eq E hv]

/-- `0 ≤ √𝓜|z|ρ_za` (the `e4A` factor). -/
theorem A0_nonneg (E : Q3Env Mode) (hv : FSParamsView E) :
    0 ≤ Real.sqrt E.bigM * |E.z| * E.rho * E.aScat :=
  mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (Work.BoseB7.rho_pos E hv).le) hv.a_pos.le

/-- `0 ≤ K_H⁻¹` at FS's parameter point. -/
theorem KH_inv_nonneg (E : Q3Env Mode) (hv : FSParamsView E) : 0 ≤ E.KH⁻¹ :=
  le_of_lt (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hv.one_le_KH))

/-- `0 ≤ (K_ℓK_L)^c` at FS's parameter point. -/
theorem KlKL_rpow_nonneg (E : Q3Env Mode) (hv : FSParamsView E) (c : ℝ) :
    0 ≤ (E.Kl * E.KL) ^ c :=
  Real.rpow_nonneg (mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hv.one_le_Kl))
    (le_of_lt (lt_of_lt_of_le zero_lt_one hv.one_le_KL))) c

/-- `0 ≤ E₀K_ℓ²𝓁⁴/b` (`b > 0`). -/
theorem E0_term_nonneg (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    0 ≤ E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b := by
  have h1 := Work.BoseB7A.errA_E0_nonneg E hv
  have h2 : 0 ≤ E.Kl ^ 2 := sq_nonneg _
  have h3 : 0 ≤ E.lille ^ 4 := by positivity
  exact div_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) hb.le

/-- **`e4A` dominates its `K_H⁻¹` term.** -/
theorem e4A_ge_KH (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * E.KH⁻¹ ≤ e4A E := by
  rw [e4A_eq E hv]
  have hA0 := A0_nonneg E hv
  have h1 := KH_inv_nonneg E hv
  have h2 := KlKL_rpow_nonneg E hv (-(E.intM : ℝ))
  have h3 : 0 ≤ (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E :=
    mul_nonneg (KlKL_rpow_nonneg E hv _) (eta_nonneg E hv)
  have h4 := E0_term_nonneg E hv hb
  nlinarith [mul_nonneg hA0 (add_nonneg h2 h3)]

/-- **`e4A` dominates its `(K_ℓK_L)^{-M}` term.** -/
theorem e4A_ge_tail (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * (E.Kl * E.KL) ^ (-(E.intM : ℝ)) ≤ e4A E := by
  rw [e4A_eq E hv]
  have hA0 := A0_nonneg E hv
  have h1 := KH_inv_nonneg E hv
  have h2 := KlKL_rpow_nonneg E hv (-(E.intM : ℝ))
  have h3 : 0 ≤ (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E :=
    mul_nonneg (KlKL_rpow_nonneg E hv _) (eta_nonneg E hv)
  have h4 := E0_term_nonneg E hv hb
  nlinarith [mul_nonneg hA0 (add_nonneg h1 h3)]

/-- **`e4A` dominates its `η` term.** -/
theorem e4A_ge_eta (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E
      ≤ e4A E := by
  rw [e4A_eq E hv]
  have hA0 := A0_nonneg E hv
  have h1 := KH_inv_nonneg E hv
  have h2 := KlKL_rpow_nonneg E hv (-(E.intM : ℝ))
  have h3 : 0 ≤ (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E :=
    mul_nonneg (KlKL_rpow_nonneg E hv _) (eta_nonneg E hv)
  have h4 := E0_term_nonneg E hv hb
  nlinarith [mul_nonneg hA0 (add_nonneg h1 h2)]

/-- **`e4A` dominates its `E₀K_ℓ²𝓁⁴/b` term.** -/
theorem e4A_ge_E0 (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b ≤ e4A E := by
  rw [e4A_eq E hv]
  have hA0 := A0_nonneg E hv
  have h1 := KH_inv_nonneg E hv
  have h2 := KlKL_rpow_nonneg E hv (-(E.intM : ℝ))
  have h3 : 0 ≤ (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E :=
    mul_nonneg (KlKL_rpow_nonneg E hv _) (eta_nonneg E hv)
  have h4 := E0_term_nonneg E hv hb
  nlinarith [mul_nonneg hA0 (add_nonneg (add_nonneg h1 h2) h3)]

/-- `√(Σ (Z f)²) = |Z|√(Σ f²)`. -/
theorem sqrt_sum_sq_mul (Z : ℝ) (f : Mode → ℝ) :
    Real.sqrt (∑ s ∈ excited Mode, (Z * f s) ^ 2)
      = |Z| * Real.sqrt (∑ s ∈ excited Mode, f s ^ 2) := by
  rw [show (∑ s ∈ excited Mode, (Z * f s) ^ 2)
      = Z ^ 2 * ∑ s ∈ excited Mode, f s ^ 2 by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring,
    Real.sqrt_mul (sq_nonneg Z), Real.sqrt_sq_eq_abs]

/-- `√(Σ (Z f)²) ≤ |Z|·Σ|f|`. -/
theorem sqrt_sum_sq_mul_le (Z : ℝ) (f : Mode → ℝ) :
    Real.sqrt (∑ s ∈ excited Mode, (Z * f s) ^ 2)
      ≤ |Z| * ∑ s ∈ excited Mode, |f s| := by
  rw [sqrt_sum_sq_mul]
  exact mul_le_mul_of_nonneg_left (sqrt_sum_sq_le_sum_abs _ _) (abs_nonneg Z)

end Work.BoseB7A
