import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.LWP.Main
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
-- ===== merged: Submission.Work.FTS.EllipticEst.Fstar_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Smoothness of the angular moment `F_*`

The angular moment `F_*(z) = ∫_θ F z θ · sin θ cos²θ dθ` of `Work.Elliptic.Defs` is a
parametric integral: the integration variable `θ` runs over the compact interval
`Iθ = [0,π/2]`, while the parameter `z` runs over `(-1,∞)`.  Since `SmoothNbhd F` says that
`(z,θ) ↦ F z θ` is smooth (indeed analytic) on the open neighbourhood
`U = (-1,∞) × (-1,π/2+1)` of the closed quadrant, and the angular weight is smooth, the
integral is smooth in the parameter: differentiating under the integral sign `k` times exhibits
the `k`-th derivative as the integral of the `k`-th `z`-derivative of the integrand, and the
differentiation step is legitimate because `Iθ` is compact (domination by a constant) and the
slices `z ↦ F z θ` are smooth on all of `(-1,∞)`.

The two inputs of the induction below are the delegated lemmas
`pzIter_uncurry_continuousOn` (joint continuity of the integrand and of all its `z`-derivatives
on `(-1,∞) × Iθ`, which is contained in the open set `U` on which `F` is smooth) and
`pzIter_integral_hasDerivAt` (differentiation under the `θ`-integral:
`∂_z ∫_θ ∂_z^k F · φ = ∫_θ ∂_z^{k+1} F · φ`).

The companion fact for the domain `(0,∞)` is `Work.Coercivity.contDiffOn_infty_integral_Itheta`;
here the domain is the full `(-1,∞)` of `SmoothNbhd`. -/

/-- **The parametric angular integral is smooth to all orders on `(-1,∞)`.**  For `u` smooth on
the open neighbourhood `U` of the closed quadrant and any angular weight `φ` continuous on `Iθ`,
the function `z ↦ ∫_θ u z θ · φ θ dθ` is `C^n` on `(-1,∞)` for every `n`. -/
theorem contDiffOn_infty_integral_Itheta_Ioi_neg_one (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) :
    ContDiffOn ℝ ∞ (fun z => ∫ θ in Work.Spaces.Iθ, u z θ * φ θ) (Set.Ioi (-1)) := by
  -- joint continuity of `(z,θ) ↦ ∂_z^k u (z,θ) · φ θ` on `(-1,∞) × Iθ`
  have hcont : ∀ k : ℕ, ContinuousOn
      (Function.uncurry fun z θ => Work.Spaces.pzIter k u z θ * φ θ)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
    fun k => pzIter_uncurry_continuousOn u φ hu hφ k
  -- the derivative of the `k`-th integral is the `(k+1)`-st one
  have hderiv : ∀ (k : ℕ) {s : ℝ}, s ∈ Set.Ioi (-1) →
      HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ)
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter (k + 1) u s θ * φ θ) s :=
    fun k _ hs => pzIter_integral_hasDerivAt u φ hu hφ k hs
  -- `C^n` for each of the iterated integrals, by induction on `n`
  have hmain : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ) (Set.Ioi (-1)) := by
    intro n
    induction n with
    | zero =>
      intro k
      exact (contDiffOn_zero (𝕜 := ℝ)).2
        (Work.Coercivity.continuousOn_integral_Itheta_of_continuousOn isOpen_Ioi (hcont k))
    | succ n ih =>
      intro k
      rw [Nat.cast_add, Nat.cast_one]
      refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ)
        (n := ((n : ℕ) : ℕ∞ω)) (s := Set.Ioi (-1)) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
      · intro s hs
        exact (hderiv k hs).differentiableAt.differentiableWithinAt
      · intro h
        exact absurd h (by simp)
      · exact (ih (k + 1)).congr (fun s hs => (hderiv k hs).deriv)
  exact contDiffOn_infty.mpr (fun n => hmain n 0)

/-- **The angular moment `F_*` of a `SmoothNbhd` function is `C^n` on `(-1,∞)`.**
Immediate from `contDiffOn_infty_integral_Itheta_Ioi_neg_one` with the angular weight
`sin θ cos²θ` and the identification `Fstar F z = ∫_θ F z θ · sin θ cos²θ dθ`. -/
theorem Fstar_contDiffOn (F : ℝ → ℝ → ℝ) (hF : Work.Spaces.SmoothNbhd F) (n : ℕ) :
    ContDiffOn ℝ n (fun z => Work.Elliptic.Fstar F z) (Set.Ioi (-1)) := by
  have hφ : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have h := contDiffOn_infty_integral_Itheta_Ioi_neg_one F Work.Elliptic.sinCos2 hF hφ
  simpa only [Work.Elliptic.Fstar] using contDiffOn_infty.mp h n

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HarOp_weighted_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted `L²` Hardy inequality for the operator `HarOp`

This module proves the `k = 0` case of the weighted Hardy estimate behind Elgindi's
Lemma `HardyInequality4` (Annals 194(3) 2021, §'The singular term', tex line 1030):

  `∫₀^∞ w(z)² (HarOp β f z)² dz ≤ (100/β²) ∫₀^∞ w(z)² f(z)² dz`  for `β ≥ 5`,

where `w(z) = (1+z)²/z²` is the weight of the paper's `H^k` spaces and

  `HarOp β f z = z^{-β} ∫₀^z s^{β-1} f(s) ds`

is the (weighted) Hardy operator of which the singular part `Ḡ` of the elliptic estimate is
`-(3/(4α))` times an instance (`Gbar_eq_HarOp`).

## Proof

The argument is the classical Cauchy–Schwarz / Tonelli pair, but with the *sharp* exponent on
the source: writing `s^{β-1} f(s) = s^{(β-1)/2} · s^{(β-1)/2} f(s)` and applying Cauchy–Schwarz
on `(0,z]` gives the pointwise bound

  `(HarOp β f z)² ≤ (1/β) z^{-β} ∫₀^z s^{β-1} f(s)² ds`      (`HarOp_pointwise_sq`),

whose constant `1/β` is exactly the sharp Hardy rate.  Multiplying by `w(z)²` and integrating,
Tonelli's theorem (`HarOp_lintegral_swap`) turns the double integral into

  `(1/β) ∫₀^∞ s^{β-1} f(s)² (∫_s^∞ w(z)² z^{-β} dz) ds`,

and since `w` is decreasing on `(0,∞)` the inner integral is bounded by
`w(s)² ∫_s^∞ z^{-β} dz = w(s)² s^{1-β}/(β-1)` (`w_tail_lintegral_bound`).  The factors
`s^{β-1} s^{1-β} = 1` cancel exactly, leaving

  `∫₀^∞ w² (HarOp β f)² ≤ (1/(β(β-1))) ∫₀^∞ w² f² ≤ (100/β²) ∫₀^∞ w² f²`,

the last step because `β ≥ 5` gives `100(β-1) ≥ β`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

theorem HarOp_weighted_lintegral (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0)) :
    ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (100 / β ^ 2) *
          ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2) := by
  have hβ1 : (1 : ℝ) < β := by linarith
  -- Step A: the pointwise Cauchy--Schwarz bound, then monotonicity of the lintegral.
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ ENNReal.ofReal (1 / β) *
          (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
    intro z hz
    have hz0 : 0 < z := hz
    have hy := HarOp_pointwise_sq β hβ1 f hf hz0
    calc ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal ((HarOp β f z) ^ 2) :=
          ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))
      _ ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
            (ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
              ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) :=
          mul_le_mul_of_nonneg_left hy bot_le
      _ = ENNReal.ofReal (1 / β) *
            (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
              ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
          rw [mul_assoc (ENNReal.ofReal (1 / β)) (ENNReal.ofReal (z ^ (-β)))
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [mul_left_comm (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
                (ENNReal.ofReal (1 / β))
                (ENNReal.ofReal (z ^ (-β)) *
                  ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [← mul_assoc (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
                (ENNReal.ofReal (z ^ (-β)))
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [← ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
  have hA : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
    have h := setLIntegral_mono' (μ := volume) measurableSet_Ioi hpt
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
    exact h
  -- Step B: Tonelli.
  rw [HarOp_lintegral_swap β hβ1 f hf] at hA
  -- Step C: the tail bound, pointwise in `s`.
  have hC : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))
      ≤ ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) :=
    setLIntegral_mono' (μ := volume) measurableSet_Ioi
      (fun s hs => mul_le_mul_of_nonneg_left (w_tail_lintegral_bound β hβ1 hs) bot_le)
  -- Step D: the algebra of the two `ofReal`s, where `s^{β-1} s^{1-β} = 1`.
  have hD : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
      = ENNReal.ofReal (1 / (β - 1)) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
    have hpt2 : ∀ s ∈ Set.Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
        = ENNReal.ofReal (1 / (β - 1)) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
      intro s hs
      have hs0 : 0 < s := hs
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _))]
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (β - 1))]
      congr 1
      have h1 : s ^ (β - 1) * s ^ (1 - β) = 1 := by
        rw [← Real.rpow_add hs0, show β - 1 + (1 - β) = 0 by ring, Real.rpow_zero]
      calc s ^ (β - 1) * f s ^ 2 * ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
          = (s ^ (β - 1) * s ^ (1 - β)) * ((Work.Spaces.w s) ^ 2 * f s ^ 2) / (β - 1) := by
            ring
        _ = (Work.Spaces.w s) ^ 2 * f s ^ 2 / (β - 1) := by rw [h1, one_mul]
        _ = 1 / (β - 1) * ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt2,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Step E: the numerical constant `1/(β(β-1)) ≤ 100/β²` for `β ≥ 5`.
  have hconst : (1 : ℝ) / β * (1 / (β - 1)) ≤ 100 / β ^ 2 := by
    rw [div_mul_div_comm, one_mul]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hβ]
  calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))) := hA
    _ ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) :=
        mul_le_mul_of_nonneg_left hC bot_le
    _ = ENNReal.ofReal (1 / β) *
        (ENNReal.ofReal (1 / (β - 1)) *
          ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2)) := by
        rw [hD]
    _ = (ENNReal.ofReal (1 / β) * ENNReal.ofReal (1 / (β - 1))) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (100 / β ^ 2) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / β)]
        exact ENNReal.ofReal_le_ofReal hconst

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.Spaces.HProductRule_Msummand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Elementary closure properties -/

/-- The pointwise product of two functions smooth on a neighbourhood of the closed
quadrant is again smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_mul {f g : ℝ → ℝ → ℝ} (hf : SmoothNbhd f) (hg : SmoothNbhd g) :
    SmoothNbhd (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) nbhU
  have h : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := rfl
  rw [h]
  exact hf.mul hg


/-- `VanishTheta` is preserved by iterated `D_z`-derivatives. -/
private lemma DzIter_vanish {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (n : ℕ) :
    VanishTheta (DzIter n f) := by
  induction n with
  | zero => exact h
  | succ m ih =>
      constructor
      · intro z
        have hfun : (fun z' => DzIter m f z' 0) = fun _ => (0 : ℝ) := funext ih.1
        simp [DzIter_succ, Dz, pz, hfun]
      · intro z
        have hfun : (fun z' => DzIter m f z' (π / 2)) = fun _ => (0 : ℝ) := funext ih.2
        simp [DzIter_succ, Dz, pz, hfun]

/-- Any positive iterate of `D_θ` vanishes on the two angular boundaries. -/
private lemma DthIter_vanish_of_pos (f : ℝ → ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    VanishTheta (DthIter a f) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  constructor
  · intro z
    show Real.sin (2 * 0) * pth (DthIter a' f) z 0 = 0
    simp
  · intro z
    show Real.sin (2 * (π / 2)) * pth (DthIter a' f) z (π / 2) = 0
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- `VanishTheta` is preserved by the mixed derivatives `D_z^b D_θ^a`. -/
private lemma VanishTheta_mixed {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (b a : ℕ) :
    VanishTheta (mixed b a f) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simpa [mixed] using DzIter_vanish h b
  · have h1 : VanishTheta (DthIter a f) := DthIter_vanish_of_pos f ha
    simpa [mixed] using DzIter_vanish h1 b

/-- A finite sum of functions integrable on a set is integrable on that set. -/
private theorem integrableOn_finsetSum {ι : Type*} {s : Set ℝ} {φ : ι → ℝ → ℝ} (t : Finset ι)
    (h : ∀ i ∈ t, IntegrableOn (φ i) s) : IntegrableOn (fun x => ∑ i ∈ t, φ i x) s := by
  classical
  induction t using Finset.induction with
  | empty =>
      simpa using (integrableOn_zero :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) s (μ := volume))
  | insert a t ha ih =>
      have hfun : (fun x => ∑ i ∈ insert a t, φ i x)
          = (fun x => φ a x) + (fun x => ∑ i ∈ t, φ i x) := by
        funext x; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ## The pointwise `L^∞` bound for derivatives of order at most `2` -/

/-- `PWB α u` is the square of the pointwise `L^∞` bound for `u` and all its first and
second `D_z`/`D_θ` derivatives: `(100²/(γ-1))·HkSq α 4 u` (Corollary
*SecondDerivativesBounded* of the paper). -/
private def PWB (α : ℝ) (u : ℝ → ℝ → ℝ) : ℝ := 100 ^ 2 / (gam α - 1) * HkSq α 4 u


/-- Pointwise form of the paper's Corollary *SecondDerivativesBounded*: every mixed
derivative of order `a + b ≤ 2` is pointwise bounded by `100²/(γ-1)·HkSq α 4 u` on the
domain. -/
private lemma mixed_sq_pw_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd u) (hvt : VanishTheta u) (hdec : DecayMixed 2 u) (hmem : HkMem α 4 u)
    (b a : ℕ) (hab : a + b ≤ 2) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ, (mixed b a u z θ) ^ 2 ≤ PWB α u := by
  have hsm' : SmoothNbhd (mixed b a u) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm a) b
  have hvt' : VanishTheta (mixed b a u) := VanishTheta_mixed hvt b a
  have hdec' : ∀ θ ∈ Iθ, Tendsto (fun z => mixed b a u z θ) atTop (𝓝 0) :=
    fun θ hθ => hdec a b hab θ hθ
  have hmem' : HkMem α 2 (mixed b a u) := HkMem_mixed_le α hα hα1 u hsm hmem b a hab
  have hγ : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hcoef : 100 / (gam α - 1) ≤ 100 ^ 2 / (gam α - 1) :=
    div_le_div_of_nonneg_right (by norm_num) hγ.le
  intro z hz θ hθ
  calc (mixed b a u z θ) ^ 2
      ≤ 100 / (gam α - 1) * HkSq α 2 (mixed b a u) :=
        HPwH2 α hα hα1 (mixed b a u) hsm' hvt' hdec' hmem' z hz θ hθ
    _ ≤ 100 ^ 2 / (gam α - 1) * HkSq α 2 (mixed b a u) :=
        mul_le_mul_of_nonneg_right hcoef (HkSq_nonneg α 2 (mixed b a u))
    _ ≤ 100 ^ 2 / (gam α - 1) * HkSq α 4 u :=
        mul_le_mul_of_nonneg_left (HkSq_mixed_le α hα hα1 u hsm hmem b a hab)
          (div_nonneg (by norm_num) hγ.le)
    _ = PWB α u := rfl

/-! ## The combinatorial case analysis -/

/-- For the pairs `(a,b)` occurring in the Leibniz expansion of `mixed j i (f g)` (so that
`a ≤ i`, `b ≤ j`) with `1 ≤ i`, `i + j ≤ 4` and `(j,i) ≠ (3,1)`, at least one of the two
factors has total order `≤ 2` while the *other* one carries a `θ`-derivative of order
`≥ 1`.  This is what makes the paper's "all other terms can be treated as `D_θ^4(fg)`"
precise: the exceptional configurations are exactly `(j,i) = (3,1)` with `a = 0, b = 3`
or `a = 1, b = 0`. -/
private lemma msum_orders {i j a b : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j) :
    (1 ≤ a ∧ (i - a) + (j - b) ≤ 2) ∨ (1 ≤ i - a ∧ a + b ≤ 2) := by
  by_cases hc : 1 ≤ a
  · by_cases hd : (i - a) + (j - b) ≤ 2
    · exact Or.inl ⟨hc, hd⟩
    · refine Or.inr ⟨?_, by omega⟩
      by_contra h
      push_neg at h
      omega
  · push_neg at hc
    exact Or.inr ⟨by omega, by omega⟩

/-! ## The Cauchy–Schwarz step of the Leibniz expansion -/

/-- Leibniz expansion of `D_z^j D_θ^i (f g)`, followed by Cauchy–Schwarz: the squared
weighted summand is bounded by `6400` times the sum over the expansion pairs of the
squared weighted pieces.  The constant is very generous: `25` for the cardinality of the
index set `(i+1)(j+1)` and `256 = 4^{i+j}` for the squared binomial coefficients. -/
private lemma expansion_cs (α : ℝ) (i j : ℕ) (hij : i + j ≤ 4) (f g : ℝ → ℝ → ℝ)
    (hfi : SmoothInt f) (hgi : SmoothInt g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
  intro z hz θ hθ
  set s : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (j + 1) with hs
  set X : ℕ × ℕ → ℝ := fun p => (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)
      * ((mixed p.2 p.1 f z θ * Wt α z θ) * mixed (j - p.2) (i - p.1) g z θ) with hX
  set Y : ℕ × ℕ → ℝ := fun p => (mixed p.2 p.1 f z θ * Wt α z θ) ^ 2
      * (mixed (j - p.2) (i - p.1) g z θ) ^ 2 with hY
  -- the exact Leibniz expansion, with the weight distributed
  have hexp : mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ = ∑ p ∈ s, X p := by
    have h1 : mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * ((mixed b a f z θ * Wt α z θ) * mixed (j - b) (i - a) g z θ) := by
      rw [mixed_mul_eq j i f g hfi hgi z hz θ hθ]
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      refine Finset.sum_congr rfl (fun b hb => ?_)
      ring
    rw [h1, hs, Finset.sum_product]
  -- the Cauchy–Schwarz step
  have hcard : ((s.card : ℕ) : ℝ) ≤ 25 := by
    have h25 : s.card ≤ 25 := by
      rw [hs, Finset.card_product, Finset.card_range, Finset.card_range]
      have hi5 : i + 1 ≤ 5 := by omega
      have hj5 : j + 1 ≤ 5 := by omega
      calc (i + 1) * (j + 1) ≤ 5 * 5 := Nat.mul_le_mul hi5 hj5
        _ = 25 := rfl
    exact_mod_cast h25
  have hcoef : ∀ p ∈ s, X p ^ 2 ≤ 256 * Y p := by
    intro p hp
    rw [hs, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have hai : p.1 ≤ i := by omega
    have hbj : p.2 ≤ j := by omega
    have hc16 : (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ) ≤ 16 := by
      have h1 : (i.choose p.1 : ℝ) ≤ 2 ^ i := by
        exact_mod_cast Nat.choose_le_two_pow i p.1
      have h2 : (j.choose p.2 : ℝ) ≤ 2 ^ j := by
        exact_mod_cast Nat.choose_le_two_pow j p.2
      calc (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)
          ≤ 2 ^ i * 2 ^ j := mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 2 ^ (i + j) := by rw [← pow_add]
        _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 16 := by norm_num
    have hid : X p ^ 2 = ((i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)) ^ 2 * Y p := by
      simp only [hX, hY]; ring
    have hYnn : 0 ≤ Y p := by simp only [hY]; positivity
    rw [hid]
    calc ((i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)) ^ 2 * Y p
        ≤ 16 ^ 2 * Y p :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc16 2) hYnn
      _ = 256 * Y p := by norm_num
  have hYsum : ∑ p ∈ s, Y p = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
      (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
    rw [hs, Finset.sum_product]
  have hYnn : 0 ≤ ∑ p ∈ s, Y p :=
    Finset.sum_nonneg (fun p _ => by simp only [hY]; positivity)
  have hX2nn : 0 ≤ ∑ p ∈ s, X p ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hbound : (∑ p ∈ s, X p) ^ 2 ≤ 6400 * ∑ p ∈ s, Y p := by
    calc (∑ p ∈ s, X p) ^ 2 ≤ (s.card : ℝ) * ∑ p ∈ s, X p ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ 25 * ∑ p ∈ s, X p ^ 2 := mul_le_mul_of_nonneg_right hcard hX2nn
      _ ≤ 25 * (256 * ∑ p ∈ s, Y p) :=
          mul_le_mul_of_nonneg_left
            (by
              calc ∑ p ∈ s, X p ^ 2 ≤ ∑ p ∈ s, 256 * Y p := Finset.sum_le_sum hcoef
                _ = 256 * ∑ p ∈ s, Y p := by rw [Finset.mul_sum])
            (by norm_num)
      _ = 6400 * ∑ p ∈ s, Y p := by ring
  calc (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
      = (∑ p ∈ s, X p) ^ 2 := by rw [hexp]
    _ ≤ 6400 * ∑ p ∈ s, Y p := hbound
    _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
        rw [hYsum]


/-! ## The majorant attached to a pair `(a,b)` of the Leibniz expansion -/

/-- The majorant of a single pair `(a,b)` of the Leibniz expansion of `mixed j i (f g)`:
whichever of the two factors has total order `≤ 2` is pulled out into its pointwise
`L^∞`-bound `PWB`, and the other one keeps its weighted `L²`-norm.

The two branches are `(a,b)` with `1 ≤ a` and `(i-a) + (j-b) ≤ 2` (the `g`-factor is
pulled out; the `f`-factor is a weighted mixed derivative with `1 ≤ a`), resp. the
complementary situation (`msum_orders` guarantees that at least one branch applies for
every pair occurring in the expansion, under the hypotheses of
`HProductRule_Msummand`). -/
private def MAJ (α : ℝ) (f g : ℝ → ℝ → ℝ) (j i a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => if 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
    then PWB α g * (mixed b a f z θ * Wt α z θ) ^ 2
    else PWB α f * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2

/-- The pointwise domination of a pair of the Leibniz expansion by its majorant. -/
private lemma MAJ_pw_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : SmoothNbhd f) (hvtf : VanishTheta f) (hdecf : DecayMixed 2 f) (hmemf : HkMem α 4 f)
    (hsimg : SmoothNbhd g) (hvtg : VanishTheta g) (hdecg : DecayMixed 2 g) (hmemg : HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1))
    {a b : ℕ} (hai : a ≤ i) (hbj : b ≤ j) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
      ≤ MAJ α f g j i a b z θ := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hB : (mixed (j - b) (i - a) g z θ) ^ 2 ≤ PWB α g :=
      mixed_sq_pw_le α hα hα1 g hsimg hvtg hdecg hmemg (j - b) (i - a) hc.2 z hz θ hθ
    have hnn : 0 ≤ (mixed b a f z θ * Wt α z θ) ^ 2 := sq_nonneg _
    rw [MAJ, if_pos hc]
    calc (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
        = (mixed (j - b) (i - a) g z θ) ^ 2 * (mixed b a f z θ * Wt α z θ) ^ 2 := by ring
      _ ≤ PWB α g * (mixed b a f z θ * Wt α z θ) ^ 2 := mul_le_mul_of_nonneg_right hB hnn
  · have h2 : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hA : (mixed b a f z θ) ^ 2 ≤ PWB α f :=
      mixed_sq_pw_le α hα hα1 f hsmf hvtf hdecf hmemf b a h2.2 z hz θ hθ
    rw [MAJ, if_neg hc]
    calc (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
        = (mixed b a f z θ) ^ 2 * (Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
          rw [mul_pow]
      _ ≤ PWB α f * (Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA (sq_nonneg _)) (sq_nonneg _)
      _ = PWB α f * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by rw [mul_pow]; ring

/-- The `θ`-slice of the majorant is integrable. -/
private lemma MAJ_integrableOn_theta (α : ℝ) (f g : ℝ → ℝ → ℝ) (j i a b : ℕ)
    (hsmf : SmoothNbhd f) (hmemf : HkMem α 4 f) (hsimg : SmoothNbhd g) (hmemg : HkMem α 4 g)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j)
    {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => MAJ α f g j i a b z θ) Iθ := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have h1 : IntegrableOn (fun θ => (mixed b a f z θ * Wt α z θ) ^ 2) Iθ :=
      mixed_sq_integrableOn hsmf hmemf a b hc.1 hab hz
    have h2 := h1.const_mul (PWB α g)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun θ _ => by simp only [MAJ]; rw [if_pos hc]) measurableSet_Icc
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have h1 : IntegrableOn (fun θ => (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2) Iθ :=
      mixed_sq_integrableOn hsimg hmemg (i - a) (j - b) h2'.1 hab hz
    have h2 := h1.const_mul (PWB α f)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun θ _ => by simp only [MAJ]; rw [if_neg hc]) measurableSet_Icc

/-- `L2Mem` for a weighted mixed derivative of order between `1` and `4`. -/
private theorem L2Mem_mixed_Wt (α : ℝ) (u : ℝ → ℝ → ℝ) (hsm : SmoothNbhd u)
    (hmem : HkMem α 4 u) (b a : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ 4) :
    L2Mem (fun z θ => mixed b a u z θ * Wt α z θ) := by
  constructor
  · intro z hz
    exact mixed_sq_integrableOn hsm hmem a b ha hab hz
  · exact (bt_prod_integrable α u hsm hmem b a ha hab).1.integral_prod_left

/-- Integrability in `z` of the angular integral of the majorant. -/
private lemma MAJ_integrableOn_z (α : ℝ) (f g : ℝ → ℝ → ℝ) (j i a b : ℕ)
    (hsmf : SmoothNbhd f) (hmemf : HkMem α 4 f) (hsimg : SmoothNbhd g) (hmemg : HkMem α 4 g)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j) :
    IntegrableOn (fun z => ∫ θ in Iθ, MAJ α f g j i a b z θ) Iz := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have h1 : IntegrableOn (fun z => ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2) Iz :=
      (L2Mem_mixed_Wt α f hsmf hmemf b a hc.1 hab).2
    have h2 := h1.const_mul (PWB α g)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z hz
    show PWB α g * ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, MAJ α f g j i a b z θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [MAJ]
    rw [if_pos hc]
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have h1 : IntegrableOn (fun z => ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2) Iz :=
      (L2Mem_mixed_Wt α g hsimg hmemg (j - b) (i - a) h2'.1 hab).2
    have h2 := h1.const_mul (PWB α f)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z hz
    show PWB α f * ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, MAJ α f g j i a b z θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [MAJ]
    rw [if_neg hc]

/-! ## Measurability of the weighted summand -/





end Work.Spaces
end
end
-- ===== merged: Submission.Work.StabilityFar.Decay.KernelDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar.Decay

open Work.LWP

/-- The Newtonian-potential kernel `b ↦ ‖b‖⁻³ • b` of the Biot–Savart integral. -/
noncomputable def kf (b : R3) : R3 := (‖b‖ ^ (3 : ℕ))⁻¹ • b

/-- The Fréchet derivative of `kf` at `b`, as a continuous linear map:
`v ↦ ‖b‖⁻³ • v - 3 ‖b‖⁻⁵ (b·v) b`. -/
noncomputable def kDerivCLM (b : R3) : R3 →L[ℝ] R3 :=
  (‖b‖ ^ (3 : ℕ))⁻¹ • ContinuousLinearMap.id ℝ R3
    - (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • (innerSL ℝ b).smulRight b

/-- The cross product with a fixed vector `u`, as a continuous linear map `v ↦ u × v`. -/
noncomputable def crossL (u : R3) : R3 →L[ℝ] R3 :=
  LinearMap.toContinuousLinearMap <|
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap).comp
      ((crossProduct u.ofLp).comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap)

/-- The candidate derivative of `biotSavart ω` at `x`, as the Bochner integral of the
derivatives of the Biot–Savart integrand.  In the far field `‖x‖ ≥ 2R` (with `ω` supported in
`B(0,R)`) this is genuinely `fderiv ℝ (biotSavart ω) x`. -/
noncomputable def bsDeriv (ω : R3 → R3) (x : R3) : R3 →L[ℝ] R3 :=
  (4 * Real.pi)⁻¹ • ∫ a : R3, (crossL (ω a)).comp (kDerivCLM (x - a))


/-! ## Elementary lemmas about the kernel objects -/

/-- The defining value of `crossL`: `crossL u v = u × v`. -/
theorem crossL_apply (u v : R3) : crossL u v = WithLp.toLp 2 (crossProduct u.ofLp v.ofLp) := rfl

/-- `crossL` is additive in its parameter. -/
theorem crossL_add (u u' : R3) : crossL (u + u') = crossL u + crossL u' := by
  ext v
  simp only [crossL_apply, ContinuousLinearMap.add_apply, WithLp.ofLp_add]
  rw [map_add]
  rfl


/-- The underlying vector of `kf`. -/
theorem kf_ofLp (b : R3) : (kf b).ofLp = (‖b‖ ^ (3 : ℕ))⁻¹ • b.ofLp := by
  simp [kf]

/-- The Biot–Savart integrand is the cross product kernel applied to `kf`. -/
theorem bsK_eq_crossL (ω : R3 → R3) (x a : R3) :
    Work.LWP.BiotSavart.bsK ω x a = crossL (ω a) (kf (x - a)) := by
  rw [Work.LWP.BiotSavart.bsK.eq_def, crossL_apply, kf_ofLp, map_smul]
  rfl

end Work.StabilityFar.Decay
end
