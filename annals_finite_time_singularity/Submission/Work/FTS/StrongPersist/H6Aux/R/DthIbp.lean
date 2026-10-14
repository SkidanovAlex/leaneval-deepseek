import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.slice_z_integrable
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.sliceThetaHardy
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyDefs
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.CoreInterpHk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false

/-!
# `CoreInterpHk` — the two-dimensional weighted interpolation for `α D_z ∂_θ`

Target (unchanged, as requested):

```
theorem CoreInterpHk (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.Spaces.SmoothNbhd V →
      Work.Spaces.VanishTheta V →
      Work.Spaces.HkMem α k V →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
            + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V)) := by
```

## Route of the proof (complete analysis; see `NOTES_CoreInterpHk.md`)

All the mathematics is in the weighted `η`-currency (`σ θ = sin(2θ)^{-η}`, `η = 99/100`).

### 1. The base case (`interp_base_case`)

The same estimate as the workspace's long-standing
`Work.FTS.EllipticEst.interpol_mixed_weighted`: for `h` smooth on a neighbourhood of the
closed quadrant, `VanishTheta h`, the four functionals finite and the two radial boundary
products vanishing,

  `α² mixInt h ≤ C (α⁴ ddInt h + ttInt h + α² dInt h)`.

Proof.  Put `ψ = D_zh` (so that `D_z∂_θh = ∂_θψ`), `X = mixInt h`, `DD = ddInt h`,
`TT = ttInt h`, `D = dInt h`, and `σ' = -2η cos(2θ) sin(2θ)^{-1-η}`,
`σ'' = 4η(1+η)cos²(2θ)sin(2θ)^{-2-η} + 4ηsin(2θ)^{-η}`.

* **IBP in `θ`.**  `∂_θ(σψ∂_θψ) = σ(∂_θψ)² + σψ∂_θ²ψ + σ'ψ∂_θψ`, and the boundary terms
  `[σψ∂_θψ]_{θ=0}^{π/2}` vanish (`ψ(z,0) = ψ(z,π/2) = 0`, `σψ∂_θψ = O(sin(2θ)^{1-η})`);
  the `σ'`-term is turned around once more, with the same vanishing boundary.  Result:
  `X = -∫∫w²σ(D_zh)(D_z∂_θ²h) + 2η(1+η)∫∫w²cos²(2θ)sin(2θ)^{-2-η}(D_zh)²
        + 2η∫∫w²σ(D_zh)²`.
* **Sharp Hardy in `θ`** (`hardy_shift_two_same_weight`, applied to the `θ`-slice of `D_zh`,
  which vanishes at `θ = 0, π/2`):
  `∫σ(D_zh)²sin(2θ)^{-2} ≤ (1+η)^{-2}∫σ(∂_θD_zh)² + C∫σ(D_zh)²`, so the `cos²`-term is
  `≤ (2η/(1+η))X + C₁D`; the `η`-term is `2ηD`.
* **IBP in `z`** (`∂_t` in `t = log z`, where `ρ = w²z² = (1+z)^4/z²` and
  `∂_z(w²z²) = w²z·2(z-1)/(1+z)`, `|2(z-1)/(1+z)| ≤ 3`;
  `z·(w²)' = -4w²/(1+z)` is `Work.FTS.EllipticEst.AngSecond.z_mul_deriv_w2`):
  `-∫∫w²σ(D_zh)(D_z∂_θ²h) = ∫∫w²σ(D_z²h)(∂_θ²h) + ∫∫w²σ((z-3)/(1+z))(D_zh)(∂_θ²h)
     + (boundary terms)`, and the boundary terms are exactly the two `Tendsto` hypotheses.
* **Assembly.**  Cauchy–Schwarz gives
  `X ≤ (2η/(1+η))X + √(DD·TT) + 3√(D·TT) + (2η + C₁)D`, hence, since
  `1 - 2η/(1+η) = (1-η)/(1+η) = 1/199`,
  `X ≤ 199[√(DD·TT) + 3√(D·TT) + C·D]`; AM–GM (`2α²√(DD·TT) ≤ α⁴DD + TT`,
  `2α²√(D·TT) ≤ α²D + α²TT ≤ α²D + TT`) yields the stated form.

### 2. The slot bookkeeping in `HkSq`

With `Y(a,b) = ∫∫w²σ(D_z^a∂_θ^bV)²`:

* the first (`D_z`-)family of `HkIntegrand α k (αD_z∂_θV)` consists of the
  `α²(D_z^{i+1}∂_θV)²w²σ = α²X(D_z^iV)`, `i ≤ k`, so the base case applied to `h = D_z^iV`
  (`i = 0,…,k`) gives `α²Σ_{a≤k+1}Y(a,1) ≤ CΣ_{i≤k}(α⁴Y(i+2,0) + Y(i,2) + α²Y(i+1,0))`,
  every slot of which is a summand of the three right-hand `H^k`-norms:
  `Y(a,0)`, `a ≤ k+1`, of `HkMem (Dz V)`; `Y(a,2)`, `a ≤ k`, of `HkMem (pthIter 2 V)`;
  `Y(a,0)`, `a ≤ k+2`, of `HkMem (z²∂_z²V)` together with `HkMem (Dz V)`, via
  `D_z^a(z²∂_z²V) = D_z^{a+2}V - D_z^{a+1}V`;
* the mixed family consists of `(D_z^{j+1}D_θ^i∂_θV)²w²sin(2θ)^{-γ}`, `1 ≤ i`, `i+j ≤ k`.
  Expanding `D_θ^i∂_θ = Σ_{L=2}^{i+1}c_{i,L}∂_θ^L` with `|c_{i,L}| ≤ C_i sin(2θ)^{L-1}`
  (`Work.FTS.EllipticEst.DthIter_eq_sum_dthCoef` + `dthCoef_bound`) and using
  `sin(2θ)^{2L-2-γ} ≤ sin(2θ)^{-η}` for `L ≥ 2` bounds each summand by
  `C_kΣ_{L≤i+1}Y(j+1,L)`; the terms `L ≥ 3` are dominated by the mixed summands
  `(D_z^{j+1}D_θ^{L-2}∂_θ²V)²W²` of `HkSq α k (∂_θ²V)`, and the terms `L = 2` by the
  summands `Y(j+1,2)` of the first family of `HkSq α k (∂_θ²V)`;
* additivity of the norm (`HkNorm_add_le`) and homogeneity (`HkNorm_const_mul`) assemble the
  two families, and taking square roots gives the target.
-/

section Elementary

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _



end Elementary

/-! ## Content lemmas: the `σ`-slots sit inside the right-hand `H^k`-norms

For `Y(a,b) = ∫∫w²σ(D_z^a∂_θ^bV)²` we need, for the bookkeeping:

* `Y(a,2)` as a summand of the first family of `HkSq α k (pthIter 2 V)` (`a ≤ k`);
* `Y(a,0)` as a summand of the first family of `HkSq α k (Dz V)` (`a ≤ k+1`).

Both are the existing `Work.Spaces.L2Sq_DzIter_le_HkSq` with the weight folded into the
function (and, in the second case, the operator shift `D_z^{a-1}(D_zV) = D_z^aV`).
-/


/-- **The pointwise identity `z² ∂_z²V = D_z²V - D_zV`** on the box `U`.

(`D_z²V = D_z(D_zV) = z ∂_z(z ∂_zV) = z ∂_zV + z²∂_z²V = D_zV + z²∂_z²V`.)  This is the
identity which turns the `z²pzIter 2 V`-slots into the `D_z`-slots of `V`. -/
theorem zsq_pzIter_two_eq {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V)
    {p : ℝ × ℝ} (hp : p ∈ Work.Spaces.U) :
    p.1 ^ 2 * Work.Spaces.pzIter 2 V p.1 p.2
      = Work.Spaces.Dz (Work.Spaces.Dz V) p.1 p.2 - Work.Spaces.Dz V p.1 p.2 := by
  have h1 : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pz V)) Work.Spaces.U :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm
  have hd2 : DifferentiableAt ℝ (fun z' => deriv (fun z'' => V z'' p.2) z') p.1 := by
    have h := Work.Spaces.differentiableAt_curry_left
      ((h1.differentiableOn (n := ⊤) (by simp)).differentiableAt
        (Work.Spaces.isOpen_U.mem_nhds hp))
    simpa only [Work.Spaces.pz, Function.uncurry] using h
  have hprod : deriv (fun z' => z' * deriv (fun z'' => V z'' p.2) z') p.1
      = deriv (fun z'' => V z'' p.2) p.1
        + p.1 * deriv (fun z' => deriv (fun z'' => V z'' p.2) z') p.1 := by
    have h := deriv_mul (c := id) (d := fun z' => deriv (fun z'' => V z'' p.2) z')
      (x := p.1) differentiableAt_id hd2
    rw [show (id * fun z' => deriv (fun z'' => V z'' p.2) z')
        = (fun z' => z' * deriv (fun z'' => V z'' p.2) z') from rfl] at h
    simpa using h
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  rw [hprod]
  ring

/-- The uncurried `D_z`-iterates of a function smooth on the box are smooth on the box. -/
theorem contDiffOn_uncurry_DzIter {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter n V)) Work.Spaces.U := by
  induction n with
  | zero =>
      simpa only [Work.Spaces.SmoothNbhd, Work.Spaces.U, Work.Spaces.DzIter_zero] using hsm
  | succ m ih =>
      have hpz := Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U ih
      have hfun : Function.uncurry (Work.Spaces.DzIter (m + 1) V)
          = (fun p : ℝ × ℝ => p.1) * Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter m V)) := by
        funext p
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, Function.uncurry,
          Pi.mul_apply]
      rw [hfun]
      exact contDiffOn_fst.mul hpz









/-- **The radial integration by parts with boundary terms.**  For `0 < a ≤ b` and `φ, ψ` of
class `C¹` on `(0,∞)`,

  `∫_a^b w² φ (z ψ') = [z w² φ ψ]_a^b - ∫_a^b (w²·((z-3)/(1+z))·φ + z w² · φ') ψ`. -/
theorem radial_ibp_bt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0)) :
    (∫ z in a..b, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = (b * (Work.Spaces.w b) ^ 2 * φ b * ψ b
          - a * (Work.Spaces.w a) ^ 2 * φ a * ψ a)
        - ∫ z in a..b, ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
            + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) * ψ z := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  have hphid : ∀ z, 0 < z → HasDerivAt φ (deriv φ z) z := fun z hz =>
    ((hφ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hpsid : ∀ z, 0 < z → HasDerivAt ψ (deriv ψ z) z := fun z hz =>
    ((hψ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hwu : ∀ z, 0 < z → HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := by
      have hw : DifferentiableAt ℝ (fun y : ℝ => Work.Spaces.w y) z := by
        have h1 : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) z := by
          apply DifferentiableAt.div <;> try fun_prop
          exact pow_ne_zero 2 hz0
        simpa only [Work.Spaces.w] using h1
      exact differentiableAt_id.mul (hw.pow 2)
    have hdv : deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
        = (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) := by
      rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z hz0, Work.Spaces.w]
      field_simp
    rw [← hdv]; exact hdiff.hasDerivAt
  have hwcont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
      apply ContinuousOn.div <;> try fun_prop
      intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
    simpa only [Work.Spaces.w] using h1.mono hsub
  have hdφcont : ContinuousOn (deriv φ) (Set.Icc a b) :=
    (hφ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hdψcont : ContinuousOn (deriv ψ) (Set.Icc a b) :=
    (hψ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hφcont : ContinuousOn φ (Set.Icc a b) := hφ.continuousOn.mono hsub
  have hu'cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
      + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) (Set.Icc a b) := by
    have hdiv : ContinuousOn (fun z : ℝ => (z - 3) / (1 + z)) (Set.Icc a b) := by
      apply ContinuousOn.div <;> try fun_prop
      intro z hz
      exact ne_of_gt (by linarith [hz.1, ha] : (0 : ℝ) < 1 + z)
    exact (((hwcont.pow 2).mul hdiv).mul hφcont).add
      ((continuousOn_id.mul (hwcont.pow 2)).mul hdφcont)
  have hu'int : IntervalIntegrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
      + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) volume a b :=
    hu'cont.intervalIntegrable_of_Icc hab
  have hψ'int : IntervalIntegrable (deriv ψ) volume a b :=
    hdψcont.intervalIntegrable_of_Icc hab
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * φ y) (v := ψ)
      (u' := fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
        + (z * (Work.Spaces.w z) ^ 2) * deriv φ z)
      (v' := deriv ψ)
      (fun x hx => by
        have hxab : a ≤ x ∧ x ≤ b := by
          rw [Set.uIcc_of_le hab] at hx; exact hx
        exact (hwu x (by linarith [hxab.1, ha])).mul (hphid x (by linarith [hxab.1, ha])))
      (fun x hx => by
        have hxab : a ≤ x ∧ x ≤ b := by
          rw [Set.uIcc_of_le hab] at hx; exact hx
        exact hpsid x (by linarith [hxab.1, ha]))
      hu'int hψ'int
  rw [show (∫ z in a..b, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in a..b, (z * (Work.Spaces.w z) ^ 2 * φ z) * deriv ψ z by
    apply intervalIntegral.integral_congr
    intro z _; ring]
  rw [hIBP]



/-! ## The `θ`-slice honesty of the two families, and the unconditional decomposition

`RPFresh.LHSDecomp` proves the pointwise decomposition of the `ℋ^k`-integrand of `α·D_z∂_θV`
into the two families `lhsZ` (radial) and `lhsM` (mixed), together with the integral estimate

`HkSq α k (α·D_z∂_θV) ≤ C (α² ∑_r ∫_z mixIntS(D_z^rV) + α² ∑_{i,j} ∫_z mixedIntS α i j V)`

**provided** the majorant

`T z = α² ∑_r mixIntS(D_z^rV) z + α² ∑_{i,j} [1 ≤ i ∧ i+j ≤ k] mixedIntS α i j V z`

is integrable in `z`.  That hypothesis is not a consequence of the target's hypotheses — the
Bochner integral of a non-integrable function is `0`, so `HkSq` can hide a finite contribution —
but for the data of the target the two families do have honest `θ`-slices for **every** `z ∈ Iz`:

* the radial family: `θ ↦ D_z∂_θ(D_z^rV) z θ` is the `θ`-slice of a function which is `C^∞` on
  an open neighbourhood of the closed quadrant, hence bounded on the compact `Iθ`, while
  `thEta θ = sin(2θ)^{-η}` is integrable on `Iθ` (`RPFresh.slice_z_integrable`);
* the mixed family: `mixed j i f` with `i ≥ 1` carries one factor `sin(2θ)` for each `D_θ`
  (since `D_θ = sin(2θ)∂_θ`), which compensates the singularity of `thGam α θ = sin(2θ)^{-γ}`
  at `θ = 0, π/2` (`RPFresh.slice_mixed_integrable`).

Hence `θ ↦ HkIntegrand α k (α·D_z∂_θV) z θ` integrates to exactly `T z`, and `HkSq` of the
left-hand side is the honest integral of `T`; the estimate follows in the integrable case from
`LHSDecomp`, and in the non-integrable case both sides are `0 ≤ ·`. -/




/-- The open-quadrant smoothness of `D_zV`. -/
private theorem smoothOpen_Dz {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz V) := by
  have hsmU : ContDiffOn ℝ ⊤ (Function.uncurry V) Work.Spaces.U := hsm
  have hpz : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pz V)) Work.Spaces.U :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsmU
  have hDsm : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz V)) Work.Spaces.U := by
    rw [show Function.uncurry (Work.Spaces.Dz V)
        = (fun p : ℝ × ℝ => p.1) * Function.uncurry (Work.Spaces.pz V) from rfl]
    exact contDiffOn_fst.mul hpz
  refine (hDsm.of_le le_top).mono (Set.prod_mono ?_ ?_)
  · exact Set.Ioi_subset_Ioi (by norm_num)
  · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])



/-! ## The target -/


end Work.FTS.EllipticEst.RPFresh
end
end
-- ===== merged: Submission.Work.FTS.H2.DivSinQR.mixedSlotFull =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivSinQR

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Measure-theoretic bookkeeping on the angular interval -/

/-- The measure of `Iθ` only sees the open interval. -/
private lemma restrict_Iθ_eq_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2)).symm

/-- A property holding on the open interval holds a.e. on `Iθ`. -/
private lemma ae_of_forall_Ioo {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ

/-- If `f` is integrable on the three pieces `(0,π/8]`, `[π/8,3π/8]`, `(3π/8,π/2)`, then it is
integrable on `Iθ`. -/
private lemma integrableOn_Iθ_of_regions {f : ℝ → ℝ}
    (h1 : MeasureTheory.IntegrableOn f (Set.Ioc 0 (Real.pi / 8)))
    (h2 : MeasureTheory.IntegrableOn f (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)))
    (h3 : MeasureTheory.IntegrableOn f (Set.Ioc (3 * Real.pi / 8) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn f Work.Spaces.Iθ := by
  have hs1 : MeasureTheory.IntegrableOn f (Set.Icc 0 (Real.pi / 8)) :=
    IntegrableOn.congr_set_ae h1
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 8)).symm
  have hs3 : MeasureTheory.IntegrableOn f (Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) :=
    IntegrableOn.congr_set_ae h3
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := 3 * Real.pi / 8)
        (b := Real.pi / 2)).symm
  have hset : Set.Icc (0 : ℝ) (Real.pi / 8) ∪ Set.Icc (Real.pi / 8) (3 * Real.pi / 8)
      ∪ Set.Icc (3 * Real.pi / 8) (Real.pi / 2) = Work.Spaces.Iθ := by
    ext x
    simp only [Work.Spaces.Iθ, Set.mem_union, Set.mem_Icc]
    constructor
    · rintro ((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩)
      · exact ⟨ha, by linarith [Real.pi_pos]⟩
      · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · exact ⟨by linarith [Real.pi_pos], hb⟩
    · rintro ⟨ha, hb⟩
      rcases le_total x (Real.pi / 8) with hle | hle
      · exact Or.inl (Or.inl ⟨ha, hle⟩)
      rcases le_total x (3 * Real.pi / 8) with hle' | hle'
      · exact Or.inl (Or.inr ⟨hle, hle'⟩)
      · exact Or.inr ⟨hle', hb⟩
  rw [← hset]
  exact (hs1.union h2).union hs3

/-- Reflection transfers integrability from the near region to the far region. -/
private lemma integrableOn_far_iff_near (F : ℝ → ℝ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => F (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 8))
      ↔ MeasureTheory.IntegrableOn F (Set.Ioo (3 * Real.pi / 8) (Real.pi / 2)) := by
  have hset : (fun θ : ℝ => Real.pi / 2 - θ) ⁻¹' Set.Ioo (3 * Real.pi / 8) (Real.pi / 2)
      = Set.Ioo 0 (Real.pi / 8) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith [Real.pi_pos]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have h := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    (Work.FTS.H2.DivQ.far_measurePreserving_reflθ)
    (Work.FTS.H2.DivQ.far_measurableEmbedding_reflθ) (f := F)
    (s := Set.Ioo (3 * Real.pi / 8) (Real.pi / 2))
  rwa [hset] at h

/-! ## The whole-interval bound and honesty for a level-`i` mixed slot -/

/-- **The full-interval bound and integrability for the level-`i` angular slot of
`h / sin(2θ)`.**  Combining `nearRegionLHS_i` (near region), `middleRegionLHS_i` (middle) and
`farRegionLHS` (far region, by reflection) gives, on the whole of `Iθ`, the weighted bound
`∫_{Iθ}(D_θ^i(h/sin2θ))² sin(2θ)^{-γ} ≤ C (Denη + Σ_{1≤m≤i} Denγ m)` in terms of the honest data
`Denη = ∫(∂_θh)²sin(2θ)^{-η}`, `Denγ m = ∫(D_θ^m(∂_θh))²sin(2θ)^{-γ}`, and the near-region
integrability `nearRegionIntegrable` (together with its reflection and compactness in the middle)
gives the integrability of the integrand on `Iθ`. -/
theorem mixedSlotBoundIθ :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨Cn, hCnpos, hN⟩ := Work.FTS.H2.DivQ.nearRegionLHS_i
  obtain ⟨Cm, hCmpos, hM⟩ := Work.FTS.H2.DivQ.middleRegionLHS_i
  obtain ⟨Cf, hCfpos, hF⟩ := Work.FTS.H2.DivQ.farRegionLHS
  refine ⟨Cn + Cm + Cf, by positivity, ?_⟩
  intro α h hα hα1 hsm ht0 ht1 hDenη i hi hDenγ
  set F : ℝ → ℝ := fun θ =>
    (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) with hFdef
  set SS : ℝ := (∫ θ in Work.Spaces.Iθ,
        (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) with hSS
  have hSSnn : 0 ≤ SS := by
    rw [hSS]
    refine add_nonneg ?_ (Finset.sum_nonneg fun m _ => ?_)
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  -- the three region bounds
  have hNb : (∫ θ in (0 : ℝ)..(Real.pi / 8), F θ) ≤ Cn * SS := by
    rw [hFdef, hSS]
    exact hN α h hα hα1 hsm ht0 hDenη i hi hDenγ
  have hMb : (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), F θ) ≤ Cm * SS := by
    rw [hFdef, hSS]
    exact hM α h hα hα1 hsm ht0 ht1 hDenη i hi hDenγ
  have hFb : (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2), F θ) ≤ Cf * SS := by
    rw [hFdef, hSS]
    exact hF α h hα hα1 hsm ht0 ht1 hDenη i hi hDenγ
  -- the three integrability statements
  have hIntNear : MeasureTheory.IntegrableOn F (Set.Ioc 0 (Real.pi / 8)) := by
    rw [hFdef]
    exact Work.FTS.H2.DivQ.nearRegionIntegrable α h hα hα1 hsm ht0 hDenη i hi hDenγ
  have hIntMid : MeasureTheory.IntegrableOn F (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := by
    rw [hFdef]
    have hcont : ContinuousOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
      (((Work.FTS.H2.DivQ.continuousOn_Dth1Iter_div hsm i).pow 2).mul
        (Work.FTS.H2.DivQ.continuousOn_rpow_neg_sin_two (Work.Spaces.gam α)))
    exact hcont.integrableOn_compact isCompact_Icc
  have hIntFarIoo : MeasureTheory.IntegrableOn F (Set.Ioo (3 * Real.pi / 8) (Real.pi / 2)) := by
    have hgsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 2)) := by
      have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.pi / 2 - θ)
          (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_const.sub contDiffOn_id
      refine (hsm.comp h2 ?_)
      intro θ hθ
      exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have hg0 : Filter.Tendsto (fun θ : ℝ => h (Real.pi / 2 - θ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0) (𝓝 (Real.pi / 2)) := by
            have h3 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0)
                (𝓝 (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
            simpa using h3
          exact h2.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with θ hθ
          simp only [Set.mem_Ioi] at hθ
          exact sub_lt_self _ hθ
      simpa [Function.comp_def] using ht1.comp h1
    have hgDenη : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (fun θ' : ℝ => h (Real.pi / 2 - θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      Work.FTS.H2.DivQ.far_data_eta_integrable hsm hDenη
    have hgDenγ : ∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' : ℝ => h (Real.pi / 2 - θ'))) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
      fun m hm => Work.FTS.H2.DivQ.far_data_gam_integrable m α hsm (hDenγ m hm)
    have hgNear : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter i
            (fun θ' : ℝ => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioc 0 (Real.pi / 8)) :=
      Work.FTS.H2.DivQ.nearRegionIntegrable α (fun θ : ℝ => h (Real.pi / 2 - θ))
        hα hα1 hgsm hg0 hgDenη i hi hgDenγ
    have hgNearIoo : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter i
            (fun θ' : ℝ => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioo 0 (Real.pi / 8)) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mp hgNear
    -- transfer to the far region
    have hrefl : MeasureTheory.IntegrableOn (fun θ : ℝ => F (Real.pi / 2 - θ))
        (Set.Ioo 0 (Real.pi / 8)) := by
      refine hgNearIoo.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hθ2 : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      show (Work.Elliptic.Dth1Iter i (fun θ' : ℝ => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = F (Real.pi / 2 - θ)
      rw [hFdef]
      change (Work.Elliptic.Dth1Iter i (fun θ' : ℝ => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Work.Elliptic.Dth1Iter i (fun θ' : ℝ => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - θ)) ^ 2
          * (Real.sin (2 * (Real.pi / 2 - θ))) ^ (-(Work.Spaces.gam α))
      rw [Work.FTS.H2.DivQ.sin_two_reflSlice θ,
        ← Work.FTS.H2.DivQ.far_sq_Dth1Iter_divSin_reflSlice_eq i hsm θ hθ2]
    exact (integrableOn_far_iff_near F).mp hrefl
  have hIntFar : MeasureTheory.IntegrableOn F (Set.Ioc (3 * Real.pi / 8) (Real.pi / 2)) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hIntFarIoo
  have hIntAll : MeasureTheory.IntegrableOn F Work.Spaces.Iθ :=
    integrableOn_Iθ_of_regions hIntNear hIntMid hIntFar
  -- integrability on the middle+far half
  have hIntMidFar : MeasureTheory.IntegrableOn F (Set.Ioc (Real.pi / 8) (Real.pi / 2)) := by
    have hunion : MeasureTheory.IntegrableOn F
        (Set.Ioc (Real.pi / 8) (3 * Real.pi / 8) ∪ Set.Ioc (3 * Real.pi / 8) (Real.pi / 2)) :=
      (hIntMid.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)).union hIntFar
    rwa [show Set.Ioc (Real.pi / 8) (3 * Real.pi / 8) ∪ Set.Ioc (3 * Real.pi / 8) (Real.pi / 2)
        = Set.Ioc (Real.pi / 8) (Real.pi / 2) from by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, le_trans h2 (by linarith [Real.pi_pos])⟩
        · exact ⟨by linarith [Real.pi_pos], h2⟩
      · rintro ⟨h1, h2⟩
        rcases lt_or_ge (3 * Real.pi / 8) x with hlt | hge
        · exact Or.inr ⟨hlt, h2⟩
        · exact Or.inl ⟨h1, hge⟩] at hunion
  -- split the integral
  have hiN : IntervalIntegrable F volume (0 : ℝ) (Real.pi / 8) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 8)]
    exact hIntNear
  have hiMF : IntervalIntegrable F volume (Real.pi / 8) (Real.pi / 2) := by
    rw [intervalIntegrable_iff,
      Set.uIoc_of_le (by linarith [Real.pi_pos] : Real.pi / 8 ≤ Real.pi / 2)]
    exact hIntMidFar
  have hiM : IntervalIntegrable F volume (Real.pi / 8) (3 * Real.pi / 8) := by
    rw [intervalIntegrable_iff,
      Set.uIoc_of_le (by linarith [Real.pi_pos] : Real.pi / 8 ≤ 3 * Real.pi / 8)]
    exact hIntMid.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hiF : IntervalIntegrable F volume (3 * Real.pi / 8) (Real.pi / 2) := by
    rw [intervalIntegrable_iff,
      Set.uIoc_of_le (by linarith [Real.pi_pos] : 3 * Real.pi / 8 ≤ Real.pi / 2)]
    exact hIntFar
  have hsplit1 : (∫ θ in Work.Spaces.Iθ, F θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  have hsplit2 : (∫ θ in (0 : ℝ)..(Real.pi / 2), F θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 8), F θ) + ∫ θ in (Real.pi / 8)..(Real.pi / 2), F θ :=
    (intervalIntegral.integral_add_adjacent_intervals hiN hiMF).symm
  have hsplit3 : (∫ θ in (Real.pi / 8)..(Real.pi / 2), F θ)
      = (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), F θ)
        + ∫ θ in (3 * Real.pi / 8)..(Real.pi / 2), F θ :=
    (intervalIntegral.integral_add_adjacent_intervals hiM hiF).symm
  refine ⟨hIntAll, ?_⟩
  rw [hsplit1, hsplit2, hsplit3]
  have harith : (Cn + Cm + Cf) * SS = Cn * SS + Cm * SS + Cf * SS := by ring
  linarith [hNb, hMb, hFb, harith]

end Work.FTS.H2.DivSinQR
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `sin(2θ)^{-q}·H²`. -/
def IbpU (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-q) * (H θ) ^ 2

/-- `sin(2θ)·∂_θH·H·sin(2θ)^{-q}`. -/
def IbpA (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.sin (2 * θ) * deriv H θ * H θ * (Real.sin (2 * θ)) ^ (-q)

/-- `cos(2θ)·sin(2θ)^{-q}·H²`. -/
def IbpE (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * (H θ) ^ 2

/-- **The one-dimensional angular integration by parts** on `[0,π/2]`, with weight
`sin(2θ)^{-q}`.  The three integrability hypotheses make the boundary terms vanish. -/
theorem sliceIbp {q : ℝ} {H : ℝ → ℝ}
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt H (deriv H θ) θ)
    (hU : MeasureTheory.IntegrableOn (IbpU q H) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn (IbpA q H) Work.Spaces.Iθ)
    (hE : MeasureTheory.IntegrableOn (IbpE q H) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, IbpA q H θ) = (q - 1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  set v' : ℝ → ℝ := fun θ => 2 * IbpA q H θ - 2 * (q - 1) * IbpE q H θ with hv'def
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * (IbpU q H θ')) (v' θ) θ := by
    intro θ hθ
    have h1 := IbpInnerDeriv (q := q) hH θ hθ
    simpa only [v', IbpA, IbpE, IbpU] using h1
  have hwnn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ IbpU q H θ := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    exact mul_nonneg (Real.rpow_nonneg hs.le _) (sq_nonneg _)
  have hv'int : MeasureTheory.IntegrableOn v' Work.Spaces.Iθ := by
    refine ((hA.const_mul 2).sub (hE.const_mul (2 * (q - 1)))).congr ?_
    filter_upwards with θ
    simp only [v', Pi.sub_apply]
    try ring
  have hlim := SinBoundaryTendsto hU hwnn hderiv hv'int
  have hInt : IntervalIntegrable v' volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hv'int.mono_set Set.Ioc_subset_Icc_self)
  have hFTC : (∫ θ in (0 : ℝ)..(Real.pi / 2), v' θ) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hInt
      hlim.1 hlim.2
    simpa using h
  have hconv : ∀ g : ℝ → ℝ,
      (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have h0 : (∫ θ in Work.Spaces.Iθ, v' θ) = 0 := by rw [hconv]; exact hFTC
  have hdecomp : (∫ θ in Work.Spaces.Iθ, v' θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, IbpA q H θ)
        - (2 * (q - 1)) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ) := by
    rw [show v' = fun θ => 2 * IbpA q H θ - (2 * (q - 1)) * IbpE q H θ from rfl,
      MeasureTheory.integral_sub (hA.const_mul 2) (hE.const_mul (2 * (q - 1))),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have h2 : (2 : ℝ) * ((∫ θ in Work.Spaces.Iθ, IbpA q H θ)
      - (q - 1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ)) = 0 := by
    rw [show (2 : ℝ) * ((∫ θ in Work.Spaces.Iθ, IbpA q H θ)
        - (q - 1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ))
        = (∫ θ in Work.Spaces.Iθ, v' θ) from by rw [hdecomp]; ring, h0]
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · linarith

/-- **The angular integration by parts for the `SmoothOpen` class.**  For `u` smooth on the
open quadrant and `Φ` a `z`-only weight, the `wip`-pairing of `D_θu` with `u` against
`Φ(z)sin(2θ)^{-q}` is `(q-1)` times the pairing of `u²` with `Φ(z)cos(2θ)sin(2θ)^{-q}`. -/
theorem wip_Dth_ibp {u : Fn} {Φ : ℝ → ℝ} {q : ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hint0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Φ z * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * Φ z
        * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Φ z * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => Φ z * (Real.sin (2 * θ)) ^ (-q)) (Work.Spaces.Dth u) u
      = (q - 1) * (∫ z in Work.Spaces.Iz, Φ z * ∫ θ in Work.Spaces.Iθ,
          Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) := by
  have hmeas : (MeasureTheory.volume.restrict (Work.Spaces.Iz : Set ℝ)).prod
      (MeasureTheory.volume.restrict (Work.Spaces.Iθ : Set ℝ))
      = MeasureTheory.volume.restrict ((Work.Spaces.Iz : Set ℝ) ×ˢ (Work.Spaces.Iθ : Set ℝ)) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
  have hI0 := hint0; rw [MeasureTheory.IntegrableOn, ← hmeas] at hI0
  have hI1 := hint1; rw [MeasureTheory.IntegrableOn, ← hmeas] at hI1
  have hI2 := hint2; rw [MeasureTheory.IntegrableOn, ← hmeas] at hI2
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have h : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
    rw [MeasureTheory.Measure.restrict_congr_set h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hslices : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => u z θ ^ 2 * Φ z * (Real.sin (2 * θ)) ^ (-q))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ∧ MeasureTheory.Integrable
          (fun θ => Work.Spaces.Dth u z θ * u z θ * Φ z * (Real.sin (2 * θ)) ^ (-q))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ∧ MeasureTheory.Integrable
          (fun θ => u z θ ^ 2 * Φ z * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 := hI0.prod_right_ae
    have h2 := hI1.prod_right_ae
    have h3 := hI2.prod_right_ae
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    exact ⟨hz1, hz2, hz3⟩
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.Dth u z θ * u z θ * (Φ z * (Real.sin (2 * θ)) ^ (-q)))
        = (q - 1) * (Φ z * ∫ θ in Work.Spaces.Iθ,
            Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) := by
    filter_upwards [hslices, hzpos] with z hz hzp
    obtain ⟨hz0, hz1, hz2⟩ := hz
    rcases eq_or_ne (Φ z) 0 with hΦ | hΦ
    · rw [hΦ]; simp
    · have hsub : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          HasDerivAt (fun θ' => u z θ') (deriv (fun θ' => u z θ') θ) θ := by
        intro θ hθ
        have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
          rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hzp, hθ.1, hθ.2⟩
        have hcd : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry u) (z, θ) :=
          hs.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
        exact (Work.Spaces.differentiableAt_curry_right
          (hcd.differentiableAt Work.FTS.LocData.smoothOrder_ne_zero)).hasDerivAt
      have hU : MeasureTheory.IntegrableOn (IbpU q (fun θ => u z θ)) Work.Spaces.Iθ := by
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Φ z * IbpU q (fun θ' => u z θ') θ) Work.Spaces.Iθ := by
          refine hz0.congr ?_
          filter_upwards with θ
          simp only [IbpU]; try ring
        refine (h1.const_mul ((Φ z)⁻¹)).congr ?_
        filter_upwards with θ
        simp only [IbpU]
        field_simp
      have hA : MeasureTheory.IntegrableOn (IbpA q (fun θ => u z θ)) Work.Spaces.Iθ := by
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Φ z * IbpA q (fun θ' => u z θ') θ) Work.Spaces.Iθ := by
          refine hz1.congr ?_
          filter_upwards with θ
          simp only [IbpA, Work.Spaces.Dth, Work.Spaces.pth]; try ring
        refine (h1.const_mul ((Φ z)⁻¹)).congr ?_
        filter_upwards with θ
        simp only [IbpA]
        field_simp
      have hE : MeasureTheory.IntegrableOn (IbpE q (fun θ => u z θ)) Work.Spaces.Iθ := by
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Φ z * IbpE q (fun θ' => u z θ') θ) Work.Spaces.Iθ := by
          refine hz2.congr ?_
          filter_upwards with θ
          simp only [IbpE]; try ring
        refine (h1.const_mul ((Φ z)⁻¹)).congr ?_
        filter_upwards with θ
        simp only [IbpE]
        field_simp
      have hkey := sliceIbp (q := q) hsub hU hA hE
      have hL : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Dth u z θ * u z θ * (Φ z * (Real.sin (2 * θ)) ^ (-q)))
          = Φ z * (∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => u z θ') θ) := by
        rw [show (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.Dth u z θ * u z θ * (Φ z * (Real.sin (2 * θ)) ^ (-q)))
            = (∫ θ in Work.Spaces.Iθ, Φ z * IbpA q (fun θ' => u z θ') θ) from by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          intro θ _
          simp only [IbpA, Work.Spaces.Dth, Work.Spaces.pth]
          ring]
        rw [MeasureTheory.integral_const_mul]
      rw [hL, hkey]
      simp only [IbpE]
      ring
  rw [Work.Coercivity.wip, MeasureTheory.integral_congr_ae hpt,
    MeasureTheory.integral_const_mul]

end Work.FTS.StrongPersist.H6Aux.R
end
end
