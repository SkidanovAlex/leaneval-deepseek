import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xSliceAgmon5
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceSupLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gDefs
import Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gInner
import Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gOuter
import Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gRad
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumB1FiveArith

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem npSinTwoNonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- **The remaining `a₁ = 0` summand: `(a,b,b₁) = (1,5,5)` (the highest pure-radial coefficient slot).**

The pairing is `∫∫ ρ · D_z⁵A · mixed 1 1 f · mixed 5 1 f`; it is the only configuration of the row with
`a₁ = 0` for which the coefficient slot has no pointwise price (`supSix` covers orders `≤ 4` only), while the
two `f`-slots have orders `2` and `6`.

Route (three-factor split; no pair of the three factors can carry the `γ`-weight alone, since the pure
`D_z⁵A`-slot only has the `η`-slot and `canonW (gam α) ≤ √(canonW q₁ · canonW q₂)` needs `q₁ + q₂ ≥ 2γ`
while the available slots give at most `η + γ < 2γ`):

1. `ρ ≤ canonW (gam α)` and `σ^{-(γ-η/2)} ≤ w²σ^{-γ}` (as `σ^{η/2} ≤ w²`), so on the open quadrant
   `ρ|X||F||G| ≤ (wσ^{-η/2}|X|)·w·(σ^{-(γ-η/2)}|F||G|)`;
2. Cauchy–Schwarz in `θ` for the two `f`-slots:
   `∫_θσ^{-(γ-η/2)}|F||G| ≤ √(∫_θσ^{-γ}F²)·√(∫_θσ^{-γ}G²) =: √(P(z)Q(z))` (split `γ-η/2 = q₁+q₂` with
   `2q₁, 2q₂ ≤ γ`);
3. Cauchy–Schwarz in `θ` for the first factor: `∫_θσ^{-η/2}|X| ≤ √(∫_θσ^{-η})·√(∫_θX²) ≤ C√(∫_θX²)`
   (`∫_θσ^{-η} < ∞` as `η < 1`);
4. Cauchy–Schwarz in `z` with `A(z) := √(∫_θX²)·√(P(z))`, `B(z) := √(Q(z))`:
   `∫_zw²AB ≤ √(∫_zw²A²)·√(∫_zw²B²)`, where
   `∫_zw²A² ≤ (sup_zP)·∫_zw²∫_θX² ≤ (C·HkSq α 4 f)·(HkSq α 6 A) ≤ C·M²·K6²` and
   `∫_zw²B² = ∫_zw²∫_θσ^{-γ}(mixed 5 1 f)² ≤ HkSq α 6 f` (`T6Coef/zProdIntLe` for the slot `(5,1)`).
   Hence `|∫| ≤ C α^{-1/2}M·K6·HkNorm α 6 f`.

The one new ingredient is the `z`-for-`θ` slice-sup `sup_z ∫_θσ^{-γ}(mixed 1 1 f z ·)² ≤ C·HkSq α 4 f`: the
`(i,j) = (1,1)` generalisation of the proved `T6Coef/vSliceSupLe` (the `(1,0)` case), by the same route
(`TransportS/SupDzAux/sda_HkSqSwap_open` + the `z`-Agmon for the pair of slots `(1,1)`/`(2,1)`, of order
`≤ 4`, e.g. `SixAux.zslice6_hardy`), together with `∫∫w²(D_z⁵A)² ≤ HkSq α 6 A` (`σ^{-η} ≥ 1`).

**Implementation note.**  The three factors are separated with the *same* `σ^{-γ}` weight as follows:
the leaf weight is compared with `leafGam α` (`ρ ≤ canonW (gam α) = leafGam α`), the pure slot `D_z⁵A` is
bounded by the `θ`-Agmon majorant `√(b1fiveMX α A z)` (`xSliceAgmon5`), the two `f`-slots by the angular
Cauchy–Schwarz `gamSliceCS11` together with the slice-sup `gamSliceSup11` (constant `3`), and the remaining
radial pair by the Cauchy–Schwarz `b1gRadCS`; the radial integrals are `xProdIntLe`, `zProdIntLe` and the
bookkeeping is `rowSumB1FiveArith`.  All the `mixed 1 1 f`-slice machinery is the already-proved
`H6Row6Gam`/`H6Row6` chain (`b1gSliceInt`, `b1gInner`, `b1gOuter`, `b1gRadCS`, `b1gMajInt`). -/
theorem rowSumB1Five : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.FTS.TransportS.IsLeafW α 1 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.DzIter 5 A p.1 p.2
          * Work.Spaces.mixed 1 1 f p.1 p.2
          * Work.Spaces.mixed 5 1 f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter 5 A p.1 p.2
            * Work.Spaces.mixed 1 1 f p.1 p.2
            * Work.Spaces.mixed 5 1 f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f := by
  refine ⟨100, by norm_num, ?_⟩
  intro α hα A f K0 K4 K6 K1 M ρ hCoef hThMem hThLe hDat hρ
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  -- ## basic nonnegativities
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hDat.bdd
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hCoef.n6
  have hNnn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  -- ## the integrand
  set F : ℝ × ℝ → ℝ := fun p => ρ p.1 p.2 * Work.Spaces.DzIter 5 A p.1 p.2
      * Work.Spaces.mixed 1 1 f p.1 p.2 * Work.Spaces.mixed 5 1 f p.1 p.2 with hF
  -- ## `ρ` is dominated by the leaf `γ`-weight on the open quadrant
  have hρle : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ ≤ Work.FTS.TransportS.leafGam α z θ := by
    intro z θ hz hθ hθ2
    have h := leafW_le_canonW_gam (α := α) hα0 hρ z θ hz hθ hθ2
    rwa [leafGam_eq_canonW]
  have hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ :=
    fun z θ => leafW_nonneg hρ z θ
  -- ## the pointwise domination `|F| ≤ |b1gF|` on the open quadrant
  have hptQ0 : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      |F p| ≤ |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have h1 : |F p| = ρ p.1 p.2 * |Work.Spaces.DzIter 5 A p.1 p.2|
        * |Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2| := by
      simp only [hF]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hρnn p.1 p.2 hz hθ0 hθ1)]
    have h2 : |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| =
        Work.FTS.TransportS.leafGam α p.1 p.2 * |Work.Spaces.DzIter 5 A p.1 p.2|
        * |Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2| := by
      rw [Work.FTS.StrongPersist.H6Row6.b1gF_apply, Work.Spaces.mixed_zero_right]
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (Work.FTS.TransportS.leafGam_nonneg α (npSinTwoNonneg hθ))]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hρle p.1 p.2 hz hθ0 hθ1) (abs_nonneg _)) (abs_nonneg _))
      (abs_nonneg _)
  -- ## the slicewise core for `b1gF` (the `mixed 1 1 f` middle slot)
  have hSliceInt := Work.FTS.StrongPersist.H6Row6.b1gSliceInt α A f hα0 hα1
    hCoef.sm hDat.sm hCoef.h6 hDat.h6
  have hinner := Work.FTS.StrongPersist.H6Row6.b1gInner α A f M hαI
    hCoef.sm hDat.sm hCoef.h6 hDat.h6 hDat.bdd
  have hIouter := Work.FTS.StrongPersist.H6Row6.b1gOuter α A f M hαI
    hCoef.sm hDat.sm hCoef.h6 hDat.h6 hDat.bdd
  have hIslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ => |Work.FTS.StrongPersist.H6Row6.b1gF α A f (0, θ)|)
          = fun _ => (0 : ℝ) := by
        funext θ
        rw [Work.FTS.StrongPersist.H6Row6.b1gF_apply, Work.Spaces.mixed_zero_right]
        simp only [Work.FTS.TransportS.leafGam, Work.Spaces.w]
        norm_num
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · exact hSliceInt z hpos
  have hcontF0 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.StrongPersist.H6Row6.b1gF α A f p)
      Work.FTS.EllipticEst.Q0 := by
    simp only [Work.FTS.StrongPersist.H6Row6.b1gF_apply]
    exact (((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hCoef.sm.mixed 5 0))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hDat.sm.mixed 1 1))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hDat.sm.mixed 5 1))
  have hI0aesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Work.FTS.StrongPersist.H6Row6.b1gF α A f p|) PM :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF0.abs
  obtain ⟨hF0abs_int, hF0abs_val⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|)
    (fun z θ => abs_nonneg _) hI0aesm hIslice hIouter
  -- ## the two radial integrals
  have hMXval := (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe α A hα0 hα1
    hCoef.sm hCoef.h6).2
  have hQval := (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe α f hα0 hα1
    hDat.sm hDat.h6).2
  have hcsz := Work.FTS.StrongPersist.H6Row6.b1gRadCS α A f hα0 hα1
    hCoef.sm hDat.sm hCoef.h6 hDat.h6
  have hMajInt := Work.FTS.StrongPersist.H6Row6.b1gMajInt α A f M hα0 hα1
    hCoef.sm hDat.sm hCoef.h6 hDat.h6 hMnn
  -- ## the arithmetic inputs
  have hSqA : Work.Spaces.HkSq α 6 A = (Work.Spaces.HkNorm α 6 A) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 A)]
  have hSqf : Work.Spaces.HkSq α 6 f = (Work.Spaces.HkNorm α 6 f) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
  have hcoefnn : 0 ≤ 4 / Real.pi + 200 / (Work.Spaces.gam α - 1) := by
    refine add_nonneg (by positivity) ?_
    refine div_nonneg (by norm_num) ?_
    rw [Work.Spaces.gam_sub_one]; positivity
  have hMXle : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * K6 ^ 2 := by
    refine le_trans (by
      simpa only [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply] using hMXval) ?_
    rw [hSqA]
    refine mul_le_mul_of_nonneg_left ?_ hcoefnn
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 A) hCoef.n6 2
  have hQle : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)
      ≤ (Work.Spaces.HkNorm α 6 f) ^ 2 := by
    refine le_trans (by
      simpa only [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply] using hQval) ?_
    rw [hSqf]
  -- ## the value bound on the `b1gF`-side
  have hval0 : (∫ z, (∫ θ, |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f := by
    have hstep1 : (∫ z, (∫ θ, |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        ≤ ∫ z, Real.sqrt 3 * M * ((Work.Spaces.w z
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
            * (Work.Spaces.w z
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.integral_mono_ae hIouter hMajInt hinner
    have hstep2 : (∫ z, Real.sqrt 3 * M * ((Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
          * (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = Real.sqrt 3 * M * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
          * (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))) :=
      MeasureTheory.integral_const_mul _ _
    have hstep3 : Real.sqrt 3 * M * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
          * (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)))
        ≤ Real.sqrt 3 * M * (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
            * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) :=
      mul_le_mul_of_nonneg_left hcsz (mul_nonneg (Real.sqrt_nonneg 3) hMnn)
    have hstep4 : Real.sqrt 3 * M * (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
            * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))
        ≤ 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f :=
      rowSumB1FiveArith hα0 hα1 hMnn hK6nn hNnn hMXle hQle
    exact hstep1.trans (hstep2.le.trans (hstep3.trans hstep4))
  -- ## a.e. strong measurability and integrability of `F`
  have hFaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p) PM := by
    simp only [hF]
    exact (((aesm_leafW hρ).mul (aesm_mixed hCoef.sm 5 0)).mul
      (aesm_mixed hDat.sm 1 1)).mul (aesm_mixed hDat.sm 5 1)
  have hptae : ∀ᵐ p ∂PM,
      |F p| ≤ |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| :=
    ae_of_forall_Qd (fun z θ hz hθ hθ2 =>
      hptQ0 (z, θ) (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩))
  have hFabs_aesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |F p|) PM :=
    continuous_abs.comp_aestronglyMeasurable hFaesm
  have hFabs_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => |F p|) PM := by
    refine hF0abs_int.mono' hFabs_aesm ?_
    filter_upwards [hptae] with p hp
    rw [Real.norm_eq_abs, abs_abs]
    exact hp
  have hF_int : MeasureTheory.Integrable F PM := by
    refine hFabs_int.mono' hFaesm ?_
    filter_upwards with p
    exact le_of_eq (by rw [Real.norm_eq_abs])
  have hle_abs : (∫ p, |F p| ∂PM)
      ≤ ∫ p, |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| ∂PM :=
    MeasureTheory.integral_mono_ae hFabs_int hF0abs_int hptae
  -- ## assembly
  refine ⟨hF_int, ?_⟩
  calc |∫ p, F p ∂PM|
      ≤ ∫ p, ‖F p‖ ∂PM := by
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm (μ := PM) F
    _ = ∫ p, |F p| ∂PM := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ p, |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| ∂PM := hle_abs
    _ = ∫ z, (∫ θ, |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := hF0abs_val
    _ ≤ 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f := hval0

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
