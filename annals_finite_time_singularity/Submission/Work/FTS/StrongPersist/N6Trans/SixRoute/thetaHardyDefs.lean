import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.EnergyGap
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.radGreen_modeEnergy_of_compactSupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

local notation "w" => Work.Spaces.w
local notation "a" => Work.FTS.PhiStar.Radial.radGreen

/-- **The two weighted `L²` slots of the mode-`m` Green function, from pointwise bounds.**

If `radGreen α m c` obeys a near-`0` bound `|a z| ≤ B z^d`, `|z a' z| ≤ B z^d` with `d > 3/2`
(on `0 < z ≤ 1`) and a far bound `|a z| ≤ C/z`, `|z a' z| ≤ C/z` (on `z ≥ 1`), then both
`(z a')² w²` and `a² w²` are integrable on `(0,∞)`.  Near `0` the weight contributes
`w² ≤ 16 z^{−4}`, so the integrands are dominated by `16 B² z^{2d−4}`, integrable because
`2d − 4 > −1`; far out `w² ≤ 16` and they are dominated by `16 C² z^{−2}`.  The two pieces are
glued at `z = 1` (a null point). -/
theorem radGreen_w2_slots_of_pointwise_bounds {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (fun z => a α m c z)
      (deriv (fun z => a α m c z) z) z)
    (hderiv2 : ∀ z : ℝ, 0 < z → HasDerivAt (deriv (fun z => a α m c z))
      (deriv (deriv (fun z => a α m c z)) z) z)
    (hnear : ∃ B d : ℝ, 0 ≤ B ∧ 3 / 2 < d ∧ ∀ z : ℝ, 0 < z → z ≤ 1 →
      |a α m c z| ≤ B * z ^ d ∧ |z * deriv (fun z' => a α m c z') z| ≤ B * z ^ d)
    (hfar : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z →
      |a α m c z| ≤ C / z ∧ |z * deriv (fun z' => a α m c z') z| ≤ C / z) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (z * deriv (fun z' => a α m c z') z) ^ 2
        * (w z) ^ 2) (Set.Ioi 0)
      ∧ MeasureTheory.IntegrableOn (fun z : ℝ => (a α m c z) ^ 2 * (w z) ^ 2) (Set.Ioi 0) := by
  obtain ⟨B, d, hBnn, _hd, hnb⟩ := hnear
  obtain ⟨C, _hCnn, hfb⟩ := hfar
  -- continuity of `deriv (radGreen α m c)` and of `radGreen α m c` on the open half-line
  have hdcont : ContinuousOn (deriv (fun z => a α m c z)) (Set.Ioi 0) :=
    fun z hz => (hderiv2 z hz).continuousAt.continuousWithinAt
  have hacont : ContinuousOn (fun z => a α m c z) (Set.Ioi 0) :=
    fun z hz => (hderiv z hz).continuousAt.continuousWithinAt
  -- continuity of `w²` on `(0,∞)`
  have hwcont : ContinuousOn (fun z : ℝ => (w z) ^ 2) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    refine (((continuous_const.add continuous_id).continuousOn.pow 2).div
      (continuous_id.continuousOn.pow 2) (fun z hz => ?_)).pow 2
    exact pow_ne_zero 2 (ne_of_gt hz)
  -- the near/far gluing: `(0,1) ∪ (1,∞)` is `(0,∞)` up to the null point `1`
  have glue : ∀ f : ℝ → ℝ, MeasureTheory.IntegrableOn f (Set.Ioo 0 1) →
      MeasureTheory.IntegrableOn f (Set.Ioi 1) → MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    intro f h1 h2
    have hA : MeasureTheory.IntegrableOn f (Set.Icc 0 1) :=
      h1.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
    have hB : MeasureTheory.IntegrableOn f (Set.Ici 1) :=
      h2.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have hU : MeasureTheory.IntegrableOn f (Set.Icc 0 1 ∪ Set.Ici 1) := hA.union hB
    have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ici 0 := by
      ext x
      simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
      constructor
      · rintro (⟨h1', _⟩ | h3) <;> linarith
      · intro h
        rcases le_or_gt x 1 with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'.le
    rw [hset] at hU
    exact hU.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici
  -- the near-`0` estimate, for any continuous `F` with `|F| ≤ B z^d`
  have near_of_bound : ∀ F : ℝ → ℝ, ContinuousOn F (Set.Ioo 0 1) →
      (∀ z : ℝ, 0 < z → z ≤ 1 → |F z| ≤ B * z ^ d) →
      MeasureTheory.IntegrableOn (fun z : ℝ => (F z) ^ 2 * (w z) ^ 2) (Set.Ioo 0 1) := by
    intro F hFc hFb
    have hpow : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (2 * d - 4)) (Set.Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (s := 2 * d - 4) (t := 1) one_pos).mpr
        (by linarith)
    have hdom : MeasureTheory.IntegrableOn (fun z : ℝ => (16 * B ^ 2) * z ^ (2 * d - 4))
        (Set.Ioo 0 1) := hpow.const_mul _
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact ((hFc.pow 2).mul (hwcont.mono (fun z hz => hz.1))).aestronglyMeasurable
        measurableSet_Ioo
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      have hz0 : 0 < z := hz.1
      have hz1 : z ≤ 1 := le_of_lt hz.2
      have hb := hFb z hz0 hz1
      have hsq : (F z) ^ 2 ≤ (B * z ^ d) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
        simpa only [sq_abs] using h
      have hBz : 0 ≤ B * z ^ d := mul_nonneg hBnn (Real.rpow_nonneg hz0.le _)
      have hw : (w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
        rw [Work.Spaces.w, div_pow]
        rw [show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring,
          show (z ^ 2) ^ 2 = z ^ 4 by ring]
      have hw16 : (w z) ^ 2 ≤ 16 / z ^ 4 := by
        rw [hw]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h2 : (1 + z) ^ 4 ≤ 2 ^ 4 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 4
        norm_num at h2
        exact h2
      have hsub : (z ^ d) ^ 2 / z ^ 4 = z ^ (2 * d - 4) := by
        rw [← Real.rpow_mul_natCast hz0.le d 2, ← Real.rpow_natCast z 4,
          ← Real.rpow_sub hz0]
        congr 1
        push_cast
        ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (F z) ^ 2 * (w z) ^ 2
          ≤ (B * z ^ d) ^ 2 * (16 / z ^ 4) :=
            mul_le_mul hsq hw16 (by positivity) (pow_nonneg hBz 2)
        _ = 16 * B ^ 2 * ((z ^ d) ^ 2 / z ^ 4) := by ring
        _ = 16 * B ^ 2 * z ^ (2 * d - 4) := by rw [hsub]
        _ = (16 * B ^ 2) * z ^ (2 * d - 4) := by ring
  -- the far estimate, for any continuous `F` with `|F| ≤ C / z` on `[1,∞)`
  have far_of_bound : ∀ F : ℝ → ℝ, ContinuousOn F (Set.Ioi 1) →
      (∀ z : ℝ, 1 ≤ z → |F z| ≤ C / z) →
      MeasureTheory.IntegrableOn (fun z : ℝ => (F z) ^ 2 * (w z) ^ 2) (Set.Ioi 1) := by
    intro F hFc hFb
    have hdom : MeasureTheory.IntegrableOn (fun z : ℝ => (16 * C ^ 2) * z ^ (-2 : ℝ))
        (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul _
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact ((hFc.pow 2).mul (hwcont.mono (fun z hz => by
        simp only [Set.mem_Ioi] at hz ⊢; linarith))).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz1 : 1 ≤ z := le_of_lt hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
      have hb := hFb z hz1
      have hsq : (F z) ^ 2 ≤ (C / z) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
        simpa only [sq_abs] using h
      have hw16 : (w z) ^ 2 ≤ 16 :=
        Work.FTS.EllExist.Honesty.w_sq_le_sixteen_of_one_le hz1
      have hzsq : (C / z) ^ 2 = C ^ 2 * z ^ (-2 : ℝ) := by
        rw [div_pow, div_eq_mul_inv, ← Real.rpow_natCast (z) 2, ← Real.rpow_neg hz0.le]
        norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (F z) ^ 2 * (w z) ^ 2 ≤ (C / z) ^ 2 * 16 :=
            mul_le_mul hsq hw16 (by positivity) (by positivity)
        _ = (16 * C ^ 2) * z ^ (-2 : ℝ) := by rw [hzsq]; ring
  refine ⟨glue _ (near_of_bound _ ?_ (fun z hz0 hz1 => (hnb z hz0 hz1).2)) ?_,
    glue _ (near_of_bound _ ?_ (fun z hz0 hz1 => (hnb z hz0 hz1).1)) ?_⟩
  · exact continuous_id.continuousOn.mul (hdcont.mono (fun z hz => hz.1))
  · exact far_of_bound _ (continuous_id.continuousOn.mul
      (hdcont.mono (fun z hz => by simp only [Set.mem_Ioi] at hz ⊢; linarith)))
      (fun z hz => (hfb z hz).2)
  · exact hacont.mono (fun z hz => hz.1)
  · exact far_of_bound _ (hacont.mono (fun z hz => by
      simp only [Set.mem_Ioi] at hz ⊢; linarith)) (fun z hz => (hfb z hz).1)


end Work.FTS.ClassC.HonestCut
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.nearRegionIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-- `Dth1Iter` of a function smooth on an open set is smooth there. -/
lemma contDiffOn_Dth1Iter_nri {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) :
    ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (Work.Elliptic.Dth1Iter m f) s := by
  intro m
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [Work.Elliptic.Dth1Iter_succ]
      change ContDiffOn ℝ (⊤ : ℕ∞)
        (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter m f) θ) s
      have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) s :=
        (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
      exact hsin.mul (contDiffOn_deriv_of_isOpen s hs ih)

/-- **Honesty of the `Wide` integrands at a variable level.**

`Work.FTS.H2.DivQ.W_integrable` proves the integrability of
`Wide α h l = x ↦ x^{2l-γ}(∂_x^{l+1}(sliceX h) x)²` on `(0,x₁)` for `1 ≤ l ≤ 4`, but it consumes
the honest angular data at *all* levels `1 ≤ m ≤ 4`.  For the region lemmas applied to the slices
`h_b = fun θ => DzIter b Φ z θ` (`b ≥ 1`) only the data with `m ≤ i = 4 - b` are available, so the
hypothesis must be weakened to the levels `1 ≤ m ≤ N` actually used.  The proof is that of
`W_integrable`: `Wide α h l ≤ Dom α h Cm l` pointwise (`Wide_le_Dom`), `Dom α h Cm l` is a
nonnegative combination of the `x`-pullbacks `SubEta`, `HonGam m` (`m ≤ l`) of the honest data,
hence integrable (`NRI.nrDom_integrable_le`, the level-parametric form of `dom_integrable`), and
`Wide` is continuous on `(0,x₁)` and nonnegative. -/
lemma wide_integrable_le_nri {α : ℝ} {h : ℝ → ℝ} (N : ℕ) (hN : N ≤ 4)
    (hα1 : α ≤ 1) (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hDenEta : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ)
    (hDenGam : ∀ m : ℕ, m ∈ Finset.Icc 1 N →
      MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    ∀ l : ℕ, 1 ≤ l → l ≤ N →
      MeasureTheory.IntegrableOn (Wide α h l) (Set.Ioc 0 xNear) := by
  intro l hl1 hlN
  obtain ⟨Cm, hCmnn, hCb, hC0⟩ := exists_Cm_aCoeffBnd
  have hEta : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) :=
    subEta_integrable hDenEta
  have hGam : ∀ m ∈ Finset.Icc 1 N,
      MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear) :=
    fun m hm => honGam_integrable (hDenGam m hm)
  have hDomInt : MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear) :=
    (NRI.nrDom_integrable_le N hEta hGam).1 l hlN
  have hle : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, Wide α h l x ≤ Dom α h Cm l x :=
    fun x hx => Wide_le_Dom hα1 hCmnn hsm hCb hC0 hl1 (le_trans hlN hN) hx
  have hcont : ContinuousOn (Wide α h l) (Set.Ioo (0 : ℝ) xNear) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul
      ((contDiffOn_iteratedDeriv_sliceX hsm (l + 1)).continuousOn.pow 2)
  have hIoo : MeasureTheory.IntegrableOn (Wide α h l) (Set.Ioo 0 xNear) := by
    refine Integrable.mono' hDomInt (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun x hx => by
      rw [Real.norm_of_nonneg (Wide_nonneg α h l (le_of_lt hx.1))]
      exact hle x hx)
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  exact hIoo

/-- **Honesty (integrability) of the left-hand integrand on the near region** (route:
`Submission/Work/FTS/H2/DivQ/NOTES.md` §9.1).

The per-slice conjunct of `HkMem` requires the left-hand integrand itself to be integrable — an
integral inequality alone does not certify that, since a non-integrable integrand silently gives
the junk value `0`.  For `0 < α ≤ 1`, `h` of class `C^∞` on `(0,π/2)` with `h(θ) → 0` at `0⁺`,
honest `∫_{Iθ}(∂_θh)² sin(2θ)^{-η}`, and honest `∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ}` for
`1 ≤ m ≤ i` (`η = 99/100`, `γ = 1+α/10`, `D_θ^m = Work.Elliptic.Dth1Iter m`), the integrand
`(D_θ^i (fun θ => h θ / sin(2θ)) θ)² sin(2θ)^{-γ}` is integrable on the near region
`(0, π/8]`.

ROUTE.  Substitute `x = sin 2θ`; by `DthIter_sliceX` (slice `fun θ => h θ/sin(2θ)`, whose `x`-form
is `f/x`, `f := sliceX h`) the near integrand is `(G^i(f/x))²x^{-γ}/(2κ)`.  `bCoeff_expansion`
gives `G^i(f/x) = Σ_{j=1}^{i} b i j x·x^j ∂_x^j(f/x)` (no `j = 0` term), so pointwise
Cauchy–Schwarz and `1/(2κ) ≤ 1/(2κ₁)` reduce to the *honesty* of
`A_j := ∫_0^{x₁}x^{2j-γ}(∂_x^j(f/x))²dx`.  Expand `∂_x^j(f/x) = Σ_{m≤j}c_{j,m}x^{m-j-1}f^{(m)}`
(Leibniz), so `x^{2j-γ}(∂_x^j(f/x))² ≤ C_jΣ_{m≤j}x^{2m-γ-2}(f^{(m)})²`; for `m ≥ 1` the honesty of
`x^{2m-γ-2}(f^{(m)})²` follows from `powerHardyBoundary` (`p = 2m-γ-2`) applied to `f^{(m)}`, whose
right-hand side `∫_0^{x₁}x^{2m-γ}(f^{(m+1)})²` is honest by `inversionNear` (its right-hand side is
honest) and whose boundary hypothesis `x^{2m-γ-1}(f^{(m)})² → 0` is `divSinPrimitive` with
`k = m-1`; the `m = 0` term `f²x^{-2-γ}` is `divSinPrimitive` with `k = 0` (`x·(f/x) = ∫_0^x∂_xf`,
using `f → 0`) together with the `η`-control `∫_0^{x₁}x^{4-γ}(∂_xf)² ≤ C∫x^{-η}(∂_xf)² ≤ C'Denη`.
The result transfers back to the `θ`-variable. -/
theorem nearRegionIntegrable (α : ℝ) (h : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hDenη : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 4)
    (hDenγ : ∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioc 0 (Real.pi / 8)) := by
  obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
  have hγneg : -1 < Work.Spaces.gam α := by linarith [Work.Spaces.one_lt_gam hα]
  -- the quotient slice and its `x`-form
  have hsm_div : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h θ / Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine hsm.div (contDiffOn_const.mul contDiffOn_id).sin ?_
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hquot : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => sliceX h x / x) (Set.Ioo 0 xNear) :=
    (contDiffOn_sliceX_Ioo_nr hsm).div contDiffOn_id (fun x hx => ne_of_gt hx.1)
  -- the honest data at the levels actually needed
  have hWide : ∀ l : ℕ, 1 ≤ l → l ≤ i →
      MeasureTheory.IntegrableOn (Wide α h l) (Set.Ioc 0 xNear) :=
    wide_integrable_le_nri i hi4 hα1 hsm hDenη (fun m hm => hDenγ m hm)
  obtain ⟨CH, hCHpos, hH⟩ := hardyA_le_W
  have hAint : ∀ k : ℕ, 1 ≤ k → k ≤ i → MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        * (iteratedDeriv k (fun y : ℝ => sliceX h y / y) x) ^ 2) (Set.Ioc 0 xNear) := by
    intro k hk1 hki
    exact (hH k (Work.Spaces.gam α) xNear xNear_pos hγneg (sliceX h)
      (contDiffOn_sliceX_Ioc_nr hsm) (tendsto_sliceX_nr h0) (hWide k hk1 hki)).1
  -- a uniform bound on the coefficients `bCoeff i j`, `j ≤ i`
  obtain ⟨B₁, hB₁nn, hb₁⟩ := (aCoeff_bounds 1).1
  obtain ⟨B₂, hB₂nn, hb₂⟩ := (aCoeff_bounds 2).1
  obtain ⟨B₃, hB₃nn, hb₃⟩ := (aCoeff_bounds 3).1
  obtain ⟨B₄, hB₄nn, hb₄⟩ := (aCoeff_bounds 4).1
  set B : ℝ := max B₁ (max B₂ (max B₃ B₄)) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; exact le_trans hB₁nn (le_max_left _ _)
  have hbB : ∀ j ≤ i, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |bCoeff i j x| ≤ B := by
    intro j hj x hx
    have h1 : B₁ ≤ B := by rw [hBdef]; exact le_max_left _ _
    have h2 : B₂ ≤ B := by
      rw [hBdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : B₃ ≤ B := by
      rw [hBdef]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have h4 : B₄ ≤ B := by
      rw [hBdef]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    interval_cases i
    · exact le_trans (hb₁ j hj x hx) h1
    · exact le_trans (hb₂ j hj x hx) h2
    · exact le_trans (hb₃ j hj x hx) h3
    · exact le_trans (hb₄ j hj x hx) h4
  -- the dominating function on the `x`-side
  set P : ℝ → ℝ := fun x => (i : ℝ) * B ^ 2 * ∑ j ∈ Finset.range i,
      x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 with hPdef
  -- the `x`-side integrand
  set K : ℝ → ℝ := fun x =>
      (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) with hKdef
  -- integrability of the dominating function
  have hPint : MeasureTheory.IntegrableOn P (Set.Ioc (0 : ℝ) xNear) := by
    have hSumInt : MeasureTheory.IntegrableOn (fun x : ℝ => ∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)
        (Set.Ioc (0 : ℝ) xNear) :=
      MeasureTheory.integrable_finsetSum _ (fun j hj => by
        have hjlt : j < i := Finset.mem_range.mp hj
        exact hAint (j + 1) (by omega) (by omega))
    have hPeq : P = fun x : ℝ => ((i : ℝ) * B ^ 2) * (∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      rw [hPdef]
    rw [hPeq]
    exact hSumInt.const_mul _
  -- continuity and nonnegativity of the `x`-side integrand
  have hKcont : ContinuousOn K (Set.Ioo (0 : ℝ) xNear) := by
    have hDth : ContinuousOn (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_Dth1Iter_nri isOpen_Ioo hsm_div i).continuousOn
    have hcomp : ContinuousOn (fun x : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2)
        (Set.Ioo (0 : ℝ) xNear) :=
      (hDth.comp (Real.continuous_arcsin.div_const 2).continuousOn
        (fun x hx => thetaOf_mem_Ioo hx)).pow 2
    have hk : ContinuousOn (fun x : ℝ => 1 / (2 * kappa x)) (Set.Ioo (0 : ℝ) xNear) :=
      continuousOn_const.div (continuousOn_const.mul contDiffOn_kappa_b.continuousOn)
        (fun x hx => by
          have hkpos : 0 < kappa x := kappa_pos_of_mem ⟨hx.1.le, hx.2.le⟩
          positivity)
    have hmono : ContinuousOn (fun x : ℝ => x ^ (-(Work.Spaces.gam α)))
        (Set.Ioo (0 : ℝ) xNear) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
    have h4 : ContinuousOn (fun x : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
          * x ^ (-(Work.Spaces.gam α))) (Set.Ioo (0 : ℝ) xNear) := hcomp.mul hmono
    have h5 : ContinuousOn (fun x : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) (Set.Ioo (0 : ℝ) xNear) :=
      h4.mul hk
    exact h5
  have hKnonneg : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, 0 ≤ K x := by
    intro x hx
    have hkpos : 0 < kappa x := kappa_pos_of_mem ⟨hx.1.le, hx.2.le⟩
    have h1 : (0 : ℝ) ≤ (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ))
        (thetaOf x)) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ x ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hx.1.le _
    have h3 : (0 : ℝ) ≤ 1 / (2 * kappa x) := div_nonneg zero_le_one (by linarith)
    rw [hKdef]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  -- the pointwise domination `K ≤ P` on `(0,x₁)`
  have hKle : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, K x ≤ P x := by
    intro x hx
    have hpos : (0 : ℝ) < x := hx.1
    have hxIcc : x ∈ Set.Icc (0 : ℝ) xNear := ⟨hx.1.le, hx.2.le⟩
    have hk1 : (1 : ℝ) ≤ 2 * kappa x := two_kappa_ge_one_nr x hxIcc
    have hknn : (0 : ℝ) ≤ 2 * kappa x := le_trans zero_le_one hk1
    have hident : Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)
        = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x :=
      (DthIter_sliceX i hsm_div hx).trans
        (Gop_iter_eqOn_nr i isOpen_Ioo (sliceX_divSin_eqOn_nr h) hx)
    have hKw : K x = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
      change (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      rw [hident]
    rw [hKw]
    have h0c : bCoeff i 0 = fun _ => (0 : ℝ) := bCoeff_zero_of_pos_nr i hi1
    have he : (Gop^[i] (fun y : ℝ => sliceX h y / y)) x
        = ∑ j ∈ Finset.range i, bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) := by
      rw [bCoeff_expansion i hquot hx, Finset.sum_range_succ']
      rw [show bCoeff i 0 x
            * (x ^ 0 * iteratedDeriv 0 (fun y : ℝ => sliceX h y / y) x) = 0 by
        rw [h0c]
        simp]
      rw [add_zero]
    have hcs : ((Gop^[i] (fun y : ℝ => sliceX h y / y)) x) ^ 2
        ≤ (i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2 := by
      rw [he]
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range i)
        (f := fun j : ℕ => bCoeff i (j + 1) x
          * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x))
      simpa using h
    have hterm : ∀ j ∈ Finset.range i,
        (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α))
        ≤ B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      intro j hj
      have hj1 : j + 1 ≤ i := by have := Finset.mem_range.mp hj; omega
      have hb : |bCoeff i (j + 1) x| ≤ B := hbB (j + 1) hj1 x hxIcc
      have hb2 : (bCoeff i (j + 1) x) ^ 2 ≤ B ^ 2 := by
        rw [show (bCoeff i (j + 1) x) ^ 2 = |bCoeff i (j + 1) x| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have hxsq : x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          = ((x ^ (j + 1)) ^ 2) * x ^ (-(Work.Spaces.gam α)) := by
        rw [show 2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α
              = 2 * (((j + 1 : ℕ) : ℝ)) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hpos]
        congr 1
        rw [show 2 * (((j + 1 : ℕ) : ℝ)) = ((2 * (j + 1) : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        rw [pow_mul]
        ring
      rw [show (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
            * x ^ (-(Work.Spaces.gam α))
          = (bCoeff i (j + 1) x) ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 from by ring]
      have hnn : (0 : ℝ) ≤ (x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)) :=
        mul_nonneg (pow_nonneg (pow_nonneg hpos.le (j + 1)) 2) (Real.rpow_nonneg hpos.le _)
      have hnn2 : (0 : ℝ) ≤ (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 :=
        sq_nonneg _
      calc (bCoeff i (j + 1) x) ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2
          ≤ B ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb2 hnn) hnn2
        _ = B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
            rw [← hxsq]; ring
    have hstep1 : (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        ≤ ((i : ℝ) * ∑ j ∈ Finset.range i,
          (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcs (Real.rpow_nonneg hpos.le _))
        (div_nonneg zero_le_one hknn)
    have hinv : 1 / (2 * kappa x) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < 2 * kappa x)]
      linarith
    have hstep2 : ((i : ℝ) * ∑ j ∈ Finset.range i,
          (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) ≤ P x := by
      have h1 : ((i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
          ≤ ((i : ℝ) * ∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
            * x ^ (-(Work.Spaces.gam α)) * 1 :=
        mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
            (Real.rpow_nonneg hpos.le _))
      refine h1.trans ?_
      rw [mul_one]
      have hPeq : P x = (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
          x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by rw [hPdef]
      rw [hPeq]
      have h2 : ((i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
          * x ^ (-(Work.Spaces.gam α))
          = (i : ℝ) * ∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)) := by
        rw [mul_assoc, Finset.sum_mul]
      rw [h2]
      have h3 : (∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)))
          ≤ ∑ j ∈ Finset.range i, B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) :=
        Finset.sum_le_sum (fun j hj => hterm j hj)
      calc (i : ℝ) * (∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)))
          ≤ (i : ℝ) * (∑ j ∈ Finset.range i,
              B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
                * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
              x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
                * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
            rw [← Finset.mul_sum]
            ring
    exact hstep1.trans hstep2
  -- integrability of `K` on `(0,x₁]`
  have hKint : MeasureTheory.IntegrableOn K (Set.Ioc (0 : ℝ) xNear) := by
    have hIoo : MeasureTheory.IntegrableOn K (Set.Ioo (0 : ℝ) xNear) := by
      have hPintIoo : MeasureTheory.IntegrableOn P (Set.Ioo (0 : ℝ) xNear) :=
        hPint.mono_set Set.Ioo_subset_Ioc_self
      refine Integrable.mono' hPintIoo (hKcont.aestronglyMeasurable measurableSet_Ioo) ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall (fun x hx => by
        rw [Real.norm_of_nonneg (hKnonneg x hx)]
        exact hKle x hx)
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIoo
  -- the `x`-side integrand of the change of variables, and the change of variables itself
  have hKs : MeasureTheory.IntegrableOn (fun x : ℝ => ((fun θ : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ∘ thetaOf) x * (1 / (2 * kappa x)))
      (Set.Ioc (0 : ℝ) xNear) := by
    refine hKint.congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hs : Real.sin (2 * thetaOf x) = x :=
      sin_two_thetaOf_Icc_nr x ⟨hx.1.le, hx.2⟩
    simp only [hKdef, Function.comp_apply, hs]
  have hIntComp : IntervalIntegrable (fun x : ℝ => ((fun θ : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ∘ thetaOf) x * (1 / (2 * kappa x)))
      volume 0 xNear := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le xNear_pos.le]
    exact hKs
  have hcθ : ContinuousOn thetaOf (Set.uIcc (0 : ℝ) xNear) :=
    (Real.continuous_arcsin.div_const 2).continuousOn
  have hdθ : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
    intro x hx
    rw [min_eq_left xNear_pos.le, max_eq_right xNear_pos.le] at hx
    exact hasDerivAt_thetaOf_nr ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  have hkθ : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      0 ≤ 1 / (2 * kappa x) := by
    intro x hx
    rw [min_eq_left xNear_pos.le, max_eq_right xNear_pos.le] at hx
    have hkpos : 0 < kappa x := kappa_pos_of_mem ⟨hx.1.le, hx.2.le⟩
    positivity
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := xNear) (f := thetaOf) (f' := fun x : ℝ => 1 / (2 * kappa x))
    (g := fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) hcθ hdθ hkθ
  have hF : IntervalIntegrable (fun θ : ℝ =>
      (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) volume 0 (Real.pi / 8) := by
    have h := hiff.mp hIntComp
    rwa [thetaOf_zero_nr, thetaOf_xNear_nr] at h
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 8)] at hF
  exact hF

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.nearRegionLHS_i =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## Auxiliary facts about `thetaOf`, `sliceX` and `Gop`

These are (copies of) the *private*, hence unreachable, helpers of
`Submission/Work/FTS/H2/DivQ/nearRegionLHS.lean`, re-proved here so that its assembly can be
re-run with the variable-level data hypothesis: the only structural input that changes is the
provider of the `x`-side Hardy bound, which at level `i` is
`Work.FTS.H2.DivQ.NRI.W_integrable_le i` (data at levels `≤ i`) instead of
`Work.FTS.H2.DivQ.W_integrable` (data at levels `≤ 4`). -/

private lemma nri_contDiffOn_thetaOf :
    ContDiffOn ℝ (⊤ : ℕ∞) thetaOf (Set.Ioo (-1 : ℝ) 1) := by
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ ({-1, 1} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) Real.arcsin (Set.Ioo (-1 : ℝ) 1) :=
    (Real.contDiffOn_arcsin (n := (⊤ : ℕ∞))).mono hsub
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.arcsin x / 2) (Set.Ioo (-1 : ℝ) 1) :=
    h1.div_const 2
  exact h2

private lemma nri_sin_two_thetaOf_Icc :
    ∀ x ∈ Set.Icc (0 : ℝ) xNear, Real.sin (2 * thetaOf x) = x := by
  intro x hx
  exact sin_two_thetaOf ⟨by linarith [hx.1], by linarith [hx.2, xNear_le_one]⟩

private lemma nri_contDiffOn_sliceX_Ioc {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioc 0 xNear) := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => h (thetaOf x)) (Set.Ioc 0 xNear)
  refine hsm.comp (nri_contDiffOn_thetaOf.mono ?_) ?_
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [thetaOf]
      exact div_pos (Real.arcsin_pos.mpr hx.1) (by norm_num)
    · rw [thetaOf]
      have h := (Real.arcsin_lt_pi_div_two).mpr (by linarith [hx.2, xNear_lt])
      linarith [h, Real.pi_pos]

private lemma nri_tendsto_sliceX {h : ℝ → ℝ}
    (hh : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (sliceX h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h1 : Filter.Tendsto thetaOf (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt thetaOf (0 : ℝ) := (Real.continuous_arcsin.div_const 2).continuousAt
      have hct := hc.tendsto
      simp only [thetaOf_zero] at hct
      exact hct.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      rw [thetaOf]
      exact div_pos (Real.arcsin_pos.mpr hx) (by norm_num)
  exact hh.comp h1

private lemma nri_Gop_congr_eqOn {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : Set.EqOn u v s) : Set.EqOn (Gop u) (Gop v) s := by
  intro x hx
  have hev : u =ᶠ[nhds x] v := Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hx, h⟩
  simp only [Gop]
  rw [hev.deriv_eq]

private lemma nri_Gop_iter_eqOn (i : ℕ) {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : Set.EqOn u v s) : Set.EqOn ((Gop^[i]) u) ((Gop^[i]) v) s := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact nri_Gop_congr_eqOn hs ih hx

private lemma nri_sliceX_divSin_eqOn (h : ℝ → ℝ) :
    Set.EqOn (sliceX (fun θ : ℝ => h θ / Real.sin (2 * θ)))
      (fun x : ℝ => sliceX h x / x) (Set.Ioo 0 xNear) := by
  intro x hx
  have hxI : x ∈ Set.Icc (0 : ℝ) xNear := ⟨hx.1.le, hx.2.le⟩
  change h (thetaOf x) / Real.sin (2 * thetaOf x) = h (thetaOf x) / x
  rw [nri_sin_two_thetaOf_Icc x hxI]

private lemma nri_bCoeff_zero_of_pos : ∀ i : ℕ, 1 ≤ i → bCoeff i 0 = fun _ => (0 : ℝ) := by
  have key : ∀ k : ℕ, genCoeff (fun _ : ℝ => 1) (k + 1) 0 = fun _ => (0 : ℝ) := by
    intro k
    induction k with
    | zero =>
        rw [genCoeff_succ_zero, genCoeff_init_zero]
        funext x
        simp
    | succ k ih =>
        rw [genCoeff_succ_zero, ih]
        funext x
        simp
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [bCoeff_eq_genCoeff]
  exact key k

/-! ## The variable-level data provider

The `x`-side Hardy bound used by the assembly is `Work.FTS.H2.DivQ.NRI.W_integrable_le`: for
**every** level `1 ≤ m ≤ N ≤ 4`, with the honest angular data given only at the levels `1 ≤ m ≤ N`,
it bounds `∫_0^{x₁} x^{2m-γ}(∂_x^{m+1}(sliceX h))²` by `C · nrSS α h m`.  A single constant
serving all four levels is obtained from the four instances (`N = 1,2,3,4`) by taking a maximum;
`nearRegionLHS_i_of_inversion` isolates the body of the assembly, which consumes the provider only
through its level-`i` instance. -/

/-- **The assembly of `nearRegionLHS_i` from the variable-level Hardy bound.**

This is the proof body of `nearRegionLHS` with `W_integrable` replaced by a provider `hW` that is
available at every level `N ≤ 4` with the data only at levels `≤ N`. -/
theorem nearRegionLHS_i_of_inversion
    (hW : ∃ CW : ℝ, 0 < CW ∧ ∀ (N : ℕ), N ≤ 4 → ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ →
      (∀ m : ℕ, m ∈ Finset.Icc 1 N →
        MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) →
      ∀ m : ℕ, m ∈ Finset.Icc 1 N →
        MeasureTheory.IntegrableOn
          (fun x : ℝ => x ^ (2 * (m : ℝ) - Work.Spaces.gam α)
            * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2) (Set.Ioc 0 xNear) ∧
        (∫ x in (0 : ℝ)..xNear, x ^ (2 * (m : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2)
          ≤ CW * NRI.nrSS α h m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        (∫ θ in (0 : ℝ)..(Real.pi / 8),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨CW, hCWpos, hWall⟩ := hW
  obtain ⟨CH, hCHpos, hH⟩ := hardyA_le_W
  obtain ⟨B₁, hB₁nn, hb₁⟩ := (aCoeff_bounds 1).1
  obtain ⟨B₂, hB₂nn, hb₂⟩ := (aCoeff_bounds 2).1
  obtain ⟨B₃, hB₃nn, hb₃⟩ := (aCoeff_bounds 3).1
  obtain ⟨B₄, hB₄nn, hb₄⟩ := (aCoeff_bounds 4).1
  refine ⟨(16 * (max B₁ (max B₂ (max B₃ B₄))) ^ 2 + 1) * CH * CW, by positivity, ?_⟩
  intro α h hα0 hα1 hsm h0h hDenη i hi hDenγ
  obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
  have hgam_pos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα0
  have hgam_neg : -1 < Work.Spaces.gam α := by linarith [Work.Spaces.one_lt_gam hα0]
  -- the bound on the `bCoeff` coefficients
  set B : ℝ := max B₁ (max B₂ (max B₃ B₄)) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; exact le_trans hB₁nn (le_max_left _ _)
  have hbB : ∀ j ≤ i, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |bCoeff i j x| ≤ B := by
    intro j hj x hx
    have h1 : B₁ ≤ B := by rw [hBdef]; exact le_max_left _ _
    have h2 : B₂ ≤ B := by
      rw [hBdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : B₃ ≤ B := by
      rw [hBdef]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have h4 : B₄ ≤ B := by
      rw [hBdef]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    interval_cases i
    · exact le_trans (hb₁ j hj x hx) h1
    · exact le_trans (hb₂ j hj x hx) h2
    · exact le_trans (hb₃ j hj x hx) h3
    · exact le_trans (hb₄ j hj x hx) h4
  -- the data functional, in the variable-level form `nrSS α h i`
  set data : ℕ → ℝ := NRI.nrSS α h with hdatadef
  have hdata_mono : ∀ m ≤ i, data m ≤ data i := by
    intro m hm
    rw [hdatadef]
    exact NRI.nrSS_mono α h hm
  have hdata_nonneg : 0 ≤ data i := by
    rw [hdatadef]
    exact NRI.nrSS_nonneg α h i
  have hdata_raw : data i
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [hdatadef]
    exact NRI.nrSS_eq α h i
  -- smoothness of the quotient slice `h/sin(2θ)` and of `(sliceX h)/x`
  have hsm_div : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h θ / Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine hsm.div (contDiffOn_const.mul contDiffOn_id).sin ?_
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hquot : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => sliceX h x / x) (Set.Ioo 0 xNear) :=
    (contDiffOn_sliceX hsm).div contDiffOn_id (fun x hx => ne_of_gt hx.1)
  -- the change of variables `θ = thetaOf x`
  have hcont_th : ContinuousOn thetaOf (Set.uIcc (0 : ℝ) xNear) :=
    (Real.continuous_arcsin.div_const 2).continuousOn
  have hderiv_th : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
    intro x hx
    rw [min_eq_left xNear_pos.le, max_eq_right xNear_pos.le] at hx
    exact hasDerivAt_thetaOf' ⟨by linarith [hx.1], by linarith [hx.2, xNear_le_one]⟩
  have hnn_th : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      0 ≤ 1 / (2 * kappa x) := by
    intro x hx
    rw [min_eq_left xNear_pos.le, max_eq_right xNear_pos.le] at hx
    have hk : 0 ≤ 2 * kappa x := by rw [kappa_eq_sqrt]; positivity
    exact div_nonneg zero_le_one hk
  have hcv := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := (0 : ℝ))
    (b := xNear) (f := thetaOf) (f' := fun x : ℝ => 1 / (2 * kappa x))
    (g := fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
    hcont_th hderiv_th hnn_th
  rw [thetaOf_zero, thetaOf_xNear] at hcv
  -- the `x`-side integrand `Hx`
  set Hx : ℝ → ℝ := fun x => (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
    * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) with hHxdef
  -- the dominating function `P`
  set P : ℝ → ℝ := fun x => (i : ℝ) * B ^ 2 * ∑ j ∈ Finset.range i,
    x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
      * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 with hPdef
  -- pointwise domination
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, Hx x ≤ P x := by
    intro x hx
    have hpos : (0 : ℝ) < x := hx.1
    have hxIcc : x ∈ Set.Icc (0 : ℝ) xNear := ⟨hx.1.le, hx.2.le⟩
    have hk1 : (1 : ℝ) ≤ 2 * kappa x := two_kappa_ge_one hxIcc
    have hknn : (0 : ℝ) ≤ 2 * kappa x := le_trans zero_le_one hk1
    have h0c : bCoeff i 0 = fun _ => (0 : ℝ) := nri_bCoeff_zero_of_pos i hi1
    have he : (Gop^[i] (fun y : ℝ => sliceX h y / y)) x
        = ∑ j ∈ Finset.range i, bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) := by
      rw [bCoeff_expansion i hquot hx, Finset.sum_range_succ']
      rw [show bCoeff i 0 x
            * (x ^ 0 * iteratedDeriv 0 (fun y : ℝ => sliceX h y / y) x) = 0 by
        rw [h0c]
        simp]
      rw [add_zero]
    have hcs : ((Gop^[i] (fun y : ℝ => sliceX h y / y)) x) ^ 2
        ≤ (i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2 := by
      rw [he]
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range i)
        (f := fun j : ℕ => bCoeff i (j + 1) x
          * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x))
      simpa using h
    have hterm : ∀ j ∈ Finset.range i,
        (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α))
        ≤ B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      intro j hj
      have hj1 : j + 1 ≤ i := by have := Finset.mem_range.mp hj; omega
      have hb : |bCoeff i (j + 1) x| ≤ B := hbB (j + 1) hj1 x hxIcc
      have hb2 : (bCoeff i (j + 1) x) ^ 2 ≤ B ^ 2 := by
        rw [show (bCoeff i (j + 1) x) ^ 2 = |bCoeff i (j + 1) x| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have hxsq : x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          = ((x ^ (j + 1)) ^ 2) * x ^ (-(Work.Spaces.gam α)) := by
        rw [show 2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α
              = 2 * (((j + 1 : ℕ) : ℝ)) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hpos]
        congr 1
        rw [show 2 * (((j + 1 : ℕ) : ℝ)) = ((2 * (j + 1) : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        rw [pow_mul]
        ring
      rw [show (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
            * x ^ (-(Work.Spaces.gam α))
          = (bCoeff i (j + 1) x) ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 from by ring]
      have hnn : (0 : ℝ) ≤ (x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)) :=
        mul_nonneg (pow_nonneg (pow_nonneg hpos.le (j + 1)) 2) (Real.rpow_nonneg hpos.le _)
      have hnn2 : (0 : ℝ) ≤ (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 :=
        sq_nonneg _
      calc (bCoeff i (j + 1) x) ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2
          ≤ B ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb2 hnn) hnn2
        _ = B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
            rw [← hxsq]; ring
    have hstep1 : Hx x ≤ ((i : ℝ) * ∑ j ∈ Finset.range i,
          (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcs (Real.rpow_nonneg hpos.le _))
        (div_nonneg zero_le_one hknn)
    have hinv : 1 / (2 * kappa x) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < 2 * kappa x)]
      linarith
    have hstep2 : ((i : ℝ) * ∑ j ∈ Finset.range i,
          (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) ≤ P x := by
      have h1 : ((i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
          ≤ ((i : ℝ) * ∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
            * x ^ (-(Work.Spaces.gam α)) * 1 :=
        mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
            (Real.rpow_nonneg hpos.le _))
      refine h1.trans ?_
      rw [mul_one]
      have hPeq : P x = (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
          x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by rw [hPdef]
      rw [hPeq]
      have h2 : ((i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
          * x ^ (-(Work.Spaces.gam α))
          = (i : ℝ) * ∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)) := by
        rw [mul_assoc, Finset.sum_mul]
      rw [h2]
      have h3 : (∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)))
          ≤ ∑ j ∈ Finset.range i, B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) :=
        Finset.sum_le_sum (fun j hj => hterm j hj)
      calc (i : ℝ) * (∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)))
          ≤ (i : ℝ) * (∑ j ∈ Finset.range i,
              B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
                * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
              x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
                * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
            rw [← Finset.mul_sum]
            ring
    exact hstep1.trans hstep2
  -- the `A_j`-type and `W_j`-type integrability and bounds
  have hWint : ∀ j ∈ Finset.range i, MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2) (Set.Ioc (0 : ℝ) xNear) := by
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    have hjmem : j + 1 ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (hWall i hi4 α h hα0 hα1 hsm hDenη hDenγ (j + 1) hjmem).1
  have hWbnd : ∀ j ∈ Finset.range i,
      (∫ x in (0 : ℝ)..xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2) ≤ CW * data i := by
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    have hjle : j + 1 ≤ i := by omega
    have hjmem : j + 1 ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨by omega, hjle⟩
    refine ((hWall i hi4 α h hα0 hα1 hsm hDenη hDenγ (j + 1) hjmem).2).trans ?_
    have hSS : NRI.nrSS α h (j + 1) ≤ data i := by
      rw [hdatadef]
      exact NRI.nrSS_mono α h hjle
    exact mul_le_mul_of_nonneg_left hSS (le_of_lt hCWpos)
  have hAint : ∀ j ∈ Finset.range i, MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)
      (Set.Ioc (0 : ℝ) xNear) := by
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    exact (hH (j + 1) (Work.Spaces.gam α) xNear xNear_pos hgam_neg (sliceX h)
      (nri_contDiffOn_sliceX_Ioc hsm) (nri_tendsto_sliceX h0h) (hWint j hj)).1
  have hAbnd : ∀ j ∈ Finset.range i,
      (∫ x in (0 : ℝ)..xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) ≤ CH * CW * data i := by
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    refine ((hH (j + 1) (Work.Spaces.gam α) xNear xNear_pos hgam_neg (sliceX h)
      (nri_contDiffOn_sliceX_Ioc hsm) (nri_tendsto_sliceX h0h) (hWint j hj)).2).trans ?_
    have hCHle : CH / (1 + Work.Spaces.gam α) ^ 2 ≤ CH := by
      have hγ1 : (1 : ℝ) < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
      have h1 : (1 : ℝ) ≤ (1 + Work.Spaces.gam α) ^ 2 := by nlinarith
      have h2 : (0 : ℝ) < (1 + Work.Spaces.gam α) ^ 2 := by linarith
      rw [div_le_iff₀ h2]
      calc CH = CH * 1 := (mul_one CH).symm
        _ ≤ CH * (1 + Work.Spaces.gam α) ^ 2 := mul_le_mul_of_nonneg_left h1 hCHpos.le
    have hWnn : (0 : ℝ) ≤ ∫ x in (0 : ℝ)..xNear,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2 := by
      rw [intervalIntegral.integral_of_le xNear_pos.le]
      refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc ?_
      intro x hx
      exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg _)
    calc CH / (1 + Work.Spaces.gam α) ^ 2
            * (∫ x in (0 : ℝ)..xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2)
        ≤ CH * (∫ x in (0 : ℝ)..xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2) :=
          mul_le_mul_of_nonneg_right hCHle hWnn
      _ ≤ CH * (CW * data i) := mul_le_mul_of_nonneg_left (hWbnd j hj) (le_of_lt hCHpos)
      _ = CH * CW * data i := by ring
  -- integrability of `P`
  have hPint : MeasureTheory.IntegrableOn P (Set.Ioc (0 : ℝ) xNear) := by
    have hSumInt : MeasureTheory.IntegrableOn (fun x : ℝ => ∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)
        (Set.Ioc (0 : ℝ) xNear) :=
      MeasureTheory.integrable_finsetSum _ (fun j hj => hAint j hj)
    have hconst := hSumInt.const_mul ((i : ℝ) * B ^ 2)
    have hPeq : P = fun x : ℝ => ((i : ℝ) * B ^ 2) * (∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      rw [hPdef]
    rw [hPeq]
    exact hconst
  -- the comparison `∫ Hx ≤ ∫ P`
  have hHxnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) xNear)] Hx := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    have hk : (0 : ℝ) ≤ 1 / (2 * kappa x) := by
      have h2 : 0 ≤ 2 * kappa x := by rw [kappa_eq_sqrt]; positivity
      exact div_nonneg zero_le_one h2
    have hHxunfold : Hx x = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := rfl
    rw [hHxunfold]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)) hk
  have hHxle : Hx ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) xNear)] P := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ xNear := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hnull] with x hne
    intro hx
    exact hpt x ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
  have hmono : ∫ x in Set.Ioc (0 : ℝ) xNear, Hx x
      ≤ ∫ x in Set.Ioc (0 : ℝ) xNear, P x :=
    integral_mono_of_nonneg hHxnn hPint hHxle
  -- value of `∫ P`
  have hPval : (∫ x in Set.Ioc (0 : ℝ) xNear, P x)
      = (i : ℝ) * B ^ 2 * ∑ j ∈ Finset.range i,
          (∫ x in Set.Ioc (0 : ℝ) xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
    have hPeq : P = fun x : ℝ => ((i : ℝ) * B ^ 2) * (∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      rw [hPdef]
    rw [hPeq, MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finsetSum _ (fun j hj => hAint j hj)
  -- bound on `∫ P`
  have hPbound : (∫ x in Set.Ioc (0 : ℝ) xNear, P x)
      ≤ 16 * B ^ 2 * CH * CW * data i := by
    rw [hPval]
    have hsum : (∑ j ∈ Finset.range i,
          (∫ x in Set.Ioc (0 : ℝ) xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2))
        ≤ (i : ℝ) * (CH * CW * data i) := by
      calc (∑ j ∈ Finset.range i,
            (∫ x in Set.Ioc (0 : ℝ) xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2))
          ≤ ∑ _j ∈ Finset.range i, (CH * CW * data i) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            rw [← intervalIntegral.integral_of_le xNear_pos.le]
            exact hAbnd j hj
        _ = (i : ℝ) * (CH * CW * data i) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
            (∫ x in Set.Ioc (0 : ℝ) xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2))
        ≤ (i : ℝ) * B ^ 2 * ((i : ℝ) * (CH * CW * data i)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 16 * B ^ 2 * CH * CW * data i := by
          have hi4' : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
          have hi2 : (i : ℝ) ^ 2 ≤ 16 := by nlinarith [hi4', hi1]
          have hnn : 0 ≤ B ^ 2 * CH * CW * data i := by positivity
          calc (i : ℝ) * B ^ 2 * ((i : ℝ) * (CH * CW * data i))
              = (i : ℝ) ^ 2 * (B ^ 2 * CH * CW * data i) := by ring
            _ ≤ 16 * (B ^ 2 * CH * CW * data i) := mul_le_mul_of_nonneg_right hi2 hnn
            _ = 16 * B ^ 2 * CH * CW * data i := by ring
  -- assembling the pieces
  have hfinal : (∫ θ in (0 : ℝ)..(Real.pi / 8),
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (16 * B ^ 2 + 1) * CH * CW * data i := by
    have hstepA : (∫ θ in (0 : ℝ)..(Real.pi / 8),
          (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = ∫ x in (0 : ℝ)..xNear,
            (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
      rw [← hcv]
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le xNear_pos.le] at hx
      simp only [Function.comp_apply]
      rw [nri_sin_two_thetaOf_Icc x hx]
    have hstepB : (∫ x in (0 : ℝ)..xNear,
          (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
            * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
        = ∫ x in Set.Ioc (0 : ℝ) xNear, Hx x := by
      have hR : (∫ x in Set.Ioc (0 : ℝ) xNear, Hx x)
          = ∫ x in Set.Ioo (0 : ℝ) xNear, Hx x := MeasureTheory.integral_Ioc_eq_integral_Ioo
      rw [intervalIntegral.integral_of_le xNear_pos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        hR]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
      intro x hx
      have h1 : Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)
          = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x :=
        (DthIter_sliceX i hsm_div hx).trans
          (nri_Gop_iter_eqOn i isOpen_Ioo (nri_sliceX_divSin_eqOn h) hx)
      have hHxunfold : Hx x = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := rfl
      show Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) = Hx x
      rw [hHxunfold, h1]
    rw [hstepA, hstepB]
    refine hmono.trans (hPbound.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ hdata_nonneg
    nlinarith [hBnn, sq_nonneg B, le_of_lt hCHpos, le_of_lt hCWpos]
  calc (∫ θ in (0 : ℝ)..(Real.pi / 8),
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (16 * B ^ 2 + 1) * CH * CW * data i := hfinal
    _ = (16 * B ^ 2 + 1) * CH * CW
          * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by rw [hdata_raw]

/-- **The near-region bound, with the data hypothesis at the level actually needed.**

This is `nearRegionLHS` with its hypothesis `∀ m ∈ Finset.Icc 1 4, IntegrableOn (Denγ m)`
*wakened* to `∀ m ∈ Finset.Icc 1 i` (the right-hand side already sums only over `m ≤ i`, and the
proof of `nearRegionLHS` applies its hypothesis only at levels `≤ i`).  The weakening matters: for
the slices `h_b = fun θ => DzIter b Φ z θ` with `b ≥ 1` only the data with `m + b ≤ 4` are
certified by `HkMem α 4 (pth Φ)`, while the assembly needs the bound at level `i ≤ 4 - b`, hence
only `m ≤ i`.

ROUTE.  The same as `nearRegionLHS` (`Submission/Work/FTS/H2/DivQ/nearRegionLHS.lean`), whose
proof body can be reused once its internal chain (`W_integrable`, `inversionNear`-applications,
`dom_integrable`) is re-run parametrically at the level `i` instead of uniformly at `4`: the
`bCoeff` sum runs over `j < i` and calls the helpers at level `j + 1 ≤ i`, and each helper consumes
`HonGam`/`hDenγ` only at levels `≤ j + 1`.  (Alternatively, re-prove it directly by the route of
`NOTES.md` §4.) -/
theorem nearRegionLHS_i :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        (∫ θ in (0 : ℝ)..(Real.pi / 8),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  -- the four instances of the variable-level inversion; a single constant is obtained by taking
  -- a maximum over the four levels
  obtain ⟨C₁, hC₁pos, hW₁⟩ := NRI.W_integrable_le 1 (by norm_num)
  obtain ⟨C₂, hC₂pos, hW₂⟩ := NRI.W_integrable_le 2 (by norm_num)
  obtain ⟨C₃, hC₃pos, hW₃⟩ := NRI.W_integrable_le 3 (by norm_num)
  obtain ⟨C₄, hC₄pos, hW₄⟩ := NRI.W_integrable_le 4 le_rfl
  have hle1 : C₁ ≤ max (max C₁ C₂) (max C₃ C₄) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hle2 : C₂ ≤ max (max C₁ C₂) (max C₃ C₄) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hle3 : C₃ ≤ max (max C₁ C₂) (max C₃ C₄) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hle4 : C₄ ≤ max (max C₁ C₂) (max C₃ C₄) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine nearRegionLHS_i_of_inversion ⟨max (max C₁ C₂) (max C₃ C₄),
    lt_max_of_lt_left (lt_max_of_lt_left hC₁pos), ?_⟩
  intro N hN α h hα0 hα1 hsm hDenη hDenγ m hm
  have hNcase : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 := by omega
  rcases hNcase with rfl | rfl | rfl | rfl | rfl
  · exfalso
    obtain ⟨hm1', hm0'⟩ := Finset.mem_Icc.mp hm
    omega
  · have h1 := hW₁ α h hα0 hα1 hsm hDenη hDenγ m hm
    exact ⟨h1.1, h1.2.trans (mul_le_mul_of_nonneg_right hle1 (NRI.nrSS_nonneg α h m))⟩
  · have h1 := hW₂ α h hα0 hα1 hsm hDenη hDenγ m hm
    exact ⟨h1.1, h1.2.trans (mul_le_mul_of_nonneg_right hle2 (NRI.nrSS_nonneg α h m))⟩
  · have h1 := hW₃ α h hα0 hα1 hsm hDenη hDenγ m hm
    exact ⟨h1.1, h1.2.trans (mul_le_mul_of_nonneg_right hle3 (NRI.nrSS_nonneg α h m))⟩
  · have h1 := hW₄ α h hα0 hα1 hsm hDenη hDenγ m hm
    exact ⟨h1.1, h1.2.trans (mul_le_mul_of_nonneg_right hle4 (NRI.nrSS_nonneg α h m))⟩

end

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf1d =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Topology Interval

/-! ## The radial self-pairing bound in one dimension

With `D = z ∂_z`, `w(z) = (1+z)²/z²` and `ρ = w²`, the estimate

`|∫_0^∞ ρ (DY) Y| ≤ 2 ∫_0^∞ ρ Y²`

is obtained from the exact identity (`s z = z ρ z = (1+z)^4/z^3`)

`(s Y²)' = s' Y² + 2 ρ (z Y') Y`

by integrating over `[ε, M] ⊂ (0,∞)`, where the boundary term `s Y²` vanishes along a
sequence `ε ↑ 0` (dyadic minimisers, `zHardy_seq_bot`) and `M → ∞`
(`zHardy_seq_top`), using `|s'| ≤ 4 ρ` pointwise. -/

noncomputable section

/-- The `L²`-weighted square `w(z)² Y(z)²` of a radial profile. -/
def selfH (Y : ℝ → ℝ) : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2

/-- The integrand `w(z)² (z Y'(z)) Y(z)` of the self-paired radial term. -/
def selfF (Y : ℝ → ℝ) : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)

/-- `w²` is continuous on any compact subinterval of `(0,∞)`. -/
theorem continuousOn_wSq {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z => (Work.Spaces.w z) ^ 2) (Set.Icc a b) := by
  have h1 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2) (Set.Icc a b) :=
    (continuousOn_const.add continuousOn_id).pow 2
  have h2 : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Icc a b) := continuousOn_id.pow 2
  have h3 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b) :=
    h1.div h2 (fun y hy => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hy.1)))
  have h4 : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Icc a b) := h3.pow 2
  unfold Work.Spaces.w
  exact h4

/-- `selfH Y` is continuous on any compact subinterval of `(0,∞)`. -/
theorem continuousOn_selfH {Y : ℝ → ℝ} (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0)) {a b : ℝ}
    (ha : 0 < a) : ContinuousOn (selfH Y) (Set.Icc a b) := by
  have h1 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Icc a b) := continuousOn_wSq ha
  have h2 : ContinuousOn (fun z : ℝ => (Y z) ^ 2) (Set.Icc a b) :=
    (hY.continuousOn.mono (fun y hy => lt_of_lt_of_le ha hy.1)).pow 2
  have h3 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Icc a b) :=
    h1.mul h2
  exact h3

theorem dzSelf1d {Y : ℝ → ℝ} (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0))
    (hF : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0))
    (hD : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
      (Set.Ioi 0)) :
    |∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)|
      ≤ 2 * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  change |∫ z in Set.Ioi 0, selfF Y z| ≤ 2 * ∫ z in Set.Ioi 0, selfH Y z
  have hHint : MeasureTheory.IntegrableOn (selfH Y) (Set.Ioi 0) := by
    change MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0)
    exact hF
  have hHnn : ∀ z, 0 ≤ selfH Y z := by
    intro z
    change 0 ≤ (Work.Spaces.w z) ^ 2 * (Y z) ^ 2
    positivity
  by_cases hint : MeasureTheory.IntegrableOn (selfF Y) (Set.Ioi 0)
  · obtain ⟨ε, M, hεpos, hεM, hε0, hMtop, hHε, hHM⟩ :=
      boundarySeqs (selfH Y) hHint hHnn
        (fun k => continuousOn_selfH hY (by positivity))
        (fun k => continuousOn_selfH hY (by positivity))
    have hL1 : Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), selfF Y z) atTop
        (𝓝 (∫ z in Set.Ioi 0, selfF Y z)) :=
      Work.FTS.EllipticEst.zHardy_tendsto_setIntegral_Ioc (selfF Y) hint hεpos hε0 hMtop
    have hL2 : Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
        (𝓝 (∫ z in Set.Ioi 0, selfH Y z)) :=
      Work.FTS.EllipticEst.zHardy_tendsto_setIntegral_Ioc (selfH Y) hHint hεpos hε0 hMtop
    have hk : ∀ k : ℕ, |∫ z in Set.Ioc (ε k) (M k), selfF Y z|
        ≤ (1 / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)
          + 2 * ∫ z in Set.Ioc (ε k) (M k), selfH Y z := by
      intro k
      have htb := truncBound (Y := Y) (a := ε k) (b := M k) hY (hεpos k) (hεM k)
      simp only [intervalIntegral.integral_of_le (hεM k)] at htb
      simpa only [selfH, selfF] using htb
    have hbound : Tendsto
        (fun k => (1 / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)
          + 2 * ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
        (𝓝 (2 * ∫ z in Set.Ioi 0, selfH Y z)) := by
      have hmid : Tendsto
          (fun k => (1 / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)) atTop (𝓝 0) := by
        have h := (hHM.add hHε).const_mul (1 / 2)
        simpa using h
      have h2 : Tendsto (fun k => 2 * ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
          (𝓝 (2 * ∫ z in Set.Ioi 0, selfH Y z)) := hL2.const_mul 2
      simpa using hmid.add h2
    exact le_of_tendsto_of_tendsto' hL1.abs hbound hk
  · rw [integral_undef hint, abs_zero]
    exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi (fun z _ => hHnn z))

end

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `thetaHardyA` : the angular weighted Hardy inequality in the open class

The target is

```
∃ C > 0, ∀ α ∈ (0,1], ∀ f, C¹ on (0,π/2) →
  ∫_{Iθ} f² sin(2θ)^{-(1-α/10)} ≤ C/α² ∫_{Iθ} (sin(2θ) f')² sin(2θ)^{-γ} + C/α f(π/4)²
```

with `γ = 1 + α/10` (`Work.Spaces.gam`).  Setting `β = α/10`, the two weights are
`sin(2θ)^{β-1}` on the left and `sin(2θ)^{1-β}` on `(f')²` on the right, i.e. exactly the
sharp `sin(2θ)`-weighted Hardy pair with the *interior* boundary term at `π/4`
(`Work.FTS.H2.Transport3Aux.sin_weight_hardy`), but the hypothesis on `f` is only `C¹` on the
*open* interval — no continuity of `f` or of `deriv f` at `0` or `π/2` is available, and the
left-hand side is not assumed integrable.

The route is the standard truncation one:

* on a compact subinterval `[δ, π/4]` the power-weight Hardy inequality
  `Work.FTS.StrongPersist.N6Trans.SixRoute.power_hardy_interval` (delegated, sibling module)
  applies; comparing `sin(2θ)` with `θ` by Jordan's inequality and using
  `(4/π)^{β-1}(4/β²)(π/4)^{β+1} = 4/β²(π/4)²`, `(4/π)^{β-1}(2/β)(π/4)^β = π/(2β)`
  turns it into the truncated `sin`-weighted bound;
* the truncated bounds are uniform in `δ`, the left-hand integrand is
  `IntegrableOn (0,π/4)` by the truncation principle
  `Work.FTS.EllSol.VthAux.traceAux.integrableOn_of_forall_Ioc_le`, and the inequality passes
  to the limit `δ → 0⁺` by the monotone convergence lemma
  `Work.FTS.StrongPersist.N6Trans.SixRoute.setIntegral_Ioc_le_of_uniform_bound` (delegated);
* the right half `(π/4, π/2)` is the same statement for the mirror `u ↦ f(π/2 - u)`
  (under which `sin 2θ` is invariant), transported back with
  `Work.FTS.H2.Transport3Aux.mirror_sq_sin_rpow`, `...mirror_deriv_sq_integral_weak` and
  `Work.FTS.EllSol.VthAux.traceAux.reflectIntegrableOn_iff`.

The constants: `4/β²(π/4)² = 25π²/α² ≤ 40000/α²` and `π/β = 10π/α ≤ 40000/α`, so `C = 40000`
works.
-/

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 2000000

/- ## The two truncated-Hardy inputs

These are the delegated lemmas `FTS/StrongPersist/N6Trans/SixRoute/power_hardy_interval` and
`FTS/StrongPersist/N6Trans/SixRoute/setIntegral_Ioc_le_of_uniform_bound`, imported above. -/

/-! ## Elementary pointwise facts -/

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` for `0 < θ < π/2`. -/
theorem sin_two_pos_of_lt_half {θ : ℝ} (h0 : 0 < θ)
    (h2 : θ < Real.pi / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- `HasDerivAt` for a `C¹` function on the open angular interval. -/
theorem hasDerivAt_of_contDiffOn_one {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : HasDerivAt f (deriv f θ) θ :=
  ((hsm.contDiffAt (Ioo_mem_nhds hθ.1 hθ.2)).differentiableAt_one).hasDerivAt

/-- The mirror of a `C¹` function on the open interval is `C¹`. -/
theorem contDiffOn_mirror_open {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 1 (fun u : ℝ => f (Real.pi / 2 - u)) (Set.Ioo 0 (Real.pi / 2)) :=
  hsm.comp ((contDiffOn_const (c := Real.pi / 2)).sub contDiffOn_id)
    (fun x hx => ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩)

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
end
